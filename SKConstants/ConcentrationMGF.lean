module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic

public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SKConstants.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

structure LocalQuadraticMGF (X : Ω → ℝ) (μ : Measure Ω) (v radius : ℝ) : Prop where
  integrable_exp_mul : ∀ t : ℝ, |t| ≤ radius →
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, |t| ≤ radius → mgf X μ t ≤ Real.exp (v * t ^ 2)

theorem LocalQuadraticMGF.neg {X : Ω → ℝ} {v radius : ℝ}
    (h : LocalQuadraticMGF X μ v radius) :
    LocalQuadraticMGF (fun ω ↦ -X ω) μ v radius where
  integrable_exp_mul t ht := by simpa using h.integrable_exp_mul (-t) (by simpa using ht)
  mgf_le t ht := by simpa [mgf] using h.mgf_le (-t) (by simpa using ht)

theorem localQuadraticMGF_sum {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} {v radius : ℝ}
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (hRows : ∀ i, LocalQuadraticMGF (X i) μ v radius) :
    LocalQuadraticMGF (fun ω ↦ ∑ i, X i ω) μ ((Fintype.card ι : ℝ) * v) radius := by
  classical
  have : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  constructor
  · intro t ht
    simpa only [Finset.sum_apply] using
      hIndep.integrable_exp_mul_sum hMeas
        (s := Finset.univ) (fun i _ ↦ (hRows i).integrable_exp_mul t ht)
  · intro t ht
    calc
      mgf (fun ω ↦ ∑ i, X i ω) μ t
          = ∏ i, mgf (X i) μ t := by
        convert hIndep.mgf_sum hMeas Finset.univ (t := t) using 1
        congr 1
        ext ω
        simp only [Finset.sum_apply]
      _ ≤ ∏ _i : ι, Real.exp (v * t ^ 2) := by
        exact Finset.prod_le_prod₀ (fun i _ ↦ mgf_nonneg)
          (fun i _ ↦ (hRows i).mgf_le t ht)
      _ = Real.exp (((Fintype.card ι : ℝ) * v) * t ^ 2) := by
        simp only [Finset.prod_const, Finset.card_univ]
        rw [← Real.exp_nat_mul]
        congr 1
        ring

theorem localQuadraticMGF_upper [IsFiniteMeasure μ]
    {X : Ω → ℝ} {v radius t u : ℝ}
    (h : LocalQuadraticMGF X μ v radius) (ht : 0 ≤ t) (htr : t ≤ radius) :
    μ.real {ω | u ≤ X ω} ≤ Real.exp (-t * u + v * t ^ 2) := by
  have hat : |t| ≤ radius := by rwa [abs_of_nonneg ht]
  calc
    μ.real {ω | u ≤ X ω}
        ≤ Real.exp (-t * u) * mgf X μ t :=
      measure_ge_le_exp_mul_mgf u ht (h.integrable_exp_mul t hat)
    _ ≤ Real.exp (-t * u) * Real.exp (v * t ^ 2) := by
      gcongr
      exact h.mgf_le t hat
    _ = Real.exp (-t * u + v * t ^ 2) := (Real.exp_add _ _).symm

theorem localQuadraticMGF_two_sided [IsFiniteMeasure μ]
    {X : Ω → ℝ} {v radius u : ℝ}
    (h : LocalQuadraticMGF X μ v radius)
    (hv : 0 < v) (hr : 0 < radius) (hu : 0 < u) :
    μ.real {ω | u ≤ |X ω|} ≤
      2 * Real.exp (-min (u ^ 2 / (4 * v)) (radius * u / 2)) := by
  let t := min (u / (2 * v)) radius
  have ht : 0 < t := lt_min (by positivity) hr
  have htr : t ≤ radius := min_le_right _ _
  have htu : t ≤ u / (2 * v) := min_le_left _ _
  have hvt : v * t ≤ u / 2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * v)).mp htu
    nlinarith
  have hquadratic : -t * u + v * t ^ 2 ≤ -t * u / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hvt ht.le]
  have heq : t * u / 2 = min (u ^ 2 / (4 * v)) (radius * u / 2) := by
    dsimp [t]
    rw [min_mul_of_nonneg _ _ hu.le]
    rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
    norm_num
  have hup := (localQuadraticMGF_upper (u := u) h ht.le htr).trans
    (Real.exp_le_exp.mpr hquadratic)
  have hdown := (localQuadraticMGF_upper (u := u) h.neg ht.le htr).trans
    (Real.exp_le_exp.mpr hquadratic)
  have hset : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω})
        ≤ μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-t * u / 2) := by linarith
    _ = 2 * Real.exp (-min (u ^ 2 / (4 * v)) (radius * u / 2)) := by
      rw [neg_mul, neg_div, heq]

theorem independent_average_bernstein {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {v radius η : ℝ}
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (hRows : ∀ i, LocalQuadraticMGF (X i) μ v radius)
    (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η) :
    μ.real {ω | η ≤ |(∑ i, X i ω) / (n : ℝ)|} ≤
      2 * Real.exp (-(n : ℝ) * min (η ^ 2 / (4 * v)) (radius * η / 2)) := by
  classical
  have : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs := localQuadraticMGF_sum hIndep hMeas hRows
  simp only [Fintype.card_fin] at hs
  have ht := localQuadraticMGF_two_sided hs (mul_pos hnr hv) hr (mul_pos hnr hη)
  have hevent : {ω | η ≤ |(∑ i, X i ω) / (n : ℝ)|} =
      {ω | (n : ℝ) * η ≤ |∑ i, X i ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hnr]
    exact (le_div_iff₀ hnr).trans (by rw [mul_comm])
  have hmin : min (((n : ℝ) * η) ^ 2 / (4 * ((n : ℝ) * v)))
      (radius * ((n : ℝ) * η) / 2) =
      (n : ℝ) * min (η ^ 2 / (4 * v)) (radius * η / 2) := by
    calc
      _ = min ((n : ℝ) * (η ^ 2 / (4 * v)))
          ((n : ℝ) * (radius * η / 2)) := by
        congr 1 <;> field_simp
      _ = _ := (mul_min_of_nonneg _ _ hnr.le).symm
  rw [hevent]
  simpa only [hmin, neg_mul] using ht

theorem independent_mesh_average {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {C c h η : ℝ}
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (hRows : ∀ i, LocalQuadraticMGF (X i) μ (C * h) (c / h))
    (hC : 0 < C) (hc : 0 < c) (hh : 0 < h)
    (hη : 0 < η) (hηsmall : η ≤ 2 * C * c) :
    μ.real {ω | η ≤ |(∑ i, X i ω) / (n : ℝ)|} ≤
      2 * Real.exp (-(n : ℝ) * η ^ 2 / (4 * C * h)) := by
  have hmin : η ^ 2 / (4 * (C * h)) ≤ (c / h) * η / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (C * h))).mpr
    have heq : (c / h) * η / 2 * (4 * (C * h)) = 2 * C * c * η := by
      field_simp
      ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hηsmall hη.le]
  have ht := independent_average_bernstein hn hIndep hMeas hRows
    (mul_pos hC hh) (div_pos hc hh) hη
  rw [min_eq_left hmin] at ht
  simpa only [mul_div_assoc, mul_assoc] using ht

theorem LocalQuadraticMGF.const_mul {X : Ω → ℝ} {v radius a : ℝ}
    (h : LocalQuadraticMGF X μ v radius) (ha : 0 < a) :
    LocalQuadraticMGF (fun ω ↦ a * X ω) μ (a ^ 2 * v) (radius / a) where
  integrable_exp_mul t ht := by
    have hta : |t * a| ≤ radius := by
      rw [abs_mul, abs_of_pos ha]
      exact (le_div_iff₀ ha).mp ht
    simpa [mul_assoc, mul_comm, mul_left_comm] using h.integrable_exp_mul (t * a) hta
  mgf_le t ht := by
    have hta : |t * a| ≤ radius := by
      rw [abs_mul, abs_of_pos ha]
      exact (le_div_iff₀ ha).mp ht
    calc
      mgf (fun ω ↦ a * X ω) μ t = mgf X μ (t * a) := by
        simp only [mgf, mul_assoc]
      _ ≤ Real.exp (v * (t * a) ^ 2) := h.mgf_le (t * a) hta
      _ = Real.exp ((a ^ 2 * v) * t ^ 2) := by congr 1; ring

theorem localQuadraticMGF_of_bounded_variance [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {B v : ℝ} (hMeas : Measurable X) (hB : 0 < B)
    (hBound : ∀ᵐ ω ∂μ, |X ω| ≤ B) (hMean : ∫ ω, X ω ∂μ = 0)
    (hVariance : ∫ ω, (X ω) ^ 2 ∂μ ≤ v) :
    LocalQuadraticMGF X μ v (1 / B) := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-B) B := by
    filter_upwards [hBound] with ω hω
    exact abs_le.mp hω
  have hIntX : Integrable X μ :=
    Integrable.of_bound hMeas.aestronglyMeasurable B (by simpa [Real.norm_eq_abs] using hBound)
  have hIntSq : Integrable (fun ω ↦ (X ω) ^ 2) μ := by
    refine Integrable.of_bound (by fun_prop) (B ^ 2) ?_
    filter_upwards [hBound] with ω hω
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (X ω)) hω 2
  constructor
  · intro t _
    exact integrable_exp_mul_of_mem_Icc hMeas.aemeasurable hIcc
  · intro t ht
    have htb : |t| * B ≤ 1 := (le_div_iff₀ hB).mp ht
    have hTaylor : ∀ᵐ ω ∂μ,
        Real.exp (t * X ω) ≤ 1 + t * X ω + t ^ 2 * (X ω) ^ 2 := by
      filter_upwards [hBound] with ω hω
      have htx : |t * X ω| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans htb
      have hr := Real.abs_exp_sub_one_sub_id_le htx
      have hs := le_abs_self (Real.exp (t * X ω) - 1 - t * X ω)
      rw [mul_pow] at hr
      linarith
    have hIntExp : Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
      integrable_exp_mul_of_mem_Icc hMeas.aemeasurable hIcc
    have hIntFirst : Integrable (fun ω ↦ 1 + t * X ω) μ :=
      (integrable_const 1).add (hIntX.const_mul t)
    have hIntTaylor : Integrable (fun ω ↦ 1 + t * X ω + t ^ 2 * (X ω) ^ 2) μ :=
      hIntFirst.add (hIntSq.const_mul (t ^ 2))
    calc
      mgf X μ t ≤ ∫ ω, 1 + t * X ω + t ^ 2 * (X ω) ^ 2 ∂μ :=
        integral_mono_ae hIntExp hIntTaylor hTaylor
      _ = 1 + t ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) := by
        rw [integral_add hIntFirst (hIntSq.const_mul (t ^ 2)),
          integral_add (integrable_const 1) (hIntX.const_mul t),
          integral_const_mul, integral_const_mul, hMean]
        simp
      _ ≤ 1 + t ^ 2 * v := by gcongr
      _ ≤ Real.exp (v * t ^ 2) := by
        simpa [mul_comm, add_comm] using Real.add_one_le_exp (v * t ^ 2)

end SKConstants.Concentration
