module

public import SKConstants.SubGaussianSquares
public import SKConstants.ScalarProcessLagMGFLimit

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LM4

open Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem localMGF_of_centered_factorial [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {B : ℝ} (hX : Measurable X) (hB : 0 < B)
    (hPowers : ∀ p : ℕ, Integrable (fun ω => X ω ^ p) μ)
    (hMean : ∫ ω, X ω ∂μ = 0)
    (hMoments : ∀ p : ℕ, 2 ≤ p →
      (∫ ω, |X ω| ^ p ∂μ) ≤ (p.factorial : ℝ) * B ^ p) :
    LocalQuadraticMGF X μ (2 * B ^ 2) (1 / (2 * B)) := by
  apply localQuadraticMGF_of_factorial_moments hX (sq_nonneg B) hB hPowers hMean
  intro p hp
  have he : B ^ p = B ^ 2 * B ^ (p - 2) := by
    rw [← pow_add, Nat.add_sub_of_le hp]
  simpa only [he, mul_assoc] using hMoments p hp

theorem independent_sum_upper_of_localMGF {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {v r η : ℝ}
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (hRows : ∀ i, LocalQuadraticMGF (X i) μ v r)
    (hv : 0 < v) (hr : 0 < r) (hη : 0 < η) :
    μ.real {ω | (n : ℝ) * η ≤ ∑ i, X i ω} ≤
      Real.exp (-(n : ℝ) * min (η ^ 2 / (4 * v)) (r * η / 2)) := by
  have : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let t := min (η / (2 * v)) r
  have ht : 0 < t := lt_min (by positivity) hr
  have htr : t ≤ r := min_le_right _ _
  have htv : v * t ≤ η / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * v)).mp
      (show t ≤ η / (2 * v) from min_le_left _ _)
    nlinarith
  have hquad : -t * ((n : ℝ) * η) + ((n : ℝ) * v) * t ^ 2 ≤
      -(n : ℝ) * (t * η / 2) := by
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right htv ht.le) hnR.le
    nlinarith
  have he : t * η / 2 = min (η ^ 2 / (4 * v)) (r * η / 2) := by
    dsimp [t]
    rw [min_mul_of_nonneg _ _ hη.le, ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
    ring
  have hs := localQuadraticMGF_sum hIndep hMeas hRows
  simp only [Fintype.card_fin] at hs
  exact (localQuadraticMGF_upper hs ht.le htr).trans
    (Real.exp_le_exp.mpr (by simpa only [he] using hquad))

theorem independent_sum_upper_of_factorial_moments [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {v B η : ℝ}
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (hv : 0 < v) (hB : 0 < B) (hη : 0 < η)
    (hPowers : ∀ i p, Integrable (fun ω => X i ω ^ p) μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hMoments : ∀ i p, 2 ≤ p → (∫ ω, |X i ω| ^ p ∂μ) ≤
      (p.factorial : ℝ) * v * B ^ (p - 2)) :
    μ.real {ω | (n : ℝ) * η ≤ ∑ i, X i ω} ≤
      Real.exp (-(n : ℝ) * min (η ^ 2 / (8 * v)) (η / (4 * B))) := by
  have hRows (i : Fin n) := localQuadraticMGF_of_factorial_moments
    (hMeas i) hv.le hB (hPowers i) (hMean i) (hMoments i)
  simpa only [show 4 * (2 * v) = 8 * v by ring,
    show (1 / (2 * B)) * η / 2 = η / (4 * B) by ring] using
    independent_sum_upper_of_localMGF hn hIndep hMeas hRows
      (by positivity) (by positivity) hη

theorem independent_sum_abs_of_factorial_moments [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {v B η : ℝ}
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (hv : 0 < v) (hB : 0 < B) (hη : 0 < η)
    (hPowers : ∀ i p, Integrable (fun ω => X i ω ^ p) μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hMoments : ∀ i p, 2 ≤ p → (∫ ω, |X i ω| ^ p ∂μ) ≤
      (p.factorial : ℝ) * v * B ^ (p - 2)) :
    μ.real {ω | (n : ℝ) * η ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(n : ℝ) * min (η ^ 2 / (8 * v)) (η / (4 * B))) := by
  have hRows (i : Fin n) := localQuadraticMGF_of_factorial_moments
    (hMeas i) hv.le hB (hPowers i) (hMean i) (hMoments i)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hevent : {ω | (n : ℝ) * η ≤ |∑ i, X i ω|} =
      {ω | η ≤ |(∑ i, X i ω) / (n : ℝ)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hnR]
    rw [le_div_iff₀ hnR, mul_comm η]
  rw [hevent]
  simpa only [show 4 * (2 * v) = 8 * v by ring,
    show (1 / (2 * B)) * η / 2 = η / (4 * B) by ring] using
    independent_average_bernstein hn hIndep hMeas hRows
      (by positivity) (by positivity) hη

theorem centered_localMGF_of_raw_factorial [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {A : ℝ} (hY : Measurable Y) (hA : 0 < A)
    (hInt : ∀ p, Integrable (fun ω => |Y ω| ^ p) μ)
    (hMom : ∀ p, (∫ ω, |Y ω| ^ p ∂μ) ≤ (p.factorial : ℝ) * A ^ p) :
    LocalQuadraticMGF (centeredObservable μ Y) μ (8 * A ^ 2) (1 / (4 * A)) := by
  have hc := factorial_moments_centered μ Y hY A hA hInt hMom
  have hI : Integrable Y μ := by
    exact (integrable_norm_iff hY.aestronglyMeasurable).mp (by simpa using hInt 1)
  have hm : ∫ ω, centeredObservable μ Y ω ∂μ = 0 := by
    unfold centeredObservable
    rw [integral_sub hI (integrable_const _)]
    simp
  convert localMGF_of_centered_factorial (X := centeredObservable μ Y)
    (hY.sub_const _) (by positivity : 0 < 2 * A)
    hc.1 hm (fun p hp => hc.2 p (by omega)) using 1 <;> ring

theorem iid_sum_upper_of_localMGF (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v r η : ℝ} (hX : Measurable X)
    (hRow : LocalQuadraticMGF X μ v r) (hv : 0 < v) (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) (hη : 0 < η) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | (n : ℝ) * η ≤ ∑ i : Fin n, X (ω i)} ≤
      Real.exp (-(n : ℝ) * min (η ^ 2 / (4 * v)) (r * η / 2)) := by
  apply independent_sum_upper_of_localMGF hn
    (iIndepFun_pi (fun _ : Fin n => hX.aemeasurable))
    (fun i => hX.comp (measurable_pi_apply i))
    (fun i => hRow.comp_hasLaw (measurePreserving_eval (fun _ : Fin n => μ) i).hasLaw)
    hv hr hη

theorem iid_sum_abs_of_localMGF (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v r η : ℝ} (hX : Measurable X)
    (hRow : LocalQuadraticMGF X μ v r) (hv : 0 < v) (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) (hη : 0 < η) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | (n : ℝ) * η ≤ |∑ i : Fin n, X (ω i)|} ≤
      2 * Real.exp (-(n : ℝ) * min (η ^ 2 / (4 * v)) (r * η / 2)) := by
  have hRows (i : Fin n) :=
    hRow.comp_hasLaw (measurePreserving_eval (fun _ : Fin n => μ) i).hasLaw
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hevent : {ω : Fin n → Ω | (n : ℝ) * η ≤ |∑ i : Fin n, X (ω i)|} =
      {ω | η ≤ |(∑ i : Fin n, X (ω i)) / (n : ℝ)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hnR]
    rw [le_div_iff₀ hnR, mul_comm η]
  rw [hevent]
  exact independent_average_bernstein hn
    (iIndepFun_pi (fun _ : Fin n => hX.aemeasurable))
    (fun i => hX.comp (measurable_pi_apply i)) hRows hv hr hη

end SKConstants.Completion.LM4
