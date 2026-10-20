module

public import SKConstants.Completion.LW.CorrelatedProducts
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LW
open Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem localMGF_zero [IsProbabilityMeasure μ] {v radius : ℝ} (hv : 0 ≤ v) :
    LocalQuadraticMGF (fun _ : Ω => 0) μ v radius := by
  constructor
  · intro t _; simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => 1) μ)
  · intro t _
    simp only [mgf, mul_zero, Real.exp_zero, integral_const, probReal_univ, smul_eq_mul,
      one_mul]
    exact Real.one_le_exp (mul_nonneg hv (sq_nonneg t))

theorem localMGF_mono {X : Ω → ℝ} {v v' radius radius' : ℝ}
    (h : LocalQuadraticMGF X μ v radius) (hv : v ≤ v') (hr : radius' ≤ radius) :
    LocalQuadraticMGF X μ v' radius' := by
  exact ⟨fun t ht => h.integrable_exp_mul t (ht.trans hr), fun t ht =>
    (h.mgf_le t (ht.trans hr)).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hv (sq_nonneg t)))⟩

theorem localMGF_subconvex [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    {v radius : ℝ} (hv : 0 ≤ v)
    (h : ∀ i, LocalQuadraticMGF (X i) μ v radius) :
    LocalQuadraticMGF (fun ω => ∑ i, p i * X i ω) μ v radius := by
  classical
  have hdom (t : ℝ) (ω : Ω) :
      Real.exp (t * ∑ i, p i * X i ω) ≤
        (1 - ∑ i, p i) + ∑ i, p i * Real.exp (t * X i ω) := by
    have H := convexOn_exp.map_add_sum_le
      (t := Finset.univ) (w := p) (p := fun i => t * X i ω)
      (q := (0 : ℝ)) (v := 1-∑ i, p i)
      (fun i _ => hp i) (by ring) (fun _ _ => Set.mem_univ _)
      (sub_nonneg.mpr hs) (Set.mem_univ _)
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
      Finset.mul_sum, mul_left_comm t] using H
  have hInt (t : ℝ) (ht : |t| ≤ radius) :
      Integrable (fun ω => Real.exp (t * ∑ i, p i * X i ω)) μ := by
    apply ((integrable_const (1-∑ i, p i)).add
      (integrable_finset_sum Finset.univ (fun i _ =>
        ((h i).integrable_exp_mul t ht).const_mul (p i)))).mono'
    · exact (Real.continuous_exp.measurable.comp
        ((Finset.measurable_fun_sum _ (fun i _ => (hX i).const_mul _)).const_mul t)).aestronglyMeasurable
    · exact ae_of_all _ (fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply] using hdom t ω)
  refine ⟨hInt, ?_⟩
  intro t ht
  calc
    mgf (fun ω => ∑ i, p i * X i ω) μ t ≤
        ∫ ω, (1-∑ i, p i) + ∑ i, p i * Real.exp (t * X i ω) ∂μ :=
      integral_mono (hInt t ht) ((integrable_const _).add
        (integrable_finset_sum Finset.univ (fun i _ =>
          ((h i).integrable_exp_mul t ht).const_mul _))) (hdom t)
    _ = (1-∑ i, p i) + ∑ i, p i * mgf (X i) μ t := by
      rw [integral_add (integrable_const _) (integrable_finset_sum Finset.univ
        (fun i _ => ((h i).integrable_exp_mul t ht).const_mul _)),
        integral_finsetSum Finset.univ
          (fun i _ => ((h i).integrable_exp_mul t ht).const_mul _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
        integral_const_mul, mgf]
    _ ≤ (1-∑ i, p i) * Real.exp (v*t^2) + ∑ i, p i * Real.exp (v*t^2) := by
      apply add_le_add
      · exact le_mul_of_one_le_right (sub_nonneg.mpr hs)
          (Real.one_le_exp (mul_nonneg hv (sq_nonneg t)))
      · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          ((h i).mgf_le t ht) (hp i))
    _ = Real.exp (v*t^2) := by rw [← Finset.sum_mul]; ring

theorem localMGF_sum_of_budget [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) {C v radius : ℝ}
    (hC : 0 < C) (hs : ∑ i, c i ≤ C) (hv : 0 ≤ v)
    (h : ∀ i, LocalQuadraticMGF (X i) μ v radius) :
    LocalQuadraticMGF (fun ω => ∑ i, c i * X i ω) μ (C^2*v) (radius/C) := by
  have H := localMGF_subconvex X hX (fun i => c i / C)
    (fun i => div_nonneg (hc i) hC.le)
    (by rw [← Finset.sum_div]; exact (div_le_one hC).mpr hs) hv h
  have H' := H.const_mul hC
  convert H' using 1
  ext ω
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

end SKConstants.Completion.LW
