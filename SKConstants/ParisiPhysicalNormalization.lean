module
public import SKConstants.ParisiContinuumEquilibrium
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def parisiPhysicalOrderLaw (β : ℝ) (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  (μ : Measure ℝ).map (fun q => β^2 * q)

instance parisiPhysicalOrderLaw_isProbability (β : ℝ) (μ : ProbabilityMeasure ℝ) :
    IsProbabilityMeasure (parisiPhysicalOrderLaw β μ) := by
  unfold parisiPhysicalOrderLaw
  infer_instance

theorem parisiPhysicalOrderLaw_cdf (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (v : ℝ) :
    cdf (parisiPhysicalOrderLaw β μ) v = cdf (μ : Measure ℝ) (v / β^2) := by
  rw [cdf_eq_real, cdf_eq_real]
  unfold Measure.real parisiPhysicalOrderLaw
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext q
  change β^2*q ≤ v ↔ q ≤ v/β^2
  simpa only [mul_comm] using (le_div_iff₀ (sq_pos_of_ne_zero hβ)).symm

def parisiPhysicalValue (β : ℝ) (μ : ProbabilityMeasure ℝ) (v : ℝ) : ℝ → ℝ :=
  parisiCDFValue β (cdf (μ : Measure ℝ)) (v / β^2)
    (Real.toNNReal (1 - v / β^2))

lemma parisiPhysicalTime_mem (β : ℝ) (hβ : β ≠ 0) (v : ℝ)
    (hv : v ∈ Icc 0 (β^2)) : v / β^2 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg hv.1 (sq_nonneg β)
  · exact (div_le_one (sq_pos_of_ne_zero hβ)).mpr hv.2

theorem parisiPhysicalValue_spatial_derivatives (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (v : ℝ) (hv : v ∈ Icc 0 (β^2)) :
    (∀ x, HasDerivAt (parisiPhysicalValue β μ v)
      (SKConstantsOAI.SK.Analytic.scalarCDFGradient β (cdf (μ : Measure ℝ)) (v / β^2)
        (Real.toNNReal (1-v/β^2)) x) x) ∧
    (∀ x, HasDerivAt (SKConstantsOAI.SK.Analytic.scalarCDFGradient β (cdf (μ : Measure ℝ))
        (v / β^2) (Real.toNNReal (1-v/β^2)))
      (SKConstantsOAI.SK.Analytic.scalarCDFHessian β (cdf (μ : Measure ℝ)) (v / β^2)
        (Real.toNNReal (1-v/β^2)) x) x) ∧
    (∀ x, |SKConstantsOAI.SK.Analytic.scalarCDFGradient β (cdf (μ : Measure ℝ)) (v / β^2)
        (Real.toNNReal (1-v/β^2)) x| ≤ 1 ∧
      0 ≤ SKConstantsOAI.SK.Analytic.scalarCDFHessian β (cdf (μ : Measure ℝ)) (v / β^2)
        (Real.toNNReal (1-v/β^2)) x ∧
      SKConstantsOAI.SK.Analytic.scalarCDFHessian β (cdf (μ : Measure ℝ)) (v / β^2)
        (Real.toNNReal (1-v/β^2)) x ≤
        1 - (SKConstantsOAI.SK.Analytic.scalarCDFGradient β (cdf (μ : Measure ℝ)) (v / β^2)
          (Real.toNNReal (1-v/β^2)) x)^2) := by
  have hq := parisiPhysicalTime_mem β hβ v hv
  apply parisiCDFValue_spatial_derivatives β (cdf (μ : Measure ℝ))
    (fun s => ⟨cdf_nonneg _ s, cdf_le_one _ s⟩) (cdf (μ : Measure ℝ)).mono
  rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
  linarith [hq.1]

theorem parisi_physical_penalty_eq (β : ℝ) (hβ : β ≠ 0) (α : ℝ → ℝ) :
    (1 / (2 * β^2)) * (∫ v in (0 : ℝ)..β^2, v * α (v / β^2)) =
      (β^2 / 2) * ∫ q in (0 : ℝ)..1, q * α q := by
  have hb : β^2 ≠ 0 := pow_ne_zero 2 hβ
  have hf : (fun v => v * α (v / β^2)) =
      fun v => β^2 * ((v / β^2) * α (v / β^2)) := by
    funext v
    field_simp
  rw [hf, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun q => q * α q) hb]
  simp only [zero_div, div_self hb, smul_eq_mul]
  field_simp

theorem parisiContinuumFunctional_eq_physical (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) :
    parisiContinuumFunctional β (cdf (μ : Measure ℝ)) =
      parisiPhysicalValue β μ 0 0 -
        (1 / (2 * β^2)) * (∫ v in (0 : ℝ)..β^2,
          v * cdf (parisiPhysicalOrderLaw β μ) v) := by
  simp only [parisiPhysicalValue, zero_div, sub_zero, Real.toNNReal_one]
  simp_rw [parisiPhysicalOrderLaw_cdf β hβ μ]
  rw [parisi_physical_penalty_eq β hβ]
  unfold parisiContinuumFunctional
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem parisiPhysicalValue_at_cdf_one (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (v : ℝ) (hv : v ∈ Icc 0 (β^2))
    (hcut : cdf (μ : Measure ℝ) (v / β^2) = 1) :
    parisiPhysicalValue β μ v =
      fun y => Real.log (2 * Real.cosh y) + (β^2 - v) / 2 := by
  let q : ℝ := v / β^2
  let t : ℝ≥0 := Real.toNNReal (1-q)
  have hq := parisiPhysicalTime_mem β hβ v hv
  have ht1 : t ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hq.1]
  have ht : (t : ℝ) = 1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)
  have hm : SKConstantsOAI.SK.Analytic.TimeChainModels (cdf (μ : Measure ℝ)) q [(1,t)] := by
    constructor
    · intro z hz
      exact le_antisymm (cdf_le_one _ _) (by
        rw [← hcut]
        exact (cdf (μ : Measure ℝ)).mono hz.1)
    · trivial
  funext y
  have H := SKConstantsOAI.SK.Analytic.scalarCDFOperator_eq_chain
    SKConstantsOAI.SK.Analytic.scalarSpinTerminal_regular SKConstantsOAI.SK.Analytic.scalarSpinTerminal_lipschitz
    β (fun z => ⟨cdf_nonneg (μ : Measure ℝ) z, cdf_le_one _ z⟩)
    (cdf (μ : Measure ℝ)).mono [(1,t)]
    (by intro p hp; simp only [List.mem_singleton] at hp; subst p; exact ⟨zero_le_one,le_rfl⟩)
    q t ht1 (by simp only [SKConstantsOAI.SK.Analytic.chainDuration, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]) hm y
  change SKConstantsOAI.SK.Analytic.scalarCDFValue β (cdf (μ : Measure ℝ)) q t y = _ at H
  simp only [SKConstantsOAI.SK.Analytic.scalarTimeChain, SKConstantsOAI.SK.Analytic.scalarTimeStep,
    SKConstantsOAI.SK.Analytic.scalarStep_one_spin, SKConstantsOAI.SK.Analytic.scalarSpinTerminal] at H
  rw [parisiPhysicalValue, parisiCDFValue_eq_upstream]
  change SKConstantsOAI.SK.Analytic.scalarCDFValue β (cdf (μ : Measure ℝ)) q t y = _
  rw [H]
  congr 1
  rw [mul_pow, Real.sq_sqrt t.coe_nonneg, ht]
  dsimp [q]
  field_simp

theorem sk_expected_pressure_le_physicalParisi (n : ℕ) (hn : 0 < n)
    (β : ℝ) (hβ : β ≠ 0) :
    (∫ W, Real.log (gibbsPartition β W) ∂skDisorderLaw n) / (n : ℝ) ≤
      parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 -
        (1 / (2 * β^2)) * (∫ v in (0 : ℝ)..β^2,
          v * cdf (parisiPhysicalOrderLaw β (parisiEquilibriumMeasure β)) v) := by
  rw [← parisiContinuumFunctional_eq_physical β hβ]
  exact sk_expected_pressure_le_parisiEquilibrium n hn β

end SKConstants
