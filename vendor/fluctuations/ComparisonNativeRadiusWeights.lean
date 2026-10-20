module

public import ComparisonNativeRadiusTraceVariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

def comparisonRadiusMassWeight (R α : ℝ→ℝ) (A : Set ℝ) (x kmin : ℝ) : ℝ→ℝ :=
  fun u=>if R u∈A then 1/(x*max kmin (deriv α (R u))) else 0

theorem comparisonRadiusMassWeight_bounds (R α : ℝ→ℝ) (A : Set ℝ)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (u : ℝ) :
    comparisonRadiusMassWeight R α A x kmin u ∈ Icc (0:ℝ) (1/(x*kmin)) := by
  unfold comparisonRadiusMassWeight
  split_ifs
  · have hm : 0 < max kmin (deriv α (R u)) := hkmin.trans_le (le_max_left _ _)
    exact ⟨div_nonneg zero_le_one (mul_nonneg hx.le hm.le),
      one_div_le_one_div_of_le (mul_pos hx hkmin)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hx.le)⟩
  · exact ⟨le_rfl,by positivity⟩

theorem comparisonRadiusMassWeight_measurable (R α : ℝ→ℝ) (hR : Measurable R)
    {A : Set ℝ} (hA : MeasurableSet A) (x kmin : ℝ) :
    Measurable (comparisonRadiusMassWeight R α A x kmin) := by
  apply Measurable.ite (hA.preimage hR)
  · exact measurable_const.div (measurable_const.mul
      (measurable_const.max ((stronglyMeasurable_deriv α).measurable.comp hR)))
  · exact measurable_const

theorem comparisonRadiusMassWeight_memLp_two (R α : ℝ→ℝ) (hR : Measurable R)
    {A : Set ℝ} (hA : MeasurableSet A) {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) :
    MemLp (comparisonRadiusMassWeight R α A x kmin) 2 (volume.restrict (Ioc (0:ℝ) 1)) :=
  memLp_of_bounded (Eventually.of_forall (comparisonRadiusMassWeight_bounds R α A hx hkmin))
    (comparisonRadiusMassWeight_measurable R α hR hA x kmin).aestronglyMeasurable 2

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

include hk hm hM in
theorem comparison_inverse_density_floor_ae (α : inverseIntegralConstraints 0 0 k M) :
    ∀ᵐ r, r∈Icc (0:ℝ) 1→k r ≤ deriv α.val.val r := by
  exact (lipschitz_ae_deriv_lower_iff zero_le_one
    (inverseIntegralConstraints_lipschitz hm hM α.property) hk).mpr
      (fun r hr s hs hrs=>(α.property.2.2 r hr s hs hrs).1)

theorem comparisonRadiusMassWeight_square_pullback
    (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Icc (0:ℝ) 1)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin ≤ k r) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      deriv α.val.val r*(comparisonRadiusMassWeight R α.val.val A x kmin (α.val.val r))^2=
        A.indicator (comparisonReciprocalDensityWeight α.val.val x kmin) r := by
  dsimp only
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (comparison_inverse_density_floor_ae hk hm hM α)] with r hr hd
  have hinv := comparisonSweepQuantile_inverse hc hk hkc hm hM α hr
  unfold comparisonRadiusMassWeight
  rw [hinv]
  by_cases hrA : r∈A
  · rw [ite_eq_left hrA,indicator_of_mem hrA]
    have hder : kmin ≤ deriv α.val.val r := (hfloor r hrA).trans (hd hr)
    have hp : 0 < deriv α.val.val r := hkmin.trans_le hder
    unfold comparisonReciprocalDensityWeight
    rw [max_eq_right hder]
    field_simp [ne_of_gt hp,hx.ne']
  · simp only [hrA,ite_false,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,indicator_of_notMem hrA]

theorem comparisonRadiusMassWeight_linear_pullback
    (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Icc (0:ℝ) 1)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin ≤ k r) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      deriv α.val.val r*comparisonRadiusMassWeight R α.val.val A x kmin (α.val.val r)=
        A.indicator (fun _ : ℝ=>1/x) r := by
  dsimp only
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (comparison_inverse_density_floor_ae hk hm hM α)] with r hr hd
  have hinv := comparisonSweepQuantile_inverse hc hk hkc hm hM α hr
  unfold comparisonRadiusMassWeight
  rw [hinv]
  by_cases hrA : r∈A
  · rw [ite_eq_left hrA,indicator_of_mem hrA]
    have hder : kmin ≤ deriv α.val.val r := (hfloor r hrA).trans (hd hr)
    have hp : 0 < deriv α.val.val r := hkmin.trans_le hder
    rw [max_eq_right hder]
    field_simp [ne_of_gt hp,hx.ne']
  · simp only [hrA,ite_false,mul_zero,indicator_of_notMem hrA]

end
end OAI.SKFluctuations.LaplaceWindowFormalization
