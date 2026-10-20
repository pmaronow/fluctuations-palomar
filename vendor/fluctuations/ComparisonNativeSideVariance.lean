module

public import ComparisonNativeCovarianceTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000

theorem physical_actual_bin_variance_le_square_column (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1)→Fin K) (x : ℕ→ℝ) {δ width : ℝ}
    (hδ : 0<δ) (hwidth : 2*δ≤width)
    (hx : ∀u : Fin K,x u.val<x (u.val+1)) :
    actualBinSideVariance n K steps q0 J unit x δ width≤
      ∑u : Fin K,physicalSelectedUnitEnergy n steps q0 J unit u*
        sideSquareColumn x δ width u.val := by
  have hpq : δ≤width-δ := by linarith
  have hL := physical_selected_weight_variance_integral_le_energy n steps ha q0 J unit
    (fun t u=>left 0 (x u.val) (x (u.val+1)) t) hpq (fun u=>by
      have ht := left_continuousOn (a:=0) (b:=width) hδ (hx u)
      exact ht.mono (by simpa only [zero_add] using (Icc_subset_Icc le_rfl (by linarith : width - δ ≤ width))))
  have hR := physical_selected_weight_variance_integral_le_energy n steps ha q0 J unit
    (fun t u=>right width (x u.val) (x (u.val+1)) t) hpq (fun u=>
      (right_continuousOn (a:=0) hδ (hx u)).mono (Icc_subset_Icc hδ.le le_rfl))
  unfold actualBinSideVariance selectedScoreVariance selectedLeftWeight selectedRightWeight
  exact (add_le_add hL hR).trans_eq (by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    unfold sideSquareColumn
    ring)

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem physical_actual_bin_variance_le_native_integral
    (n dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ→ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)))
    (unit : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)→Fin K)
    (x : ℕ→ℝ) {δ width : ℝ} (hstart : x 0=0) (hend : x K=width)
    (hδ : 0<δ) (hwidth : 2*δ≤width)
    (hx : ∀u : Fin K,x u.val<x (u.val+1))
    {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hleft : ∀i∈J,a≤comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 as i.val)) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    actualBinSideVariance (n+1) K (sampleClockSteps q 0 as) (q 0) J unit x δ width≤
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as J unit (fun u=>sideSquareColumn x δ width u.val) r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α as ho)+4*mesh/δ)/α.val.val a := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  have ht := physical_actual_bin_variance_le_square_column (n+1) K
    (sampleClockSteps q 0 as) (sampleClockSteps_ordered q _ ho) (q 0) J unit x hδ hwidth hx
  have hW := comparisonNativeWeightedUnitEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he hmesh hmesh0 J unit
    (fun u=>sideSquareColumn x δ width u.val)
    (fun u=>sideSquareColumn_nonneg x hwidth u.val)
    (show (0:ℝ)≤2/δ by positivity)
    (fun u=>sideSquareColumn_le_two_inv x K hstart hend hδ hwidth hx u)
    ha ha1 hleft
  convert ht.trans hW using 1 <;> ring

end
end OAI.SKFluctuations.LaplaceWindowFormalization
