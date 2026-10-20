module

public import ComparisonActualHighWallThetaZeroTraceLimitPositiveOrigin
public import ComparisonNativeRadiusTraceVariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

theorem plain_radius_trace_eventually_first
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z : ℝ} (hlo : a.data.rmin < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj : ℕ in atTop,(∫_r in A,(1:ℝ)∂m.radiusMeasure dphys e (as j) (ho j))  ≤ 
      (a.radiusS z-a.radiusS lo)/F+epsilon := by
  dsimp only
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
  have hF : 0 < F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d (a.hlam) z))
  have hSm : MonotoneOn a.radiusS (Icc lo z):=
    a.radius_moments.1.mono (Icc_subset_Icc hlo.le hz)
  have HFTC:=reciprocal_density_derivative_budget (weight:=fun _ : ℝ=>(1:ℝ)) hloz hSm
    (a.radiusS_absolutelyContinuous_positive_origin dphys e hlo.le hloz hz) hA
    (hAD.trans Ioo_subset_Icc_self) measurable_const.aestronglyMeasurable
    (by norm_num : (0:ℝ)  ≤  1) (fun _ _=>by norm_num) (fun _ _=>by norm_num)
  have Htrace:=a.radius_trace_boundedWeight_positive_origin hN hlog hnd dphys e as ho hend mesh hmesh hmesh0
    hlim hlo.le hloz hz hA hAD (fun _=>1) measurable_const.aestronglyMeasurable 1
    (fun _ _=>by norm_num) (fun _ _=>by norm_num) hepsilon
  filter_upwards [Htrace] with j hj
  have HB:=div_le_div_of_nonneg_right HFTC hF.le
  exact hj.trans (add_le_add (by simpa only [one_mul] using HB) le_rfl)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
