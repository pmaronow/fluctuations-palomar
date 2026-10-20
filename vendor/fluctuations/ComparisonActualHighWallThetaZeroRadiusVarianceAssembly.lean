module

public import ComparisonActualHighWallThetaZeroRadiusVarianceFirstNext
public import ComparisonActualHighWallThetaZeroRadiusReciprocalFirstNext
public import ComparisonActualHighWallThetaZeroRadiusCovarianceFirstNext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

theorem reciprocal_radius_trace_eventually
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z x kmin : ℝ} (hlo : a.data.rmin < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (hx : 0 < x) (hkmin : 0 < kmin) {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,comparisonReciprocalDensityWeight a.alpha.val.val x kmin r
        ∂m.radiusMeasure dphys e (as j) (ho j))  ≤ 
          (a.radiusS z-a.radiusS lo)/(x^2*kmin*F)+epsilon := by
  exact a.reciprocal_radius_trace_eventually_first hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim hlo hloz hz hx hkmin hA hAD hepsilon

theorem plain_radius_trace_eventually
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
  exact a.plain_radius_trace_eventually_first hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim hlo hloz hz hA hAD hepsilon

theorem original_radius_variance_eventually
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z x kmin : ℝ} (hlo : a.data.rmin < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (hx : 0 < x) (hkmin : 0 < kmin) {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    (hfloor : ∀r∈A,kmin  ≤  a.data.k r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let f:=comparisonRadiusMassWeight m.R a.alpha.val.val A x kmin
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj : ℕ in atTop,
      let steps:=sampleClockSteps m.q 0 (as j)
      let w:=comparisonOriginalRadiusWeights m.q (as j) f
      variance (fun p=>(physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
        (spinSource (n+1)) steps 0 w p.1 p.2).1)
        (rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (m.q 0) steps)  ≤ 
          4*(a.radiusS z-a.radiusS lo)/(a.alpha.val.val lo*x^2*kmin*F)+epsilon := by
  exact a.original_radius_variance_eventually_first hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hlo hloz hz hx hkmin hA hAD hfloor hepsilon

theorem original_radius_covariance_eventually
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z kmin : ℝ} (hlo : a.data.rmin < lo) (hloz : lo ≤ z) (hz : z ≤ 1)
    (hkmin : 0 < kmin) {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    (hfloor : ∀r∈A,kmin ≤ a.data.k r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let f:=comparisonRadiusMassWeight m.R a.alpha.val.val A 1 kmin
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj : ℕ in atTop,
      let steps:=sampleClockSteps m.q 0 (as j)
      let w:=comparisonOriginalRadiusWeights m.q (as j) f
      (∑i,pathMassDifferences steps 0 i*w i*actualCutCovarianceEnergy (n+1) steps (m.q 0) i.val) ≤
        8*(a.radiusS z-a.radiusS lo)/(a.alpha.val.val lo^2*F)+epsilon := by
  exact a.original_radius_covariance_eventually_first hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hlo hloz hz hkmin hA hAD hfloor hepsilon

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
