module

public import ComparisonShiftedNativeTraceLimit
public import ComparisonActualHighWallTraceMeasure
public import OmittedWallPhysicalRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

theorem radiusS_absolutelyContinuous
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {lo z : ℝ} (hlo : a.data.rmin < lo) (hloz : lo ≤ z) (hz : z ≤ 1) :
    AbsolutelyContinuousOnInterval a.radiusS lo z := by
  have hgmono := laplaceComparisonStrength_monotonicities a.data.hd.ne'
    (sq_pos_of_pos a.data.hd) a.data.hrbounds.1.le
  exact actual_wall_radius_overlap_absolutelyContinuous
    a.data.hr a.data.hs1 a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM
    a.data.g a.data.hg n dphys e a.data.hs.1 a.data.htau a.data.hrbounds.1.le
    a.data.hepsilon a.data.htheta a.data.hdepsilon
    (concreteWallStrength_initial a.data.hN a.data.hE a.data.hd a.data.hd1
      a.data.hs.1.le a.data.hq a.data.hsmall)
    hgmono.1 hgmono.2 (fun r _ => laplaceComparisonStrength_le _ (sq_nonneg _) r)
    a.alpha hlo hloz hz

theorem radius_trace_boundedWeight
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (hend : ∀j,partitionEnd 0 (as j)=1)
    (mesh : ℕ→ℝ) (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hmesh0 : ∀j,0 ≤ mesh j) (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z : ℝ} (hlo : a.data.rmin < lo) (hloz : lo ≤ z) (hz : z ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    (weight : ℝ→ℝ) (hwm : AEStronglyMeasurable weight volume) (K : ℝ)
    (hwb : ∀r∈A,‖weight r‖ ≤ K) (hw0 : ∀r∈A,0 ≤ weight r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*a.data.g z)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,weight r∂m.radiusMeasure dphys e (as j) (ho j)) ≤
        (∫r in A,weight r*deriv a.radiusS r)/F+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*a.data.g z)
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) m.q
  let err : ℝ→ℝ→ℕ→ℝ≥0∞:=fun _ _ j=>
    ENNReal.ofReal (2*(mesh j*Cnode)/F+2*(mesh j/m.c))
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) z))
  have herr (p q : ℝ) (_hp : lo ≤ p) (_hpq : p < q) (_hq : q ≤ z) :
      Tendsto (err p q) atTop (𝓝 0) := by
    have ht : Tendsto (fun j=>2*(mesh j*Cnode)/F+2*(mesh j/m.c)) atTop (𝓝 0) := by
      simpa only [zero_mul,mul_zero,zero_div,zero_add] using
        (((hlim.mul_const Cnode).const_mul 2).div_const F).add
          ((hlim.div_const m.c).const_mul 2)
    simpa only [err,Function.comp_def,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hinterval (p q : ℝ) (hp : lo ≤ p) (hpq : p < q) (hq : q ≤ z) :
      ∀ᶠj : ℕ in atTop,m.radiusMeasure dphys e (as j) (ho j) (Ioo p q) ≤
        ENNReal.ofReal ((a.radiusS q-a.radiusS p)/F)+err p q j := by
    exact Filter.Eventually.of_forall (fun j=>
      a.radiusMeasure_interval_le_fixedStrength hN hlog hnd dphys e (as j) (ho j)
        (hend j) (hmesh j) (hmesh0 j) (hlo.trans_le hp) hpq.le hq hz)
  have hSm : MonotoneOn a.radiusS (Icc lo z) :=
    a.radius_moments.1.mono (Icc_subset_Icc hlo.le hz)
  exact m.radius_trace_boundedWeight_of_interval_budgets dphys e as ho hlo.le hloz hz hF
    a.radiusS hSm (a.radiusS_absolutelyContinuous dphys e hlo hloz hz)
    err herr hinterval hA hAD weight hwm K hwb hw0 hepsilon

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
