module

public import ComparisonActualHighWallThetaZeroRadiusPlainTraceFirstNext
public import ComparisonActualHighWallThetaZeroRadiusColumnIntegrableFirstNext
public import ComparisonShiftedNativeRadiusOriginalWeights

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

theorem original_radius_covariance_eventually_first
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
  dsimp only
  let m:=a.shiftedNativeModel
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A 1 kmin
  let w:=fun j=>comparisonOriginalRadiusWeights m.q (as j) f
  let W:=fun j r=>deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id (w j) r
  let fixed:=A.indicator (fun _=>(1:ℝ))
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
  let mu:=fun j=>m.radiusMeasure dphys e (as j) (ho j)
  let B:=1/kmin
  let err:=epsilon*m.alpha.val.val lo^2/48
  have hmass : 0 < m.alpha.val.val lo:=m.profile_pos hlo (hloz.trans hz)
  have hwall : 0 < m.alpha.val.val lo-m.u0:=by
    have H:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
      ⟨le_rfl,m.hr⟩ ⟨hlo.le,hloz.trans hz⟩ hlo
    rw [m.alpha.property.1] at H
    exact sub_pos.mpr H
  have herr : 0 < err:=by dsimp [err];positivity
  have hwbound j i : w j i∈Icc (0:ℝ) B:=by
    simpa only [one_mul] using
      m.original_radius_weights_bounds hA (by norm_num : (0:ℝ) < 1) hkmin (as j) (ho j) i
  have hiW j : IntegrableOn (W j) (Icc m.rmin 1):=
    original_column_integrable_first m (as j) (ho j) _ (by positivity) (hwbound j)
  have hiFixed : IntegrableOn fixed (Icc m.rmin 1):=(integrable_const (1:ℝ)).indicator hA
  have herror:=m.originalRadiusWeights_linear_tendsto_L1 hA (by norm_num : (0:ℝ) < 1) hkmin hfloor
    as mesh ho hend hmesh hlim
  have htrace:=a.plain_radius_trace_eventually_first hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hlo hloz hz hA hAD herr
  have hmeshError : Tendsto (fun j=>mesh j*B) atTop (𝓝 0):=by simpa using hlim.mul_const B
  filter_upwards [htrace,(tendsto_order.mp herror).2 err herr,
    (tendsto_order.mp hlim).2 (m.alpha.val.val lo/2) (by positivity),
    (tendsto_order.mp hlim).2 (m.alpha.val.val lo-m.u0) hwall,
    (tendsto_order.mp hmeshError).2 err herr] with j hjtrace hjerror hjcut hjwall hjmesh
  have hdom:=m.radius_measure_le_compact_volume dphys e (as j) (ho j)
  have hsupport : (mu j).restrict (Icc m.rmin 1)=mu j:=
    Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem measurableSet_Icc).filter_mono (ae_mono hdom))
  have hmoving:=dominated_setIntegral_difference_le (Icc m.rmin 1) (Icc m.rmin 1)
    (Subset.refl _) (mu j) (hdom.trans Measure.restrict_le_self) fixed (W j) hiFixed (hiW j)
  rw [hsupport] at hmoving
  have hfixedInt : (∫r,fixed r∂mu j)=∫_r in A,(1:ℝ)∂mu j:=integral_indicator hA
  rw [hfixedInt] at hmoving
  have hfilled : (∫r,W j r∂mu j) ≤ (a.radiusS z-a.radiusS lo)/F+2*err:=by
    have HE : (fun r : ℝ=>1/(1:ℝ))=(fun _=>(1:ℝ)):=by funext r;norm_num
    dsimp only [W,w,f,fixed,mu] at hmoving
    dsimp only [F,m] at hjtrace ⊢
    simp only [HE] at hjerror
    linarith
  have Hcov:=m.original_radius_covariance_le_filled_of_mesh dphys e (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) hlo hloz hz hkmin hA hAD hjcut.le hjwall.le
  have Hbudget : (2*(∫r,W j r∂mu j)+2*(mesh j*B))/(m.alpha.val.val lo/2)^2 ≤
      8*(a.radiusS z-a.radiusS lo)/(m.alpha.val.val lo^2*F)+epsilon:=by
    apply (div_le_iff₀ (by positivity : 0 < (m.alpha.val.val lo/2)^2)).mpr
    have HF:=mul_le_mul_of_nonneg_left hfilled (by norm_num : (0:ℝ) ≤ 2)
    have heq : (8*(a.radiusS z-a.radiusS lo)/(m.alpha.val.val lo^2*F)+epsilon)*
        (m.alpha.val.val lo/2)^2=2*((a.radiusS z-a.radiusS lo)/F)+epsilon*m.alpha.val.val lo^2/4:=by
      field_simp [hmass.ne'];ring
    rw [heq]
    dsimp only [err] at HF hjmesh
    have HP:=mul_pos hepsilon (sq_pos_of_pos hmass)
    linarith
  exact Hcov.trans Hbudget

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
