module

public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyCriticalScaleNumerics
public import ComparisonActualHighOnlyRawResourcePairBudget
public import ComparisonActualHighOnlyPullbackFourCutReadout
public import ComparisonActualHighOnlyCavityCategoryInterfaces
public import ComparisonActualHighOnlyInheritedResourceSiteDifferenceRate
public import ComparisonSignedCavityActualDeletedSiteReadout
public import ComparisonSignedCavityInheritedResourceSiteDifferenceRate
public import ComparisonSignedCavityActualResourceScalarScale

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_minimum_inherited_centered_deleted_site_rate_high_only
    (degree : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let center:=nativePhysicalResourceCenter n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U i star k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
          (seed : List NativeResourceMark),
          NativeActualResourceGenerated i star U seed k T P → seed.length+k ≤ degree →
          i ≤ star → star < as.length →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
          |(W⁻¹)^k*nativeActualOriginalOtherSourceCategory .deletedSite n q U b h K center T
            (nativeOriginalCenteredRestTest n q U b h K T
              (nativeActualResourceRestValue P 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 center))
              P.live.test.target star| ≤
            C*|P.coefficient| *((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*
              nativeResourceScale x W 1 seed := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_resource_site_deleted_rate_high_only
    (D:=D) degree Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let center:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho:=finiteCutMasses_ordered us hus jGrid
  intro U i star k T P seed hP hd hi hs x W hxsx hxW hmi hms
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have hres : P.resources.length ≤ degree:=by rw [hP.total_factor_depth];exact hd
  have H1:=hj U U i star g.tree (P.retarget 0)
    (by simpa only [NativeResourceTerm.retarget_resources] using hres)
    hi hs x W hxsx hxW hmi hms (g.embed P.live.test.target) g.mark
  have H2:=hj U U i star g.tree (P.retarget 0).freeze
    (by simpa only [NativeResourceTerm.freeze_resources,NativeResourceTerm.retarget_resources] using hres)
    hi hs x W hxsx hxW hmi hms (g.embed P.live.test.target) g.mark
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  rw [←HQ]
  rw [native_actual_original_deleted_site_eq_two_resources U b h K center T P ho]
  rw [←HQ] at H1 H2
  have Hcoef1 : (P.retarget 0).coefficient=P.coefficient:=rfl
  have Hcoef2 : (P.retarget 0).freeze.coefficient= -P.coefficient:=rfl
  simp only [Hcoef1,Hcoef2,abs_neg,NativeResourceTerm.freeze_resources,
    NativeResourceTerm.retarget_resources] at H1 H2
  let E1:=nativeOriginalResourceSiteDeletedDifference (P.retarget 0) 0
    (cutFullVariance n q U 1 1 b h K) 0 U b h K center (g.embed P.live.test.target) g.mark
  let E2:=nativeOriginalResourceSiteDeletedDifference (P.retarget 0).freeze 0
    (cutFullVariance n q U 1 1 b h K) 0 U b h K center (g.embed P.live.test.target) g.mark
  let e:=((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)
  have Hsum : |E1+E2| ≤ 2*C*|P.coefficient| *e*nativeResourceScale x W 1 P.resources:=by
    exact ((abs_add_le _ _).trans (add_le_add H1 H2)).trans_eq (by dsimp only [e];ring)
  have hW : 0 < W:=M.hxs.trans_le (hxsx.trans hxW)
  have Hscale:=hP.saved_scale x W 1
  simp only [one_mul] at Hscale
  have Hcancel : (W⁻¹)^k*W^k=1:=by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow]
  rw [abs_mul,abs_neg,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hW.le) k)]
  apply (mul_le_mul_of_nonneg_left Hsum (pow_nonneg (inv_nonneg.mpr hW.le) k)).trans_eq
  rw [Hscale]
  calc
    _=2*C*|P.coefficient| *e*nativeResourceScale x W 1 seed*((W⁻¹)^k*W^k):=by ring
    _=_:=by rw [Hcancel,mul_one];dsimp only [e];ring

end OAI.SKFluctuations.Cavity
