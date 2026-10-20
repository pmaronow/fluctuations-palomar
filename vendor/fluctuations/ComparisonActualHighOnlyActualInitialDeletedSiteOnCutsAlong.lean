module

public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyCriticalScaleNumerics
public import ComparisonActualHighOnlyRawResourcePairBudget
public import ComparisonActualHighOnlyPullbackFourCutReadout
public import ComparisonActualHighOnlyCavityCategoryInterfaces
public import ComparisonActualHighOnlyInheritedDeletedSiteForestRate
public import ComparisonSignedCavityInheritedDeletedSiteForestRate
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator
public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_initial_deleted_site_on_given_cuts_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_high_only (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialDeletedSiteOnGivenCutsAlong_high_only depth A err M W w high outer := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_inherited_deleted_site_forest_rate_high_only
    (D:=D) 1 0 2 depth Bclock Temp Cf A cK hTemp hCf (zero_le_one.trans hA) hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  let err:=fun n=>(C/Cd)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)
  have Hpow:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul (C/Cd)
  have herr n : 0 ≤ err n:=by dsimp only [err];positivity
  refine ⟨err,herr,Herr,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HR,Hsource,Hcuts,HW,Hcutoff] with n hn hsource hcuts hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  have hx1 : (M n).xs ≤ 1:=hxW.trans hW1
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  refine ⟨HI,HU,?_⟩
  intro seedMass
  rw [←hcut] at hj
  let old:=pre++(mid++tail)
  let i:=pre.length
  let star:=pre.length+mid.length
  have hi : i ≤ star:=by dsimp only [i,star];omega
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old i star seedMass (hi.trans (HI.le.trans HU))
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed old HU seedMass .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old star:=by
    dsimp only [old,star];rw [hcut,hindex];exact HstarK
  have H:=hj U i star [.initial] st (by simp) rfl
    (nativeActualInitialState_leaves_le old i star seedMass (hi.trans (HI.le.trans HU)))
    hP hi HI HU (M n).xs (W n) le_rfl hxW
    (by simpa only [old,i,hcut] using hmi)
    (by dsimp only [old,star];rw [hcut,hindex];exact Hmass) HK
  have ho : MassOrdered 0 old:=by dsimp only [old];rw [hcut];exact finiteCutMasses_ordered us hus jGrid
  obtain ⟨hden,_,Hden⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only
    (M n) hCf hsource hx1 hW hcK ho HI HU HK
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  change Cd*W n ≤ chi*K star at Hden
  change 0 < chi*K star at hden
  change |nativeActualFourOtherCategorySum_high_only (M n) U (W n)
    (nativeActualMinimumFourCenteredForest_high_only (M n) HI HU (W n) depth [st]) .deletedSite|/
      (chi*K star) ≤ err n*(M n).xs^3
  apply (div_le_iff₀ hden).2
  apply H.trans
  have HP:=mul_le_mul_of_nonneg_left Hden
    (show 0 ≤ err n*(M n).xs^3 from mul_nonneg (herr n) (pow_nonneg (M n).hxs.le 3))
  apply le_trans (le_of_eq ?_) HP
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one]
  dsimp only [err]
  field_simp [hCd.ne']

end OAI.SKFluctuations.Cavity
