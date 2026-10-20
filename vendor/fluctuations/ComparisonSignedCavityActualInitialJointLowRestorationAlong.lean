module

public import ComparisonSignedCavityInheritedWorkingScaleFreshResourceJointLowRestorationRateAlong
public import ComparisonSignedCavityActualFourJointLowRestorationProfile
public import ComparisonSignedCavityActualJointLowRestorationCategorySum
public import ComparisonSignedCavityActualFourForestTaylorVariation
public import ComparisonSignedCavityActualFourRestorationSeedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_joint_LOW_restoration_forest_rate_along
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as i ≤ Cmass*x → ∀seedMass : ℝ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]).map
          (fun Q=>|nativeActualOriginalFourJointLowRestorationError (M n) U (W n) Q|)).sum ≤
            err n*x*(M n).xs^2 := by
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_working_scale_resource_fresh_joint_LOW_restoration_rate_along
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(4*Vv/Cd)*|eLow n|
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero,abs_zero] using heLow.abs.const_mul (4*Vv/Cd)
  refine ⟨err,fun n=>by dsimp only [err];positivity,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HLow,Hsource,HW1] with n hnL hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnL L us hus hret hmesh hstar] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro i U hi hs hU hcut hmassstar hstarK x hxsx hxWscale hmi seedMass
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈[st]) : Q.tree.leaves ≤ 2:=by
    have hQ' : Q=st:=by simpa using hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hseed Q (hQ : Q∈[st]) : NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    have hQ' : Q=st:=by simpa using hQ
    subst Q
    exact .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st] Hseed Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
    0 (by
      intro P hP
      have hP' : P=st:=by simpa using hP
      subst P
      rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
    2 Hleaves Q hQ
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointLowRestorationError (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(2/Cd)*(x*|eLow n| *(M n).xs^2):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : [NativeResourceMark.initial].length+Q.generation ≤ degree:=by dsimp only [degree,List.length];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    have Hlow0:=hgridL U hs hU hcut i Q.generation [.initial] Q.tree Q.term HV hi
      (by dsimp only [rBound];omega) HD x hxsx hxWscale hmi hmassstar
    have Hlow1:=hgridL U hs hU hcut i Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hi
      hg HD x hxsx hxWscale hmi hmassstar
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one,NativeResourceTerm.retarget] at Hlow0 Hlow1
    have Hlowmajor : |Q.term.coefficient| *x*eLow n*(W n*(M n).xs^2) ≤
        |Q.term.coefficient| *W n*(x*|eLow n| *(M n).xs^2):=by
      have H:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self (eLow n))
          (mul_nonneg (abs_nonneg Q.term.coefficient) hx.le))
        (show 0 ≤ W n*(M n).xs^2 by positivity)
      convert H using 1
      ring
    have Herror:=actual_minimum_four_joint_LOW_restoration_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ x*|eLow n| *(M n).xs^2 by positivity) hstarK
      (Hlow0.trans Hlowmajor) (Hlow1.trans Hlowmajor)
    simpa only [Cd] using Herror
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth [st] 2 Hleaves
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 2*Vv:=by
    change (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤
      2*Vv*([st].map (fun Q=>|Q.term.coefficient|)).sum at Hvariation
    have hcoeff : st.term.coefficient=1:=rfl
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hcoeff,
      abs_one,add_zero,mul_one] using Hvariation
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  apply Hsum.trans
  have H:=mul_le_mul_of_nonneg_right Htotal
    (show 0 ≤ (2/Cd)*(x*|eLow n| *(M n).xs^2) by positivity)
  convert H using 1 <;> (try dsimp only [err]) <;> ring

end OAI.SKFluctuations.Cavity
