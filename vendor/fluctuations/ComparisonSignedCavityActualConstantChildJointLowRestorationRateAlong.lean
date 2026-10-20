module

public import ComparisonSignedCavityActualFourJointLowRestorationProfile
public import ComparisonSignedCavityActualConstantResourceFreshJointLowRestorationRateAlong
public import ComparisonSignedCavityActualFourForestTaylorVariation
public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonSignedCavityActualConstantChildHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_joint_LOW_restoration_forest_rate_along
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
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourJointLowRestorationError (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^2 := by
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_resource_fresh_joint_LOW_restoration_rate_along
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(24*Vv/Cd)*|eLow n|
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero,abs_zero] using heLow.abs.const_mul (24*Vv/Cd)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HLow,Hsource,HW1] with n hnL hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnL L us hus hret hmesh hstar] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro U hs hU hcut hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth children
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
    simp only [partitionPoint,partitionValues_zero,id_eq]
    exact mul_nonneg hCmass (M n).hxs.le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointLowRestorationError (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(2/Cd)*(|eLow n| *(M n).xs^2):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    have Hlow0:=hgridL U hs hU hcut 0 Q.generation Q.tree Q.term HV (Nat.zero_le star)
      (by dsimp only [rBound];omega) HD Hmi hmassstar
    have Hlow1:=hgridL U hs hU hcut 0 Q.generation g.tree (Q.term.retarget 0) HV.retarget (Nat.zero_le star)
      hg HD Hmi hmassstar
    have Hlowmajor : |Q.term.coefficient| *eLow n*(W n*(M n).xs^2) ≤
        |Q.term.coefficient| *W n*(|eLow n| *(M n).xs^2):=by
      have H:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self (eLow n)) (abs_nonneg Q.term.coefficient))
        (show 0 ≤ W n*(M n).xs^2 by positivity)
      convert H using 1
      ring
    have Herror:=actual_minimum_four_joint_LOW_restoration_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ |eLow n| *(M n).xs^2 by positivity) hstarK
      (Hlow0.trans Hlowmajor) (Hlow1.trans Hlowmajor)
    simpa only [Cd] using Herror
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 3 Hleaves
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hcoeff : (children.map (fun Q=>|Q.term.coefficient|)).sum ≤ 6:=by
    have H:=native_actual_constant_child_family_coefficient_variation_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi
    norm_num only [NativeActualExpansionOp.coefficientCost,Nat.cast_one] at H
    exact H
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 12*Vv:=by
    apply Hvariation.trans
    have H:=mul_le_mul_of_nonneg_left Hcoeff (show 0 ≤ 2*Vv by positivity)
    convert H using 1
    ring
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  apply Hsum.trans
  have H:=mul_le_mul_of_nonneg_right Htotal
    (show 0 ≤ (2/Cd)*(|eLow n| *(M n).xs^2) by positivity)
  convert H using 1 <;> (try dsimp only [err]) <;> ring

end OAI.SKFluctuations.Cavity
