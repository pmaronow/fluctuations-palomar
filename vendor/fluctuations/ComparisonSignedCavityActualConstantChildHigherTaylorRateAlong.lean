module

public import ComparisonSignedCavityActualFourHigherTaylorProfile
public import ComparisonSignedCavityActualFreshResourceHighTaylorFromMinimum
public import ComparisonSignedCavityActualConstantResourceFreshLowTaylorRateAlong
public import ComparisonSignedCavityActualFourForestTaylorProfile
public import ComparisonSignedCavityActualConstantChildHighProfile
public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonNativeActualInheritedHighTailPowers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_higher_Taylor_forest_rate_along
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourHigherTaylorError (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^2 := by
  let eta:=actualMassSavingExponent m delta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_fresh_resource_HIGH_parts_from_minimum
    (D:=D) degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1:=by
    filter_upwards [Hshell] with n hn
    rcases hn with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Tbase epsilon shell ts (M n).b (M n).h hb hh le_rfl zero_le_one le_rfl
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_resource_fresh_third_LOW_rate_along
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim Hsource hsmall Hclock w hw
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vp:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  let J:=1+nativeActualProfileOpVariation 1 .highRow
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVp : 0 ≤ Vp:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  have hJ : 0 ≤ J:=by norm_num [J,nativeActualProfileOpVariation]
  let err:=fun n=>(8*CH/Cd*Vp*J)*((dim n+1:ℕ):ℝ)^(-eta/256)+(12*Vv/Cd)*|eLow n|
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=(Hpow.const_mul (8*CH/Cd*Vp*J)).add (heLow.abs.const_mul (12*Vv/Cd))
    simpa only [err,Function.comp_def,zero_mul,mul_zero,abs_zero,add_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,HLow,Hsource,hsmall,Hshell,HW1] with
    n hnH hnTail hnL hsource hnSmall hnShell hW1
  rcases hnShell with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hsource hxs1 L us hus hret hmesh,
    hnL L us hus hret hmesh hstar,
    hnTail (M n) Tbase epsilon shell ts hb hh hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridL hgridTail
  dsimp only at hgridH hgridL hgridTail ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).bf (M n).hf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let BH:=4*CH/Cd
  let BL:=|eLow n|/Cd*(M n).xs^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by dsimp only [f];rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have hBH : 0 ≤ BH:=by dsimp only [BH];positivity
  have hBL : 0 ≤ BL:=by dsimp only [BL];positivity
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
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourHigherTaylorError (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(BH*(Q.tree.forkCost f+edgeBudget 0 as f+
        W n*(Q.tree.forkCost R+edgeBudget 0 as R))+BL):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    let cost:=Q.tree.forkCost f+edgeBudget 0 as f+W n*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have HF:=add_nonneg (Q.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
      have HR:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost]
      positivity
    have Hhigh0 l t hl ht part:=hgridH 0 star U Q.generation [] Q.tree Q.term HV (Nat.zero_le star) hs hU
      (by dsimp only [rBound];omega) (by simpa using HD) (M n).xs (W n) le_rfl hxW hW1
      Hmi hmassstar (hcut.trans (min_le_left _ _)) l t hl ht part
    have Hhigh1 l t hl ht part:=hgridH 0 star U Q.generation [] g.tree (Q.term.retarget 0) HV.retarget (Nat.zero_le star) hs hU
      hg (by simpa using HD) (M n).xs (W n) le_rfl hxW hW1 Hmi hmassstar (hcut.trans (min_le_left _ _)) l t hl ht part
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at Hhigh0 Hhigh1
    have Hforkf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f hflo
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change ∀l t, l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceHigherHighPart (M n) U (Q.term.retarget 0) part l t| ≤
        |Q.term.coefficient| *(CH*W n*(g.tree.forkCost f+edgeBudget 0 as f+W n*(g.tree.forkCost R+edgeBudget 0 as R))) at Hhigh1
    rw [show g.tree.forkCost f=Q.tree.forkCost f from Hforkf,show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Hlow0 l t hl ht:=hgridL U hs hU hcut 0 Q.generation Q.tree Q.term HV (Nat.zero_le star)
      (by dsimp only [rBound];omega) HD Hmi hmassstar l t hl ht
    have Hlow1 l t hl ht:=hgridL U hs hU hcut 0 Q.generation g.tree (Q.term.retarget 0) HV.retarget (Nat.zero_le star)
      hg HD Hmi hmassstar l t hl ht
    have Hlowmajor : |Q.term.coefficient| *eLow n*(W n*(M n).xs^2) ≤
        |Q.term.coefficient| *|eLow n| *(W n*(M n).xs^2):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)) (by positivity)
    let B:=2*CH*cost+|eLow n|/2*(M n).xs^2
    have hB : 0 ≤ B:=by dsimp only [B];positivity
    have H0:=actual_minimum_normalized_fresh_resource_Taylor_abs_le (M n) U Q.generation Q.term ho hW
      (H:=|Q.term.coefficient| *(CH*W n*cost)) (L:=|Q.term.coefficient| *|eLow n| *(W n*(M n).xs^2))
      (by positivity) (by positivity) Hhigh0
      (fun l t hl ht=>(Hlow0 l t hl ht).trans Hlowmajor)
    have H1:=actual_minimum_normalized_fresh_resource_Taylor_abs_le (M n) U Q.generation (Q.term.retarget 0) ho hW
      (H:=|Q.term.coefficient| *(CH*W n*cost)) (L:=|Q.term.coefficient| *|eLow n| *(W n*(M n).xs^2))
      (by positivity) (by positivity) Hhigh1
      (fun l t hl ht=>(Hlow1 l t hl ht).trans Hlowmajor)
    have Herror:=actual_minimum_four_higher_Taylor_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU hW hcK hB hstarK
      (by apply H0.trans_eq;dsimp only [B];ring)
      (by apply H1.trans_eq;dsimp only [B];ring)
    apply Herror.trans_eq
    dsimp only [BH,BL,B,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le hBH hBL depth children 3 Hleaves f R hf hR hflo hRlo
    (nativeActualOriginalFourHigherTaylorError (M n) U (W n)) Hrow
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hfamily (ff : ℕ→ℝ) (hff : ∀j,0 ≤ ff j) (hfflo : ∀j,j<U→ff j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost ff+edgeBudget 0 as ff))).sum ≤ J*edgeBudget 0 as ff:=
    native_actual_constant_child_family_wholeProfile_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi ff hff hfflo
  have Hcoeff : (children.map (fun Q=>|Q.term.coefficient|)).sum ≤ 6:=by
    have H:=native_actual_constant_child_family_coefficient_variation_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi
    norm_num only [NativeActualExpansionOp.coefficientCost,Nat.cast_one] at H
    exact H
  have Hrate : edgeBudget 0 as f+W n*edgeBudget 0 as R ≤
      ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [show f=(fun j=>(R j)^(4/p)) from rfl,HReq]
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) (4/p) htheta1 htheta2.le hdeficit
    simpa only [←hcanonical,NativeOverlapContext.N,eta,neg_div] using H
  have Hmajor:=add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add (Hfamily f hf hflo) (mul_le_mul_of_nonneg_left (Hfamily R hR hRlo) hW.le))
      (show 0 ≤ 2*BH*Vp by positivity))
    (mul_le_mul_of_nonneg_left Hcoeff (show 0 ≤ 2*BL*Vv by positivity))
  have Htailmajor:=mul_le_mul_of_nonneg_left Hrate (show 0 ≤ 2*BH*Vp*J by positivity)
  apply Hsum.trans
  apply Hmajor.trans
  have HE : 2*BH*Vp*(J*edgeBudget 0 as f+W n*(J*edgeBudget 0 as R))+2*BL*Vv*6 ≤
      2*BH*Vp*J*(((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2)+2*BL*Vv*6:=by
    convert add_le_add_right Htailmajor (2*BL*Vv*6) using 1 <;> ring
  apply HE.trans_eq
  dsimp only [BH,BL,err]
  ring

end OAI.SKFluctuations.Cavity
