module

public import ComparisonSignedCavityActualResourceGammaHighSecondProfileAlong
public import ComparisonSignedCavityActualFourGammaRestorationReadout
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
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_gamma_HIGH_restoration_forest_rate_along
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourGammaRestorationError (M n) U (W n) Q true|)).sum ≤
            err n*(M n).xs^2 := by
  let eta:=actualMassSavingExponent m delta
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨CH,hCH,HH⟩:=actual_inherited_resource_gamma_high_second_profile_along
    degree (rBound+1) Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource hsmall
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers
    (D:=D) (Cs:=Ccal^2) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
    (sq_nonneg _) hc hcouter
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vp:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  let J:=1+nativeActualProfileOpVariation 1 .highRow
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVp : 0 ≤ Vp:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  have hJ : 0 ≤ J:=by norm_num [J,nativeActualProfileOpVariation]
  let err:=fun n=>(4*CH/Cd*Vp*J)*((dim n+1:ℕ):ℝ)^(-eta/256)
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul (4*CH/Cd*Vp*J)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HH,hdim.eventually Htail,Hsource,hsmall,Hshell,HW1] with
    n hnH hnTail hsource hnSmall hnShell hW1
  rcases hnShell with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH L us hus hret hmesh,
    hnTail (M n) Tbase epsilon shell ts hb hh hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridTail
  dsimp only at hgridH hgridTail ⊢
  intro U hs hU hcutlo hmassstar hstarK
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
  let BH:=2*CH/Cd
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hBH : 0 ≤ BH:=by dsimp only [BH];positivity
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
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGammaRestorationError (M n) U (W n) Q true| ≤
      (BH*W n)*(|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R)):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    let cost:=Q.tree.forkCost R+edgeBudget 0 as R
    have hcost : 0 ≤ cost:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have Hhigh0:=hgridH Q.tree 0 star U Q.generation [] Q.term HV (by simpa using HD) (Nat.zero_le star) hs hU
      (by dsimp only [rBound];omega) Hmi hmassstar
    have Hhigh1:=hgridH g.tree 0 star U Q.generation [] (Q.term.retarget 0) HV.retarget
      (by simpa using HD) (Nat.zero_le star) hs hU hg Hmi hmassstar
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at Hhigh0 Hhigh1
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |((W n)⁻¹)^Q.generation*nativeActualResourceGammaSecondRestoration (M n) U (Q.term.retarget 0) true| ≤
      |Q.term.coefficient| *CH*(W n)^2*(g.tree.forkCost R+edgeBudget 0 as R) at Hhigh1
    rw [show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Herror:=actual_minimum_four_gamma_restoration_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU true hW hcK
      (show 0 ≤ CH*W n*cost by positivity) hstarK
      (by apply Hhigh0.trans_eq;dsimp only [cost];ring)
      (by apply Hhigh1.trans_eq;dsimp only [cost];ring)
    apply Herror.trans_eq
    dsimp only [BH,cost,Cd]
    ring
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_left] at Hsum
  have Hprofile:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 3 Hleaves R hR hRlo
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hfamily : (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum ≤ J*edgeBudget 0 as R:=
    native_actual_constant_child_family_wholeProfile_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi R hR hRlo
  have Hrate : W n*edgeBudget 0 as R ≤ ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) 2 (by norm_num) le_rfl
      (by simp only [sub_self];exact div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num))
    have Hzero:=edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) 2)
    rw [HReq] at Hzero ⊢
    have HH : edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) j)^(2:ℝ))+
        W n*edgeBudget 0 as (nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
          (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp)) ≤
          ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
      simpa only [←hcanonical,NativeOverlapContext.N,eta,neg_div] using H
    linarith
  apply Hsum.trans
  apply (mul_le_mul_of_nonneg_left Hprofile (mul_nonneg hBH hW.le)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Hfamily
    (show 0 ≤ 2*Vp by positivity)) (mul_nonneg hBH hW.le)).trans
  have Hfinal:=mul_le_mul_of_nonneg_left Hrate (show 0 ≤ BH*2*Vp*J by positivity)
  convert Hfinal using 1 <;> (try dsimp only [err,BH]) <;> ring

end OAI.SKFluctuations.Cavity
