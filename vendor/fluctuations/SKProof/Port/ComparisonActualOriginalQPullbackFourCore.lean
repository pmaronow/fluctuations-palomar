module

public import ComparisonNativeActualInheritedHighTailPowers
public import ComparisonSignedCavityActualConstantChildGammaHighRateAlong
public import ComparisonSignedCavityActualConstantChildGammaHighCategoryAlong
public import ComparisonSignedCavityActualConstantGammaRestorationOnCutsAlong
public import ComparisonSignedCavityActualConstantB0CategoryEnvelopeAlong
public import ComparisonSignedCavityActualConstantFreshHighTaylorRate
public import ComparisonSignedCavityActualConstantFreshTaylorRateAlong
public import ComparisonSignedCavityActualConstantB0OnStrongCutsAlong
public import ComparisonSignedCavityActualConstantFullB0EnvelopeSavingAlong
public import ComparisonSignedCavityActualConstantChildHigherTaylorRateAlong
public import ComparisonSignedCavityActualConstantChildHigherTaylorCategoryAlong
public import ComparisonSignedCavityActualConstantPostTaylorEnvelopeAlong
public import ComparisonSignedCavityActualConstantChildJointHighRestorationRateAlong
public import ComparisonSignedCavityActualConstantChildJointHighRestorationCategoryAlong
public import ComparisonSignedCavityActualConstantSavedJointOnCutsAlong
public import ComparisonSignedCavityActualConstantThreeCategoryEnvelopeAlong
public import ComparisonSignedCavityActualInitialHigherTaylorForestModulusAlong
public import ComparisonSignedCavityActualInitialHigherTaylorCategoryModulusAlong
public import ComparisonSignedCavityActualInitialJointHighRestorationRateAlong
public import ComparisonSignedCavityActualInitialJointHighRestorationCategoryAlong
public import ComparisonSignedCavityActualFourLongitudinalRestorationSeedAtoms
public import ComparisonSignedCavityActualInitialLongitudinalForestAlong
public import ComparisonSignedCavityActualInitialLongitudinalOnCutsAlong
public import ComparisonSignedCavityActualFourGaRestorationRate
public import ComparisonSignedCavityActualFourGaRestorationRateAlong
public import ComparisonSignedCavityActualInitialRestoredGaOnCutsAlong
public import ComparisonSignedCavityActualInitialGammaHighRateAlong
public import ComparisonSignedCavityActualInitialGammaHighCategoryAlong
public import ComparisonSignedCavityActualInitialThreeGammaOnCutsAlong
public import ComparisonSignedCavityActualFourGaRestorationSeedAtoms
public import ComparisonSignedCavityActualConstantChildGaRestorationRate
public import ComparisonSignedCavityActualConstantChildGaRestorationRateAlong
public import ComparisonSignedCavityActualConstantChildLongitudinalRestorationRate
public import ComparisonSignedCavityActualConstantChildLongitudinalRestorationRateAlong
public import ComparisonSignedCavityActualConstantChildLongitudinalCategoryAlong
public import ComparisonSignedCavityActualConstantFreshCTwoHighRate
public import ComparisonSignedCavityActualConstantFreshFourGLowRate
public import ComparisonSignedCavityActualConstantFreshRestorationRatesAlong
public import ComparisonSignedCavityInheritedFourFirstHighForest
public import ComparisonSignedCavityActualConstantSourceFirstHighRate
public import ComparisonSignedCavityInheritedFourFirstHighRoots
public import ComparisonSignedCavityInheritedConstantLongitudinalRate
public import ComparisonSignedCavityInheritedRetainedConstantLongitudinal
public import ComparisonSignedCavityInheritedRetainedConstantLongitudinalAlong
public import ComparisonNativeActualTargetHighTailPowers
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQPullbackFourCutReadout
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQGammaHighSecondCutoffAlong
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQTargetHighTailPowers
public import SKProof.Port.ComparisonActualOriginalQFirstHighFourProfile
public import SKProof.Port.ComparisonActualOriginalQFirstHighReadoutPrimitives
public import SKProof.Port.ComparisonActualOriginalQLowRestorationCompatibleSourceAlong
public import SKProof.Port.ComparisonActualOriginalQOriginalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics

@[expose] public section
noncomputable section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks_original_q
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h M.data.rmin 1 →
        M.xs^2≤Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
        M.directTestWorkingScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let Cerr:=Cavity.actualLowErrorComparisonConstant
          (4*Cf+2*Temp) Temp
        ∀U : ℕ,U≤as.length → 2*c*M.directTestWorkingScale≤partitionPoint 0 as U →
        ∀theta : ℝ,1≤theta → theta≤2 → 2-theta≤actualMassSavingExponent m delta/128 →
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.sweepBf M.sweepHf as Cerr j)^theta)+
            M.directTestWorkingScale*ClockTree.edgeBudget 0 as
              (nativeOriginalHighTailEnvelope n U M.sweepBf M.sweepHf as Cerr)≤
            M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2  := by
  have H := eventually_actual_regular_original_target_high_envelope_powers_original_q
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  filter_upwards [H] with n hn
  intro M hs0 hsxs hs64 hclock hsmall hW1 us hus
  filter_upwards [hn M hclock hs0 hsxs hs64 hsmall hW1 us hus] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass theta htheta1 htheta2 hdeficit
  have hmass' : 2*c*M.xs ≤ partitionPoint 0 (finiteCutMasses us jGrid) U :=
    (mul_le_mul_of_nonneg_left M.canonical_direct_test_band_ge_scale
      (by positivity : 0 ≤ 2*c)).trans hmass
  exact hj U hU hmass' theta htheta1 htheta2 hdeficit

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_gamma_HIGH_restoration_forest_rate_along_of_pullback_clocks_original_q
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
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
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourGammaRestorationError_original_q (M n) U (W n) Q true|)).sum ≤
            err n*(M n).xs^2 := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  let eta:=actualMassSavingExponent m delta
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨CH,hCH,HH⟩:=actual_inherited_resource_gamma_high_second_profile_along_of_cutoff_original_q
    degree (rBound+1) Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks_original_q
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
  filter_upwards [HH,hdim.eventually Htail,Hsource,hsmall,Hshell,HW1,Hcutoff,HOmit] with n hnH hnTail hsource hnSmall hnShell hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH L us hus hret hmesh,
    hnTail (M n) hs0 hsxs hs64 hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridTail
  dsimp only at hgridH hgridTail ⊢
  intro U hs hU hcutlo hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren_original_q (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as (4*Cf+2*Temp) Temp
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
    actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves_original_q (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid_original_q (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation_original_q (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
    simp only [partitionPoint,partitionValues_zero,id_eq]
    exact mul_nonneg hCmass (M n).hxs.le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGammaRestorationError_original_q (M n) U (W n) Q true| ≤
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
    change |((W n)⁻¹)^Q.generation*nativeActualResourceGammaSecondRestoration_original_q (M n) U (Q.term.retarget 0) true| ≤
      |Q.term.coefficient| *CH*(W n)^2*(g.tree.forkCost R+edgeBudget 0 as R) at Hhigh1
    rw [show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Herror:=actual_minimum_four_gamma_restoration_error_abs_le_original_q (M n) hCf hsource hxs1 Q ho hs hU true hW hcK
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
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hfamily : (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum ≤ J*edgeBudget 0 as R:=
    native_actual_constant_child_family_wholeProfile_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi R hR hRlo
  have Hrate : W n*edgeBudget 0 as R ≤ ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) 2 (by norm_num) le_rfl
      (by simp only [sub_self];exact div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num))
    have Hzero:=edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) 2)
    rw [HReq] at Hzero ⊢
    have HH : edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) j)^(2:ℝ))+
        W n*edgeBudget 0 as (nativeOriginalHighTailEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as
          (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp)) ≤
          ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
      simpa only [←hcanonical,ActualHighWallData.N,eta,neg_div] using H
    linarith
  apply Hsum.trans
  apply (mul_le_mul_of_nonneg_left Hprofile (mul_nonneg hBH hW.le)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Hfamily
    (show 0 ≤ 2*Vp by positivity)) (mul_nonneg hBH hW.le)).trans
  have Hfinal:=mul_le_mul_of_nonneg_left Hrate (show 0 ≤ BH*2*Vp*J by positivity)
  convert Hfinal using 1 <;> (try dsimp only [err,BH]) <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_gamma_HIGH_restoration_category_rate_along_of_pullback_clocks_original_q
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
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
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q (M n) U Q .gammaHighRestoration)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_gamma_HIGH_restoration_forest_rate_along_of_pullback_clocks_original_q
    depth Bclock Temp Cf Cmass Ccal cK hTemp hCf hCmass hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall Hshell Homit w
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1,Hcutoff,HOmit] with n hn hsClocks hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcutlo hmassstar hstarK
  apply (actual_gamma_restoration_category_signed_sum_abs_le_error_sum_original_q (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _ true).trans
  exact hj U hs hU hcutlo hmassstar hstarK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_gamma_restoration_on_given_cuts_along_of_pullback_clocks_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualConstantGammaRestorationOnGivenCutsAlong_original_q depth err M W w high outer := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨eL,heL,HL⟩:=actual_inherited_constant_child_gamma_LOW_restoration_category_rate_along_original_q
    depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource Hcutoff w hw
  obtain ⟨eH,heH,HH⟩:=actual_inherited_constant_child_gamma_HIGH_restoration_category_rate_along_of_pullback_clocks_original_q
    depth Bclock Temp Cf A Ccal cK hTemp hCf hA0.le hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource Hcutoff hcompare Hshell Homit w
  let err n:=|eL n|+|eH n|
  have herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,abs_zero,zero_add] using heL.abs.add heH.abs
  refine ⟨err,(fun n=>by dsimp only [err];positivity),herr,?_⟩
  filter_upwards [HL,HH,Hcuts,Hcutoff,HOmit] with n hnL hnH hcuts hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnL L us hus hret hmesh hstar,hnH L us hus hret hmesh hstar] with jGrid hjL hjH
  dsimp only at hjL hjH ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  have HL':=hjL U hs hU Hupper Hmass HstarK
  have HH':=hjH U hs hU Hlo Hmass HstarK
  refine ⟨hs,hU,?_⟩
  intro cat hcat
  simp only [nativeActualSavedGammaRestorationCategories,List.mem_cons,List.not_mem_nil,or_false] at hcat
  have hle : eL n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eL n),abs_nonneg (eH n)]
  have hhe : eH n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eH n),abs_nonneg (eL n)]
  rcases hcat with rfl|rfl
  · exact HH'.trans (mul_le_mul_of_nonneg_right hhe (sq_nonneg _))
  · exact HL'.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_b0_category_envelope_along_of_pullback_clocks_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK cKcut A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourceB0CategoryEnvelopeAlong_original_q depth Temp cK err M W w high outer := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  have HR d:=actual_inherited_constant_gamma_restoration_on_given_cuts_along_of_pullback_clocks_original_q
    d hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W radius hcanonical hWlim Hsource Hcutoff hcompare Hshell Homit w high outer hw Hcuts
  choose e he0 he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper_original_q
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+A)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];linarith [mul_pos hCK (show 0 < 1+A by linarith)]
  let err n:=2*((List.range depth).map (fun d=>e d n)).sum*(R/B)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>e d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil => simp only [List.map_nil,List.sum_nil]; exact tendsto_const_nhds
    | cons d ds ih => simpa only [List.map_cons,List.sum_cons,zero_add] using (he d).add ih
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [mul_zero,zero_mul] using ((Hlim (List.range depth)).const_mul 2).mul_const (R/B)
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW,Hcutoff,HOmit] with n hn hclock hsource hcuts hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hs0 hsxs hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).sweepBf (M n).sweepHf
        (M n).sweep_bf_monotone (M n).sweep_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_three_category_envelope_gamma_paid_original_q
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*(e d n)) (by
      intro d hd cat hcat
      obtain ⟨_,_,H⟩:=hj ⟨d,hd⟩
      have H':=H cat hcat
      change |nativeActualFourOtherCategorySum_original_q (M n) U (W n)
        (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)) cat|/
        (chi*K star) ≤ e d n*(M n).xs^2 at H'
      exact actual_saved_denominator_upper_transfer hden hW hB (he0 d n) Hd H')
  apply Hpaid.trans_eq
  dsimp only [err]
  simp only [List.sum_map_mul_left]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_shell_history_constant_fresh_HIGH_parts_rate_of_pullback_clocks_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h M.data.rmin 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.data.d M.lam M.xs → M.directTestWorkingScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.directTestWorkingScale
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀(a z : g.tree.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
            |nativeActualHigherHighPart part n q U b h K g.tree (fun _=>1) a z l t| ≤
              C*M.data.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨C,hC,Hparts⟩:=eventually_actual_minimum_inherited_constant_HIGH_parts_profile_original_q
    (D:=D) 2 dOrder hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks_original_q (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M hs0 hsxs hs64 hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh,
    hnTail M hs0 hsxs hs64 hb hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU hcutlo hcutup seedMass a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let W:=M.directTestWorkingScale
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  have hg : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves seedMass _
      (nativeFreshAtSlot_mem (single as) seedMass (singleSlot as) star)
    simpa only [g,single_leaves_exact] using H
  have hlo j (hj : j < U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have HF1 : g.tree.forkCost R=0:=native_initial_seed_high_forkCost as seedMass hs R hlo
  have HF2 : g.tree.forkCost (fun j=>(R j)^(4/p))=0:=by
    apply native_initial_seed_high_forkCost as seedMass hs
    intro j hj
    rw [hlo j hj,Real.zero_rpow (by positivity : (4:ℝ)/p≠0)]
  have H:=hjParts U g.tree hU hg W M.canonical_direct_test_band_ge_scale hW1 hcutup a z l t hl ht part
  change |nativeActualHigherHighPart part n _ U _ _ _ g.tree (fun _=>1) a z l t| ≤
    C*W*(g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
      W*(g.tree.forkCost R+edgeBudget 0 as R)) at H
  rw [HF1,HF2,zero_add,zero_add] at H
  have HE:=hjTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R ≤
      M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left HE' (mul_nonneg hC.le M.canonical_direct_test_band_pos.le)
  convert HH using 1; ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_inherited_constant_fresh_full_Taylor_rate_along_of_pullback_clocks_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) (hCs : 0≤Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠ n : ℕ in atTop,(M n).xs^2≤Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀U : ℕ,star < U → U≤as.length → 2*c*W n≤partitionPoint 0 as U → partitionPoint 0 as U≤ min (Ccut*W n) 1 →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeActualTaylorRemainder (dim n) q U b h K g.tree (fun _=>1) a z|≤
              err n*(W n*(M n).xs^2) := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  obtain ⟨CH,hCH,HH⟩:=eventually_actual_shell_history_constant_fresh_HIGH_parts_rate_of_pullback_clocks_original_q
    (D:=D) (Cs:=Cs) Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hclock := Hshell
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_fresh_third_LOW_rate_along_original_q
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs
    dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall Hclock Homit w hw
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>2*CH*((dim n+1:ℕ):ℝ)^(-eta/256)+|eLow n|/2
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=(Hpow.const_mul (2*CH)).add (heLow.abs.div_const 2)
    simpa only [err,Function.comp_def,abs_zero,zero_mul,mul_zero,zero_div,add_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,HLow,Hsource,hsmall,HW1,Hshell,Hcutoff,HOmit] with n hnH hnL hsource hnSmall hnW hnShell hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hb := hnShell
  have hxW : (M n).xs≤W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hs0 hsxs hs64 hsource hb
      hnSmall (by simpa only [←hcanonical] using hnW) L us hus hret hmesh,
    hnL L us hus hret hmesh hstar] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U hs hU hcutlo hcut seedMass a z
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hbf:=(M n).sweep_bf_monotone
  have hhf:=(M n).sweep_hf_monotone
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).sweepBf u:ℝ)≤(M n).sweepBf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).sweepHf u:ℝ)≤(M n).sweepHf v from hhf hu hv huv) as ho
  let H:=CH*((dim n+1:ℕ):ℝ)^(-eta/256)*W n*(M n).xs^2
  let LL:=|eLow n| *(W n*(M n).xs^2)
  have hW : 0<W n:=(M n).hxs.trans_le hxW
  have hH : 0≤H:=by dsimp only [H];positivity
  have hLL : 0≤LL:=by dsimp only [LL];positivity
  have HHi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (part : Fin 3) :
      |nativeActualHigherHighPart part (dim n) q U b h K g.tree (fun _=>1) a z l t|≤H:=by
    have HH:=hgridH star U hs hU (by simpa only [←hcanonical] using hcutlo)
      (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) seedMass a z l t hl ht part
    simpa only [H,eta,ActualHighWallData.N,←hcanonical,neg_div] using HH
  have HLo (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
      |nativeActualCenteredThirdLowPart (dim n) q U b h K g.tree (fun _=>1) a z l t|≤LL:=by
    apply (hgridL U hs hU hcut seedMass a z l t hl ht).trans
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have HB:=native_actual_taylor_remainder_abs_le_HIGH_LOW (dim n) q U b h K g.tree ho (fun _=>1) a z
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg (dim n) (M n).sweepBf (M n).sweepHf hbf hhf as ho) hbm hhm
    (native_continuum_mixed_clock_monotone (dim n) (M n).sweepBf (M n).sweepHf hbf hhf as ho)
    H LL hH hLL HHi HLo
  apply HB.trans_eq
  dsimp only [H,LL,err]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_higher_Taylor_forest_rate_along_of_pullback_clocks_original_q
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourHigherTaylorError_original_q (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^2 := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  let eta:=actualMassSavingExponent m delta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_fresh_resource_HIGH_parts_from_minimum_original_q
    (D:=D) degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hclock := Hshell
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_resource_fresh_third_LOW_rate_along_original_q
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall Hclock Homit w hw
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks_original_q
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
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,HLow,Hsource,hsmall,Hshell,HW1,Hcutoff,HOmit] with n hnH hnTail hnL hsource hnSmall hnShell hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hs0 hsxs hsource hxs1 L us hus hret hmesh,
    hnL L us hus hret hmesh hstar,
    hnTail (M n) hs0 hsxs hs64 hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridL hgridTail
  dsimp only at hgridH hgridL hgridTail ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren_original_q (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as (4*Cf+2*Temp) Temp
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
    actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves_original_q (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid_original_q (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation_original_q (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
    simp only [partitionPoint,partitionValues_zero,id_eq]
    exact mul_nonneg hCmass (M n).hxs.le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourHigherTaylorError_original_q (M n) U (W n) Q| ≤
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
      |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceHigherHighPart_original_q (M n) U (Q.term.retarget 0) part l t| ≤
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
    have H0:=actual_minimum_normalized_fresh_resource_Taylor_abs_le_original_q (M n) U Q.generation Q.term ho hW
      (H:=|Q.term.coefficient| *(CH*W n*cost)) (L:=|Q.term.coefficient| *|eLow n| *(W n*(M n).xs^2))
      (by positivity) (by positivity) Hhigh0
      (fun l t hl ht=>(Hlow0 l t hl ht).trans Hlowmajor)
    have H1:=actual_minimum_normalized_fresh_resource_Taylor_abs_le_original_q (M n) U Q.generation (Q.term.retarget 0) ho hW
      (H:=|Q.term.coefficient| *(CH*W n*cost)) (L:=|Q.term.coefficient| *|eLow n| *(W n*(M n).xs^2))
      (by positivity) (by positivity) Hhigh1
      (fun l t hl ht=>(Hlow1 l t hl ht).trans Hlowmajor)
    have Herror:=actual_minimum_four_higher_Taylor_error_abs_le_original_q (M n) hCf hsource hxs1 Q ho hs hU hW hcK hB hstarK
      (by apply H0.trans_eq;dsimp only [B];ring)
      (by apply H1.trans_eq;dsimp only [B];ring)
    apply Herror.trans_eq
    dsimp only [BH,BL,B,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le hBH hBL depth children 3 Hleaves f R hf hR hflo hRlo
    (nativeActualOriginalFourHigherTaylorError_original_q (M n) U (W n)) Hrow
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q (M n)
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
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [show f=(fun j=>(R j)^(4/p)) from rfl,HReq]
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) (4/p) htheta1 htheta2.le hdeficit
    simpa only [←hcanonical,ActualHighWallData.N,eta,neg_div] using H
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

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_higher_Taylor_category_rate_along_of_pullback_clocks_original_q
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q (M n) U Q .higherTaylor)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_higher_Taylor_forest_rate_along_of_pullback_clocks_original_q
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall Hshell Homit w hw
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1,Hcutoff,HOmit] with n hn hsClocks hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  apply (actual_higher_Taylor_category_signed_sum_abs_le_error_sum_original_q (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj U hs hU hcutlo hcut hmassstar hstarK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_post_Taylor_envelope_along_of_pullback_clocks_original_q
    (depth : ℕ) (Bclock Temp Cf A cK cKcut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 < A) (hcK : 0 < cK) (hcKcut : 0 < cKcut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourcePostTaylorEnvelopeAlong_original_q depth Temp cK err M W w high outer := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  have HR d:=actual_inherited_constant_child_higher_Taylor_category_rate_along_of_pullback_clocks_original_q
    d Bclock Temp Cf A A cKcut hTemp hCf hA.le hA hcKcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall Hshell Homit w hw
  choose e he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper_original_q
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+A)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];positivity
  let err n:=((List.range depth).map (fun d=>|e d n|)).sum*(R/B)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>|e d n|)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil => simp only [List.map_nil,List.sum_nil]; exact tendsto_const_nhds
    | cons d ds ih => simpa only [List.map_cons,List.sum_cons,abs_zero,zero_add] using (he d).abs.add ih
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [zero_mul] using (Hlim (List.range depth)).mul_const (R/B)
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW,Hcutoff,HOmit] with n hn hclock hsource hcuts hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hs0 hsxs hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).sweepBf (M n).sweepHf
        (M n).sweep_bf_monotone (M n).sweep_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_pending_envelope_higher_Taylor_paid_original_q
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*|e d n|) (by
      intro d hd
      have H:=hj ⟨d,hd⟩ U hs hU Hlo Hupper Hmass HstarK
      change |nativeActualFourOtherCategorySum_original_q (M n) U (W n)
        (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)) .higherTaylor|/
          (chi*K star) ≤ e d n*(M n).xs^2 at H
      have H':=H.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg (M n).xs))
      exact actual_saved_denominator_upper_transfer hden hW hB (abs_nonneg _) Hd H')
  apply Hpaid.trans_eq
  dsimp only [err]
  rw [List.sum_map_mul_left]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_joint_HIGH_restoration_forest_rate_along_of_pullback_clocks_original_q
    (kind : NativeJointHighRestorationKind) (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourJointHighRestorationError_original_q kind (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^2 := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  let eta:=actualMassSavingExponent m delta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_fresh_resource_joint_HIGH_restoration_from_minimum_original_q
    (D:=D) kind degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks_original_q
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
  let err:=fun n=>(4*CH/Cd*Vp*J)*((dim n+1:ℕ):ℝ)^(-eta/256)
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul (4*CH/Cd*Vp*J)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,Hsource,hsmall,Hshell,HW1,Hcutoff,HOmit] with n hnH hnTail hsource hnSmall hnShell hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hs0 hsxs hsource hxs1 L us hus hret hmesh,
    hnTail (M n) hs0 hsxs hs64 hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridTail
  dsimp only at hgridH hgridTail ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren_original_q (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let BH:=2*CH/Cd
  let BL : ℝ:=0
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
    actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves_original_q (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid_original_q (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation_original_q (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
    simp only [partitionPoint,partitionValues_zero,id_eq]
    exact mul_nonneg hCmass (M n).hxs.le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointHighRestorationError_original_q kind (M n) U (W n) Q| ≤
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
    have Hhigh0:=hgridH 0 star U Q.generation [] Q.tree Q.term HV (Nat.zero_le star) hs hU
      (by dsimp only [rBound];omega) (by simpa using HD) (W n) hxW hW1
      Hmi hmassstar (hcut.trans (min_le_left _ _))
    have Hhigh1:=hgridH 0 star U Q.generation [] g.tree (Q.term.retarget 0) HV.retarget (Nat.zero_le star) hs hU
      hg (by simpa using HD) (W n) hxW hW1 Hmi hmassstar (hcut.trans (min_le_left _ _))
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at Hhigh0 Hhigh1
    have Hforkf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f hflo
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind (M n) U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *(CH*W n*(g.tree.forkCost f+edgeBudget 0 as f+W n*(g.tree.forkCost R+edgeBudget 0 as R))) at Hhigh1
    rw [show g.tree.forkCost f=Q.tree.forkCost f from Hforkf,show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Herror:=actual_minimum_four_joint_HIGH_restoration_error_abs_le_original_q kind (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ CH*cost by positivity) hstarK
      (by apply Hhigh0.trans_eq;dsimp only [cost];ring)
      (by apply Hhigh1.trans_eq;dsimp only [cost];ring)
    apply Herror.trans_eq
    dsimp only [BH,BL,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le hBH hBL depth children 3 Hleaves f R hf hR hflo hRlo
    (nativeActualOriginalFourJointHighRestorationError_original_q kind (M n) U (W n)) Hrow
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q (M n)
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
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).sweepBf (M n).sweepHf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [show f=(fun j=>(R j)^(4/p)) from rfl,HReq]
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) (4/p) htheta1 htheta2.le hdeficit
    simpa only [←hcanonical,ActualHighWallData.N,eta,neg_div] using H
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

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_joint_HIGH_restoration_category_rate_along_of_pullback_clocks_original_q
    (kind : NativeJointHighRestorationKind) (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star →
        let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q (M n) U Q kind.category)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  have HOmit : ∀ᶠn in atTop,64*(M n).data.s≤c*(M n).xs := by
    filter_upwards [Homit.eventually (eventually_le_nhds (div_pos hc (by norm_num : (0:ℝ)<64)))] with n hn
    have HH:=(div_le_iff₀ (M n).hxs).mp hn
    nlinarith only [HH]

  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_joint_HIGH_restoration_forest_rate_along_of_pullback_clocks_original_q
    kind depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource Hcutoff hsmall Hshell Homit w
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1,Hcutoff,HOmit] with n hn hsClocks hW1 hgate hs64
  have hs0 := hgate.1
  have hsxs := hgate.2
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  apply (actual_joint_HIGH_restoration_category_signed_sum_abs_le_error_sum_original_q kind (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj U hs hU hcutlo hcut hmassstar hstarK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 26000000

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
end OAI.SKFluctuations.Cavity
