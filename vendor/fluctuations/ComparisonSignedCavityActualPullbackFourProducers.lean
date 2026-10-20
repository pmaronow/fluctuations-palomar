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

@[expose] public section

noncomputable section
set_option linter.unusedVariables false

set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let Cerr:=Cavity.actualLowErrorComparisonConstant
          (4*Cf+2*Temp) Temp
        ∀U : ℕ,U≤as.length → 2*c*M.canonicalDirectTestBandScale≤partitionPoint 0 as U →
        ∀theta : ℝ,1≤theta → theta≤2 → 2-theta≤actualMassSavingExponent m delta/128 →
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr j)^theta)+
            M.canonicalDirectTestBandScale*ClockTree.edgeBudget 0 as
              (nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr)≤
            M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2  := by
  have H := eventually_actual_regular_original_target_high_envelope_powers
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  filter_upwards [H] with n hn
  intro M hclock hsmall hW1 us hus
  filter_upwards [hn M hclock hsmall hW1 us hus] with jGrid hj
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
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_gamma_HIGH_restoration_forest_rate_along_of_pullback_clocks
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
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
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
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
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
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH L us hus hret hmesh,
    hnTail (M n)  hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
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

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_gamma_HIGH_restoration_category_rate_along_of_pullback_clocks
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
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
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
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .gammaHighRestoration)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_gamma_HIGH_restoration_forest_rate_along_of_pullback_clocks
    depth Bclock Temp Cf Cmass Ccal cK hTemp hCf hCmass hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcutlo hmassstar hstarK
  apply (actual_gamma_restoration_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _ true).trans
  exact hj U hs hU hcutlo hmassstar hstarK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_gamma_restoration_on_given_cuts_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualConstantGammaRestorationOnGivenCutsAlong depth err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨eL,heL,HL⟩:=actual_inherited_constant_child_gamma_LOW_restoration_category_rate_along
    depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  obtain ⟨eH,heH,HH⟩:=actual_inherited_constant_child_gamma_HIGH_restoration_category_rate_along_of_pullback_clocks
    depth Bclock Temp Cf A Ccal cK hTemp hCf hA0.le hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource hcompare Hshell w
  let err n:=|eL n|+|eH n|
  have herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,abs_zero,zero_add] using heL.abs.add heH.abs
  refine ⟨err,(fun n=>by dsimp only [err];positivity),herr,?_⟩
  filter_upwards [HL,HH,Hcuts] with n hnL hnH hcuts
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
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_b0_category_envelope_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK cKcut A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourceB0CategoryEnvelopeAlong depth Temp cK err M W w high outer := by
  have HR d:=actual_inherited_constant_gamma_restoration_on_given_cuts_along_of_pullback_clocks
    d hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W radius hcanonical hWlim Hsource hcompare Hshell w high outer hw Hcuts
  choose e he0 he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
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
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
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
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_three_category_envelope_gamma_paid
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*(e d n)) (by
      intro d hd cat hcat
      obtain ⟨_,_,H⟩:=hj ⟨d,hd⟩
      have H':=H cat hcat
      change |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) cat|/
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

theorem eventually_actual_shell_history_constant_fresh_HIGH_parts_rate_of_pullback_clocks
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀(a z : g.tree.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
            |nativeActualHigherHighPart part n q U b h K g.tree (fun _=>1) a z l t| ≤
              C*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨C,hC,Hparts⟩:=eventually_actual_minimum_inherited_constant_HIGH_parts_profile
    (D:=D) 2 dOrder hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU hcutlo hcutup seedMass a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
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
      M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left HE' (mul_nonneg hC.le M.canonical_direct_test_band_pos.le)
  convert HH using 1; ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_inherited_constant_fresh_full_Taylor_rate_along_of_pullback_clocks
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) (hCs : 0≤Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠ n : ℕ in atTop,(M n).xs^2≤Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀U : ℕ,star < U → U≤as.length → 2*c*W n≤partitionPoint 0 as U → partitionPoint 0 as U≤ min (Ccut*W n) 1 →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeActualTaylorRemainder (dim n) q U b h K g.tree (fun _=>1) a z|≤
              err n*(W n*(M n).xs^2) := by
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_shell_history_constant_fresh_HIGH_parts_rate_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hclock := Hshell
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_fresh_third_LOW_rate_along
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs
    dim hdim M W hcanonical hWlim Hsource hsmall Hclock w hw
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
  filter_upwards [hdim.eventually HH,HLow,Hsource,hsmall,HW1,Hshell] with n hnH hnL hsource hnSmall hnW hnShell
  have hb := hnShell
  have hxW : (M n).xs≤W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n)  hsource hb
      hnSmall (by simpa only [←hcanonical] using hnW) L us hus hret hmesh,
    hnL L us hus hret hmesh hstar] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U hs hU hcutlo hcut seedMass a z
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).bf u:ℝ)≤(M n).bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).hf u:ℝ)≤(M n).hf v from hhf hu hv huv) as ho
  let H:=CH*((dim n+1:ℕ):ℝ)^(-eta/256)*W n*(M n).xs^2
  let LL:=|eLow n| *(W n*(M n).xs^2)
  have hW : 0<W n:=(M n).hxs.trans_le hxW
  have hH : 0≤H:=by dsimp only [H];positivity
  have hLL : 0≤LL:=by dsimp only [LL];positivity
  have HHi (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (part : Fin 3) :
      |nativeActualHigherHighPart part (dim n) q U b h K g.tree (fun _=>1) a z l t|≤H:=by
    have HH:=hgridH star U hs hU (by simpa only [←hcanonical] using hcutlo)
      (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) seedMass a z l t hl ht part
    simpa only [H,eta,NativeOverlapContext.N,←hcanonical,neg_div] using HH
  have HLo (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
      |nativeActualCenteredThirdLowPart (dim n) q U b h K g.tree (fun _=>1) a z l t|≤LL:=by
    apply (hgridL U hs hU hcut seedMass a z l t hl ht).trans
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have HB:=native_actual_taylor_remainder_abs_le_HIGH_LOW (dim n) q U b h K g.tree ho (fun _=>1) a z
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf hbf hhf as ho) hbm hhm
    (native_continuum_mixed_clock_monotone (dim n) (M n).bf (M n).hf hbf hhf as ho)
    H LL hH hLL HHi HLo
  apply HB.trans_eq
  dsimp only [H,LL,err]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_b0_on_strong_given_cuts_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2) (hCx : 0<Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualConstantB0OnStrongGivenCutsAlong depth err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  have Hclock := Hshell
  let F:=max (1+2*cu) (1+1/Rmacro)
  obtain ⟨eps,heps,hE,HE⟩:=actual_inherited_constant_resource_star_only_full_B0_saving_along
    (eta:=m) (1+depth) (3+6*depth+1) A A Ccal Rmacro F Cx hCx hm hTemp hCf hA0.le hA0.le hCcal
    hm hdelta hroom (by linarith) hcl hcu hAz hC0 hCt hmacro hRhalf (le_max_left _ _) (le_max_right _ _)
    dim hdim M W hcanonical hWlim w Hsource Hclock hcompare hw
  have HH:=actual_constant_resource_star_only_full_half_B0_from_resource_rows_along
    (1+depth) (3+6*depth) A A Rmacro Cx eps dim M W w HE
  obtain ⟨e,he,HF⟩:=actual_constant_child_star_only_full_B0_from_actual_half_rows_along
    depth Bclock Temp Cf A A Rmacro Cx cK hTemp hCf hcK dim M W hcanonical hWlim Hsource w
    (fun n=>(3/2:ℝ)*eps n) (fun n=>mul_nonneg (by norm_num) (heps n))
    (by simpa only [mul_zero] using hE.const_mul (3/2:ℝ)) HH
  refine ⟨fun n=>|e n|,(fun n=>abs_nonneg _),by simpa only [abs_zero] using he.abs,?_⟩
  filter_upwards [HF,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,_,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  obtain ⟨_,_,_,_,Hhighmass,_,Hfour,HstarR,Hz,HCx,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hupper:partitionPoint 0 as U≤A*W n:=(partitionPoint_mono as ho HUV.le).trans Houter
  let mid:=as.take star
  let tail:=as.drop star
  have hparts:as=mid++tail:=(List.take_append_drop star as).symm
  have hindex:mid.length=star:=List.length_take_of_le (retainedMassPrefixIndex_le_length _ _)
  have hs':mid.length<U:=by simpa only [hindex] using hs
  have hU':U≤(mid++tail).length:=by rw [←hparts];exact hU
  have H:=hj mid tail hparts hindex U hs' hU' Hupper
    (by simpa only [hindex] using Hmass) Hfour Hz (by simpa only [hindex] using HstarR)
    (high n).val (high n).property (by simpa only [Hhighmass] using HCx) Hhighmass hnodes
    (by simpa only [hindex] using HstarK)
  refine ⟨hs,hU,?_⟩
  have H':=H.trans (mul_le_mul_of_nonneg_right (le_abs_self (e n)) (sq_nonneg _))
  exact actual_constant_second_low_family_reindex (M n) as mid tail hparts star U hindex
    hs hU hs' hU' (W n) (|e n| *(M n).xs^2) depth H'

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_full_b0_envelope_saving_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK cKcut A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hcKcut : 0 < cKcut)
    (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2) (hCx : 0<Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A Rmacro Cx) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantFullB0EnvelopeSavingAlong depth Temp cK err M W w high outer := by
  have HR d:=actual_inherited_constant_b0_on_strong_given_cuts_along_of_pullback_clocks
    d hA hcKcut hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W radius hcanonical hWlim Hsource hcompare Hshell w high outer hw Hcuts
  choose e he0 he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+A)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];linarith [mul_pos hCK (show 0 < 1+A by linarith)]
  let err n:=((List.range depth).map (fun d=>e d n)).sum*(R/B)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>e d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil => simp only [List.map_nil,List.sum_nil]; exact tendsto_const_nhds
    | cons d ds ih => simpa only [List.map_cons,List.sum_cons,zero_add] using (he d).add ih
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [mul_zero,zero_mul] using (Hlim (List.range depth)).mul_const (R/B)
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hnet:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter hnodes)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hrow d (hd : d∈List.range depth) :
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) .secondLow|/
        (Real.exp (-4*Temp)*cK*W n) ≤ R/B*(e d n)*(M n).xs^2:=by
    obtain ⟨_,_,H⟩:=hj ⟨d,List.mem_range.mp hd⟩
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
        (nativeActualConstantSourceChildren (M n) as star U hs hU)) .secondLow|/
      (chi*K star) ≤ e d n*(M n).xs^2 at H
    exact actual_saved_denominator_upper_transfer hden hW hB (he0 d n) Hd H
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_mul_left,List.sum_map_mul_right] at Hsum
  simp only [nativeActualConstantSourceB0CategoryEnvelope,nativeActualFinalB0SourceCategories,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  apply Hsum.trans_eq
  dsimp only [err]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_higher_Taylor_forest_rate_along_of_pullback_clocks
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
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
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
  have Hclock := Hshell
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_resource_fresh_third_LOW_rate_along
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim Hsource hsmall Hclock w hw
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
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
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hsource hxs1 L us hus hret hmesh,
    hnL L us hus hret hmesh hstar,
    hnTail (M n)  hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
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

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_higher_Taylor_category_rate_along_of_pullback_clocks
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
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
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
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .higherTaylor)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_higher_Taylor_forest_rate_along_of_pullback_clocks
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w hw
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  apply (actual_higher_Taylor_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj U hs hU hcutlo hcut hmassstar hstarK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_post_Taylor_envelope_along_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf A cK cKcut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 < A) (hcK : 0 < cK) (hcKcut : 0 < cKcut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourcePostTaylorEnvelopeAlong depth Temp cK err M W w high outer := by
  have HR d:=actual_inherited_constant_child_higher_Taylor_category_rate_along_of_pullback_clocks
    d Bclock Temp Cf A A cKcut hTemp hCf hA.le hA hcKcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w hw
  choose e he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
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
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
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
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_pending_envelope_higher_Taylor_paid
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*|e d n|) (by
      intro d hd
      have H:=hj ⟨d,hd⟩ U hs hU Hlo Hupper Hmass HstarK
      change |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) .higherTaylor|/
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
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_joint_HIGH_restoration_forest_rate_along_of_pullback_clocks
    (kind : NativeJointHighRestorationKind) (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
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
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourJointHighRestorationError kind (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^2 := by
  let eta:=actualMassSavingExponent m delta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_fresh_resource_joint_HIGH_restoration_from_minimum
    (D:=D) kind degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
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
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,Hsource,hsmall,Hshell,HW1] with
    n hnH hnTail hsource hnSmall hnShell hW1
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hsource hxs1 L us hus hret hmesh,
    hnTail (M n)  hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridTail
  dsimp only at hgridH hgridTail ⊢
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
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointHighRestorationError kind (M n) U (W n) Q| ≤
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
    change |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceJointHighRestoration kind (M n) U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *(CH*W n*(g.tree.forkCost f+edgeBudget 0 as f+W n*(g.tree.forkCost R+edgeBudget 0 as R))) at Hhigh1
    rw [show g.tree.forkCost f=Q.tree.forkCost f from Hforkf,show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Herror:=actual_minimum_four_joint_HIGH_restoration_error_abs_le kind (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ CH*cost by positivity) hstarK
      (by apply Hhigh0.trans_eq;dsimp only [cost];ring)
      (by apply Hhigh1.trans_eq;dsimp only [cost];ring)
    apply Herror.trans_eq
    dsimp only [BH,BL,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le hBH hBL depth children 3 Hleaves f R hf hR hflo hRlo
    (nativeActualOriginalFourJointHighRestorationError kind (M n) U (W n)) Hrow
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

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_constant_child_joint_HIGH_restoration_category_rate_along_of_pullback_clocks
    (kind : NativeJointHighRestorationKind) (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
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
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q kind.category)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_joint_HIGH_restoration_forest_rate_along_of_pullback_clocks
    kind depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcutlo hcut hmassstar hstarK
  apply (actual_joint_HIGH_restoration_category_signed_sum_abs_le_error_sum kind (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj U hs hU hcutlo hcut hmassstar hstarK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_saved_joint_on_given_cuts_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (saving : ℝ) (hsaving : 0 ≤ saving)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualConstantSavedJointOnGivenCutsAlong depth err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨C,hC,HG⟩:=eventually_inherited_same_star_constant_source_retained_Gamma_along
    (eta:=m) hdim depth A cK hA hcK hm hm hdelta hroom (by linarith)
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare Hsource saving hsaving w Hmixed
  obtain ⟨eL,heL,HL⟩:=actual_inherited_constant_child_joint_LOW_restoration_category_rate_along
    depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  have HH kind:=actual_inherited_constant_child_joint_HIGH_restoration_category_rate_along_of_pullback_clocks
    kind depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK (Cs:=Ccal^2)
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
    dim hdim M W hcanonical hWlim Hsource hcompare Hshell w
  obtain ⟨eH,heH,HH⟩:=HH .lowTwoHigh
  obtain ⟨eF,heF,HF⟩:=actual_inherited_constant_child_joint_HIGH_restoration_category_rate_along_of_pullback_clocks
    .fourGLow depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK (Cs:=Ccal^2)
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
    dim hdim M W hcanonical hWlim Hsource hcompare Hshell w
  let eG n:=C*(dim n:ℝ)^(-m)
  let err n:=eG n+|eL n|+|eH n|+|eF n|
  have hG n : 0 ≤ eG n:=by dsimp only [eG];positivity
  have heG : Tendsto eG atTop (𝓝 0):=by
    simpa only [eG,Function.comp_def,mul_zero] using
      ((tendsto_rpow_neg_atTop hm).comp (tendsto_natCast_atTop_atTop.comp hdim)).const_mul C
  have herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,abs_zero,zero_add] using ((heG.add heL.abs).add heH.abs).add heF.abs
  refine ⟨err,(fun n=>by dsimp only [err];positivity),herr,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HG,HL,HH,HF,Hcuts,Hsource,HW] with n hnG hnL hnH hnF hcuts hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnG L us hus hret hmesh hstar,hnL L us hus hret hmesh hstar,
    hnH L us hus hret hmesh hstar,hnF L us hus hret hmesh hstar] with jGrid hjG hjL hjH hjF
  dsimp only at hjG hjL hjH hjF ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,Hrad,Hrad1,HradU,HstarR,Hz,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  have HG':=(actual_retained_gamma_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks
    (hxW.trans hW1) ho hs hU hW hcK HstarK _).trans
      (hjG U hs hU (radius n) Hmass Hrad Hrad1 HradU HstarR Hz HstarK)
  have HL':=hjL U hs hU Hupper Hmass HstarK
  have HH':=hjH U hs hU Hlo Hupper Hmass HstarK
  have HF':=hjF U hs hU Hlo Hupper Hmass HstarK
  refine ⟨hs,hU,?_⟩
  intro cat hcat
  simp only [nativeActualSavedJointSourceCategories,List.mem_cons,List.not_mem_nil,or_false] at hcat
  have hge : eG n ≤ err n:=by
    dsimp only [err]
    linarith [abs_nonneg (eL n),abs_nonneg (eH n),abs_nonneg (eF n)]
  have hle : eL n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eL n),abs_nonneg (eH n),abs_nonneg (eF n),hG n]
  have hhe : eH n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eH n),abs_nonneg (eL n),abs_nonneg (eF n),hG n]
  have hfe : eF n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eF n),abs_nonneg (eL n),abs_nonneg (eH n),hG n]
  rcases hcat with rfl|rfl|rfl|rfl
  · exact HG'.trans (mul_le_mul_of_nonneg_right hge (sq_nonneg _))
  · exact HL'.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _))
  · exact HH'.trans (mul_le_mul_of_nonneg_right hhe (sq_nonneg _))
  · exact HF'.trans (mul_le_mul_of_nonneg_right hfe (sq_nonneg _))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_constant_three_category_envelope_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK cKcut A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (saving : ℝ) (hsaving : 0 ≤ saving)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourceThreeCategoryEnvelopeAlong depth Temp cK err M W w high outer := by
  have HR d:=actual_inherited_constant_saved_joint_on_given_cuts_along_of_pullback_clocks
    d hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W radius hcanonical hWlim Hsource hcompare Hshell saving hsaving w high outer hw Hmixed Hcuts
  choose e he0 he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+A)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];linarith [mul_pos hCK (show 0 < 1+A by linarith)]
  let err n:=4*((List.range depth).map (fun d=>e d n)).sum*(R/B)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>e d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil => simp only [List.map_nil,List.sum_nil]; exact tendsto_const_nhds
    | cons d ds ih => simpa only [List.map_cons,List.sum_cons,zero_add] using (he d).add ih
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [mul_zero,zero_mul] using ((Hlim (List.range depth)).const_mul 4).mul_const (R/B)
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
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
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_post_longitudinal_envelope_joint_paid
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*(e d n)) (by
      intro d hd cat hcat
      obtain ⟨_,_,H⟩:=hj ⟨d,hd⟩
      have H':=H cat hcat
      change |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) cat|/
        (chi*K star) ≤ e d n*(M n).xs^2 at H'
      exact actual_saved_denominator_upper_transfer hden hW hB (he0 d n) Hd H')
  apply Hpaid.trans_eq
  dsimp only [err]
  simp only [List.sum_map_mul_left]
  ring

end OAI.SKFluctuations.Cavity

set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_higher_Taylor_forest_modulus_along_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Cinitial Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCinitial : 0 ≤ Cinitial) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        0 < V → i < V → V ≤ star → partitionPoint 0 as V ≤ Cinitial*(M n).xs →
        partitionPoint 0 as i ≤ Cmass*(M n).xs →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>|nativeActualOriginalFourHigherTaylorError (M n) U (W n) Q|)).sum ≤
            Ci*(M n).xs^2*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*(M n).xs^3 := by
  let eta:=actualMassSavingExponent m delta
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_fresh_resource_HIGH_parts_from_minimum
    (D:=D) degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hclock := Hshell
  obtain ⟨CiLow,hCiLow,eLow,heLow,hELow,HLow⟩:=actual_inherited_initial_fresh_resource_third_LOW_saving_along
    degree (rBound+1) Bclock Temp Cf Cmass Cinitial Ccut hTemp hCf hCmass hCinitial hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim Hsource hsmall Hclock w hw
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc hcouter
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vp:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ (by dsimp only [Cw,Cd];positivity) _ _ _
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVp : 0 ≤ Vp:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(8*CH/Cd*Vp)*((dim n+1:ℕ):ℝ)^(-eta/256)+(2*Vv/Cd)*eLow n
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have HH:=(Hpow.const_mul (8*CH/Cd*Vp)).add (hELow.const_mul (2*Vv/Cd))
    simpa only [err,Function.comp_def,mul_zero,add_zero,neg_div] using HH
  have hErr n : 0 ≤ err n:=by
    have HL:=heLow n
    dsimp only [err]
    positivity
  refine ⟨2*Vv/Cd*CiLow+1,by positivity,err,hErr,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,HLow,Hsource,hsmall,Hshell,HW1] with
    n hnH hnTail hnLow hsource hnSmall hnShell hW1
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  have hx : 0 < (M n).xs:=(M n).hxs
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hsource hxs1 L us hus hret hmesh,
    hnLow L us hus hret hmesh hstar,
    hnTail (M n)  hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridLow hgridTail
  dsimp only at hgridH hgridLow hgridTail ⊢
  intro i V U hi hs hU hcutlo hcut hV hiV hVstar hcutI hmi hmassstar hstarK seedMass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let root:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let children:=[root]
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).bf (M n).hf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let BH:=4*CH/Cd
  let initialError:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))
  let lowPrice:=CiLow*(M n).xs*initialError+eLow n*(M n).xs^2
  let BL:=(M n).xs/Cd*lowPrice
  have hInitialError:0 ≤ initialError:=by
    dsimp only [initialError,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have hLowPrice:0 ≤ lowPrice:=by
    have HL:=heLow n
    dsimp only [lowPrice];positivity
  have hBL:0 ≤ BL:=by dsimp only [BL];positivity
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have hflo j (hj : j<U) : f j=0:=by dsimp only [f];rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have hBH : 0 ≤ BH:=by dsimp only [BH];positivity
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hroot : NativeActualResourceGenerated i star U [.initial] root.generation root.tree root.term:=
    .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 2:=by
    have HQ : Q=root:=List.mem_singleton.mp hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;exact Hroot) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    0 (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    2 Hleaves Q hQ
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourHigherTaylorError (M n) U (W n) Q| ≤
      |Q.term.coefficient| *((BH*(M n).xs)*(Q.tree.forkCost f+edgeBudget 0 as f+
        W n*(Q.tree.forkCost R+edgeBudget 0 as R))+BL):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : 1+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    let cost:=Q.tree.forkCost f+edgeBudget 0 as f+W n*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have HF:=add_nonneg (Q.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
      have HR:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost];positivity
    have Hhigh0 l t hl ht part:=hgridH i star U Q.generation [.initial] Q.tree Q.term HV hi hs hU
      (by dsimp only [rBound];omega) (by simpa using HD) (M n).xs (W n) le_rfl hxW hW1 hmi hmassstar hcut l t hl ht part
    have Hhigh1 l t hl ht part:=hgridH i star U Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hi hs hU
      hg (by simpa using HD) (M n).xs (W n) le_rfl hxW hW1 hmi hmassstar hcut l t hl ht part
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one] at Hhigh0 Hhigh1
    have Hforkf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f hflo
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change ∀l t,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceHigherHighPart (M n) U (Q.term.retarget 0) part l t| ≤
      |Q.term.coefficient| *(M n).xs*(CH*W n*(g.tree.forkCost f+edgeBudget 0 as f+W n*(g.tree.forkCost R+edgeBudget 0 as R))) at Hhigh1
    rw [show g.tree.forkCost f=Q.tree.forkCost f from Hforkf,show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Hlow0 l t hl ht:=hgridLow i V U Q.generation [.initial] Q.tree Q.term HV hU
      (by dsimp only [rBound];omega) (by simpa using HD) hV hiV hVstar hs hcutI hmi hmassstar hcut l t hl ht
    have Hlow1 l t hl ht:=hgridLow i V U Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hU
      hg (by simpa using HD) hV hiV hVstar hs hcutI hmi hmassstar hcut l t hl ht
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one,NativeResourceTerm.retarget] at Hlow0 Hlow1
    let B:=2*CH*(M n).xs*cost+(M n).xs/2*lowPrice
    have hB:0 ≤ B:=by dsimp only [B];positivity
    have H0:=actual_minimum_normalized_fresh_resource_Taylor_abs_le (M n) U Q.generation Q.term ho hW
      (H:=|Q.term.coefficient| *((M n).xs*CH*W n*cost)) (L:=|Q.term.coefficient| *(M n).xs*W n*lowPrice)
      (by positivity) (by positivity)
      (by
        intro l t hl ht part
        convert Hhigh0 l t hl ht part using 1
        all_goals try dsimp only [cost]
        all_goals ring)
      (by
        intro l t hl ht
        convert Hlow0 l t hl ht using 1
        all_goals try dsimp only [lowPrice,initialError,as,NativeResourceTerm.retarget]
        all_goals ring)
    have H1:=actual_minimum_normalized_fresh_resource_Taylor_abs_le (M n) U Q.generation (Q.term.retarget 0) ho hW
      (H:=|Q.term.coefficient| *((M n).xs*CH*W n*cost)) (L:=|Q.term.coefficient| *(M n).xs*W n*lowPrice)
      (by positivity) (by positivity)
      (by
        intro l t hl ht part
        convert Hhigh1 l t hl ht part using 1
        all_goals try dsimp only [cost]
        all_goals ring)
      (by
        intro l t hl ht
        convert Hlow1 l t hl ht using 1
        all_goals try dsimp only [lowPrice,initialError,as,NativeResourceTerm.retarget]
        all_goals ring)
    have Herror:=actual_minimum_four_higher_Taylor_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU hW hcK hB hstarK
      (by apply H0.trans_eq;dsimp only [B];ring)
      (by apply H1.trans_eq;dsimp only [B];ring)
    apply Herror.trans_eq
    dsimp only [BH,BL,B,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le (show 0 ≤ BH*(M n).xs by positivity) hBL depth children 2 Hleaves f R hf hR hflo hRlo
    (nativeActualOriginalFourHigherTaylorError (M n) U (W n)) Hrow
  have Hfamily (ff : ℕ→ℝ) (hfflo : ∀j,j<U→ff j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost ff+edgeBudget 0 as ff))).sum = edgeBudget 0 as ff:=by
    have Hfork:=nativeActualInitialState_high_forkCost_zero (S:=Spin (dim n)×Bool)
      as i star U hi hs (hi.trans (hs.le.trans hU)) seedMass ff hfflo
    simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change |(1:ℝ)| *(root.tree.forkCost ff+edgeBudget 0 as ff)=_
    rw [show root.tree.forkCost ff=0 from Hfork]
    norm_num
  rw [Hfamily f hflo,Hfamily R hRlo] at Hsum
  have Hcoeff:(children.map (fun Q=>|Q.term.coefficient|)).sum=1:=by
    simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change |(1:ℝ)|=1
    norm_num
  rw [Hcoeff] at Hsum
  have Hrate : edgeBudget 0 as f+W n*edgeBudget 0 as R ≤
      ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [show f=(fun j=>(R j)^(4/p)) from rfl,HReq]
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) (4/p) htheta1 htheta2.le hdeficit
    simpa only [←hcanonical,NativeOverlapContext.N,eta,neg_div] using H
  apply Hsum.trans
  have Hfinal:=add_le_add_right (mul_le_mul_of_nonneg_left Hrate (show 0 ≤ 2*(BH*(M n).xs)*Vp by positivity)) (2*BL*Vv*1)
  have Hfinal' : 2*(BH*(M n).xs)*Vp*(edgeBudget 0 as f+W n*edgeBudget 0 as R)+2*BL*Vv*1 ≤
      2*(BH*(M n).xs)*Vp*(((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2)+2*BL*Vv*1:=by
    convert Hfinal using 1 <;> ring
  apply Hfinal'.trans
  have Hinitial:=mul_le_mul_of_nonneg_right (show 2*Vv/Cd*CiLow ≤ 2*Vv/Cd*CiLow+1 by linarith)
    (show 0 ≤ (M n).xs^2*initialError by positivity)
  have Htotal:=add_le_add_right Hinitial (err n*(M n).xs^3)
  convert Htotal using 1 <;> dsimp only [err,BH,BL,lowPrice,initialError,as] <;> ring

end OAI.SKFluctuations.Cavity

set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_higher_Taylor_category_modulus_along_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Cinitial Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCinitial : 0 ≤ Cinitial) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        0 < V → i < V → V ≤ star → partitionPoint 0 as V ≤ Cinitial*(M n).xs →
        partitionPoint 0 as i ≤ Cmass*(M n).xs →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .higherTaylor)).sum|/
          (chi*K star) ≤
            Ci*(M n).xs^2*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*(M n).xs^3 := by
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_higher_Taylor_forest_modulus_along_of_pullback_clocks
    depth Bclock Temp Cf Cmass Cinitial Ccut cK hTemp hCf hCmass hCinitial hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w hw
  refine ⟨Ci,hCi,err,herr,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW:(M n).xs≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW:0< W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i V U hi hs hU hcutlo hcut hV hiV hVstar hcutI hmi hmassstar hstarK seedMass
  apply (actual_higher_Taylor_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj i V U hi hs hU hcutlo hcut hV hiV hVstar hcutI hmi hmassstar hstarK seedMass

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_joint_HIGH_restoration_forest_rate_along_of_pullback_clocks
    (kind : NativeJointHighRestorationKind) (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>|nativeActualOriginalFourJointHighRestorationError kind (M n) U (W n) Q|)).sum ≤
            err n*(x n*(M n).xs^2) := by
  let eta:=actualMassSavingExponent m delta
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_minimum_inherited_working_scale_fresh_resource_joint_HIGH_restoration_from_minimum
    (D:=D) kind degree dOrder (rBound+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc hcouter
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vp:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVp : 0 ≤ Vp:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(4*CH/Cd*Vp)*((dim n+1:ℕ):ℝ)^(-eta/256)
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul (4*CH/Cd*Vp)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HH,hdim.eventually Htail,Hsource,hsmall,Hshell,HW1,hxsx,hxW] with
    n hnH hnTail hsource hnSmall hnShell hW1 hnx hnW
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  have hx : 0 < x n:=(M n).hxs.trans_le hnx
  intro L us hus hret hmesh hstar
  filter_upwards [hnH (M n) hsource hxs1 L us hus hret hmesh,
    hnTail (M n)  hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridTail
  dsimp only at hgridH hgridTail ⊢
  intro i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let root:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let children:=[root]
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth children
  let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).bf (M n).hf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let BH:=2*CH/Cd
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have hflo j (hj : j<U) : f j=0:=by dsimp only [f];rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have hBH : 0 ≤ BH:=by dsimp only [BH];positivity
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hroot : NativeActualResourceGenerated i star U [.initial] root.generation root.tree root.term:=
    .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 2:=by
    have HQ : Q=root:=List.mem_singleton.mp hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;exact Hroot) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    0 (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    2 Hleaves Q hQ
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointHighRestorationError kind (M n) U (W n) Q| ≤
      |Q.term.coefficient| *((BH*x n)*(Q.tree.forkCost f+edgeBudget 0 as f+
        W n*(Q.tree.forkCost R+edgeBudget 0 as R))+0):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : 1+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    let cost:=Q.tree.forkCost f+edgeBudget 0 as f+W n*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have HF:=add_nonneg (Q.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
      have HR:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost];positivity
    have Hhigh0:=hgridH i star U Q.generation [.initial] Q.tree Q.term HV hi hs hU
      (by dsimp only [rBound];omega) (by simpa using HD) (x n) (W n) hnx hnW hW1 hmi hmassstar hcut
    have Hhigh1:=hgridH i star U Q.generation [.initial] g.tree (Q.term.retarget 0) HV.retarget hi hs hU
      hg (by simpa using HD) (x n) (W n) hnx hnW hW1 hmi hmassstar hcut
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one] at Hhigh0 Hhigh1
    have Hforkf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f hflo
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |((W n)⁻¹)^Q.generation*nativeActualOriginalFreshResourceJointHighRestoration kind (M n) U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *x n*(CH*W n*(g.tree.forkCost f+edgeBudget 0 as f+W n*(g.tree.forkCost R+edgeBudget 0 as R))) at Hhigh1
    rw [show g.tree.forkCost f=Q.tree.forkCost f from Hforkf,show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Herror:=actual_minimum_four_joint_HIGH_restoration_error_abs_le kind (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ x n*CH*cost by positivity) hstarK
      (by apply Hhigh0.trans_eq;dsimp only [cost];ring)
      (by apply Hhigh1.trans_eq;dsimp only [cost];ring)
    apply Herror.trans_eq
    dsimp only [BH,cost,Cd]
    ring
  have Hsum:=nativeActualFourCenteredForest_profile_and_constant_sum_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW hW.le (show 0 ≤ BH*x n by positivity) (le_refl 0) depth children 2 Hleaves f R hf hR hflo hRlo
    (fun Q=>nativeActualOriginalFourJointHighRestorationError kind (M n) U (W n) Q) Hrow
  have Hfamily (ff : ℕ→ℝ) (hfflo : ∀j,j<U→ff j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost ff+edgeBudget 0 as ff))).sum = edgeBudget 0 as ff:=by
    have Hfork:=nativeActualInitialState_high_forkCost_zero (S:=Spin (dim n)×Bool)
      as i star U hi hs (hi.trans (hs.le.trans hU)) seedMass ff hfflo
    simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change |(1:ℝ)| *(root.tree.forkCost ff+edgeBudget 0 as ff)=_
    rw [show root.tree.forkCost ff=0 from Hfork]
    norm_num
  rw [Hfamily f hflo,Hfamily R hRlo] at Hsum
  simp only [mul_zero,zero_mul,add_zero] at Hsum
  have Hrate : edgeBudget 0 as f+W n*edgeBudget 0 as R ≤
      ((dim n+1:ℕ):ℝ)^(-eta/256)*(M n).xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope (dim n) U (M n).bf (M n).hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [show f=(fun j=>(R j)^(4/p)) from rfl,HReq]
    have H:=hgridTail U hU (by simpa only [hcanonical] using hcutlo) (4/p) htheta1 htheta2.le hdeficit
    simpa only [←hcanonical,NativeOverlapContext.N,eta,neg_div] using H
  apply Hsum.trans
  have Hfinal:=mul_le_mul_of_nonneg_left Hrate (show 0 ≤ 2*(BH*x n)*Vp by positivity)
  convert Hfinal using 1; dsimp only [err,BH]; ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_joint_HIGH_restoration_category_rate_along_of_pullback_clocks
    (kind : NativeJointHighRestorationKind) (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]) kind.category|/
          (chi*K star) ≤ err n*(x n*(M n).xs^2) := by
  obtain ⟨err,herr,H⟩:=actual_inherited_initial_joint_HIGH_restoration_forest_rate_along_of_pullback_clocks
    kind depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource x hxsx hxW hsmall Hshell w
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass
  apply (actual_joint_HIGH_restoration_category_signed_sum_abs_le_error_sum kind (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_shell_history_resource_longitudinal_restoration_forest_with_seed_atoms_of_pullback_clocks
    (seedBound k₀ r₀ depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃p : ℝ,2 < p ∧ 1 ≤ 4/p ∧ 4/p < 2 ∧
      2-4/p ≤ actualMassSavingExponent m delta/128 ∧
      ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
        i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x → ∀right : Bool,
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        let f2:=fun j=>((R j)^(2/p))^2
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
          |st.term.coefficient| *C*nativeResourceScale x W 1 seed*
            (st.tree.forkCost f2+W*st.tree.forkCost R+
              M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2) := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=exists_native_high_profile_holder_orders heta
  let degree:=seedBound+k₀+depth
  obtain ⟨Csrc,hCsrc,Hsource⟩:=eventually_actual_minimum_inherited_fresh_resource_longitudinal_restoration_profile
    (D:=D) degree dOrder (r₀+6*depth+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0 ≤ Vcost:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let C:=4*Csrc*Vcost+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨p,hp,htheta1,htheta2,hdeficit,C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro i star U seed st hseed hgen hleaf hP hi hs hU hcutlo hcutup hmassstar hstarK x hx hxW hmi right
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let seedScale:=nativeResourceScale x W 1 seed
  let B:=2*Csrc*seedScale
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=M.canonical_direct_test_band_pos
  have hx0 : 0 < x:=M.hxs.trans_le hx
  have hscale : 0 ≤ seedScale:=(actual_resource_raw_scale_pos seed hx0 hW).le
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourLongitudinalError M U W Q right| ≤
      |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
        W*(Q.tree.forkCost R+edgeBudget 0 as R)) := by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hP) Q hQ
    have Hgen:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hgen) Q hQ
    have Hleaves:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hleaf) Q hQ
    have Hdegree : seed.length+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ r₀+6*depth+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      omega
    let cost:=Q.tree.forkCost f2+edgeBudget 0 as f2+W*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have H2:=add_nonneg (Q.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have H1:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost]
      positivity
    have Hpow : (fun j=>(R j)^(4/p))=f2:=by
      funext j
      dsimp only [f2]
      rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
      congr 1
      ring
    have H0:=hgridSource i star U Q.generation seed Q.tree Q.term Hvalid hi hs hU (by omega)
      Hdegree x W hx hxW hW1 hmi hmassstar hcutup right
    have H1:=hgridSource i star U Q.generation seed g.tree (Q.term.retarget 0) Hvalid.retarget hi hs hU hg
      Hdegree x W hx hxW hW1 hmi hmassstar hcutup right
    change |(W⁻¹)^Q.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U Q.term right| ≤
      |Q.term.coefficient| *seedScale*(Csrc*(Q.tree.forkCost (fun j=>(R j)^(4/p))+
        edgeBudget 0 as (fun j=>(R j)^(4/p))+W*(Q.tree.forkCost R+edgeBudget 0 as R))) at H0
    change |(W⁻¹)^Q.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U (Q.term.retarget 0) right| ≤
      |Q.term.coefficient| *seedScale*(Csrc*(g.tree.forkCost (fun j=>(R j)^(4/p))+
        edgeBudget 0 as (fun j=>(R j)^(4/p))+W*(g.tree.forkCost R+edgeBudget 0 as R))) at H1
    rw [Hpow] at H0 H1
    have Hf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f2 hf2lo
    have HR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    rw [show g.tree.forkCost f2=Q.tree.forkCost f2 from Hf,
      show g.tree.forkCost R=Q.tree.forkCost R from HR] at H1
    have Hbound:=actual_four_longitudinal_error_abs_le M W Q right
      (B:=|Q.term.coefficient| *seedScale*(Csrc*cost)) (by positivity) H0 H1
    apply Hbound.trans_eq
    dsimp only [B,cost]
    ring
  have Hsum:=actual_minimum_four_longitudinal_restoration_forest_profile_le M ho hs hU hTemp hCf hsource hxs1
    hW hcK hB hstarK right depth st hleaf f2 R hf2 hR hf2lo hRlo Hrow
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ M.context.N^(-eta/256)*M.xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    simpa only [W,as,eta,neg_div] using hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have Hcost : st.tree.forkCost f2+edgeBudget 0 as f2+W*(st.tree.forkCost R+edgeBudget 0 as R) ≤
      st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2:=by
    linarith only [Hrate]
  have HtailBound:=mul_le_mul_of_nonneg_left Hcost
    (show 0 ≤ 2*|st.term.coefficient| *B*Vcost by positivity)
  have HseedCost : 0 ≤ st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2:=by
    have H2:=st.tree.forkCost_nonneg hf2
    have H1:=st.tree.forkCost_nonneg hR
    positivity
  have Hmajor:=mul_le_mul_of_nonneg_left
    (show 4*Csrc*Vcost ≤ C by dsimp only [C];linarith)
    (show 0 ≤ |st.term.coefficient| *seedScale*
      (st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2) by positivity)
  have Hfinal : 2*|st.term.coefficient| *B*Vcost*
      (st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2) ≤
      |st.term.coefficient| *C*seedScale*
      (st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2):=by
    convert Hmajor using 1 <;> (try dsimp only [B]) <;> ring
  apply Hsum.trans
  simpa only [eta,seedScale,W,neg_div] using HtailBound.trans Hfinal

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_shell_history_initial_longitudinal_forest_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x → ∀right : Bool,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2*x := by
  obtain ⟨p,hp,_,_,_,C,hC,H⟩:=eventually_actual_shell_history_resource_longitudinal_restoration_forest_with_seed_atoms_of_pullback_clocks
    1 0 2 depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually H] with n hn
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  filter_upwards [hn M  hsource hb hsmall hW1 L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi hs hU hlo hup hstarKmass hstarK x hx hxW hmi right
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have HR:=hj i star U [.initial] st (by simp) rfl
    (nativeActualInitialState_leaves_le as i star 0 (hi.trans (hs.le.trans hU)))
    hP hi hs hU hlo hup hstarKmass hstarK x hx hxW hmi right
  let R:=nativeOriginalHighErrorEnvelope (dim n) U M.bf M.hf as (4*Cf+2*Temp) Temp
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : ((R j)^(2/p))^2=0:=by
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have HF:=actual_initial_four_seed_high_fork_free (S:=Spin (dim n)×Bool) i star U hi hs hU 0
    (fun j=>((R j)^(2/p))^2) hflo
  have HR0:=actual_initial_four_seed_high_fork_free (S:=Spin (dim n)×Bool) i star U hi hs hU 0 R hRlo
  change ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
      (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
      |st.term.coefficient| *C*nativeResourceScale x W 1 [.initial]*
        (st.tree.forkCost (fun j=>((R j)^(2/p))^2)+W*st.tree.forkCost R+
          M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2) at HR
  rw [HF,HR0] at HR
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one,mul_zero,zero_mul,zero_add,mul_assoc,mul_left_comm,mul_comm] using HR

theorem eventually_actual_shell_history_initial_longitudinal_category_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x → ∀right : Bool,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum M U W
          (nativeActualMinimumFourCenteredForest M hs hU W depth [st])
          (nativeActualLongitudinalCategory right)|/(chi*K star) ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2*x := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_initial_longitudinal_forest_rate_along_of_pullback_clocks
    dim hdim depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  filter_upwards [hn M  hsource hb hsmall hW1 L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi hs hU hlo hup hmassstar hstarK x hx hxW hmi right
  have hW:=M.hxs.trans_le M.canonical_direct_test_band_ge_scale
  have HR:=actual_longitudinal_category_signed_sum_abs_le_error_sum M hCf hsource
    (M.canonical_direct_test_band_ge_scale.trans hW1) (finiteCutMasses_ordered us hus jGrid)
    hs hU hW hcK hstarK
    (nativeActualMinimumFourCenteredForest M hs hU M.canonicalDirectTestBandScale depth
      [nativeActualInitialState (S:=Spin (dim n)×Bool) (finiteCutMasses us jGrid) i star 0
        (hi.trans (hs.le.trans hU))]) right
  exact HR.trans (hj i star U hi hs hU hlo hup hmassstar hstarK x hx hxW hmi right)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_initial_longitudinal_on_given_cuts_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal c cK A : ℝ}
    (depth : ℕ) (hA : 0 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialLongitudinalOnGivenCutsAlong depth A err M W w high outer := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_initial_longitudinal_category_rate_along_of_pullback_clocks
    dim hdim depth Bclock Temp Cf A A cK hTemp hCf hA hA hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
  let eta:=actualMassSavingExponent m delta/256
  let err n:=2*C*((dim n+1:ℕ):ℝ)^(-eta)
  have hlim : Tendsto err atTop (𝓝 0):=by
    have H0:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
      (by norm_num : (0:ℝ)<256))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [err,eta,Function.comp_def,mul_zero] using H0.const_mul (2*C)
  refine ⟨err,(fun n=>by dsimp only [err];positivity),hlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,Hshell,Hcuts,hcompare,HW] with n hn hsClocks hshell hcuts hsmall hW1
  have hb := hshell
  intro L us hus hret hmesh hstar hhigh houter
  have HW1 : (M n).canonicalDirectTestBandScale ≤ 1:=by rw [←hcanonical];exact hW1
  filter_upwards [hn (M n)  hsClocks hb hsmall HW1 L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  rw [←hcanonical n] at hj
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ A*W n:=
    (partitionPoint_mono as ho HUV.le).trans Houter
  refine ⟨hs,hU,?_⟩
  intro i hi x hx hxW hmi
  have HL:=hj i star U hi hs hU Hlo Hupper Hmass HstarK x hx hxW hmi false
  have HR:=hj i star U hi hs hU Hlo Hupper Hmass HstarK x hx hxW hmi true
  have HB:=add_le_add HL HR
  apply HB.trans_eq
  change C*((dim n+1:ℕ):ℝ)^(-eta)*(M n).xs^2*x+
    C*((dim n+1:ℕ):ℝ)^(-eta)*(M n).xs^2*x=err n*(x*(M n).xs^2)
  dsimp only [err]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_shell_history_resource_G_restoration_forest_rate_of_pullback_clocks
    (seedBound k₀ r₀ depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
        i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → st.tree.forkCost f=0) →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          |st.term.coefficient| *C*M.context.N^(-(actualMassSavingExponent m delta/256))*
            M.xs^2*nativeResourceScale x W 1 seed := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=exists_native_high_profile_holder_orders heta
  let degree:=seedBound+k₀+depth
  obtain ⟨Csrc,hCsrc,Hsource⟩:=eventually_actual_minimum_inherited_resource_G_restoration_from_minimum
    (D:=D) degree dOrder (r₀+6*depth+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0 ≤ Vcost:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let C:=2*(2*Temp/cK)*Csrc*Vcost+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro i star U seed st hseed hgen hleaf hP hi hs hU hcutlo hcutup hmassstar hstarK hseedFork x hx hxW hmi
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let seedScale:=nativeResourceScale x W 1 seed
  let B:=(2*Temp/cK)*Csrc*seedScale
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=M.canonical_direct_test_band_pos
  have hx0 : 0 < x:=M.hxs.trans_le hx
  have hscale : 0 ≤ seedScale:=(actual_resource_raw_scale_pos seed hx0 hW).le
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGaRestorationError M U W Q| ≤
      |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
        W*(Q.tree.forkCost R+edgeBudget 0 as R)) := by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hP) Q hQ
    have Hgen:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hgen) Q hQ
    have Hleaves:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hleaf) Q hQ
    have Hdegree : seed.length+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ r₀+6*depth+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      omega
    let cost:=Q.tree.forkCost f2+edgeBudget 0 as f2+W*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have H2:=add_nonneg (Q.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have H1:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost]
      positivity
    have H0:=hgridSource i star U Q.generation seed Q.tree Q.term Hvalid hi hs hU (by omega)
      Hdegree x W hx hxW hmi hmassstar hcutup
    have H1:=hgridSource i star U Q.generation seed g.tree (Q.term.retarget 0) Hvalid.retarget hi hs hU hg
      Hdegree x W hx hxW hmi hmassstar hcutup
    have Hf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f2 hf2lo
    have HR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U Q.term| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*cost) at H0
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*(g.tree.forkCost f2+edgeBudget 0 as f2+
        W*(g.tree.forkCost R+edgeBudget 0 as R))) at H1
    rw [show g.tree.forkCost f2=Q.tree.forkCost f2 from Hf,
      show g.tree.forkCost R=Q.tree.forkCost R from HR] at H1
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*cost) at H1
    have Hbound:=actual_minimum_four_Ga_restoration_error_abs_le M Q hW hcK
      (B:=Csrc*seedScale*cost) (by positivity) hTemp
      (hsource _ (partitionPoint_mem as ho star)).1 hstarK
      (by apply H0.trans_eq;ring)
      (by apply H1.trans_eq;ring)
    apply Hbound.trans_eq
    dsimp only [B,cost]
    ring
  have Hsum:=actual_minimum_four_Ga_restoration_forest_profile_le M ho hs hU hTemp hCf hsource hxs1
    hW hcK hB hstarK depth st hleaf f2 R hf2 hR hf2lo hRlo Hrow
  rw [hseedFork f2 hf2lo,hseedFork R hRlo,zero_add,zero_add] at Hsum
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ M.context.N^(-eta/256)*M.xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    simpa only [W,as,eta,neg_div] using hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HtailBound:=mul_le_mul_of_nonneg_left Hrate
    (show 0 ≤ 2*|st.term.coefficient| *B*Vcost by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_left
    (show 2*(2*Temp/cK)*Csrc*Vcost ≤ C by dsimp only [C];linarith)
    (show 0 ≤ |st.term.coefficient| *M.context.N^(-eta/256)*M.xs^2*seedScale by positivity)
  have Hfinal : 2*|st.term.coefficient| *B*Vcost*(M.context.N^(-eta/256)*M.xs^2) ≤
      |st.term.coefficient| *C*M.context.N^(-eta/256)*M.xs^2*seedScale := by
    convert Hmajor using 1 <;> (try dsimp only [B]) <;> ring
  apply Hsum.trans
  simpa only [eta,seedScale,W,neg_div] using HtailBound.trans Hfinal

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_shell_history_resource_G_restoration_forest_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (seedBound k₀ r₀ depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin (dim n)×Bool) as i star),
        seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
        i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → st.tree.forkCost f=0) →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          |st.term.coefficient| *C*M.context.N^(-(actualMassSavingExponent m delta/256))*
            M.xs^2*nativeResourceScale x W 1 seed := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_resource_G_restoration_forest_rate_of_pullback_clocks
    seedBound k₀ r₀ depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_initial_restored_Ga_on_given_cuts_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialRestoredGaOnGivenCutsAlong depth A err M W w high outer := by
  have hA0 : 0 ≤ A:=zero_le_one.trans hA
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_resource_G_restoration_forest_rate_along_of_pullback_clocks
    (D:=D) (Cs:=Ccal^2) dim hdim 1 0 2 depth Bclock Temp Cf A A cK
    hTemp hCf hA0 hA0 hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    (pow_nonneg (zero_le_one.trans hCcal) 2) hc hcouter
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/256)
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,(fun n=>by dsimp only [err];positivity),Herr,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HR,Hsource,hcompare,Hshell,Hcuts,HW] with n hn hsource hsmall hshell hcuts hW1
  have hb := hshell
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn (M n)  hsource hb hsmall
    (by rw [←hcanonical];exact hW1) L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  rw [←hcanonical n] at hj
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hupper : partitionPoint 0 as U ≤ A*W n:=
    (partitionPoint_mono as ho HUV.le).trans Houter
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
  have H:=hj i star U [.initial] st (by simp) rfl
    (nativeActualInitialState_leaves_le old i star seedMass (hi.trans (HI.le.trans HU)))
    hP hi HI HU (by simpa only [hcut] using Hlo) (by simpa only [hcut] using Hupper)
    (by dsimp only [old,star];rw [hcut,hindex];exact Hmass)
    (by dsimp only [old,star];rw [hcut,hindex];exact HstarK)
    (actual_initial_four_seed_high_fork_free i star U hi HI HU seedMass)
    (M n).xs le_rfl (by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale)
    (by simpa only [old,i,hcut] using hmi)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] at H
  apply H.trans_eq
  change C*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))*(M n).xs^2*(M n).xs=
    err n*(M n).xs^3
  dsimp only [err,eta]
  ring_nf

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_gamma_HIGH_restoration_forest_rate_along_of_pullback_clocks
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
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>|nativeActualOriginalFourGammaRestorationError (M n) U (W n) Q true|)).sum ≤
            err n*(x n*(M n).xs^2) := by
  let eta:=actualMassSavingExponent m delta
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨CH,hCH,HH⟩:=actual_inherited_resource_gamma_high_second_profile_working_scale_along
    degree (rBound+1) Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource x hxsx hxW hsmall
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Ccal^2) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
    (sq_nonneg _) hc hcouter
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vp:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVp : 0 ≤ Vp:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(4*CH/Cd*Vp)*((dim n+1:ℕ):ℝ)^(-eta/256)
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul (4*CH/Cd*Vp)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HH,hdim.eventually Htail,Hsource,hsmall,Hshell,HW1,hxsx,hxW] with
    n hnH hnTail hsource hnSmall hnShell hW1 hnx hnW
  have hb := hnShell
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  have hx : 0 < x n:=(M n).hxs.trans_le hnx
  intro L us hus hret hmesh hstar
  filter_upwards [hnH L us hus hret hmesh,
    hnTail (M n)  hb hnSmall (by simpa only [←hcanonical] using hW1) us hus]
    with jGrid hgridH hgridTail
  dsimp only at hgridH hgridTail ⊢
  intro i U hi hs hU hcutlo hmi hmassstar hstarK seedMass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let root:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let children:=[root]
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
  have Hroot : NativeActualResourceGenerated i star U [.initial] root.generation root.tree root.term:=
    .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 2:=by
    have HQ : Q=root:=List.mem_singleton.mp hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;exact Hroot) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    0 (fun P hP=>by have HP : P=root:=List.mem_singleton.mp hP;subst P;rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    2 Hleaves Q hQ
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGammaRestorationError (M n) U (W n) Q true| ≤
      (BH*x n*W n)*(|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R)):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : 1+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    let cost:=Q.tree.forkCost R+edgeBudget 0 as R
    have hcost : 0 ≤ cost:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have Hhigh0:=hgridH Q.tree i star U Q.generation [.initial] Q.term HV (by simpa using HD) hi hs hU
      (by dsimp only [rBound];omega) hmi hmassstar
    have Hhigh1:=hgridH g.tree i star U Q.generation [.initial] (Q.term.retarget 0) HV.retarget
      (by simpa using HD) hi hs hU hg hmi hmassstar
    simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      NativeResourceMark.savedScale,mul_one] at Hhigh0 Hhigh1
    have HforkR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |((W n)⁻¹)^Q.generation*nativeActualResourceGammaSecondRestoration (M n) U (Q.term.retarget 0) true| ≤
      |Q.term.coefficient| *CH*x n*(W n)^2*(g.tree.forkCost R+edgeBudget 0 as R) at Hhigh1
    rw [show g.tree.forkCost R=Q.tree.forkCost R from HforkR] at Hhigh1
    have Herror:=actual_minimum_four_gamma_restoration_error_abs_le (M n) hCf hsource hxs1 Q ho hs hU true hW hcK
      (show 0 ≤ CH*x n*W n*cost by positivity) hstarK
      (by apply Hhigh0.trans_eq;dsimp only [cost];ring)
      (by apply Hhigh1.trans_eq;dsimp only [cost];ring)
    apply Herror.trans_eq
    dsimp only [BH,cost,Cd]
    ring
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_left] at Hsum
  have Hprofile:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 2 Hleaves R hR hRlo
  have Hfamily : (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum = edgeBudget 0 as R:=by
    have Hfork:=nativeActualInitialState_high_forkCost_zero (S:=Spin (dim n)×Bool)
      as i star U hi hs (hi.trans (hs.le.trans hU)) seedMass R hRlo
    simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change |(1:ℝ)| *(root.tree.forkCost R+edgeBudget 0 as R)=_
    rw [show root.tree.forkCost R=0 from Hfork]
    norm_num
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
  apply (mul_le_mul_of_nonneg_left Hprofile (show 0 ≤ BH*x n*W n by positivity)).trans
  rw [Hfamily]
  have Hfinal:=mul_le_mul_of_nonneg_left Hrate (show 0 ≤ BH*x n*2*Vp by positivity)
  convert Hfinal using 1 <;> (try dsimp only [err,BH]) <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_gamma_HIGH_restoration_category_rate_along_of_pullback_clocks
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
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .gammaHighRestoration)).sum|/
          (chi*K star) ≤ err n*(x n*(M n).xs^2) := by
  obtain ⟨err,herr,H⟩:=actual_inherited_initial_gamma_HIGH_restoration_forest_rate_along_of_pullback_clocks
    depth Bclock Temp Cf Cmass Ccal cK hTemp hCf hCmass hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource x hxsx hxW hsmall Hshell w
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i U hi hs hU hcutlo hmi hmassstar hstarK seedMass
  apply (actual_gamma_restoration_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _ true).trans
  exact hj i U hi hs hU hcutlo hmi hmassstar hstarK seedMass

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_inherited_initial_three_Gamma_on_given_cuts_along_of_pullback_clocks
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (saving : ℝ) (hsaving : 0 ≤ saving)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialThreeGammaOnGivenCutsAlong depth A err M x W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨C,hC,HG⟩:=eventually_inherited_same_star_four_retained_Gamma_initial_along
    (eta:=m) hdim depth A cK hA hcK hm hm hdelta hroom (by linarith)
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare Hsource saving hsaving w Hmixed
  obtain ⟨eL,heL,HL⟩:=actual_inherited_initial_gamma_LOW_restoration_category_rate_along
    depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource x hxsx hxW w hw
  obtain ⟨eH,heH,HH⟩:=actual_inherited_initial_gamma_HIGH_restoration_category_rate_along_of_pullback_clocks
    depth Bclock Temp Cf A Ccal cK hTemp hCf hA0.le hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource x hxsx hxW hcompare Hshell w
  let eG n:=C*(dim n:ℝ)^(-m)
  let err n:=eG n+|eH n|+|eL n|
  have hG n : 0 ≤ eG n:=by dsimp only [eG];positivity
  have heG : Tendsto eG atTop (𝓝 0):=by
    simpa only [eG,Function.comp_def,mul_zero] using
      ((tendsto_rpow_neg_atTop hm).comp (tendsto_natCast_atTop_atTop.comp hdim)).const_mul C
  have herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,abs_zero,zero_add] using (heG.add heH.abs).add heL.abs
  refine ⟨err,(fun n=>by dsimp only [err];positivity),herr,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HG,HL,HH,Hcuts,Hsource,HW,hxsx,hxW] with n hnG hnL hnH hcuts hsClocks hW1 hnx hnW
  have hxWn : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxWn
  have hx : 0 < x n:=(M n).hxs.trans_le hnx
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnG L us hus hret hmesh hstar,hnL L us hus hret hmesh hstar,
    hnH L us hus hret hmesh hstar] with jGrid hjG hjL hjH
  dsimp only at hjG hjL hjH ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,Hrad,Hrad1,HradU,HstarR,Hz,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  have hindex' : retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))=pre.length+mid.length:=by
    rw [hcut];exact hindex.symm
  have ho' : MassOrdered 0 (pre++(mid++tail)):=by rw [hcut];exact ho
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf
      (pre++(mid++tail)) (pre.length+mid.length):=by rw [hcut,hindex];exact HstarK
  rw [←hcut] at hjL hjH
  let PR (cat : NativeActualOtherSourceCategory) (e : ℝ) (ss : ℕ) : Prop:=
    ∀(hi : pre.length ≤ ss) (hs' : ss<U) (seedMass : ℝ),
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs' HU (W n) depth
          [nativeActualInitialState (pre++(mid++tail)) pre.length ss seedMass
            (hi.trans (hs'.le.trans HU))]) cat|/
        ((scalarTerminal.schedule (scalarBoundaryClocks (pre++(mid++tail))
          (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)))))).H 0 0*
          nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)) ss) ≤
        e*(x n*(M n).xs^2)
  have HL0 : PR .gammaLowRestoration (eL n) (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))):=by
    intro hi hs' seedMass
    exact hjL pre.length U hi hs' HU (by simpa only [hcut] using Hupper)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using Hmass)
      (by simpa only [hcut] using HstarK) seedMass
  have HH0 : PR .gammaHighRestoration (eH n) (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))):=by
    intro hi hs' seedMass
    exact hjH pre.length U hi hs' HU (by simpa only [hcut] using Hlo)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using Hmass)
      (by simpa only [hcut] using HstarK) seedMass
  have HL : PR .gammaLowRestoration (eL n) (pre.length+mid.length):=hindex' ▸ HL0
  have HH : PR .gammaHighRestoration (eH n) (pre.length+mid.length):=hindex' ▸ HH0
  refine ⟨HI,HU,?_⟩
  intro seedMass
  have HG:=hjG pre mid tail hcut hindex (by rw [hindex];exact Hmass) hmid U HI HU
    seedMass (x n) (radius n) hnx hnW hmi Hrad Hrad1 HradU
    (by rw [hindex];exact HstarR) Hz (by rw [hindex];exact HstarK)
  have Hbound:=(actual_retained_gamma_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks
    (hxWn.trans hW1) ho' HI HU hW hcK HK _).trans HG
  have HG' : |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) seedMass (by omega)])
      .gammaRetained|/((scalarTerminal.schedule (scalarBoundaryClocks (pre++(mid++tail))
        (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)))))).H 0 0*
          nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)) (pre.length+mid.length)) ≤
        eG n*(x n*(M n).xs^2):=by
    apply Hbound.trans_eq
    dsimp only [eG]
    ring
  have HL':=HL (by omega) HI seedMass
  have HH':=HH (by omega) HI seedMass
  have Hsum:=add_le_add (add_le_add HG' HH') HL'
  change nativeActualThreeGammaCategoryEnvelope (M n) U (W n) _ ≤ _
  apply Hsum.trans
  have HHL:=add_le_add (le_abs_self (eH n)) (le_abs_self (eL n))
  have HE:=mul_le_mul_of_nonneg_right (add_le_add_left HHL (eG n))
    (show 0 ≤ x n*(M n).xs^2 by positivity)
  convert HE using 1 <;> (try dsimp only [err]) <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_shell_history_resource_G_restoration_forest_with_seed_atoms_of_pullback_clocks
    (seedBound k₀ r₀ depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃p : ℝ,2 < p ∧ 1 ≤ 4/p ∧ 4/p < 2 ∧
      2-4/p ≤ actualMassSavingExponent m delta/128 ∧
      ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
        i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        let f2:=fun j=>((R j)^(2/p))^2
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          |st.term.coefficient| *C*nativeResourceScale x W 1 seed*
            (st.tree.forkCost f2+W*st.tree.forkCost R+
              M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2) := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=exists_native_high_profile_holder_orders heta
  let degree:=seedBound+k₀+depth
  obtain ⟨Csrc,hCsrc,Hsource⟩:=eventually_actual_minimum_inherited_resource_G_restoration_from_minimum
    (D:=D) degree dOrder (r₀+6*depth+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0 ≤ Vcost:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let C:=2*(2*Temp/cK)*Csrc*Vcost+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨p,hp,htheta1,htheta2,hdeficit,C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro i star U seed st hseed hgen hleaf hP hi hs hU hcutlo hcutup hmassstar hstarK x hx hxW hmi
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let seedScale:=nativeResourceScale x W 1 seed
  let B:=(2*Temp/cK)*Csrc*seedScale
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=M.canonical_direct_test_band_pos
  have hx0 : 0 < x:=M.hxs.trans_le hx
  have hscale : 0 ≤ seedScale:=(actual_resource_raw_scale_pos seed hx0 hW).le
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGaRestorationError M U W Q| ≤
      |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
        W*(Q.tree.forkCost R+edgeBudget 0 as R)) := by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hP) Q hQ
    have Hgen:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hgen) Q hQ
    have Hleaves:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hleaf) Q hQ
    have Hdegree : seed.length+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ r₀+6*depth+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      omega
    let cost:=Q.tree.forkCost f2+edgeBudget 0 as f2+W*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have H2:=add_nonneg (Q.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have H1:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost]
      positivity
    have H0:=hgridSource i star U Q.generation seed Q.tree Q.term Hvalid hi hs hU (by omega)
      Hdegree x W hx hxW hmi hmassstar hcutup
    have H1:=hgridSource i star U Q.generation seed g.tree (Q.term.retarget 0) Hvalid.retarget hi hs hU hg
      Hdegree x W hx hxW hmi hmassstar hcutup
    have Hf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f2 hf2lo
    have HR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U Q.term| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*cost) at H0
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*(g.tree.forkCost f2+edgeBudget 0 as f2+
        W*(g.tree.forkCost R+edgeBudget 0 as R))) at H1
    rw [show g.tree.forkCost f2=Q.tree.forkCost f2 from Hf,
      show g.tree.forkCost R=Q.tree.forkCost R from HR] at H1
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*cost) at H1
    have Hbound:=actual_minimum_four_Ga_restoration_error_abs_le M Q hW hcK
      (B:=Csrc*seedScale*cost) (by positivity) hTemp
      (hsource _ (partitionPoint_mem as ho star)).1 hstarK
      (by apply H0.trans_eq;ring)
      (by apply H1.trans_eq;ring)
    apply Hbound.trans_eq
    dsimp only [B,cost]
    ring
  have Hsum:=actual_minimum_four_Ga_restoration_forest_profile_le M ho hs hU hTemp hCf hsource hxs1
    hW hcK hB hstarK depth st hleaf f2 R hf2 hR hf2lo hRlo Hrow
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ M.context.N^(-eta/256)*M.xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    simpa only [W,as,eta,neg_div] using hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have Hcost : st.tree.forkCost f2+edgeBudget 0 as f2+W*(st.tree.forkCost R+edgeBudget 0 as R) ≤
      st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2:=by
    linarith only [Hrate]
  have HtailBound:=mul_le_mul_of_nonneg_left Hcost
    (show 0 ≤ 2*|st.term.coefficient| *B*Vcost by positivity)
  have HseedCost : 0 ≤ st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2:=by
    have H2:=st.tree.forkCost_nonneg hf2
    have H1:=st.tree.forkCost_nonneg hR
    positivity
  have Hmajor:=mul_le_mul_of_nonneg_left
    (show 2*(2*Temp/cK)*Csrc*Vcost ≤ C by dsimp only [C];linarith)
    (show 0 ≤ |st.term.coefficient| *seedScale*
      (st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2) by positivity)
  have Hfinal : 2*|st.term.coefficient| *B*Vcost*
      (st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2) ≤
      |st.term.coefficient| *C*seedScale*
      (st.tree.forkCost f2+W*st.tree.forkCost R+M.context.N^(-eta/256)*M.xs^2):=by
    convert Hmajor using 1 <;> (try dsimp only [B]) <;> ring
  apply Hsum.trans
  simpa only [eta,seedScale,W,neg_div] using HtailBound.trans Hfinal

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_shell_history_constant_child_G_restoration_forest_rate_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Ttotal : ℝ),
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        (((nativeActualConstantSourceChildren M as star U hs hU).flatMap
          (fun st=>nativeActualMinimumFourCenteredForest M hs hU W depth [st])).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨p,hp,htheta1,htheta2,hdeficit,Csrc,hCsrc,Hsource⟩:=
    eventually_actual_shell_history_resource_G_restoration_forest_with_seed_atoms_of_pullback_clocks
      (D:=D) (Cs:=Cs) 0 1 3 depth Bclock Temp Cf Cmass Ccut cK
      hTemp hCf hCmass hCcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let J:=1+nativeActualProfileOpVariation 1 .highRow
  have hJ : 0 ≤ J:=by
    dsimp only [J,nativeActualProfileOpVariation]
    positivity
  let C:=Csrc*(J+6)+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Ttotal hsource hb htotal hsmall hW1 L us hus hret hmesh
  filter_upwards [hnSource M  hsource hb hsmall hW1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro star U hs hU hcutlo hcutup hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let Nrate:=M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.canonical_direct_test_band_pos.le
  have hNrate : 0 ≤ Nrate:=by dsimp only [Nrate];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg Hchi.1];exact Hchi.2
  have Hfamily (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
        J*edgeBudget 0 as f:=by
    exact native_actual_constant_child_family_wholeProfile_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi f hf hlo
  have Hfork (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f)).sum ≤ J*edgeBudget 0 as f:=by
    apply (List.sum_le_sum (fun Q _=>mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (edgeBudget_nonneg ho hf)) (abs_nonneg Q.term.coefficient))).trans
    exact Hfamily f hf hlo
  have Hcoeff:=nativeActualConstantSourceChildren_coefficient_variation M htotal ho hs hU
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ Nrate:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    exact hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have Hrow Q (hQ : Q∈children) :
      ((nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map
        (fun P=>|nativeActualOriginalFourGaRestorationError M U W P|)).sum ≤
      Csrc*(|Q.term.coefficient| *(Q.tree.forkCost f2+W*Q.tree.forkCost R+Nrate)):=by
    have Hvalid:=nativeActualConstantSourceChildren_valid M hs hU Q hQ
    have Hgen:=nativeActualConstantSourceChildren_generation M hs hU Q hQ
    have Hleaf:=nativeActualConstantSourceChildren_leaves M hs hU Q hQ
    have H:=hgridSource 0 star U [] Q (by simp) Hgen Hleaf Hvalid (Nat.zero_le star)
      hs hU hcutlo hcutup hmassstar hstarK M.xs le_rfl M.canonical_direct_test_band_ge_scale
      (by
        simp only [partitionPoint,partitionValues_zero,id_eq]
        exact mul_nonneg hCmass M.hxs.le)
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
    apply H.trans_eq
    ring
  simp only [List.map_flatMap,native_sum_flatMap]
  apply (List.sum_le_sum Hrow).trans
  have HE : (children.map (fun Q=>Csrc*(|Q.term.coefficient| *
      (Q.tree.forkCost f2+W*Q.tree.forkCost R+Nrate)))).sum=
      Csrc*((children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f2)).sum+
        W*(children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost R)).sum+
        Nrate*(children.map (fun Q=>|Q.term.coefficient|)).sum):=by
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  rw [HE]
  have Hbound:=mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (Hfork f2 hf2 hf2lo) (mul_le_mul_of_nonneg_left (Hfork R hR hRlo) hW))
      (mul_le_mul_of_nonneg_left Hcoeff hNrate)) hCsrc.le
  have Htotal:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left Hrate hJ) (le_refl (6*Nrate))) hCsrc.le
  have Hlast : Csrc*(J*Nrate+6*Nrate) ≤ C*Nrate:=by
    have H:=mul_nonneg hNrate (show 0 ≤ C-Csrc*(J+6) by dsimp only [C];linarith)
    nlinarith only [H]
  apply Hbound.trans
  have Htotal' : Csrc*(J*edgeBudget 0 as f2+W*(J*edgeBudget 0 as R)+Nrate*6) ≤
      Csrc*(J*Nrate+6*Nrate):=by
    convert Htotal using 1
    ring
  simpa only [Nrate,mul_assoc] using Htotal'.trans Hlast

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_shell_history_constant_child_G_restoration_forest_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Ttotal : ℝ),
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        (((nativeActualConstantSourceChildren M as star U hs hU).flatMap
          (fun st=>nativeActualMinimumFourCenteredForest M hs hU W depth [st])).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_constant_child_G_restoration_forest_rate_of_pullback_clocks
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_shell_history_constant_child_longitudinal_restoration_forest_rate_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Ttotal : ℝ),
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star → ∀right : Bool,
        (((nativeActualConstantSourceChildren M as star U hs hU).flatMap
          (fun st=>nativeActualMinimumFourCenteredForest M hs hU W depth [st])).map
          (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨p,hp,htheta1,htheta2,hdeficit,Csrc,hCsrc,Hsource⟩:=
    eventually_actual_shell_history_resource_longitudinal_restoration_forest_with_seed_atoms_of_pullback_clocks
      (D:=D) (Cs:=Cs) 0 1 3 depth Bclock Temp Cf Cmass Ccut cK
      hTemp hCf hCmass hCcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let J:=1+nativeActualProfileOpVariation 1 .highRow
  have hJ : 0 ≤ J:=by
    dsimp only [J,nativeActualProfileOpVariation]
    positivity
  let C:=Csrc*(J+6)+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Ttotal hsource hb htotal hsmall hW1 L us hus hret hmesh
  filter_upwards [hnSource M  hsource hb hsmall hW1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro star U hs hU hcutlo hcutup hmassstar hstarK right
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let Nrate:=M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.canonical_direct_test_band_pos.le
  have hNrate : 0 ≤ Nrate:=by dsimp only [Nrate];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg Hchi.1];exact Hchi.2
  have Hfamily (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
        J*edgeBudget 0 as f:=by
    exact native_actual_constant_child_family_wholeProfile_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi f hf hlo
  have Hfork (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f)).sum ≤ J*edgeBudget 0 as f:=by
    apply (List.sum_le_sum (fun Q _=>mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (edgeBudget_nonneg ho hf)) (abs_nonneg Q.term.coefficient))).trans
    exact Hfamily f hf hlo
  have Hcoeff:=nativeActualConstantSourceChildren_coefficient_variation M htotal ho hs hU
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ Nrate:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    exact hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have Hrow Q (hQ : Q∈children) :
      ((nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map
        (fun P=>|nativeActualOriginalFourLongitudinalError M U W P right|)).sum ≤
      Csrc*(|Q.term.coefficient| *(Q.tree.forkCost f2+W*Q.tree.forkCost R+Nrate)):=by
    have Hvalid:=nativeActualConstantSourceChildren_valid M hs hU Q hQ
    have Hgen:=nativeActualConstantSourceChildren_generation M hs hU Q hQ
    have Hleaf:=nativeActualConstantSourceChildren_leaves M hs hU Q hQ
    have H:=hgridSource 0 star U [] Q (by simp) Hgen Hleaf Hvalid (Nat.zero_le star)
      hs hU hcutlo hcutup hmassstar hstarK M.xs le_rfl M.canonical_direct_test_band_ge_scale
      (by
        simp only [partitionPoint,partitionValues_zero,id_eq]
        exact mul_nonneg hCmass M.hxs.le) right
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
    apply H.trans_eq
    ring
  simp only [List.map_flatMap,native_sum_flatMap]
  apply (List.sum_le_sum Hrow).trans
  have HE : (children.map (fun Q=>Csrc*(|Q.term.coefficient| *
      (Q.tree.forkCost f2+W*Q.tree.forkCost R+Nrate)))).sum=
      Csrc*((children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f2)).sum+
        W*(children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost R)).sum+
        Nrate*(children.map (fun Q=>|Q.term.coefficient|)).sum):=by
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  rw [HE]
  have Hbound:=mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (Hfork f2 hf2 hf2lo) (mul_le_mul_of_nonneg_left (Hfork R hR hRlo) hW))
      (mul_le_mul_of_nonneg_left Hcoeff hNrate)) hCsrc.le
  have Htotal:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left Hrate hJ) (le_refl (6*Nrate))) hCsrc.le
  have Hlast : Csrc*(J*Nrate+6*Nrate) ≤ C*Nrate:=by
    have H:=mul_nonneg hNrate (show 0 ≤ C-Csrc*(J+6) by dsimp only [C];linarith)
    nlinarith only [H]
  apply Hbound.trans
  have Htotal' : Csrc*(J*edgeBudget 0 as f2+W*(J*edgeBudget 0 as R)+Nrate*6) ≤
      Csrc*(J*Nrate+6*Nrate):=by
    convert Htotal using 1
    ring
  simpa only [Nrate,mul_assoc] using Htotal'.trans Hlast

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_shell_history_constant_child_longitudinal_restoration_forest_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Ttotal : ℝ),
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star → ∀right : Bool,
        (((nativeActualConstantSourceChildren M as star U hs hU).flatMap
          (fun st=>nativeActualMinimumFourCenteredForest M hs hU W depth [st])).map
          (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_constant_child_longitudinal_restoration_forest_rate_of_pullback_clocks
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_shell_history_constant_child_longitudinal_category_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Ttotal : ℝ),
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star → ∀right : Bool,
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest M hs hU W depth
          (nativeActualConstantSourceChildren M as star U hs hU)).map
          (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast M U Q
            (nativeActualLongitudinalCategory right))).sum|/(chi*K star) ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_constant_child_longitudinal_restoration_forest_rate_along_of_pullback_clocks
    dim hdim depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M Ttotal HS hb htotal hsmall hW1 L us hus hret hmesh
  filter_upwards [hn M Ttotal HS hb htotal hsmall hW1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro star U hs hU hcutlo hcutup hmassstar hstarK right
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  have Hsum:=actual_longitudinal_category_signed_sum_abs_le_error_sum M hCf HS hxs1 ho hs hU
    M.canonical_direct_test_band_pos hcK hstarK
    (nativeActualMinimumFourCenteredForest M hs hU W depth children) right
  apply Hsum.trans
  have Hforest : nativeActualMinimumFourCenteredForest M hs hU W depth children=
      children.flatMap (fun Q=>nativeActualMinimumFourCenteredForest M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  rw [Hforest]
  exact hj star U hs hU hcutlo hcutup hmassstar hstarK right

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_shell_history_constant_fresh_C_two_HIGH_rate_of_pullback_clocks
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,g.tree.splitIndex a z<U →
            |nativeCenteredLowGammaHighSecondRemainder n q U b h K
              (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z| ≤
              C*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨Cp,hCp,Hparts⟩:=eventually_actual_minimum_inherited_canonical_C_two_high_profile_budget
    (D:=D) 0 dOrder 2 hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mc:=4*Cf+2*Temp
  let Cjet:=pairForkVariation 4*pairForkVariation 6*
    (Real.exp (wholeLawRowComparisonConstant 4*Mc)*Cp)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation 2
  have hCjet : 0≤Cjet:=by
    dsimp only [Cjet]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) (pairForkVariation_nonneg _)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _))
      (pairForkVariation_nonneg _)
  let C:=Cjet+1
  have hC : 0<C:=by dsimp only [C];linarith
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU hcutlo hcutup seedMass a z haz
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  have hW : 0<W:=M.canonical_direct_test_band_pos
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
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
  let G : ActualNaturalBoundaryShape n 0 g.tree:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HP : (G.canonicalMinimumSource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have H:=hjParts U g.tree hU hg G forms ∅ W M.canonical_direct_test_band_ge_scale
    hcutup (fun e=>Fin.elim0 e) a z haz
  rw [HP] at H
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at H
  norm_num only [Nat.reduceAdd,pow_one] at H
  change |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) a z| ≤
    pairForkVariation 4*pairForkVariation 6*(Real.exp (wholeLawRowComparisonConstant 4*Mc)*Cp*W)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation 2*
    (g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))) at H
  rw [HF2,zero_add] at H
  have HE:=hjTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R ≤
      M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  have Hextra : 0≤W*edgeBudget 0 as R:=mul_nonneg M.canonical_direct_test_band_pos.le
    (edgeBudget_nonneg (finiteCutMasses_ordered us hus jGrid) (by
      intro j
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))))
  have HEtheta : edgeBudget 0 as (fun j=>(R j)^(4/p))≤
      M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by linarith only [HE',Hextra]
  have HH:=mul_le_mul_of_nonneg_left HEtheta (mul_nonneg hCjet M.canonical_direct_test_band_pos.le)
  have Hsaved : |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) a z|≤
      Cjet*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2:=by
    apply H.trans
    convert HH using 1 <;> dsimp only [Cjet,Mc] <;> ring
  have HC:=mul_le_mul_of_nonneg_right (show Cjet≤C by dsimp only [C];linarith)
    (show 0≤M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 by positivity)
  exact Hsaved.trans (by simpa only [mul_assoc] using HC)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_shell_history_constant_fresh_FOUR_G_LOW_rate_of_pullback_clocks
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeOriginalGKernelLowRestoration n q U b h K
              (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z
              (restCenteredLowKernel n U b (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))| ≤
              C*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,Hparts⟩:=eventually_actual_minimum_inherited_canonical_four_G_low_restoration
    (D:=D) 0 dOrder 2 hd p hp hOrder Bclock Temp Cf 0 Ccut hTemp hCf (by norm_num) hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mc:=4*Cf+2*Temp
  let Kh:=2*pairForkVariation 6*(Real.exp (wholeLawRowComparisonConstant 6*Mc)*Ch)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*7*pairForkVariation 4*pairForkVariation 2
  let Kl:=2*absJetVariation 6 1*(Real.exp (wholeLawRowComparisonConstant 6*Mc)*Cl)*
    (Cq*(1+Ccut))*pairForkVariation 4*pairForkVariation 2
  have hKh : 0≤Kh:=by
    dsimp only [Kh]
    have H6:=pairForkVariation_nonneg 6
    have H4:=pairForkVariation_nonneg 4
    have H2:=pairForkVariation_nonneg 2
    positivity
  have hKl : 0≤Kl:=by
    dsimp only [Kl]
    have H6:=absJetVariation_nonneg 6 1
    have H4:=pairForkVariation_nonneg 4
    have H2:=pairForkVariation_nonneg 2
    positivity
  let C:=Kh+Kl+1
  have hC : 0<C:=by dsimp only [C];linarith
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU hcutlo hcutup seedMass a z
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
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
  let G : ActualNaturalBoundaryShape n 0 g.tree:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HP : (G.canonicalMinimumSource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have H:=hjParts U g.tree hU hg G forms ∅ W M.canonical_direct_test_band_ge_scale
    hcutup (fun e=>Fin.elim0 e) a z
  rw [HP] at H
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at H
  norm_num only [Nat.reduceAdd,pow_one,Nat.cast_ofNat] at H
  let f2:=fun j=>((R j)^(2/p))^2
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hf : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    change ((R j)^(2/p))^2=(R j)^(4/p)
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hprofile : |nativeOriginalGKernelLowRestoration n q U b h K S g.tree (fun _=>1) a z (restCenteredLowKernel n U b S)|≤
      Kh*W*(g.tree.forkCost f2+edgeBudget 0 as f2)+Kl*W^2*(g.tree.forkCost R+edgeBudget 0 as R):=by
    convert H using 1
    · rfl
    · dsimp only [Kh,Kl,Mc,f2,R,W,as]
      ring
  rw [Hf,HF1,HF2,zero_add,zero_add] at Hprofile
  have HE:=hjTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R ≤
      M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Htheta0 : 0≤edgeBudget 0 as (fun j=>(R j)^(4/p)):=edgeBudget_nonneg ho
    (fun j=>Real.rpow_nonneg (hR j) _)
  have HE10 : 0≤edgeBudget 0 as R:=edgeBudget_nonneg ho hR
  have Hkh:=mul_le_mul_of_nonneg_right (show Kh≤C by dsimp only [C];linarith)
    (mul_nonneg M.canonical_direct_test_band_pos.le Htheta0)
  have Hkl:=mul_le_mul_of_nonneg_right (show Kl≤C by dsimp only [C];linarith)
    (mul_nonneg (sq_nonneg W) HE10)
  have Hpaid : |nativeOriginalGKernelLowRestoration n q U b h K S g.tree (fun _=>1) a z (restCenteredLowKernel n U b S)|≤
      C*W*(edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R):=by
    apply Hprofile.trans
    convert add_le_add Hkh Hkl using 1 <;> ring
  apply Hpaid.trans
  have HH:=mul_le_mul_of_nonneg_left HE' (mul_nonneg hC.le M.canonical_direct_test_band_pos.le)
  convert HH using 1; ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_shell_history_constant_fresh_C_two_HIGH_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,g.tree.splitIndex a z<U →
            |nativeCenteredLowGammaHighSecondRemainder (dim n) q U b h K
              (fun j=>orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z| ≤
              C*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_constant_fresh_C_two_HIGH_rate_of_pullback_clocks
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

theorem eventually_actual_shell_history_constant_fresh_FOUR_G_LOW_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeOriginalGKernelLowRestoration (dim n) q U b h K
              (fun j=>orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z
              (restCenteredLowKernel (dim n) U b (fun j=>orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)))| ≤
              C*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_constant_fresh_FOUR_G_LOW_rate_of_pullback_clocks
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_shell_history_four_first_high_forest_rate_of_pullback_clocks
    (depth k₀ seedBound r₀ : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0  ≤  Temp) (hCf : 0  ≤  Cf) (hCm : 0  ≤  Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hCcal : 1  ≤  Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hc : 0<c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        NativeActualSmallSourceClocks M Temp Cf →
        M.xs^2  ≤  Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale  ≤  Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale  ≤  Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (_hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
          (seed : List NativeResourceMark) (st : NativeActualResourceState (Spin n×Bool) as i star),
          seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
          (∀f : ℕ→ℝ,(∀j,j<U→f j=0)→st.tree.forkCost f=0) →
          2*c*W ≤ partitionPoint 0 as U →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum  ≤
          |st.term.coefficient| *C*M.context.N^(-(actualMassSavingExponent m delta/256))*
            nativeResourceScale M.xs W 1 seed*M.xs^2 := by
  let rBound:=r₀+6*depth
  let Ttot:=Temp+2*Cf
  let Cweight:=Ttot/(Real.exp (-4*Ttot)*cK)
  have hw0 : 0 ≤ Cweight:=by dsimp only [Cweight,Ttot];positivity
  let V:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 r₀ depth
  have hV : 0 ≤ V:=nativeActualWeightedProfileFrontierCost_nonneg _ hw0 _ _ _
  obtain ⟨C₀,hC₀,Hsource⟩:=eventually_actual_minimum_inherited_four_first_high_profile
    (D:=D) (seedBound+k₀+depth) Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks (D:=D) (Cs:=Ccal^2)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
  let C₁:=2*C₀*nativeGammaFirstHighVariation (rBound+1)*V
  have hC₁ : 0 ≤ C₁:=by dsimp only [C₁];exact mul_nonneg (mul_nonneg (by positivity)
    (nativeGammaFirstHighVariation_nonneg _)) hV
  let C:=C₁+1
  refine ⟨C,by dsimp only [C];linarith,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M  hb hsource hcompare hmacroW hsmall L us hus hret hmesh
  have hW1 : M.canonicalDirectTestBandScale ≤ 1:=by linarith
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 hcompare L us hus hret hmesh,
    hnTail M  hb hcompare hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro i star U hi hs hU seed st hseedlength hgen hleaf hP hfork hcutlo hmi hms hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW : 0<W:=M.canonical_direct_test_band_pos
  have hlo j (hj : j<U) : R j=0:=by simp [R,nativeOriginalHighErrorEnvelope,hj]
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hrate : W*edgeBudget 0 as R ≤ M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by
    have HH:=hgridTail U hU hcutlo 2 (by norm_num) (by norm_num)
      (show 2-(2:ℝ) ≤ actualMassSavingExponent m delta/128 by
        have Heta:=actualMassSavingExponent_pos hm hdelta;linarith)
    have Hextra:=edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) 2)
    change edgeBudget 0 as (fun j=>R j^ (2:ℝ))+W*edgeBudget 0 as R ≤ _ at HH
    linarith
  have hseed : 0 ≤ nativeResourceScale M.xs W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos M.hxs hW zero_lt_one).le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourFirstHighError M U W Q| ≤
      |Q.term.coefficient| *C₀*nativeResourceScale M.xs W 1 seed*W*
        nativeGammaFirstHighVariation (rBound+1)*(Q.tree.forkCost R+edgeBudget 0 as R):=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hgen) Q hQ
    have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) Q hQ
    have Hdegree : Q.term.resources.length ≤ seedBound+k₀+depth:=by
      rw [Hvalid.total_factor_depth]
      omega
    exact hgridSource i star U rBound seed Q Hvalid Hdegree hi hs hU Hleaf hmacroW hsmall hmi hms hstarK
  have HS : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
      C₀*nativeResourceScale M.xs W 1 seed*W*nativeGammaFirstHighVariation (rBound+1)*
        (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum:=by
    apply (List.sum_le_sum Hrow).trans_eq
    rw [←List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  have Hhist:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight hw0 (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks M hCf hsource hxs1 hW hcK
      as ho hs hU hstarK Q tag) depth [st] r₀
    (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) R hR hlo
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hfork R hlo,zero_add] at Hhist
  have Hscaled:=mul_le_mul_of_nonneg_left Hhist
    (show 0 ≤ C₀*nativeResourceScale M.xs W 1 seed*W*nativeGammaFirstHighVariation (rBound+1) by
      exact mul_nonneg (by positivity) (nativeGammaFirstHighVariation_nonneg _))
  have Hsaved:=mul_le_mul_of_nonneg_left Hrate
    (show 0 ≤ |st.term.coefficient| *C₁*nativeResourceScale M.xs W 1 seed by positivity)
  apply HS.trans
  apply Hscaled.trans
  calc
    _=|st.term.coefficient| *C₁*nativeResourceScale M.xs W 1 seed*(W*edgeBudget 0 as R):=by
      dsimp only [C₁,V]
      ring
    _ ≤ |st.term.coefficient| *C₁*nativeResourceScale M.xs W 1 seed*
      (M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=Hsaved
    _ ≤ |st.term.coefficient| *C*nativeResourceScale M.xs W 1 seed*
      (M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=by
      gcongr
      dsimp only [C]
      linarith
    _=_:=by ring

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 26000000

theorem eventually_actual_shell_history_constant_source_first_high_rate_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCcal : 1≤Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Ttotal : ℝ),
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Ttotal) →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale≤Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(star U : ℕ) (hs : star < U) (hU : U≤as.length),
          2*c*W≤partitionPoint 0 as U → partitionPoint 0 as star≤Cmass*W →
          cK*W≤nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth
          (nativeActualConstantSourceChildren M as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  let rBound:=3+6*depth
  let Cweight:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hw0 : 0≤Cweight:=by dsimp only [Cweight];positivity
  let V:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 3 depth
  have hV : 0≤V:=nativeActualWeightedProfileFrontierCost_nonneg _ hw0 _ _ _
  obtain ⟨C₀,hC₀,Hsource⟩:=eventually_actual_minimum_inherited_four_first_high_profile
    (D:=D) (1+depth) Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks (D:=D) (Cs:=Ccal^2)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
  let C₁:=12*C₀*nativeGammaFirstHighVariation (rBound+1)*V
  have hC₁ : 0≤C₁:=by dsimp only [C₁];exact mul_nonneg (mul_nonneg (by positivity)
    (nativeGammaFirstHighVariation_nonneg _)) hV
  let C:=C₁+1
  refine ⟨C,by dsimp only [C];linarith,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Ttotal hb hsource htotal hcompare hmacroW hsmall L us hus hret hmesh
  have hW1 : M.canonicalDirectTestBandScale≤1:=by linarith
  have hxs1 : M.xs≤1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 hcompare L us hus hret hmesh,
    hnTail M  hb hcompare hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro star U hs hU hcutlo hms hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (st : NativeActualResourceState (Spin n×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth children
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=M.canonical_direct_test_band_pos
  have hlo j (hj : j < U) : R j=0:=by simp [R,nativeOriginalHighErrorEnvelope,hj]
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hrate : W*edgeBudget 0 as R≤M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by
    have HH:=hgridTail U hU hcutlo 2 (by norm_num) (by norm_num)
      (show 2-(2:ℝ)≤actualMassSavingExponent m delta/128 by
        have Heta:=actualMassSavingExponent_pos hm hdelta;linarith)
    have Hextra:=edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) 2)
    change edgeBudget 0 as (fun j=>R j^(2:ℝ))+W*edgeBudget 0 as R≤_ at HH
    linarith
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourFirstHighError M U W Q|≤
      |Q.term.coefficient| *C₀*W*nativeGammaFirstHighVariation (rBound+1)*
        (Q.tree.forkCost R+edgeBudget 0 as R):=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
      (seed:=[]) (fun P hP=>nativeActualConstantSourceChildren_valid M hs hU P hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
      1 (fun P hP=>nativeActualConstantSourceChildren_generation M hs hU P hP) Q hQ
    have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
      3 (fun P hP=>nativeActualConstantSourceChildren_leaves M hs hU P hP) Q hQ
    have Hdegree : Q.term.resources.length≤1+depth:=by rw [Hvalid.total_factor_depth];simp only [List.length_nil,zero_add];omega
    have Hmi : partitionPoint 0 as 0≤Cmass*M.xs:=by
      simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm M.hxs.le
    have H:=hgridSource 0 star U rBound [] Q Hvalid Hdegree (Nat.zero_le _) hs hU Hleaf
      hmacroW hsmall Hmi hms hstarK
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] using H
  have HS : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum≤
      C₀*W*nativeGammaFirstHighVariation (rBound+1)*
        (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum:=by
    apply (List.sum_le_sum Hrow).trans_eq
    rw [←List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  have Hhist:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight hw0 (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks M hCf hsource hxs1 hW hcK
      as ho hs hU hstarK Q tag) depth children 3
    (fun P hP=>nativeActualConstantSourceChildren_leaves M hs hU P hP) R hR hlo
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have hchi : |chi|≤1:=by rw [abs_of_nonneg Hchi.1];exact Hchi.2
  have Hfamily : (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum≤
      6*edgeBudget 0 as R:=by
    have H:=native_actual_constant_child_family_wholeProfile_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi R hR hlo
    norm_num only [nativeActualProfileOpVariation,Nat.cast_one] at H
    exact H
  have Hprofile:=Hhist.trans (mul_le_mul_of_nonneg_left Hfamily (by positivity : 0≤2*V))
  have Hscaled:=mul_le_mul_of_nonneg_left Hprofile
    (show 0≤C₀*W*nativeGammaFirstHighVariation (rBound+1) by
      exact mul_nonneg (by positivity) (nativeGammaFirstHighVariation_nonneg _))
  have Hsaved:=mul_le_mul_of_nonneg_left Hrate hC₁
  apply HS.trans
  apply Hscaled.trans
  calc
    _=C₁*(W*edgeBudget 0 as R):=by dsimp only [C₁,V];ring
    _≤C₁*(M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=Hsaved
    _≤C*(M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=by
      gcongr
      dsimp only [C]
      linarith
    _=_:=by ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_shell_history_four_first_high_initial_rate_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0  ≤  Temp) (hCf : 0  ≤  Cf) (hCm : 0  ≤  Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hCcal : 1  ≤  Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hc : 0<c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        NativeActualSmallSourceClocks M Temp Cf →
        M.xs^2  ≤  Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale  ≤  Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale  ≤  Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (a : ℝ),
          2*c*W ≤ partitionPoint 0 as U →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth
          [nativeActualInitialState as i star a (by omega)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^3 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_four_first_high_forest_rate_of_pullback_clocks
    (D:=D) depth 0 1 2 Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M  hb hsource hcompare hmacroW hsmall L us hus hret hmesh
  filter_upwards [hn M  hb hsource hcompare hmacroW hsmall L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  intro i star U hi hs hU a hcutlo hmi hms hstarK
  change U ≤ as.length at hU
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star a (by omega)
  have Hleaf:=nativeActualInitialState_leaves_le (S:=Spin n×Bool) as i star a (by omega)
  have Hvalid : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU a .initial (Or.inl rfl) (by change i ≤ as.length;omega))
  have Hfork f hf:=nativeActualInitialState_high_forkCost_zero (S:=Spin n×Bool)
    as i star U hi hs (by omega) a f hf
  have HH:=hj i star U hi hs hU [.initial] st (by simp) rfl Hleaf Hvalid Hfork hcutlo hmi hms hstarK
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one,mul_assoc,←pow_succ',Nat.reduceAdd] using HH

theorem eventually_actual_shell_history_four_first_high_projected_constant_rate_of_pullback_clocks
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0  ≤  Temp) (hCf : 0  ≤  Cf) (hCm : 0  ≤  Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hCcal : 1  ≤  Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hc : 0<c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        NativeActualSmallSourceClocks M Temp Cf →
        M.xs^2  ≤  Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale  ≤  Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale  ≤  Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(star U : ℕ) (hs : star<U) (hU : U ≤ as.length),
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth
          [(nativeActualConstantState as 0 star).projection (hs.le.trans hU)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_four_first_high_forest_rate_of_pullback_clocks
    (D:=D) depth 1 0 2 Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M  hb hsource hcompare hmacroW hsmall L us hus hret hmesh
  filter_upwards [hn M  hb hsource hcompare hmacroW hsmall L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  intro star U hs hU hcutlo hms hstarK
  let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection (hs.le.trans hU)
  have Hleaf : st.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0
      (nativeFreshAtSlot (single as) 0 (singleSlot as) star)
      (nativeFreshAtSlot_mem (single as) 0 (singleSlot as) star)
    simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
      NativeResourceTerm.ofLive,nativeResourceConstant,single_leaves_exact] using H
  have Hvalid : NativeActualResourceGenerated 0 star U [] st.generation st.tree st.term:=
    (show NativeActualResourceGenerated 0 star U []
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).generation
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).tree
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).term from
        .physical (.constant as hU)).projection (hs.le.trans hU)
  have Hfork (f : ℕ→ℝ) (hf : ∀j,j<U→f j=0) : st.tree.forkCost f=0:=by
    change (nativeFreshAtSlot (single as) 0 (singleSlot as) star).tree.forkCost f=0
    rw [nativeFreshAtSlot_high_forkCost _ _ _ hs f hf,single_forkCost]
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*M.xs:=by
    simpa [partitionPoint,partitionValues] using mul_nonneg hCm M.hxs.le
  have HH:=hj 0 star U (Nat.zero_le _) hs hU [] st (by simp) rfl Hleaf Hvalid Hfork hcutlo Hmi hms hstarK
  simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
    NativeResourceTerm.projection,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_nil,List.prod_nil,mul_one] using HH

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_shell_history_constant_longitudinal_restoration_rate_of_pullback_clocks
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → T.forkCost f=0) →∀a : T.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a| ≤
            C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨p,_dOrder,hp,_hdOrder,_hOrder,htheta1,htheta2,hdeficit⟩:=exists_native_high_profile_holder_orders heta
  obtain ⟨Cq,hCq,Hprofile⟩:=eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile
    (D:=D) rBound p hp Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers_of_pullback_clocks
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let KH:=pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    nativeOriginalRestorationProfileVariation rBound
  let KL:=absJetVariation (rBound+3) 1*Cq*forkVariation rBound 3
  have hKH : 0 ≤ KH:=by
    dsimp only [KH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (nativeOriginalRestorationProfileVariation_nonneg _)
  have hKL : 0 ≤ KL:=by
    dsimp only [KL]
    exact mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCq.le) (forkVariation_nonneg _ _)
  let C:=KH+KL+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Hprofile,Htail] with n hnProfile hnTail
  intro M  hsource hb hsmall hW1 L us hus hret hmesh
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnProfile M hsource hxs1 L us hus hret hmesh,
    hnTail M  hb hsmall hW1 us hus] with jGrid hgridProfile hgridTail
  dsimp only at hgridProfile hgridTail ⊢
  intro U T hU hT hcutlo hcutup hFork a
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.canonical_direct_test_band_pos.le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ M.context.N^(-eta/256)*M.xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    simpa only [W,as,eta,neg_div] using hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HS:=hgridProfile U T hU hT W M.canonical_direct_test_band_ge_scale hcutup a
  change _ ≤ KH*(T.forkCost f2+edgeBudget 0 as f2)+
    (absJetVariation (rBound+3) 1*(Cq*W))*forkVariation rBound 3*
      (T.forkCost R+edgeBudget 0 as R) at HS
  have Heq : (absJetVariation (rBound+3) 1*(Cq*W))*forkVariation rBound 3*
      (T.forkCost R+edgeBudget 0 as R)=KL*(W*(T.forkCost R+edgeBudget 0 as R)):=by
    dsimp only [KL]
    ring
  rw [Heq] at HS
  rw [hFork f2 hf2lo,hFork R hRlo,zero_add,zero_add] at HS
  have HE2 : 0 ≤ edgeBudget 0 as f2:=edgeBudget_nonneg ho (fun j=>sq_nonneg _)
  have HE1 : 0 ≤ W*edgeBudget 0 as R:=mul_nonneg hW (edgeBudget_nonneg ho hR)
  have Hmajor : KH*edgeBudget 0 as f2+KL*(W*edgeBudget 0 as R) ≤
      C*(edgeBudget 0 as f2+W*edgeBudget 0 as R):=by
    have H1:=mul_nonneg (show 0 ≤ C-KH by dsimp only [C];linarith) HE2
    have H2:=mul_nonneg (show 0 ≤ C-KL by dsimp only [C];linarith) HE1
    nlinarith
  exact HS.trans (Hmajor.trans (by
    simpa only [eta,neg_div,mul_assoc] using mul_le_mul_of_nonneg_left Hrate hC.le))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_shell_history_retained_constant_longitudinal_rate_of_pullback_clocks
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp) → M.h 0=0 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → T.forkCost f=0) →∀a : T.Slot,
          |nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) a| ≤
            (M.context.N^(-(1:ℝ)/3)+C*M.context.N^(-(actualMassSavingExponent m delta/256)))*M.xs^2 := by
  obtain ⟨C,hC,Hrest⟩:=eventually_actual_shell_history_constant_longitudinal_restoration_rate_of_pullback_clocks
    (D:=D) (Cs:=Cs) rBound Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hmean:=eventually_actual_inherited_original_clock_longitudinal_mean_saving
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) rBound Bclock Temp hTemp hm hC0
  refine ⟨C,hC,?_⟩
  filter_upwards [Hrest,Hmean] with n hnRest hnMean
  intro M  hsource hb htotal hroot hsmall hW1 L us hus hret hmesh
  filter_upwards [hnRest M  hsource hb hsmall hW1 L us hus hret hmesh,
    hnMean M htotal hroot us hus] with jGrid hgridRest hgridMean
  dsimp only at hgridRest hgridMean ⊢
  intro U T hU hT hcutlo hcutup hFork a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hcenter : (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))=S:=by
    funext j
    exact native_ordered_source_center_eq_completed n M.bf M.hf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)
  have HR:=hgridRest U T hU hT hcutlo hcutup hFork a
  change |nativeOriginalLongitudinalRestoration n q U b h K
    (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) T (fun _=>1) a| ≤ _ at HR
  rw [Hcenter] at HR
  have HM:=hgridMean K T U a hT
  have HM' : |nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S
      T (fun _=>1) a| ≤ M.context.N^(-(1:ℝ)/3)*M.xs^2:=by
    unfold nativeOriginalLongitudinalMean at HM
    have Hpath : cavityPath n U 1 1 q b h K=cutFullVariance n q U 1 1 b h K:=rfl
    change |((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        ((r.tree.markedAttach 0).map (fun z=>z.coeff*
          z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cavityPath n U 1 1 q b h K)
            (nativeOriginalHighGAtom z.tree U K b S (z.embed (r.embed (p.embed a)))
              (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark) 0)).sum)).sum)).sum| ≤ _ at HM
    rw [Hpath] at HM
    simpa only [nativeOriginalLongitudinalPairing,one_mul,NativeOverlapContext.N] using HM
  have hKS : ∀j,K j=h j+b j*S j:=native_continuum_mixed_clock_eq_original_center n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.inherited_hf_monotone hu hv huv) as ho
  have hq0 : ∀j i,0 ≤ q j i:=by
    intro j i
    cases i <;> exact NNReal.coe_nonneg _
  have hqm : ∀i,Monotone (fun j=>q j i):=by
    intro i
    cases i <;> first | exact hbm | exact hhm
  have HK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have Hlaw:=native_original_longitudinal_eq_retained_add_restoration n q U b h K S hKS
    T ho (fun _=>1) a hU hq0 hqm (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    HK0 hbm hhm HKm
  have Hret : nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) a=
      nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T (fun _=>1) a-
        nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a:=by
    simpa only [add_sub_cancel_right] using congrArg (fun z=>z-nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a) Hlaw.symm
  rw [Hret]
  exact (abs_sub _ _).trans (by nlinarith only [HM',HR])

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
theorem eventually_actual_shell_history_retained_constant_longitudinal_rate_along_of_pullback_clocks
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        ,
        NativeActualSmallSourceClocks M Temp Cf →
        NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1 →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp) → M.h 0=0 →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → T.forkCost f=0) →∀a : T.Slot,
          |nativeRetainedLongitudinalPairing (dim n) q U b h K T (fun _=>1) a| ≤
            (M.context.N^(-(1:ℝ)/3)+C*M.context.N^(-(actualMassSavingExponent m delta/256)))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_retained_constant_longitudinal_rate_of_pullback_clocks
    (D:=D) (Cs:=Cs) rBound Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
