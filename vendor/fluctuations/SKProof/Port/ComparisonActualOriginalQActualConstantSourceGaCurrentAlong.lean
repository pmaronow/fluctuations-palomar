module

public import SKProof.Port.ComparisonActualOriginalQActualFourGaCurrent
public import ComparisonSignedCavityActualConstantSourceGaCurrentAlong
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQInheritedFourGaCurrentForestAlong

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_constant_source_children_forest_abs_sum_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp B : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (F : NativeActualResourceState (Spin n×Bool) as 0 star→ℝ) (hB : 0 ≤ B)
    (H : ∀Q∈nativeActualConstantSourceChildren_original_q M as star U hs hU,
      ((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [Q]).map (fun R=>|F R|)).sum ≤ |Q.term.coefficient| *B) :
    ((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth
      (nativeActualConstantSourceChildren_original_q M as star U hs hU)).map (fun R=>|F R|)).sum ≤ 6*B := by
  unfold nativeActualMinimumFourCenteredForest_original_q at H ⊢
  rw [nativeActualFourCenteredForest_eq_flatMap_singletons,List.map_flatMap,native_sum_flatMap]
  apply (List.sum_le_sum H).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualConstantSourceChildren_coefficient_variation_original_q M htotal ho hs hU) hB

def ActualConstantSourceGaCurrentOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    ∀(U : ℕ) (hs : star < U) (hU : U ≤ as.length) (V : ℝ),
      partitionPoint 0 as star ≤ Cmass*W n→W n ≤ V→V ≤ 1→V ≤ (M n).sweepRadius (partitionPoint 0 as U)→
      (M n).sweepRadius (partitionPoint 0 as star) ≤ V/2→(M n).z ≤ V/2→
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as star→
    ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum ≤ C*(dim n:ℝ)^(-eta)*(M n).xs^2

theorem ActualFourGaCurrentForestOnEveryFinalNetAlong_original_q.constant_source_children
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C Temp : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourGaCurrentForestOnEveryFinalNetAlong_original_q 0 1 3 depth eta Cmass cK C M W w)
    (hC : 0 ≤ C) (hCm : 0 ≤ Cmass) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp) :
    ActualConstantSourceGaCurrentOnEveryFinalNetAlong_original_q depth eta Cmass cK (6*C) M W w := by
  filter_upwards [H,htotal] with n hn hnTotal
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let mid:=retainedMassBefore (w n).star.val as
  let tail:=retainedMassAfter (w n).star.val as
  have Hcut : mid++tail=as:=retainedMass_append (w n).star.val as
  have Hmid : 0 < mid.length:=by
    have HP:=nativeRetainedCut_partitionPoint as (finiteCutMasses_ordered us hus j)
      (w n).star (finiteCutMasses_nodes us j hstar)
    by_contra Hm
    have Hz : star=0:=by change mid.length=0;omega
    change partitionPoint 0 as star=(w n).star.val at HP
    rw [Hz] at HP
    simp only [partitionPoint,partitionValues_zero,id_eq] at HP
    linarith [(w n).star.property]
  intro U hs hU V hmass hWV hV1 hVU hlow hz hstarK
  let B:=C*(dim n:ℝ)^(-eta)*(M n).xs^2
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  let P : ℕ→List PositiveMass→Prop:=fun ss bs=>
    ∀(hs' : ss < U) (hU' : U ≤ bs.length) (st : NativeActualResourceState (Spin (dim n)×Bool) bs 0 ss),
      NativeActualResourceGenerated 0 ss U [] st.generation st.tree st.term→
      st.generation=1→st.tree.leaves ≤ 3→
      ((nativeActualMinimumFourCenteredForest_original_q (M n) hs' hU' (W n) depth [st]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum ≤ |st.term.coefficient| *B
  have HP : P (0+mid.length) (mid++tail):=by
    intro hs' hU' st hgen hdepth hleaf
    have Hj:=hj [] mid tail
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at Hj
    have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
      simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm (M n).hxs.le
    have HH:=Hj Hcut rfl hmass U [] st (by simp) hdepth hleaf hgen Hmid (by simpa only [Nat.zero_add] using hs') hU'
      (M n).xs V le_rfl (hxs n) Hmi hWV hV1 hVU hlow hz hstarK
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one,B,mul_assoc] using HH
  have HP0 : P mid.length (mid++tail):=(Nat.zero_add mid.length) ▸ HP
  have HP' : P star as:=Hcut ▸ HP0
  have HB:=actual_constant_source_children_forest_abs_sum_le_original_q (M n) hnTotal
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth
    (nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n)) hB (by
      intro Q hQ
      exact HP' hs hU Q (nativeActualConstantSourceChildren_valid_original_q (M n) hs hU Q hQ)
        (nativeActualConstantSourceChildren_generation_original_q (M n) hs hU Q hQ)
        (nativeActualConstantSourceChildren_leaves_original_q (M n) hs hU Q hQ))
  exact HB.trans_eq (by dsimp only [B];ring)

theorem eventually_inherited_same_star_constant_source_Ga_current_along_original_q
    {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal Ttotal : ℝ}
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0 < cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Ttotal)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_original_q j k saving M W w) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceGaCurrentOnEveryFinalNetAlong_original_q depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,H⟩:=eventually_inherited_same_star_four_Ga_current_forest_along_original_q hdim
    0 1 3 depth Cmass cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCf hCcal M W hcanonical hWlim hcompare hsource hcutoff saving hsaving w Hmixed
  exact ⟨6*C,by positivity,H.constant_source_children hC.le (zero_le_one.trans hCm)
    (fun n=>(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm) htotal⟩

end OAI.SKFluctuations.Cavity
