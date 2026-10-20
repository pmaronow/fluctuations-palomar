module

public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonSignedCavityActualSharpSourceCuts
public import ComparisonSignedCavityActualConstantSourceCategoryReduction
public import ComparisonSignedCavityActualInitialThreeGammaOnCutsAlong
public import ComparisonSignedCavityActualStrongSharpSourceCuts
public import ComparisonSignedCavityActualConstantPendingCategoryEnvelope
public import ComparisonSignedCavityActualConstantPostTaylorEnvelope
public import ComparisonSignedCavityActualFourLongitudinalRestorationReadout
public import ComparisonSignedCavityActualConstantPostLongitudinalEnvelope
public import ComparisonSignedCavityActualConstantThreeCategoryEnvelope
public import ComparisonSignedCavityActualConstantB0CategoryEnvelope
public import ComparisonSignedCavityActualConstantB0OnStrongCutsAlong
public import ComparisonSignedCavityActualLongitudinalCategorySum
public import ComparisonSignedCavityActualConstantGammaRestorationOnCutsAlong
public import ComparisonSignedCavityActualHigherTaylorCategorySum
public import ComparisonSignedCavityActualConstantPostTaylorEnvelopeAlong
public import ComparisonSignedCavityActualConstantB0CategoryEnvelopeAlong
public import ComparisonSignedCavityActualConstantFullB0EnvelopeSavingAlong
public import ComparisonSignedCavityActualJointHighRestorationCategorySum
public import ComparisonSignedCavityActualConstantSavedJointOnCutsAlong
public import ComparisonSignedCavityActualConstantThreeCategoryEnvelopeAlong
public import ComparisonSignedCavityActualInitialLongitudinalOnCutsAlong
public import ComparisonSignedCavityActualInitialRestoredGaOnCutsAlong
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyFourReadoutPrimitives
public import ComparisonActualHighOnlyOriginalTaylorProfiles
public import ComparisonActualHighOnlyFirstHighReadoutPrimitives
public import ComparisonActualHighOnlyLowSharpWindowSourceAlong

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

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourceChildren_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    List (NativeActualResourceState (Spin n×Bool) as 0 star) :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  (base.projection (hs.le.trans hU)).reweight chi::
    nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU) .highRow base

theorem nativeActualConstantSourceChildren_valid_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length)
    (Q : NativeActualResourceState (Spin n×Bool) as 0 star)
    (hQ : Q∈nativeActualConstantSourceChildren_high_only M as star U hs hU) :
    NativeActualResourceGenerated 0 star U [] Q.generation Q.tree Q.term := by
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have Hbase : NativeActualResourceGenerated 0 star U [] base.generation base.tree base.term:=
    .physical (.constant as hU)
  rcases List.mem_cons.mp hQ with rfl|hQ
  · exact (Hbase.projection (hs.le.trans hU)).reweight _
  · exact nativeActualResourceStep_valid _ hs (hs.le.trans hU) .highRow base Hbase Q hQ

theorem nativeActualConstantSourceChildren_generation_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length)
    (Q : NativeActualResourceState (Spin n×Bool) as 0 star)
    (hQ : Q∈nativeActualConstantSourceChildren_high_only M as star U hs hU) : Q.generation=1 := by
  rcases List.mem_cons.mp hQ with rfl|hQ
  · rfl
  · exact nativeActualResourceStep_generation _ hs (hs.le.trans hU) .highRow _ Q hQ

theorem nativeActualConstantSourceChildren_leaves_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length)
    (Q : NativeActualResourceState (Spin n×Bool) as 0 star)
    (hQ : Q∈nativeActualConstantSourceChildren_high_only M as star U hs hU) : Q.tree.leaves≤3 := by
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have hb : base.tree.leaves≤1:=by rw [show base.tree=ClockTree.single (S:=Spin n×Bool) as from rfl,ClockTree.single_leaves_exact]
  rcases List.mem_cons.mp hQ with rfl|hQ
  · change (base.projection (hs.le.trans hU)).tree.leaves≤3
    exact nativeActualResourceStep_leaves_le
      (nativeOriginalHighRowGamma U (nativeContinuumMixedClock n M.bf M.hf as))
      hs (hs.le.trans hU) .projection base _ hb (List.mem_singleton_self _)
  · exact nativeActualResourceStep_leaves_le _ hs (hs.le.trans hU) .highRow base Q hb hQ

theorem nativeActualConstantSourceChildren_coefficient_variation_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length) :
    ((nativeActualConstantSourceChildren_high_only M as star U hs hU).map
      (fun Q=>|Q.term.coefficient|)).sum≤6 := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit_high_only M htotal as ho U (by omega) hU
  have Hrow:=nativeActualResourceStep_coefficient_variation_le ho (nativeOriginalHighRowGamma U K)
    (fun st p _=>nativeOriginalHighRowGamma_abs_le_one ho U K st p)
    hs (hs.le.trans hU) .highRow base
    (show base.tree.leaves≤1 by simp only [base,nativeActualConstantState,single_leaves_exact,le_refl])
  have Hcoef : base.term.coefficient=1:=rfl
  rw [Hcoef] at Hrow
  norm_num only [abs_one,NativeActualExpansionOp.coefficientCost,Nat.cast_one,mul_one,one_mul] at Hrow
  unfold nativeActualConstantSourceChildren_high_only
  simp only [List.map_cons,List.sum_cons,NativeActualResourceState.reweight,
    NativeResourceTerm.reweight,NativeActualResourceState.projection,NativeResourceTerm.projection,
    nativeActualConstantState,NativeResourceTerm.ofLive,mul_one]
  change |chi|+_≤6
  rw [abs_of_nonneg Hchi.1]
  have Hchi1 : chi≤1:=Hchi.2
  change chi+((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    .highRow base).map (fun Q=>|Q.term.coefficient|)).sum≤6
  linarith

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualHighOnlyOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

structure ActualSharpSourceCutGeometry_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℝ) (w : ActualSlowWindowChoice) (high outer : PositiveMass)
    (radius cFirst cK A : ℝ) : Prop where
  star_lt : w.star.val < high.val
  high_lt : high.val < outer.val
  outer_le_one : outer.val ≤ 1
  outer_scale : outer.val ≤ A*W
  first_high : 2*cFirst*W ≤ high.val
  radius_lower : W ≤ radius
  radius_upper : radius ≤ 1
  radius_high : radius ≤ M.R high.val
  star_radius : M.R w.star.val ≤ radius/2
  regular_radius : M.z ≤ radius/2
  clock_star : cK*W ≤ actualMixedClock (n+1) M.bf M.hf w.star.val

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourOtherCategorySum_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    (cat : NativeActualOtherSourceCategory) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only M U Q cat)).sum

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualThreeGammaCategoryEnvelope_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |nativeActualFourOtherCategorySum_high_only M U W rows .gammaRetained|/(chi*K star)+
    |nativeActualFourOtherCategorySum_high_only M U W rows .gammaHighRestoration|/(chi*K star)+
    |nativeActualFourOtherCategorySum_high_only M U W rows .gammaLowRestoration|/(chi*K star)

def ActualInitialThreeGammaOnGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*x n →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        nativeActualThreeGammaCategoryEnvelope_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
            [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length)
              seedMass (by omega)]) ≤ err n*(x n*(M n).xs^2)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualHighOnlyOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000

structure ActualStrongSharpSourceCutGeometry_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℝ) (w : ActualSlowWindowChoice) (high outer : PositiveMass)
    (radius cFirst cK A Rmacro Cx : ℝ) : Prop extends
      ActualSharpSourceCutGeometry_high_only M W w high outer radius cFirst cK A where
  four_band : 4*W ≤ M.R high.val
  star_gap : M.R w.star.val ≤ min (M.R high.val/8) (Rmacro/4)
  regular_gap : M.z ≤ min (M.R high.val/8) (Rmacro/4)
  source_lower : Cx*M.xs ≤ high.val
  macro_band : W ≤ Rmacro/2

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourcePendingCategoryEnvelope_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualPendingOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 4000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualPostTaylorOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_pending_envelope_higher_Taylor_paid_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
          (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .higherTaylor|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourcePendingCategoryEnvelope_high_only M hs hU W Temp cK depth ≤
      nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only M hs hU W Temp cK depth+
        ((List.range depth).map err).sum*M.xs^2 := by
  have HE : nativeActualConstantSourcePendingCategoryEnvelope_high_only M hs hU W Temp cK depth=
      nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only M hs hU W Temp cK depth+
        ((List.range depth).map (fun j=>
          |nativeActualFourOtherCategorySum_high_only M U W
            (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
              (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .higherTaylor|/
            (Real.exp (-4*Temp)*cK*W))).sum := by
    unfold nativeActualConstantSourcePendingCategoryEnvelope_high_only nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [(native_actual_pending_categories_perm_higher_Taylor.map _).sum_eq]
    simp only [List.map_cons,List.sum_cons,add_div]
    ring
  rw [HE]
  apply add_le_add le_rfl
  apply (List.sum_le_sum (fun j hj=>H j (List.mem_range.mp hj))).trans_eq
  exact List.sum_map_mul_right _ _ _

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem native_actual_four_longitudinal_contrast_eq_resources_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as)
    (hstar : star ≤ as.length) (right : Bool) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourOtherCategoryContrast_high_only M U st (nativeActualLongitudinalCategory right)=
      -chi*K star*(nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U st.term right-
        (1/2:ℝ)*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U (st.term.retarget 0) right) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  have hsplit (T : ClockTree (Spin n×Bool) as) (s : T.Slot) :
      (nativeFreshAtSlot T 0 s star).tree.splitIndex ((nativeFreshAtSlot T 0 s star).embed s)
        (nativeFreshAtSlot T 0 s star).mark=star:=by
    rw [ClockTree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hstar]
  cases right <;>
    unfold nativeActualLongitudinalCategory nativeActualOriginalFourOtherCategoryContrast_high_only
      nativeActualOriginalOtherSourceCategory nativeActualOriginalFreshResourceLongitudinalRestoration_high_only <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,
      NativeGeneratedTest.retarget] <;>
    simp only [hsplit] <;> ring_nf <;> rfl

theorem actual_four_longitudinal_error_abs_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (right : Bool)
    {B : ℝ} (hB : 0 ≤ B)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U st.term right| ≤ B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U (st.term.retarget 0) right| ≤ B) :
    |nativeActualOriginalFourLongitudinalError_high_only M U W st right| ≤ 2*B := by
  have H:=abs_sub_le ((W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U st.term right) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U (st.term.retarget 0) right))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at H
  have HE : nativeActualOriginalFourLongitudinalError_high_only M U W st right=
      (W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U st.term right-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration_high_only M U (st.term.retarget 0) right):=by
    unfold nativeActualOriginalFourLongitudinalError_high_only
    ring
  rw [HE]
  linarith

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualPostLongitudinalOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourceThreeCategoryEnvelope_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualFinalThreeSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_post_longitudinal_envelope_joint_paid_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,∀cat∈nativeActualSavedJointSourceCategories,
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
          (nativeActualConstantSourceChildren_high_only M as star U hs hU)) cat|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only M hs hU W Temp cK depth ≤
      nativeActualConstantSourceThreeCategoryEnvelope_high_only M hs hU W Temp cK depth+
        4*((List.range depth).map err).sum*M.xs^2 := by
  unfold nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only nativeActualConstantSourceThreeCategoryEnvelope_high_only
  have Hrow j (hj : j∈List.range depth) :
      (nativeActualPostLongitudinalOtherSourceCategories.map (fun cat=>
        |nativeActualFourOtherCategorySum_high_only M U W
          (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
            (nativeActualConstantSourceChildren_high_only M as star U hs hU)) cat|)).sum/
        (Real.exp (-4*Temp)*cK*W) ≤
      (nativeActualFinalThreeSourceCategories.map (fun cat=>
        |nativeActualFourOtherCategorySum_high_only M U W
          (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
            (nativeActualConstantSourceChildren_high_only M as star U hs hU)) cat|)).sum/
        (Real.exp (-4*Temp)*cK*W)+4*err j*M.xs^2 := by
    rw [(native_actual_post_longitudinal_categories_perm_saved_joint.map _).sum_eq]
    simp only [List.map_append,List.sum_append,add_div]
    apply add_le_add le_rfl
    have HH:=List.sum_le_sum (fun cat hcat=>H j (List.mem_range.mp hj) cat hcat)
    simp only [nativeActualSavedJointSourceCategories,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,add_div] at HH ⊢
    linarith only [HH]
  have HH:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right,List.sum_map_mul_left] at HH
  exact HH

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourceB0CategoryEnvelope_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualFinalB0SourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_three_category_envelope_gamma_paid_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,∀cat∈nativeActualSavedGammaRestorationCategories,
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
          (nativeActualConstantSourceChildren_high_only M as star U hs hU)) cat|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourceThreeCategoryEnvelope_high_only M hs hU W Temp cK depth ≤
      nativeActualConstantSourceB0CategoryEnvelope_high_only M hs hU W Temp cK depth+
        2*((List.range depth).map err).sum*M.xs^2 := by
  unfold nativeActualConstantSourceThreeCategoryEnvelope_high_only nativeActualConstantSourceB0CategoryEnvelope_high_only
  have Hrow j (hj : j∈List.range depth) :
      (nativeActualFinalThreeSourceCategories.map (fun cat=>
        |nativeActualFourOtherCategorySum_high_only M U W
          (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
            (nativeActualConstantSourceChildren_high_only M as star U hs hU)) cat|)).sum/
        (Real.exp (-4*Temp)*cK*W) ≤
      (nativeActualFinalB0SourceCategories.map (fun cat=>
        |nativeActualFourOtherCategorySum_high_only M U W
          (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
            (nativeActualConstantSourceChildren_high_only M as star U hs hU)) cat|)).sum/
        (Real.exp (-4*Temp)*cK*W)+2*err j*M.xs^2 := by
    rw [(native_actual_three_categories_perm_saved_gamma.map _).sum_eq]
    simp only [List.map_append,List.sum_append,add_div]
    apply add_le_add le_rfl
    have HH:=List.sum_le_sum (fun cat hcat=>H j (List.mem_range.mp hj) cat hcat)
    simp only [nativeActualSavedGammaRestorationCategories,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,add_div] at HH ⊢
    linarith only [HH]
  have HH:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right,List.sum_map_mul_left] at HH
  exact HH

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_constant_second_low_family_reindex_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as mid tail : List PositiveMass) (hparts : as=mid++tail)
    (star U : ℕ) (hindex : mid.length=star) (hs : star<U) (hU : U≤as.length)
    (hs' : mid.length<U) (hU' : U≤(mid++tail).length) (W B : ℝ) (depth : ℕ)
    (H :
      let K:=nativeContinuumMixedClock n M.bf M.hf (mid++tail)
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks (mid++tail) (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs' hU' W depth
          (nativeActualConstantSourceChildren_high_only M (mid++tail) mid.length U hs' hU')) .secondLow|/
        (chi*K mid.length) ≤ B) :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
          (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .secondLow|/(chi*K star) ≤ B := by
  subst as
  subst star
  exact H

def ActualConstantB0OnStrongGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_high_only (M n) U (W n)
        (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)) .secondLow|/(chi*K star) ≤
            err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_longitudinal_category_signed_sum_abs_le_error_sum_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) (right : Bool) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only M U Q
      (nativeActualLongitudinalCategory right))).sum|/(chi*K star) ≤
      (xs.map (fun Q=>|nativeActualOriginalFourLongitudinalError_high_only M U W Q right|)).sum := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only M hCf HS hxs hW hcK ho hs hU hstarK
  have Hsum : (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only M U Q
      (nativeActualLongitudinalCategory right))).sum=
      -den*(xs.map (fun Q=>nativeActualOriginalFourLongitudinalError_high_only M U W Q right)).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro Q _
    rw [native_actual_four_longitudinal_contrast_eq_resources_high_only M U Q ho (hs.le.trans hU) right]
    dsimp only [nativeActualOriginalFourLongitudinalError_high_only,den,chi,K]
    ring
  dsimp only
  rw [Hsum,abs_mul,abs_neg,abs_of_pos hden]
  change den*|(xs.map (fun Q=>nativeActualOriginalFourLongitudinalError_high_only M U W Q right)).sum|/den ≤ _
  rw [mul_div_cancel_left₀ _ (ne_of_gt hden)]
  exact native_abs_sum_map_le xs (fun Q=>nativeActualOriginalFourLongitudinalError_high_only M U W Q right)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantGammaRestorationOnGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      ∀cat∈nativeActualSavedGammaRestorationCategories,
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_high_only (M n) U (W n)
        (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)) cat|/(chi*K star) ≤
            err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000

theorem actual_higher_Taylor_category_signed_sum_abs_le_error_sum_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only M U Q .higherTaylor)).sum|/
      (chi*K star) ≤ (xs.map (fun Q=>|nativeActualOriginalFourHigherTaylorError_high_only M U W Q|)).sum := by
  dsimp only
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only M hCf HS hxs hW hcK ho hs hU hstarK
  have H:=native_abs_sum_map_le xs (nativeActualOriginalFourHigherTaylorError_high_only M U W)
  unfold nativeActualOriginalFourHigherTaylorError_high_only at H
  dsimp only at H
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [nativeActualOriginalFourHigherTaylorError_high_only,one_div,one_mul,mul_comm,div_eq_mul_inv] using H

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSourcePostTaylorEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourcePendingCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
        nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth+
          err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSourceB0CategoryEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourceThreeCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
        nativeActualConstantSourceB0CategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth+
          err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantFullB0EnvelopeSavingAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourceB0CategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
        err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000

theorem actual_joint_HIGH_restoration_category_signed_sum_abs_le_error_sum_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only M U Q kind.category)).sum|/
      (chi*K star) ≤ (xs.map (fun Q=>|nativeActualOriginalFourJointHighRestorationError_high_only kind M U W Q|)).sum := by
  dsimp only
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only M hCf HS hxs hW hcK ho hs hU hstarK
  have H:=native_abs_sum_map_le xs (nativeActualOriginalFourJointHighRestorationError_high_only kind M U W)
  unfold nativeActualOriginalFourJointHighRestorationError_high_only at H
  dsimp only at H
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [nativeActualOriginalFourJointHighRestorationError_high_only,one_div,one_mul,mul_comm,div_eq_mul_inv] using H

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSavedJointOnGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      ∀cat∈nativeActualSavedJointSourceCategories,
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_high_only (M n) U (W n)
        (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)) cat|/(chi*K star) ≤
            err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSourceThreeCategoryEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
        nativeActualConstantSourceThreeCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth+
          err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialLongitudinalEnvelope_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |nativeActualFourOtherCategorySum_high_only M U W rows .longitudinalLeft|/(chi*K star)+
    |nativeActualFourOtherCategorySum_high_only M U W rows .longitudinalRight|/(chi*K star)

def ActualInitialLongitudinalOnGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      ∀(i : ℕ) (hi : i ≤ star) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
        partitionPoint 0 as i ≤ A*x →
        nativeActualInitialLongitudinalEnvelope_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
            [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]) ≤ err n*(x*(M n).xs^2)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualInitialRestoredGaOnGivenCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length)
            seedMass (by omega)]).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError_high_only (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^3

end OAI.SKFluctuations.Cavity
