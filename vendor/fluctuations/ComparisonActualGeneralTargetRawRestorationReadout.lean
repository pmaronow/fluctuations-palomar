module

public import ComparisonActualGeneralTargetMeanReadout
public import ComparisonActualGeneralResourceJointHighRestorationReadout
public import ComparisonActualGeneralResourceJointLowRestorationReadout
public import ComparisonActualGeneralResourceLongitudinalRestorationReadout
public import ComparisonActualGeneralResourceFullB0Readout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

def actualGeneralTargetFreshConstantResource {n : ℕ} (as : List PositiveMass) (i : ℕ) :
    NativeResourceTerm 0 i (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree :=
  (nativeActualConstantState (S:=Spin n×Bool) as 0 i).term.retarget 0

theorem actual_general_target_fresh_constant_resource_generated
    {n : ℕ} (as : List PositiveMass) (i U : ℕ) (hU : U ≤ as.length) :
    NativeActualResourceGenerated 0 i U [] 0
      (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree
      (actualGeneralTargetFreshConstantResource as i) :=
  (show NativeActualResourceGenerated 0 i U [] 0
      (nativeActualConstantState (S:=Spin n×Bool) as 0 i).tree
      (nativeActualConstantState (S:=Spin n×Bool) as 0 i).term from
    .physical (.constant as hU)).retarget

theorem actual_general_target_fresh_constant_rest_value_eq_one
    {n : ℕ} (as : List PositiveMass) (i : ℕ)
    (v x : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (C : ℕ→ℝ) :
    nativeActualResourceRestValue (actualGeneralTargetFreshConstantResource (n:=n) as i) v q x C=(fun _=>1) := by
  funext sigma
  simp [actualGeneralTargetFreshConstantResource,nativeActualConstantState,NativeResourceTerm.retarget,
    NativeResourceMonomial.retarget,NativeGeneratedTest.retarget,nativeResourceConstant,
    NativeResourceTerm.ofLive,nativeActualResourceRestValue,NativeResourceTerm.scalar,
    nativeRestGeneratedTestValue,NativeGeneratedTest.edges]

theorem actual_general_target_fresh_constant_full_value_eq_one
    {n : ℕ} (as : List PositiveMass) (i : ℕ)
    (v x : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (C : ℕ→ℝ) :
    (actualGeneralTargetFreshConstantResource (n:=n) as i).value (fullWeight n) (fullFeature n) v q
      (fun sigma tau=>deletedOverlap n (joinSpin sigma) (joinSpin tau)) C x=(fun _=>1) := by
  funext sigma
  simp [actualGeneralTargetFreshConstantResource,nativeActualConstantState,NativeResourceTerm.retarget,
    NativeResourceMonomial.retarget,NativeGeneratedTest.retarget,nativeResourceConstant,
    NativeResourceTerm.ofLive,NativeResourceTerm.value,NativeResourceTerm.scalar,
    NativeGeneratedTest.value,nativeGeneratedEdgeProduct,NativeGeneratedTest.edges]

section Readers
variable {n : ℕ} (bf hf : ℝ→ℝ≥0)

def actualGeneralTargetRawFreshB0Part (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  nativeSecondLowFreshFullB0Source n q U b h K (single (S:=Spin n×Bool) as) (singleSlot as) i (fun _=>1)

def actualGeneralTargetRawTaylorRemainder (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  nativeActualTaylorRemainder n q U b h K g.tree (fun _=>1) (g.embed s) g.mark

def actualGeneralTargetRawJointHighPart (kind : NativeJointHighRestorationKind)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  actualGeneralResourceJointHighRestoration kind bf hf U (actualGeneralTargetFreshConstantResource as i)
    (g.embed s) g.mark

def actualGeneralTargetRawJointLowPart (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  actualGeneralResourceJointLowRestoration bf hf U (actualGeneralTargetFreshConstantResource as i)
    (g.embed s) g.mark

def actualGeneralTargetRawLongitudinalPart (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K i*(actualGeneralResourceLongitudinalRestoration bf hf U (actualGeneralTargetFreshConstantResource as i) (g.embed s)+
    actualGeneralResourceLongitudinalRestoration bf hf U (actualGeneralTargetFreshConstantResource as i) g.mark)

def actualGeneralTargetRawRestorationBudget (as : List PositiveMass) (i U : ℕ) : ℝ :=
  |actualGeneralTargetRawFreshB0Part (n:=n) bf hf as i U|+
    |actualGeneralTargetRawJointHighPart (n:=n) bf hf .lowTwoHigh as i U|+
    |actualGeneralTargetRawJointLowPart (n:=n) bf hf as i U|+
    |actualGeneralTargetRawLongitudinalPart (n:=n) bf hf as i U|+
    |actualGeneralTargetRawJointHighPart (n:=n) bf hf .fourGLow as i U|
end Readers

theorem actual_general_target_original_Taylor_eq_raw_parts
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i U : ℕ} (hi : i < U) (hU : U ≤ as.length) :
    actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U=
      actualGeneralTargetRawFreshB0Part (n:=n) bf hf as i U+
      actualGeneralTargetRawTaylorRemainder (n:=n) bf hf as i U-
      actualGeneralTargetRawJointHighPart (n:=n) bf hf .lowTwoHigh as i U-
      actualGeneralTargetRawJointLowPart (n:=n) bf hf as i U-
      actualGeneralTargetRawLongitudinalPart (n:=n) bf hf as i U-
      actualGeneralTargetRawJointHighPart (n:=n) bf hf .fourGLow as i U := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=i:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hi.le.trans hU)]
  have HB : (1/2:ℝ)*nativeRetainedCenteredCoefficient n q U b h K g.tree (fun _=>1) [g.embed s,g.mark] 2 0=
      nativeSecondLowFreshFullB0Source n q U b h K T s i (fun _=>1):=by
    unfold nativeSecondLowFreshFullB0Source
    dsimp only
    rw [native_second_low_centered_eq_scalar_subtraction n q U b h K g.tree ho (fun _=>1)
      (g.embed s) g.mark hU (by rw [Hsplit];exact hi),
      ←native_second_low_joint_ledger_eq_scalar_subtraction n q U b h K g.tree ho (fun _=>1) [g.embed s,g.mark]]
    ring
  unfold actualGeneralTargetOriginalTaylorPart actualGeneralTargetRawFreshB0Part
    actualGeneralTargetRawTaylorRemainder actualGeneralTargetRawJointHighPart actualGeneralTargetRawJointLowPart
    actualGeneralTargetRawLongitudinalPart actualGeneralResourceJointHighRestoration
    actualGeneralResourceJointLowRestoration actualGeneralResourceLongitudinalRestoration
  dsimp only
  rw [actual_general_target_fresh_constant_rest_value_eq_one,
    actual_general_target_fresh_constant_full_value_eq_one]
  unfold nativeActualOriginalForwardTaylorError nativeActualHigherAllocatedRemainder
    nativeJointHighRestorationSource
  change _= _
  rw [show (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree.splitIndex
      ((nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).embed (singleSlot as))
      (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).mark=i from Hsplit]
  rw [HB]

theorem actual_general_target_original_Taylor_abs_le_raw_restoration_and_Taylor
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i U : ℕ} (hi : i < U) (hU : U ≤ as.length) :
    |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U| ≤
      actualGeneralTargetRawRestorationBudget (n:=n) bf hf as i U+
        |actualGeneralTargetRawTaylorRemainder (n:=n) bf hf as i U| := by
  rw [actual_general_target_original_Taylor_eq_raw_parts bf hf as ho hi hU]
  calc
    _ ≤ |actualGeneralTargetRawFreshB0Part (n:=n) bf hf as i U|+
        |actualGeneralTargetRawTaylorRemainder (n:=n) bf hf as i U|+
        |actualGeneralTargetRawJointHighPart (n:=n) bf hf .lowTwoHigh as i U|+
        |actualGeneralTargetRawJointLowPart (n:=n) bf hf as i U|+
        |actualGeneralTargetRawLongitudinalPart (n:=n) bf hf as i U|+
        |actualGeneralTargetRawJointHighPart (n:=n) bf hf .fourGLow as i U| :=
      (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ = _:=by unfold actualGeneralTargetRawRestorationBudget;ring

end OAI.SKFluctuations.Cavity
