module

public import ComparisonSignedCavitySecondLowScalarResourceReadout
public import ComparisonSignedCavityActualFourOtherSourceCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

 theorem native_second_low_retained_coefficient_eq_joint_ledger
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) :
    nativeRetainedCenteredCoefficient n q U b h K T P [a,z] 2 0=
      nativeSecondLowJointLedger n q U b h K T P [a,z] := by
  rw [native_second_low_centered_eq_scalar_subtraction n q U b h K T ho P a z hU haz,
    native_second_low_joint_ledger_eq_scalar_subtraction n q U b h K T ho P [a,z]]

 theorem native_actual_second_low_category_eq_joint_ledger_half
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ)
    (hs : star < U) (hU : U ≤ as.length) :
    nativeActualOriginalOtherSourceCategory .secondLow n q U b h K C T P s star=
      let g:=nativeFreshAtSlot T 0 s star
      nativeSecondLowJointLedger n q U b h K g.tree (fun σ=>P (g.restRestrict σ)) [g.embed s,g.mark]/2 := by
  let g:=nativeFreshAtSlot T 0 s star
  have Hsplit:g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      Nat.min_eq_left (hs.le.trans hU)]
  unfold nativeActualOriginalOtherSourceCategory
  dsimp only
  rw [native_second_low_retained_coefficient_eq_joint_ledger n q U b h K g.tree ho
    (fun σ=>P (g.restRestrict σ)) (g.embed s) g.mark hU (by rwa [Hsplit])]
  ring

 def nativeActualOriginalCenteredResourceCReplacement
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (hU : U ≤ as.length) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi^2*nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T P.live.test.target star hU Pc

 def nativeActualOriginalFourCReplacementContrast
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  nativeActualOriginalCenteredResourceCReplacement M U hU st.term-
    (1/2:ℝ)*nativeActualOriginalCenteredResourceCReplacement M U hU (st.term.retarget 0)

 theorem native_actual_second_low_resource_category_minus_c_replacement
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (hU : U ≤ as.length) (ho : MassOrdered 0 as) (hs : star < U)
    (P : NativeResourceTerm i star T) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualOriginalOtherSourceCategory .secondLow n q U b h K C T
      (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))
      P.live.test.target star-nativeActualOriginalCenteredResourceCReplacement M U hU P=
        nativeActualOriginalCenteredResourceB0MinusCReplacement M U hU P := by
  dsimp only
  rw [native_actual_second_low_category_eq_joint_ledger_half _ _ _ _ _ _ _ T ho _ _ star hs hU]
  rfl

 theorem native_actual_four_second_low_minus_c_replacement_eq_two_resource_sources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) (hs : star < U)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourOtherCategoryContrast M U st .secondLow-
      nativeActualOriginalFourCReplacementContrast M U hU st=
      nativeActualOriginalCenteredResourceB0MinusCReplacement M U hU st.term-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceB0MinusCReplacement M U hU (st.term.retarget 0) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have HC:nativeOriginalCenteredRestTest n q U b h K g.tree
      (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C)=
      fun σ=>nativeOriginalCenteredRestTest n q U b h K st.tree
        (nativeActualResourceRestValue st.term 0 qfull 0 C) (g.restRestrict σ):=by
    rw [native_actual_resource_rest_value_retarget]
    exact native_original_centered_rest_test_fresh n q U b h K st.tree ho _ _ star
  have H0:=native_actual_second_low_resource_category_minus_c_replacement M U hU ho hs st.term
  have H1:=native_actual_second_low_resource_category_minus_c_replacement M U hU ho hs (st.term.retarget 0)
  dsimp only at H0 H1
  rw [HC] at H1
  have Htarget:(st.term.retarget 0).live.test.target=g.mark:=rfl
  rw [Htarget] at H1
  dsimp only [b,h,K,C,q,qfull,g] at H1
  unfold nativeActualOriginalFourOtherCategoryContrast nativeActualOriginalFourCReplacementContrast
  dsimp only
  linear_combination H0-(1/2:ℝ)*H1

end OAI.SKFluctuations.Cavity
