module

public import ComparisonSignedCavitySecondLowIndexedCloneMomentLedger

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
attribute [local instance] nativeSecondLowSlotFintype

omit [Fintype ι] [Fintype S] [Nonempty S] in
theorem indexed_native_slot_card {as : List PositiveMass} (T : ClockTree S as) :
    Fintype.card T.Slot=T.leaves := by
  induction T with
  | leaf=>rfl
  | step b T ih=>exact ih
  | fork T E ihT ihE=>
    change Fintype.card (T.Slot⊕E.Slot)=T.leaves+E.leaves
    rw [Fintype.card_sum,ihT,ihE]

omit [Fintype ι] [Fintype S] [Nonempty S] in
theorem indexed_native_leaves_pos {as : List PositiveMass} (T : ClockTree S as) :
    0 < T.leaves := by
  induction T with
  | leaf=>norm_num [ClockTree.leaves]
  | step b T ih=>exact ih
  | fork T E ihT ihE=>change 0 < T.leaves+E.leaves;omega

omit [Nonempty S] in
theorem native_retained_clone_root_eq_fork {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→T.Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ T s 0 q Q x=
      (T.fork T).expect w φ q (fun σ=>Q σ.1 σ.2) x := by
  cases T <;> exact nativeRetainedCloneRootMean_eq_clone w φ _ q Q x

omit [Nonempty S] in
theorem native_retained_old_clone_sum_root {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedOldCloneSquareSum T w φ 0 q P x=
      (T.leaves:ℝ)*actualForkResamplingSquare (T.realize q) w φ
        (fun σ=>P ((T.assignmentEquiv q).symm σ)) x := by
  unfold nativeRetainedOldCloneSquareSum
  simp_rw [native_retained_clone_root_eq_fork]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,indexed_native_slot_card]
  rw [(T.fork T).expect_realize]
  rfl

private theorem indexed_actual_twin_slot_square
    {steps : List (GaussianStep ι)} (A : ReplicaTree ι S steps) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : OrderedSteps a steps) (F : S→ℝ) (x : ι→ℝ) :
    actualForkResamplingSquare A w φ (fun σ=>F (A.atSlot σ s)) x=
      actualSingleResamplingSquare steps w φ F x := by
  unfold actualSingleResamplingSquare actualForkResamplingSquare
  rw [ReplicaTree.expect_fork,ReplicaTree.expect_fork]
  have H1:∀σ,A.expect w φ (fun τ=>(F (A.atSlot σ s)-F (A.atSlot τ s))^2) x=
      gaussianHierarchyMean w φ (fun z=>(F (A.atSlot σ s)-F z)^2) steps x:=by
    intro σ
    exact A.expect_atSlot hw φ ho s (fun z=>(F (A.atSlot σ s)-F z)^2) x
  simp_rw [H1]
  rw [A.expect_atSlot hw φ ho s (fun u=>gaussianHierarchyMean w φ (fun z=>(F u-F z)^2) steps x) x]
  have HS:∀σ:(ReplicaTree.single (S:=S) steps).Assignment,
      (ReplicaTree.single (S:=S) steps).expect w φ
        (fun τ=>(F (ReplicaTree.singleEquiv (S:=S) steps σ)-F (ReplicaTree.singleEquiv (S:=S) steps τ))^2) x=
      gaussianHierarchyMean w φ (fun z=>(F (ReplicaTree.singleEquiv (S:=S) steps σ)-F z)^2) steps x:=by
    intro σ
    exact ReplicaTree.single_expect hw φ steps ho
      (fun z=>(F (ReplicaTree.singleEquiv (S:=S) steps σ)-F z)^2) x
  simp_rw [HS]
  exact (ReplicaTree.single_expect hw φ steps ho
    (fun u=>gaussianHierarchyMean w φ (fun z=>(F u-F z)^2) steps x) x).symm

private theorem indexed_native_twin_slot_square {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (F : S→ℝ) (x : ι→ℝ) :
    (T.fork T).expect w φ q (fun σ=>(F (T.atSlot σ.1 s)-F (T.atSlot σ.2 s))^2) x=
      actualSingleResamplingSquare (clockSteps as q) w φ F x := by
  rw [(T.fork T).expect_realize]
  change actualForkResamplingSquare (T.realize q) w φ
    (fun σ=>F (T.atSlot ((T.assignmentEquiv q).symm σ) s)) x=_
  have Hslot:∀σ:(T.realize q).Assignment,T.atSlot ((T.assignmentEquiv q).symm σ) s=
      (T.realize q).atSlot σ (T.slotEquiv q s):=by
    intro σ
    have H:=T.realize_atSlot q ((T.assignmentEquiv q).symm σ) s
    simpa only [Equiv.apply_symm_apply] using H.symm
  simp_rw [Hslot]
  exact indexed_actual_twin_slot_square (T.realize q) (T.slotEquiv q s) hw φ (clockSteps_ordered ho q) F x

theorem native_retained_new_clone_sum_root {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (F : S→ℝ) (x : ι→ℝ) :
    nativeRetainedNewCloneSquareSum T w φ 0 q F x=
      (T.leaves:ℝ)*actualSingleResamplingSquare (clockSteps as q) w φ F x := by
  unfold nativeRetainedNewCloneSquareSum
  simp_rw [native_retained_clone_root_eq_fork]
  simp_rw [indexed_native_twin_slot_square T _ hw φ ho q F x]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,indexed_native_slot_card]

end OAI.SKFluctuations.Cavity
