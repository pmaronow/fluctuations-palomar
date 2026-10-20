module

public import ComparisonSignedCavityCanonicalRestCloneTransport
public import ComparisonSignedCavityActualDummyScalarTree

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {S B : Type*}

theorem nativeCloneBlockAtSlot_cavityLeft_tree {as : List PositiveMass}
    (T : ClockTree (S×B) as) (target : T.Slot) (cut : ℕ) :
    (nativeCloneBlockAtSlot T target cut).tree.cavityLeft=
      (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).tree := by
  induction T generalizing cut with
  | leaf=>cases cut <;> rfl
  | step b T ih=>
    cases cut with
    | zero=>rfl
    | succ cut=>exact congrArg (ClockTree.step b) (ih target cut)
  | fork T E ihT ihE=>
    cases cut with
    | zero=>rfl
    | succ cut=>cases target with
      | inl target=>exact congrArg (fun R=>ClockTree.fork R E.cavityLeft) (ihT target (cut+1))
      | inr target=>exact congrArg (ClockTree.fork T.cavityLeft) (ihE target (cut+1))

theorem nativeCloneBlockAtSlot_cavityLeft_old_slot {as : List PositiveMass}
    (T : ClockTree (S×B) as) (target : T.Slot) (cut : ℕ) (s : T.Slot) :
    cast (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree T target cut))
      ((nativeCloneBlockAtSlot T target cut).tree.cavityLeftSlot
        ((nativeCloneBlockAtSlot T target cut).oldEmbed s))=
      (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).oldEmbed
        (T.cavityLeftSlot s) := by
  induction T generalizing cut with
  | leaf=>cases cut <;> cases s <;> rfl
  | step b T ih=>cases cut with
    | zero=>rfl
    | succ cut=>exact ih target cut s
  | fork T E ihT ihE=>
    cases cut with
    | zero=>rfl
    | succ cut=>cases target with
      | inl target=>cases s with
        | inl s=>
          change cast _ (Sum.inl _) = Sum.inl _
          rw [dummy_cast_sum_inl (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree T target (cut+1))) rfl]
          exact congrArg Sum.inl (ihT target (cut+1) s)
        | inr s=>
          change cast _ (Sum.inr _) = Sum.inr _
          rw [dummy_cast_sum_inr (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree T target (cut+1))) rfl]
          rfl
      | inr target=>cases s with
        | inl s=>
          change cast _ (Sum.inl _) = Sum.inl _
          rw [dummy_cast_sum_inl rfl (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree E target (cut+1)))]
          rfl
        | inr s=>
          change cast _ (Sum.inr _) = Sum.inr _
          rw [dummy_cast_sum_inr rfl (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree E target (cut+1)))]
          exact congrArg Sum.inr (ihE target (cut+1) s)

theorem nativeCloneBlockAtSlot_cavityLeft_new_slot {as : List PositiveMass}
    (T : ClockTree (S×B) as) (target : T.Slot) (cut : ℕ) (s : T.Slot) :
    cast (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree T target cut))
      ((nativeCloneBlockAtSlot T target cut).tree.cavityLeftSlot
        ((nativeCloneBlockAtSlot T target cut).newEmbed s))=
      (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).newEmbed
        (T.cavityLeftSlot s) := by
  induction T generalizing cut with
  | leaf=>cases cut <;> cases s <;> rfl
  | step b T ih=>cases cut with
    | zero=>rfl
    | succ cut=>exact ih target cut s
  | fork T E ihT ihE=>
    cases cut with
    | zero=>rfl
    | succ cut=>cases target with
      | inl target=>cases s with
        | inl s=>
          change cast _ (Sum.inl _) = Sum.inl _
          rw [dummy_cast_sum_inl (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree T target (cut+1))) rfl]
          exact congrArg Sum.inl (ihT target (cut+1) s)
        | inr s=>
          change cast _ (Sum.inr _) = Sum.inr _
          rw [dummy_cast_sum_inr (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree T target (cut+1))) rfl]
          rfl
      | inr target=>cases s with
        | inl s=>
          change cast _ (Sum.inl _) = Sum.inl _
          rw [dummy_cast_sum_inl rfl (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree E target (cut+1)))]
          rfl
        | inr s=>
          change cast _ (Sum.inr _) = Sum.inr _
          rw [dummy_cast_sum_inr rfl (congrArg ClockTree.Slot (nativeCloneBlockAtSlot_cavityLeft_tree E target (cut+1)))]
          exact congrArg Sum.inr (ihE target (cut+1) s)

theorem nativeCloneBlockAtSlot_cavityLeft_old_reader {as : List PositiveMass}
    (T : ClockTree (S×B) as) (target : T.Slot) (cut : ℕ)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).oldRestrict
      (cast (congrArg ClockTree.Assignment (nativeCloneBlockAtSlot_cavityLeft_tree T target cut)) σ)=
        (nativeCloneBlockAtSlot T target cut).restOldRestrict σ := by
  apply T.cavityLeft.assignment_ext
  intro s
  obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
  rw [NativeRetainedSubtreeClone.restOldRestrict_at,
    (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).old_at]
  have HH:=atSlot_cast_tree (nativeCloneBlockAtSlot_cavityLeft_tree T target cut) σ
    ((nativeCloneBlockAtSlot T target cut).tree.cavityLeftSlot
      ((nativeCloneBlockAtSlot T target cut).oldEmbed s))
  rw [nativeCloneBlockAtSlot_cavityLeft_old_slot] at HH
  exact HH

theorem nativeCloneBlockAtSlot_cavityLeft_new_reader {as : List PositiveMass}
    (T : ClockTree (S×B) as) (target : T.Slot) (cut : ℕ)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).newRestrict
      (cast (congrArg ClockTree.Assignment (nativeCloneBlockAtSlot_cavityLeft_tree T target cut)) σ)=
        (nativeCloneBlockAtSlot T target cut).restNewRestrict σ := by
  apply T.cavityLeft.assignment_ext
  intro s
  obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
  rw [NativeRetainedSubtreeClone.restNewRestrict_at,
    (nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).new_at]
  have HH:=atSlot_cast_tree (nativeCloneBlockAtSlot_cavityLeft_tree T target cut) σ
    ((nativeCloneBlockAtSlot T target cut).tree.cavityLeftSlot
      ((nativeCloneBlockAtSlot T target cut).newEmbed s))
  rw [nativeCloneBlockAtSlot_cavityLeft_new_slot] at HH
  exact HH

variable {ι : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem nativeRetainedCloneCut_rest_disorderLaw
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree (S×B) as) {a : ℝ} (ho : MassOrdered a as)
    (target : T.Slot) (cut : ℕ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (Q : T.cavityLeft.Assignment→T.cavityLeft.Assignment→ℝ) (x : ι→ℝ) :
    zeroContinuation (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
      (nativeRetainedCloneCutMean w φ T.cavityLeft (T.cavityLeftSlot target) cut
        (cumulativeIncrements (q 0) (fun k=>q (k+1))) Q) x=
      (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.disorderExpect w φ v q
        (fun σ=>Q ((nativeCloneBlockAtSlot T target cut).restOldRestrict σ)
          ((nativeCloneBlockAtSlot T target cut).restNewRestrict σ)) x := by
  rw [nativeRetainedCloneCut_disorderLaw hw φ T.cavityLeft ho]
  have HE:=disorderExpect_cast_tree (nativeCloneBlockAtSlot_cavityLeft_tree T target cut)
    w φ v q (fun σ=>Q
      ((nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).oldRestrict σ)
      ((nativeCloneBlockAtSlot T.cavityLeft (T.cavityLeftSlot target) cut).newRestrict σ)) x
  simp_rw [nativeCloneBlockAtSlot_cavityLeft_old_reader,
    nativeCloneBlockAtSlot_cavityLeft_new_reader] at HE
  exact HE.symm

end OAI.SKFluctuations.Hierarchy.ClockTree
