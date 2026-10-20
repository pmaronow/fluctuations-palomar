module

public import ComparisonSignedCavityGeneratedResources

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

theorem native_single_slot_eq (as : List PositiveMass)
    (s : (single (S := S) as).Slot) : s = singleSlot as := by
  induction as with
  | nil =>
    change s = ()
    cases s
    rfl
  | cons b as ih => exact ih s

theorem nativeFreshAtSlot_slot_coverage (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (j : ℕ)
    (c : (nativeFreshAtSlot T a s j).tree.Slot) :
    c = (nativeFreshAtSlot T a s j).mark ∨
      ∃ d : T.Slot, c = (nativeFreshAtSlot T a s j).embed d := by
  induction T generalizing a j with
  | leaf =>
    cases c with
    | inl d => exact Or.inr ⟨d,rfl⟩
    | inr d => exact Or.inl (congrArg Sum.inr (native_single_slot_eq [] d))
  | @step b tail T ih =>
    cases j with
    | zero =>
      cases c with
      | inl d => exact Or.inr ⟨d,rfl⟩
      | inr d => exact Or.inl (congrArg Sum.inr (native_single_slot_eq (b::tail) d))
    | succ j => exact ih b.val s j c
  | @fork tail T V ihT ihV =>
    cases j with
    | zero =>
      cases c with
      | inl d => exact Or.inr ⟨d,rfl⟩
      | inr d => exact Or.inl (congrArg Sum.inr (native_single_slot_eq tail d))
    | succ j =>
      cases s with
      | inl s =>
        cases c with
        | inl c =>
          rcases ihT a s (j+1) c with h | ⟨d,h⟩
          · exact Or.inl (congrArg Sum.inl h)
          · exact Or.inr ⟨Sum.inl d,congrArg Sum.inl h⟩
        | inr c => exact Or.inr ⟨Sum.inr c,rfl⟩
      | inr s =>
        cases c with
        | inl c => exact Or.inr ⟨Sum.inl c,rfl⟩
        | inr c =>
          rcases ihV a s (j+1) c with h | ⟨d,h⟩
          · exact Or.inl (congrArg Sum.inr h)
          · exact Or.inr ⟨Sum.inr d,congrArg Sum.inr h⟩

def NativePersistentLowForks (i star U : ℕ) (T : ClockTree S as) : Prop :=
  ∀ c d : T.Slot,
    T.splitIndex c d = i ∨ T.splitIndex c d = star ∨ U ≤ T.splitIndex c d

theorem nativePersistentLowCut_min {i star U j k : ℕ}
    (hj : j = i ∨ j = star ∨ U ≤ j)
    (hk : k = i ∨ k = star ∨ U ≤ k) :
    min j k = i ∨ min j k = star ∨ U ≤ min j k := by
  rcases le_total j k with h | h
  · simpa only [Nat.min_eq_left h] using hj
  · simpa only [Nat.min_eq_right h] using hk

theorem NativePersistentLowForks.graft {i star U : ℕ} {T : ClockTree S as}
    (hT : NativePersistentLowForks i star U T)
    (a : ℝ) (s : T.Slot) (j : ℕ)
    (hj : j = i ∨ j = star ∨ U ≤ j) :
    NativePersistentLowForks i star U (nativeFreshAtSlot T a s j).tree := by
  intro c d
  rcases nativeFreshAtSlot_slot_coverage T a s j c with rfl | ⟨c,rfl⟩
  · rcases nativeFreshAtSlot_slot_coverage T a s j d with rfl | ⟨d,rfl⟩
    · have h := hT s s
      simpa only [splitIndex_self] using h
    · rw [nativeFreshAtSlot_split]
      exact nativePersistentLowCut_min hj (hT s d)
  · rcases nativeFreshAtSlot_slot_coverage T a s j d with rfl | ⟨d,rfl⟩
    · rw [splitIndex_symm,nativeFreshAtSlot_split]
      exact nativePersistentLowCut_min hj (hT s c)
    · rw [(nativeFreshAtSlot_old_splits T a s j).2]
      exact hT c d

theorem NativePersistentLowForks.freshStar {i star U : ℕ} {T : ClockTree S as}
    (hT : NativePersistentLowForks i star U T) (a : ℝ) (s : T.Slot) :
    NativePersistentLowForks i star U (nativeFreshAtSlot T a s star).tree :=
  hT.graft a s star (Or.inr (Or.inl rfl))

theorem NativePersistentLowForks.highRelative {i star U j : ℕ}
    {T : ClockTree S as} (hT : NativePersistentLowForks i star U T)
    (a : ℝ) (s : T.Slot) (hj : U ≤ j) :
    NativePersistentLowForks i star U (nativeFreshAtSlot T a s j).tree :=
  hT.graft a s j (Or.inr (Or.inr hj))

theorem nativeFreshAtSlot_unique_fresh_block (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) {star U : ℕ} (hstar : star < U)
    (c : (nativeFreshAtSlot T a s star).tree.Slot)
    (hc : U ≤ (nativeFreshAtSlot T a s star).tree.splitIndex
      (nativeFreshAtSlot T a s star).mark c) :
    c = (nativeFreshAtSlot T a s star).mark := by
  rcases nativeFreshAtSlot_slot_coverage T a s star c with h | ⟨d,rfl⟩
  · exact h
  · have h := nativeFreshAtSlot_outside_old_blocks T a s hstar d
    omega

theorem NativePersistentLowForks.low_split {i star U : ℕ}
    {T : ClockTree S as} (hT : NativePersistentLowForks i star U T)
    (c d : T.Slot) (hcd : T.splitIndex c d < U) :
    T.splitIndex c d = i ∨ T.splitIndex c d = star := by
  rcases hT c d with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · omega

theorem native_single_persistentLowForks (i star U : ℕ) (hU : U ≤ as.length) :
    NativePersistentLowForks i star U (single (S := S) as) := by
  intro c d
  have hc := native_single_slot_eq as c
  have hd := native_single_slot_eq as d
  subst c
  subst d
  exact Or.inr (Or.inr (by simpa only [splitIndex_self] using hU))

theorem native_initial_seed_persistentLowForks (i star U : ℕ)
    (hU : U ≤ as.length) (a : ℝ) :
    NativePersistentLowForks i star U
      (nativeFreshAtSlot (single (S := S) as) a (singleSlot as) i).tree :=
  (native_single_persistentLowForks i star U hU).graft a (singleSlot as) i (Or.inl rfl)

theorem NativePersistentLowForks.no_intermediate {i star U : ℕ}
    {T : ClockTree S as} (hT : NativePersistentLowForks i star U T)
    (hi : i ≤ star) (c d : T.Slot) :
    ¬ (star < T.splitIndex c d ∧ T.splitIndex c d < U) := by
  intro h
  rcases hT c d with hsplit | hsplit | hsplit
  · omega
  · omega
  · omega

end OAI.SKFluctuations.Hierarchy.ClockTree
