module

public import ComparisonSignedCavityGWordSupport

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem native_fresh_leaves_eq (T : ClockTree S as) (a : ℝ) (s : T.Slot) (star : ℕ) :
    (nativeFreshAtSlot T a s star).tree.leaves=T.leaves+1 := by
  induction T generalizing a star with
  | leaf=>simp [nativeFreshAtSlot,MarkedPlacement.fresh,leaves,single_leaves_exact]
  | step b T ih=>
    cases star with
    | zero=>simp [nativeFreshAtSlot,MarkedPlacement.fresh,leaves,single_leaves_exact]
    | succ star=>simpa only [nativeFreshAtSlot,MarkedPlacement.step,leaves] using ih b.val s star
  | fork T V ihT ihV=>
    cases star with
    | zero=>simp [nativeFreshAtSlot,MarkedPlacement.fresh,leaves,single_leaves_exact]
    | succ star=>
      cases s with
      | inl s=>simp only [nativeFreshAtSlot,MarkedPlacement.left,leaves,ihT];omega
      | inr s=>simp only [nativeFreshAtSlot,MarkedPlacement.right,leaves,ihV];omega

theorem NativeProjectionSpine.leaves_eq {B T : ClockTree S as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (spine : NativeProjectionSpine base star P) : T.leaves=B.leaves+spine.toothCount := by
  induction spine with
  | base=>simp only [toothCount,Nat.add_zero]
  | projection h a hl ih=>
    rw [native_fresh_leaves_eq,ih]
    simp only [toothCount,Nat.add_assoc]

end OAI.SKFluctuations.Hierarchy.ClockTree
