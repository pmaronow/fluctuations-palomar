module

public import ComparisonSignedCavityTransientMixedAllocation
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockForkCost

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

def nativeForkWitnessSlot : {as : List PositiveMass} → (T : ClockTree S as) → T.Slot
  | _,.leaf => ()
  | _,.step _ T => nativeForkWitnessSlot T
  | _,.fork T _ => Sum.inl (nativeForkWitnessSlot T)

theorem native_forkCost_le_pair_bound {as : List PositiveMass}
    (T : ClockTree S as) (f : ℕ → ℝ) (C : ℝ)
    (h : ∀ s t : T.Slot,s ≠ t → f (T.splitIndex s t) ≤ C) :
    T.forkCost f ≤ ((T.leaves:ℝ)-1)*C := by
  induction T generalizing f with
  | leaf => simp only [forkCost,leaves,Nat.cast_one,sub_self,zero_mul,le_refl]
  | step b T ih =>
    exact ih (fun j => f (1+j)) (fun s t hst => h s t hst)
  | fork T V ihT ihV =>
    have h0 : f 0 ≤ C := h (Sum.inl (nativeForkWitnessSlot T))
      (Sum.inr (nativeForkWitnessSlot V)) (by intro H; cases H)
    have hT := ihT f (fun s t hst => h (Sum.inl s) (Sum.inl t)
      (fun H => hst (Sum.inl.inj H)))
    have hV := ihV f (fun s t hst => h (Sum.inr s) (Sum.inr t)
      (fun H => hst (Sum.inr.inj H)))
    simp only [forkCost,leaves,Nat.cast_add]
    nlinarith

theorem NativePersistentLowForks.low_forkCost_le {as : List PositiveMass}
    {i star U : ℕ} {T : ClockTree S as} (hT : NativePersistentLowForks i star U T)
    (f : ℕ → ℝ) (hf : ∀ j,0 ≤ f j) (hhigh : ∀ j,U ≤ j → f j=0) :
    T.forkCost f ≤ ((T.leaves:ℝ)-1)*(f i+f star) := by
  apply native_forkCost_le_pair_bound
  intro s t _
  rcases hT s t with H | H | H
  · rw [H]
    exact le_add_of_nonneg_right (hf star)
  · rw [H]
    exact le_add_of_nonneg_left (hf i)
  · rw [hhigh _ H]
    exact add_nonneg (hf i) (hf star)

theorem nativeFreshAtSlot_forkCost {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s : T.Slot) (j : ℕ) (f : ℕ → ℝ) :
    (nativeFreshAtSlot T a s j).tree.forkCost f =
      T.forkCost f+f (min j as.length) := by
  induction T generalizing a j f with
  | leaf =>
    simp only [nativeFreshAtSlot,MarkedPlacement.fresh,forkCost,single,List.length_nil,
      Nat.min_zero]
    ring
  | @step b tail T ih =>
    cases j with
    | zero =>
      simp only [nativeFreshAtSlot,MarkedPlacement.fresh,forkCost,single_forkCost,
        Nat.zero_min,add_zero]
      ring
    | succ j =>
      simp only [nativeFreshAtSlot,MarkedPlacement.step,forkCost,List.length_cons]
      rw [ih]
      congr 1
      congr 1
      omega
  | @fork tail T V ihT ihV =>
    cases j with
    | zero =>
      simp only [nativeFreshAtSlot,MarkedPlacement.fresh,forkCost,single_forkCost,
        Nat.zero_min,add_zero]
      ring
    | succ j =>
      cases s with
      | inl s =>
        simp only [nativeFreshAtSlot,MarkedPlacement.left,forkCost]
        rw [ihT]
        ring
      | inr s =>
        simp only [nativeFreshAtSlot,MarkedPlacement.right,forkCost]
        rw [ihV]
        ring

theorem nativeFreshAtSlot_high_forkCost {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s : T.Slot) {star U : ℕ} (hs : star<U)
    (f : ℕ → ℝ) (hlo : ∀ j,j<U → f j=0) :
    (nativeFreshAtSlot T a s star).tree.forkCost f=T.forkCost f := by
  rw [nativeFreshAtSlot_forkCost,hlo _ ((Nat.min_le_left _ _).trans_lt hs),add_zero]

theorem native_initial_seed_high_forkCost (as : List PositiveMass)
    (a : ℝ) {i U : ℕ} (hi : i<U) (f : ℕ → ℝ)
    (hlo : ∀ j,j<U → f j=0) :
    (nativeFreshAtSlot (single (S := S) as) a (singleSlot as) i).tree.forkCost f=0 := by
  rw [nativeFreshAtSlot_high_forkCost _ _ _ hi f hlo,single_forkCost]

theorem native_transient_forkLedger_le {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (f : ℕ → ℝ)
    (hf : ∀ j,0 ≤ f j) (k : ℕ) :
    forkLedger 0 f k T ≤ forkVariation T.leaves k*(T.forkCost f+edgeBudget 0 as f) :=
  T.forkLedger_le ho hf (le_refl _) k

theorem native_transient_forkLedger_le_edgeBudget {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (f : ℕ → ℝ)
    (hf : ∀ j,0 ≤ f j) (hT : T.forkCost f=0) (k : ℕ) :
    forkLedger 0 f k T ≤ forkVariation T.leaves k*edgeBudget 0 as f := by
  simpa only [hT,zero_add] using native_transient_forkLedger_le T ho f hf k

end OAI.SKFluctuations.Hierarchy.ClockTree
