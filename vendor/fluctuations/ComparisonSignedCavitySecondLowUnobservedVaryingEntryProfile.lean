module

public import ComparisonSignedCavitySecondLowUnobservedEntry
public import ComparisonSignedCavityTargetRowInterval

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

private theorem nonnegative_filtered_sum_le {α : Type*} (L : List α)
    (P : α → Prop) (F : α → ℝ) (hF : ∀x∈L,0 ≤ F x) :
    ((L.filter (fun x=>decide (P x))).map F).sum ≤ (L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>
    have H:=ih (fun y hy=>hF y (List.mem_cons_of_mem x hy))
    by_cases HP : P x
    · simpa only [List.filter_cons,HP,decide_true,ite_true,List.map_cons,List.sum_cons]
        using add_le_add (le_refl (F x)) H
    · simp only [List.filter_cons,HP,decide_false,Bool.false_eq_true,ite_false,
        List.map_cons,List.sum_cons]
      exact H.trans (le_add_of_nonneg_left (hF x List.mem_cons_self))

theorem native_second_low_unobserved_entry_ne_target
    (T : ClockTree S as) (s : T.Slot) (U : ℕ) (hU : U ≤ as.length) (a : ℝ)
    (p : MarkedPlacement T) (hp : p∈nativeSecondLowUnobservedEntryRows T U a) :
    p.embed s≠p.mark := by
  have H:=(mem_nativeSecondLowUnobservedEntryRows T U a p).mp hp
  intro HE
  apply H.2
  refine ⟨s,?_⟩
  rw [HE,p.tree.splitIndex_self]
  exact hU

theorem native_second_low_unobserved_entry_split_profile_le_edgeBudget
    (T : ClockTree S as) (s : T.Slot) (U : ℕ) (hU : U ≤ as.length)
    {a : ℝ} (ho : MassOrdered a as) (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j)
    (hzero : ∀c : T.Slot,c≠s → f (T.splitIndex s c)=0) :
    ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
      f (p.tree.splitIndex (p.embed s) p.mark))).sum ≤ edgeBudget a as f := by
  have Hprofile:
      ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
        f (p.tree.splitIndex (p.embed s) p.mark))).sum=
      ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
        nativeTargetOffDiagonalProfile T s f p)).sum := by
    congr 1
    apply List.map_congr_left
    intro p hp
    simp only [nativeTargetOffDiagonalProfile,
      native_second_low_unobserved_entry_ne_target T s U hU a p hp,ite_false]
  rw [Hprofile,nativeSecondLowUnobservedEntryRows_eq_filter]
  calc
    _ ≤ ((T.markedAttach a).map (fun p=>|p.coeff| *nativeTargetOffDiagonalProfile T s f p)).sum:=by
      apply nonnegative_filtered_sum_le
      intro p _hp
      apply mul_nonneg (abs_nonneg _)
      unfold nativeTargetOffDiagonalProfile
      split_ifs <;> first | exact le_rfl | exact hf _
    _=edgeBudget a as f:=native_target_profile_variation_eq_edgeBudget T s ho f hzero

theorem NativeTargetStarSingleton.unobserved_entry_split_profile_le_edgeBudget
    {T : ClockTree S as} {s : T.Slot} {star : ℕ}
    (H : NativeTargetStarSingleton T s star) (U : ℕ) (hU : U ≤ as.length)
    {a : ℝ} (ho : MassOrdered a as) (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j)
    (hlo : ∀j,j ≤ star → f j=0) :
    ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
      f (p.tree.splitIndex (p.embed s) p.mark))).sum ≤ edgeBudget a as f := by
  apply native_second_low_unobserved_entry_split_profile_le_edgeBudget T s U hU ho f hf
  intro c hc
  apply hlo
  exact le_of_not_gt (fun h=>hc (H c h))

theorem native_actual_second_low_unobserved_entry_split_profile
    {i star U : ℕ} {T : ClockTree S as} {seed : List NativeResourceMark}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hU : U ≤ as.length) {a : ℝ} (ho : MassOrdered a as)
    (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j ≤ star → f j=0) :
    ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
      f (p.tree.splitIndex (p.embed P.live.test.target) p.mark))).sum ≤ edgeBudget a as f :=
  (hP.targetStarSingleton hi).unobserved_entry_split_profile_le_edgeBudget U hU ho f hf hlo

theorem NativePersistentLowForks.unobserved_moving_entry_split_profile_le_edgeBudget
    {T : ClockTree S as} {i star U : ℕ} (H : NativePersistentLowForks i star U T)
    (s : T.Slot) (hU : U ≤ as.length) {a : ℝ} (ho : MassOrdered a as)
    (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j) (hfi : f i=0) (hfstar : f star=0)
    (hfhigh : ∀j,U ≤ j → f j=0) :
    ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
      f (p.tree.splitIndex (p.embed s) p.mark))).sum ≤ edgeBudget a as f := by
  apply native_second_low_unobserved_entry_split_profile_le_edgeBudget T s U hU ho f hf
  intro c _hc
  rcases H s c with HE | HE | HE
  · rw [HE];exact hfi
  · rw [HE];exact hfstar
  · exact hfhigh _ HE

theorem native_actual_second_low_unobserved_moving_entry_split_profile
    {i star U : ℕ} {T : ClockTree S as} {seed : List NativeResourceMark}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) (s : T.Slot)
    {a : ℝ} (ho : MassOrdered a as) (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j)
    (hfi : f i=0) (hfstar : f star=0) (hfhigh : ∀j,U ≤ j → f j=0) :
    ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff| *
      f (p.tree.splitIndex (p.embed s) p.mark))).sum ≤ edgeBudget a as f :=
  (hP.persistentLowForks hi).unobserved_moving_entry_split_profile_le_edgeBudget s
    hP.highCut_le_length ho f hf hfi hfstar hfhigh

end OAI.SKFluctuations.Hierarchy.ClockTree
