module

public import ComparisonSignedCavityActualTargetSingleton
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockForkCost

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open scoped BigOperators
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

def nativeTargetOffDiagonalProfile (T : ClockTree S as) (s : T.Slot)
    (f : ℕ → ℝ) (p : MarkedPlacement T) : ℝ :=
  if p.embed s=p.mark then 0 else f (p.tree.splitIndex (p.embed s) p.mark)

theorem native_target_profile_variation_eq_edgeBudget
    (T : ClockTree S as) (s : T.Slot) {a : ℝ} (ho : MassOrdered a as)
    (f : ℕ → ℝ) (hzero : ∀c : T.Slot,c≠s → f (T.splitIndex s c)=0) :
    ((T.markedAttach a).map (fun p=>|p.coeff| *
      nativeTargetOffDiagonalProfile T s f p)).sum=edgeBudget a as f := by
  induction T generalizing a f with
  | leaf=>
    cases s
    simp [markedAttach,nativeTargetOffDiagonalProfile,MarkedPlacement.coincide,
      MarkedPlacement.fresh,splitIndex,edgeBudget,abs_of_nonpos (sub_nonpos.mpr ho.2)]
  | step b T ih=>
    have hz : ∀c:T.Slot,c≠s → (fun j=>f (1+j)) (T.splitIndex s c)=0 := hzero
    have H:=ih s ho.2.2 (fun j=>f (1+j)) hz
    simpa only [markedAttach,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.step,
      nativeTargetOffDiagonalProfile,Sum.inl_ne_inr,ite_false,splitIndex,Sum.elim_inl,Sum.elim_inr,
      edgeBudget,abs_of_nonpos (sub_nonpos.mpr ho.2.1),neg_sub] using
      congrArg (fun z=>(b.val-a)*f 0+z) H
  | fork T V ihT ihV=>
    cases s with
    | inl s=>
      have hf0 : f 0=0:=hzero (Sum.inr (nativeFirstSlot V)) (by intro H;cases H)
      have hz : ∀c:T.Slot,c≠s → f (T.splitIndex s c)=0 := by
        intro c hc
        exact hzero (Sum.inl c) (fun H=>hc (Sum.inl.inj H))
      have H:=ihT s ho f hz
      simpa [markedAttach,List.map_map,Function.comp_def,MarkedPlacement.fresh,
        MarkedPlacement.left,MarkedPlacement.right,nativeTargetOffDiagonalProfile,
        splitIndex,hf0] using H
    | inr s=>
      have hf0 : f 0=0:=hzero (Sum.inl (nativeFirstSlot T)) (by intro H;cases H)
      have hz : ∀c:V.Slot,c≠s → f (V.splitIndex s c)=0 := by
        intro c hc
        exact hzero (Sum.inr c) (fun H=>hc (Sum.inr.inj H))
      have H:=ihV s ho f hz
      simpa [markedAttach,List.map_map,Function.comp_def,MarkedPlacement.fresh,
        MarkedPlacement.left,MarkedPlacement.right,nativeTargetOffDiagonalProfile,
        splitIndex,hf0] using H

theorem NativeTargetStarSingleton.profile_variation_eq_edgeBudget
    {T : ClockTree S as} {s : T.Slot} {star : ℕ}
    (h : NativeTargetStarSingleton T s star) {a : ℝ} (ho : MassOrdered a as)
    (f : ℕ → ℝ) (hlo : ∀j,j ≤ star → f j=0) :
    ((T.markedAttach a).map (fun p=>|p.coeff| *
      nativeTargetOffDiagonalProfile T s f p)).sum=edgeBudget a as f := by
  apply native_target_profile_variation_eq_edgeBudget T s ho f
  intro c hc
  apply hlo
  exact le_of_not_gt (fun H=>hc (h c H))

theorem native_actual_generated_target_profile_variation
    {i star U : ℕ} {T : ClockTree S as} {seed : List NativeResourceMark}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    {a : ℝ} (ho : MassOrdered a as) (f : ℕ → ℝ)
    (hlo : ∀j,j ≤ star → f j=0) :
    ((T.markedAttach a).map (fun p=>|p.coeff| *
      nativeTargetOffDiagonalProfile T P.live.test.target f p)).sum=
      edgeBudget a as f :=
  (hP.targetStarSingleton hi).profile_variation_eq_edgeBudget ho f hlo

theorem native_target_weighted_profile_le
    (T : ClockTree S as) (s : T.Slot) {a C : ℝ} (ho : MassOrdered a as)
    (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j)
    (hzero : ∀c : T.Slot,c≠s → f (T.splitIndex s c)=0)
    (Γ : MarkedPlacement T → ℝ)
    (hΓ : ∀p∈T.markedAttach a,p.embed s≠p.mark →
      f (p.tree.splitIndex (p.embed s) p.mark)≠0 → |Γ p| ≤ C) :
    ((T.markedAttach a).map (fun p=>|p.coeff| * |Γ p| *
      nativeTargetOffDiagonalProfile T s f p)).sum ≤ C*edgeBudget a as f := by
  calc
    _ ≤ ((T.markedAttach a).map (fun p=>C*(|p.coeff| *
        nativeTargetOffDiagonalProfile T s f p))).sum := by
      apply List.sum_le_sum
      intro p hp
      unfold nativeTargetOffDiagonalProfile
      split_ifs with hdiag
      · simp only [mul_zero,le_refl]
      · by_cases hz : f (p.tree.splitIndex (p.embed s) p.mark)=0
        · simp only [hz,mul_zero,le_refl]
        · have H:=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hΓ p hp hdiag hz) (hf (p.tree.splitIndex (p.embed s) p.mark))) (abs_nonneg p.coeff)
          nlinarith only [H]
    _=C*edgeBudget a as f := by
      rw [List.sum_map_mul_left,native_target_profile_variation_eq_edgeBudget T s ho f hzero]

end OAI.SKFluctuations.Hierarchy.ClockTree
