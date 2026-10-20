module

public import ComparisonSignedCavitySecondLowTwoLevelConditionalIntegral

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

private theorem complete_clock_expect_smooth {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) :
    BddSmooth 0 (T.expect w φ q P) := by
  have H:T.expect w φ q P=(T.realize q).expect w φ
      (fun σ=>P ((T.assignmentEquiv q).symm σ)):=funext (T.expect_realize w φ q P)
  rw [H]
  exact (T.realize q).expect_smooth hw φ (clockSteps_ordered ho q) _ 0

private theorem complete_list_smooth {J : Type} (ps : List J) (c : J→ℝ)
    (F : J→(ι→ℝ)→ℝ) (hF : ∀p∈ps,BddSmooth 0 (F p)) :
    BddSmooth 0 (fun x=>(ps.map (fun p=>c p*F p x)).sum) := by
  induction ps with
  | nil=>exact BddSmooth.const 0 0
  | cons p ps ih=>
    exact ((hF p List.mem_cons_self).const_mul (c p)).add
      (ih (fun r hr=>hF r (List.mem_cons_of_mem p hr)))

theorem nativeJointAttachmentRow_smooth0 {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement T)) (H : T.Assignment→S→ℝ) :
    BddSmooth 0 (nativeJointAttachmentRow w φ q ps H) := by
  unfold nativeJointAttachmentRow
  exact complete_list_smooth ps (fun p=>p.coeff) _
    (fun p _=>complete_clock_expect_smooth p.tree hw φ ho q _)

theorem nativeSecondLowCReplacementValue_smooth0 {as : List PositiveMass}
    (T : ClockTree S as) (c : T.Slot) (U : ℕ) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (rf rz : NativeSecondLowCReader T) (Q : S→S→S→ℝ) :
    BddSmooth 0 (nativeSecondLowCReplacementValue T c U a w φ q P rf rz Q) := by
  unfold nativeSecondLowCReplacementValue
  exact (nativeJointAttachmentRow_smooth0 T hw φ ho q _ _).sub
    ((complete_clock_expect_smooth T hw φ ho q _).const_mul _)

theorem nativeSecondLowCCouplingFold_fixed_smooth0 {as : List PositiveMass}
    (T : ClockTree S as) (c : T.Slot) (U : ℕ) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (hU : U ≤ as.length) (hroot : U=0 → 0 < a) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (f z : S) (Q : S→S→S→ℝ) :
    BddSmooth 0 (nativeSecondLowCCouplingFold w φ T c U a q P (.fixed f) (.fixed z) Q) := by
  have H:nativeSecondLowCCouplingFold w φ T c U a q P (.fixed f) (.fixed z) Q=
      nativeSecondLowCReplacementValue T c U a w φ q P (.fixed f) (.fixed z) Q:=
    funext fun x=>native_second_low_c_coupling_fold_eq_original hw φ T c U ho hU hroot q P
      (.fixed f) (.fixed z) (by trivial) (by trivial) Q x
  rw [H]
  exact nativeSecondLowCReplacementValue_smooth0 T c U hw φ ho q P _ _ Q

theorem nativeExteriorCompleteCFold_smooth_joint {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (c : D.Slot) (U : ℕ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {ai a : ℝ} (hoi : MassOrdered ai ias) (ho : MassOrdered a sas)
    (hU : U ≤ sas.length) (hroot : U=0 → 0 < a) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ) :
    BddSmooth 0 (nativeExteriorCompleteCFold Ei Es D w φ c U a qi qs P f z Q) := by
  unfold nativeExteriorCompleteCFold ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  apply ((Ei.weight_smooth hw φ hoi qi η 0).compCLM
    (ContinuousLinearMap.fst ℝ (ι→ℝ) (ι→ℝ))).mul
  apply BddSmooth.sum Finset.univ
  intro ζ _
  exact ((Es.weight_smooth hw φ ho qs ζ 0).compCLM
    (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ))).mul
      ((nativeSecondLowCCouplingFold_fixed_smooth0 D c U hw φ ho hU hroot qs (P η ζ) (f η ζ) (z η ζ) Q).compCLM
        (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ)))

theorem nativeExteriorCompleteCFold_smooth_star {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (c : D.Slot) (U : ℕ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a sas) (hU : U ≤ sas.length) (hroot : U=0 → 0 < a)
    (qi qs : ℕ→ι→ℝ≥0) (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ) (xi : ι→ℝ) :
    BddSmooth 0 (fun xs=>nativeExteriorCompleteCFold Ei Es D w φ c U a qi qs P f z Q (xi,xs)) := by
  unfold nativeExteriorCompleteCFold ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  change BddSmooth 0 (fun xs=>Ei.weight w φ qi η xi*
    ∑ζ:Es.Assignment,Es.weight w φ qs ζ xs*
      nativeSecondLowCCouplingFold w φ D c U a qs (P η ζ) (.fixed (f η ζ)) (.fixed (z η ζ)) Q xs)
  refine (show BddSmooth 0 (fun xs=>∑ζ:Es.Assignment,Es.weight w φ qs ζ xs*
    nativeSecondLowCCouplingFold w φ D c U a qs (P η ζ) (.fixed (f η ζ)) (.fixed (z η ζ)) Q xs) from ?_).const_mul _
  apply BddSmooth.sum Finset.univ
  intro ζ _
  exact (Es.weight_smooth hw φ ho qs ζ 0).mul
    (nativeSecondLowCCouplingFold_fixed_smooth0 D c U hw φ ho hU hroot qs (P η ζ) (f η ζ) (z η ζ) Q)

end OAI.SKFluctuations.Cavity
