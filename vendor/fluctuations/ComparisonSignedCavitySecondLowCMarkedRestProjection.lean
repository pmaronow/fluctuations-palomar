module

public import ComparisonSignedCavitySecondLowNativeCSourceFold
public import ComparisonSignedCavityForestFullFreshRestTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def nativeSecondLowRestJointRows {as : List PositiveMass} {T : ClockTree (S×B) as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement T)) (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  (ps.map (fun p=>p.coeff*p.tree.cavityLeft.expect w φ q
    (fun σ=>H (p.restRestrict σ) (p.restSpin σ)) x)).sum

omit [Nonempty S] in
private theorem c_rest_joint_rows_projected {as : List PositiveMass} {T : ClockTree (S×B) as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement T)) (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (ps.map (fun p=>p.restPlacement)) H x=
      nativeSecondLowRestJointRows w φ q ps H x := by
  unfold nativeJointAttachmentRow nativeSecondLowRestJointRows
  simp only [List.map_map,Function.comp_def]
  rfl

omit [Nonempty S] in
private theorem c_rest_joint_rows_append {as : List PositiveMass} {T : ClockTree (S×B) as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps rs : List (MarkedPlacement T)) (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (ps++rs) H x=
      nativeSecondLowRestJointRows w φ q ps H x+nativeSecondLowRestJointRows w φ q rs H x := by
  simp only [nativeSecondLowRestJointRows,List.map_append,List.sum_append]

omit [Nonempty S] in
private theorem c_joint_rows_append {as : List PositiveMass} {T : ClockTree S as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps rs : List (MarkedPlacement T)) (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (ps++rs) H x=
      nativeJointAttachmentRow w φ q ps H x+nativeJointAttachmentRow w φ q rs H x := by
  simp only [nativeJointAttachmentRow,List.map_append,List.sum_append]

omit [Nonempty S] in
private theorem c_rest_joint_rows_cons {as : List PositiveMass} {T : ClockTree (S×B) as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (p : MarkedPlacement T) (ps : List (MarkedPlacement T))
    (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (p::ps) H x=
      nativeSecondLowRestJointRows w φ q [p] H x+nativeSecondLowRestJointRows w φ q ps H x := by
  simp only [nativeSecondLowRestJointRows,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]

omit [Nonempty S] in
private theorem c_joint_rows_cons {as : List PositiveMass} {T : ClockTree S as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (p : MarkedPlacement T) (ps : List (MarkedPlacement T))
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (p::ps) H x=
      nativeJointAttachmentRow w φ q [p] H x+nativeJointAttachmentRow w φ q ps H x := by
  simp only [nativeJointAttachmentRow,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

omit [Nonempty S] in
theorem native_second_low_c_rest_fresh_row {as : List PositiveMass} (T : ClockTree (S×B) as)
    (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q [MarkedPlacement.fresh T a] H x=
      nativeJointAttachmentRow w φ q [MarkedPlacement.fresh T.cavityLeft a] H x := by
  simp only [nativeSecondLowRestJointRows,nativeJointAttachmentRow,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]
  exact congrArg (fun t:ℝ=>a*t) (native_fresh_full_rest_expect_transport T a w φ q H x)

omit [Nonempty S] in
theorem native_second_low_c_rest_step_rows {as : List PositiveMass} (T : ClockTree (S×B) as)
    (b : PositiveMass) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement T)) (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (ps.map (MarkedPlacement.step b)) H x=
      nativeJointAttachmentRow w φ q ((ps.map (fun p=>p.restPlacement)).map (MarkedPlacement.step b)) H x := by
  unfold nativeSecondLowRestJointRows nativeJointAttachmentRow
  simp only [List.map_map]
  rfl

omit [Nonempty S] in
theorem native_second_low_c_rest_left_rows {as : List PositiveMass} (T E : ClockTree (S×B) as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement T)) (H : (T.fork E).cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (ps.map (fun p=>p.left E)) H x=
      nativeJointAttachmentRow w φ q ((ps.map (fun p=>p.restPlacement)).map
        (fun p=>p.left E.cavityLeft)) H x := by
  unfold nativeSecondLowRestJointRows nativeJointAttachmentRow
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp_rw [MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left]
  rfl

omit [Nonempty S] in
theorem native_second_low_c_rest_right_rows {as : List PositiveMass} (T E : ClockTree (S×B) as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement E)) (H : (T.fork E).cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (ps.map (fun p=>p.right T)) H x=
      nativeJointAttachmentRow w φ q ((ps.map (fun p=>p.restPlacement)).map
        (fun p=>p.right T.cavityLeft)) H x := by
  unfold nativeSecondLowRestJointRows nativeJointAttachmentRow
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp_rw [MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right]
  rfl

theorem native_second_low_c_full_rest_row_projection
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree (S×B) as) (a : ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock as) (q : ℕ→ι→ℝ≥0)
    (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (T.markedAttach a) H x=
      nativeJointAttachmentRow w φ q (T.cavityLeft.markedAttach a) H x := by
  induction T generalizing a aClock q x with
  | leaf=>
    simp only [markedAttach,cavityLeft]
    rw [c_rest_joint_rows_cons,c_joint_rows_cons,native_second_low_c_rest_fresh_row]
    rfl
  | step b T ih=>
    change T.cavityLeft.Assignment→S→ℝ at H
    simp only [markedAttach,cavityLeft]
    rw [c_rest_joint_rows_cons,c_joint_rows_cons,native_second_low_c_rest_fresh_row,native_second_low_c_rest_step_rows,
      native_second_low_c_joint_rows_step hw φ T.cavityLeft b ho.2.2,
      native_second_low_c_joint_rows_step hw φ T.cavityLeft b ho.2.2]
    simp_rw [c_rest_joint_rows_projected,ih b.val ho.2.2 (fun j=>q (j+1))]
    rfl
  | fork T E ihT ihE=>
    change T.cavityLeft.Assignment×E.cavityLeft.Assignment→S→ℝ at H
    simp only [markedAttach,cavityLeft]
    rw [c_rest_joint_rows_cons,c_joint_rows_cons,c_rest_joint_rows_append,c_joint_rows_append,
      native_second_low_c_rest_fresh_row,native_second_low_c_rest_left_rows,
      native_second_low_c_rest_right_rows,native_second_low_c_joint_rows_left,
      native_second_low_c_joint_rows_left,native_second_low_c_joint_rows_right,
      native_second_low_c_joint_rows_right]
    simp_rw [c_rest_joint_rows_projected,ihT a ho q,ihE a ho q]
    rfl

theorem native_second_low_c_HIGH_rest_row_projection
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree (S×B) as) (c : T.Slot) (star : ℕ) (a : ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock as) (q : ℕ→ι→ℝ≥0)
    (H : T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowRestJointRows w φ q (nativeHighMarkedRows T c star a) H x=
      nativeJointAttachmentRow w φ q
        (nativeHighMarkedRows T.cavityLeft (T.cavityLeftSlot c) star a) H x := by
  induction T generalizing star a aClock q x with
  | leaf=>simp [nativeHighMarkedRows,nativeSecondLowRestJointRows,nativeJointAttachmentRow,cavityLeft]
  | step b T ih=>
    change T.cavityLeft.Assignment→S→ℝ at H
    cases star with
    | zero=>
      simp only [nativeHighMarkedRows,cavityLeft,cavityLeftSlot]
      rw [native_second_low_c_rest_step_rows,
        native_second_low_c_joint_rows_step hw φ T.cavityLeft b ho.2.2,
        native_second_low_c_joint_rows_step hw φ T.cavityLeft b ho.2.2]
      simp_rw [c_rest_joint_rows_projected,
        native_second_low_c_full_rest_row_projection hw φ T b.val ho.2.2]
    | succ star=>
      simp only [nativeHighMarkedRows,cavityLeft,cavityLeftSlot]
      rw [native_second_low_c_rest_step_rows,
        native_second_low_c_joint_rows_step hw φ T.cavityLeft b ho.2.2,
        native_second_low_c_joint_rows_step hw φ T.cavityLeft b ho.2.2]
      simp_rw [c_rest_joint_rows_projected,ih c star b.val ho.2.2]
  | fork T E ihT ihE=>
    change T.cavityLeft.Assignment×E.cavityLeft.Assignment→S→ℝ at H
    cases c with
    | inl c=>
      simp only [nativeHighMarkedRows,cavityLeft,cavityLeftSlot,Equiv.sumCongr_apply,Sum.map_inl]
      rw [native_second_low_c_rest_left_rows,native_second_low_c_joint_rows_left,
        native_second_low_c_joint_rows_left]
      simp_rw [c_rest_joint_rows_projected,ihT c star a ho q]
    | inr c=>
      simp only [nativeHighMarkedRows,cavityLeft,cavityLeftSlot,Equiv.sumCongr_apply,Sum.map_inr]
      rw [native_second_low_c_rest_right_rows,native_second_low_c_joint_rows_right,
        native_second_low_c_joint_rows_right]
      simp_rw [c_rest_joint_rows_projected,ihE c star a ho q]

end OAI.SKFluctuations.Cavity
