module

public import ComparisonSignedCavitySecondLowClassifiedWholeCRowJoin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Set Filter MeasureTheory ProbabilityTheory Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_group_root_forest_high_joint_rows
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (d : (nativeGroupRootForest T s).occupied.Slot) (U : ℕ) (a : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock as) (q : ℕ→ι→ℝ≥0)
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows T ((nativeGroupRootForest T s).occupiedEmbed d) (U-1) a) H x=
      (nativeGroupRootForest T s).exterior.expect w φ q (fun η=>
        nativeJointAttachmentRow w φ q
          (nativeHighMarkedRows (nativeGroupRootForest T s).occupied d (U-1) a)
          (fun δ new=>H ((nativeGroupRootForest T s).read η δ) new) x) x := by
  induction T generalizing aClock with
  | leaf=>
    change _=(single []).expect w φ q (fun _=>nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows .leaf d (U-1) a) H x) x
    exact (expect_const hw φ (single []) ho q _ x).symm
  | @step b tail T ih=>
    change _=(single (b::tail)).expect w φ q (fun _=>nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows (T.step b) d (U-1) a) H x) x
    exact (expect_const hw φ (single (b::tail)) ho q _ x).symm
  | @fork tail T V ihT ihV=>
    cases s with
    | inl s=>
      change nativeJointAttachmentRow w φ q
        ((nativeHighMarkedRows T ((nativeGroupRootForest T s).occupiedEmbed d) (U-1) a).map
          (fun p=>p.left V)) H x=
        (V.fork (nativeGroupRootForest T s).exterior).expect w φ q (fun η=>
          nativeJointAttachmentRow w φ q (nativeHighMarkedRows (nativeGroupRootForest T s).occupied d (U-1) a)
            (fun δ new=>H ((nativeGroupRootForest T s).read η.2 δ,η.1) new) x) x
      rw [native_second_low_c_joint_rows_left,expect_fork]
      apply congrArg (fun F=>V.expect w φ q F x)
      funext η
      exact ihT s d ho _
    | inr s=>
      change nativeJointAttachmentRow w φ q
        ((nativeHighMarkedRows V ((nativeGroupRootForest V s).occupiedEmbed d) (U-1) a).map
          (fun p=>p.right T)) H x=
        (T.fork (nativeGroupRootForest V s).exterior).expect w φ q (fun η=>
          nativeJointAttachmentRow w φ q (nativeHighMarkedRows (nativeGroupRootForest V s).occupied d (U-1) a)
            (fun δ new=>H (η.1,(nativeGroupRootForest V s).read η.2 δ) new) x) x
      rw [native_second_low_c_joint_rows_right,expect_fork]
      apply congrArg (fun F=>T.expect w φ q F x)
      funext η
      exact ihV s d ho _

theorem native_high_joint_rows_prepend_prefix_law
    (pre : List PositiveMass) {tail : List PositiveMass} (A : ClockTree S tail) (s : A.Slot)
    (U : ℕ) (hU : 0 < U) (a : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock (pre++tail)) (q : ℕ→ι→ℝ≥0)
    (H : (exteriorPrepend pre A).Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows (exteriorPrepend pre A) ((exteriorPrependSlotEquiv pre A).symm s)
        (pre.length+U-1) a) H x=
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
        (fun y=>nativeJointAttachmentRow w φ (fun j=>q (pre.length+j))
          (nativeHighMarkedRows A s (U-1) (partitionPoint a pre pre.length))
          (fun δ new=>H ((exteriorPrependAssignmentEquiv pre A).symm δ) new) y) x := by
  induction pre generalizing aClock a q x with
  | nil=>
    simp only [exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,
      List.length_nil,Nat.zero_add,Equiv.refl_symm,Equiv.refl_apply,clockSteps,prefixTest,
      partitionPoint,partitionValues_zero,id_eq]
  | cons b pre ih=>
    change (exteriorPrepend pre A).Assignment→S→ℝ at H
    have hcut : (b::pre).length+U-1=(pre.length+U-1)+1:=by simp only [List.length_cons];omega
    rw [hcut]
    change nativeJointAttachmentRow w φ q
      ((nativeHighMarkedRows (exteriorPrepend pre A) ((exteriorPrependSlotEquiv pre A).symm s)
        (pre.length+U-1) b.val).map (MarkedPlacement.step b)) H x=_
    rw [native_second_low_c_joint_rows_step hw φ (exteriorPrepend pre A) b ho.2.2]
    have HI:=funext fun y=>ih b.val ho.2.2 (fun j=>q (j+1)) H y
    change shiftedMean _ _ _ (fun y=>nativeJointAttachmentRow w φ (fun j=>q (j+1))
      (nativeHighMarkedRows (exteriorPrepend pre A) ((exteriorPrependSlotEquiv pre A).symm s)
        (pre.length+U-1) b.val) H y) x=_
    conv_lhs=>rw [HI]
    simp only [clockSteps,prefixTest,List.length_cons]
    rw [prefixContinuation_hierarchy]
    have Hq:(fun j=>q (pre.length+j+1))=(fun j=>q (pre.length+1+j)):=by
      funext j;congr 1;omega
    rw [Hq,clockSteps_append,Hq]
    rfl

theorem exteriorPrepend_high_joint_rows_map_congr
    (pre : List PositiveMass) {tail : List PositiveMass} (A B : ClockTree S tail)
    (s : A.Slot) (t : B.Slot) (R : B.Assignment→A.Assignment) (U : ℕ) (hU : 0 < U)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock (pre++tail))
    (hLaw : ∀(a : ℝ) (q : ℕ→ι→ℝ≥0) (H : A.Assignment→S→ℝ) (x : ι→ℝ),
      nativeJointAttachmentRow w φ q (nativeHighMarkedRows A s (U-1) a) H x=
        nativeJointAttachmentRow w φ q (nativeHighMarkedRows B t (U-1) a) (fun δ new=>H (R δ) new) x)
    (a : ℝ) (q : ℕ→ι→ℝ≥0)
    (H : (exteriorPrepend pre A).Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows (exteriorPrepend pre A) ((exteriorPrependSlotEquiv pre A).symm s)
        (pre.length+U-1) a) H x=
      nativeJointAttachmentRow w φ q
        (nativeHighMarkedRows (exteriorPrepend pre B) ((exteriorPrependSlotEquiv pre B).symm t)
          (pre.length+U-1) a) (fun δ new=>H (exteriorPrependRead pre A B R δ) new) x := by
  rw [native_high_joint_rows_prepend_prefix_law pre A s U hU a hw φ ho,
    native_high_joint_rows_prepend_prefix_law pre B t U hU a hw φ ho]
  apply congrArg (fun F=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j)))) F x)
  funext y
  simpa only [exteriorPrependRead,Equiv.apply_symm_apply] using hLaw (partitionPoint a pre pre.length)
    (fun j=>q (pre.length+j)) (fun δ new=>H ((exteriorPrependAssignmentEquiv pre A).symm δ) new) y

end OAI.SKFluctuations.Hierarchy.ClockTree
