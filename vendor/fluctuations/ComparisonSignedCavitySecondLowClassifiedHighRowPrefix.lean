module

public import ComparisonSignedCavitySecondLowClassifiedWholeHighRowSource
public import ComparisonSignedCavityTwinPrefixNativeLaw
public import ComparisonSignedCavitySampledMeanUniform

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_classified_partitionPoint_append_shift (a : ℝ) (pre tail : List PositiveMass) (j : ℕ) :
    partitionPoint a (pre++tail) (pre.length+j)=partitionPoint (partitionEnd a pre) tail j := by
  induction pre generalizing a with
  | nil=>simp only [List.nil_append,List.length_nil,Nat.zero_add,partitionEnd]
  | cons b pre ih=>
    simpa only [List.cons_append,List.length_cons,Nat.succ_add,partitionPoint,partitionValues,
      partitionEnd] using ih b.val

theorem native_classified_star_mass_eq_nested_prefix
    (a : ℝ) (pre mid tail : List PositiveMass) :
    partitionPoint a (pre++(mid++tail)) (pre.length+mid.length)=
      partitionPoint (partitionPoint a pre pre.length) mid mid.length := by
  rw [native_classified_partitionPoint_append_shift,
    partitionPoint_eq_end_take,partitionPoint_eq_end_take,partitionPoint_eq_end_take]
  simp only [List.take_length,List.take_left]

theorem native_joint_attachment_row_smooth
    {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (ps : List (MarkedPlacement T)) (H : T.Assignment→S→ℝ) (r : ℕ) :
    BddSmooth r (fun x=>nativeJointAttachmentRow w φ q ps H x) := by
  unfold nativeJointAttachmentRow
  induction ps with
  | nil=>
    change BddSmooth r (fun _ : ι→ℝ=>(0:ℝ))
    exact BddSmooth.const r (0:ℝ)
  | cons p ps ih=>
    exact ((p.tree.nativeAnchor_expect_smooth hw φ ho q
      (fun σ=>H (p.restrict σ) (p.spin σ)) r).const_mul p.coeff).add ih

def nativeClassifiedHighJointMean
    {ias sas : List PositiveMass} (Ei : ClockTree S ias) (Es D : ClockTree S sas)
    (d : D.Slot) (U : ℕ) (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (qi qs : ℕ→ι→ℝ≥0) (H : Ei.Assignment→Es.Assignment→D.Assignment→S→ℝ)
    (xi xs : ι→ℝ) : ℝ:=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
    (nativeHighMarkedRows D d (U-1) a) (H η ζ) xs) xs) xi

theorem native_classified_forest_high_joint_rows_eq_prefix
    (pre mid tail : List PositiveMass) (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (d : D.Slot) (U : ℕ) (hU : pre.length+mid.length < U) (a : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock (pre++(mid++tail)))
    (q : ℕ→ι→ℝ≥0) (H : Ei.Assignment→Es.Assignment→D.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows (nativeExteriorForestTree pre mid Ei Es D)
        (nativeClassifiedForestOccupiedSlot pre mid Ei Es D d) (U-1) a)
      (fun σ new=>nativeClassifiedSourceRead pre mid Ei Es D (fun η ζ δ=>H η ζ δ new) σ) x=
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps (mid++tail) (fun j=>q (pre.length+j))))
        (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
          (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
          (nativeClassifiedHighJointMean Ei Es D d (U-(pre.length+mid.length))
            (partitionPoint a (pre++(mid++tail)) (pre.length+mid.length)) w φ
            (fun j=>q (pre.length+j)) (fun j=>q (pre.length+(mid.length+j))) H xi) xi) x := by
  let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
  let qi:=fun j=>q (pre.length+j)
  let qs:=fun j=>q (pre.length+(mid.length+j))
  let ai:=partitionPoint a pre pre.length
  let astar:=partitionPoint ai mid mid.length
  have Hpre:=native_high_joint_rows_prepend_prefix_law pre V
    (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)))
    (U-pre.length) (by omega) a hw φ ho q
    (fun σ new=>nativeClassifiedSourceRead pre mid Ei Es D (fun η ζ δ=>H η ζ δ new) σ) x
  rw [show pre.length+(U-pre.length)=U by omega] at Hpre
  dsimp only [nativeExteriorForestTree,nativeClassifiedForestOccupiedSlot,V] at Hpre ⊢
  rw [Hpre]
  apply congrArg (fun F=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps (mid++tail) qi)) F x)
  funext xi
  change nativeJointAttachmentRow w φ qi
    ((nativeHighMarkedRows (exteriorPrepend mid (Es.fork D))
      ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)) ((U-pre.length)-1) ai).map
      (fun p=>p.right Ei))
    (fun σ new=>nativeClassifiedSourceRead pre mid Ei Es D (fun η ζ δ=>H η ζ δ new)
      ((exteriorPrependAssignmentEquiv pre (Ei.fork (exteriorPrepend mid (Es.fork D)))).symm σ)) xi=_
  rw [native_second_low_c_joint_rows_right]
  dsimp only [nativeClassifiedSourceRead]
  simp only [Equiv.apply_symm_apply]
  have Hpoint (η : Ei.Assignment) : nativeJointAttachmentRow w φ qi
      (nativeHighMarkedRows (exteriorPrepend mid (Es.fork D))
        ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)) ((U-pre.length)-1) ai)
      (fun σ new=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ;H η u.1 u.2 new) xi=
      prefixTest (clockSteps mid qi) (gaussianHierarchy w φ (clockSteps tail qs))
        (fun xs=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
          (nativeHighMarkedRows D d ((U-(pre.length+mid.length))-1) astar) (H η ζ) xs) xs) xi := by
    have HM:=native_high_joint_rows_prepend_prefix_law mid (Es.fork D) (.inr d)
      (U-(pre.length+mid.length)) (by omega) ai hw φ ho.suffix_end qi
      (fun σ new=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ;H η u.1 u.2 new) xi
    rw [show mid.length+(U-(pre.length+mid.length))=U-pre.length by omega] at HM
    rw [HM]
    apply congrArg (fun F=>prefixTest (clockSteps mid qi) (gaussianHierarchy w φ (clockSteps tail qs)) F xi)
    funext xs
    dsimp only
    simp only [Equiv.apply_symm_apply]
    change nativeJointAttachmentRow w φ qs
      ((nativeHighMarkedRows D d ((U-(pre.length+mid.length))-1) astar).map (fun p=>p.right Es))
      (fun (σ : (Es.fork D).Assignment) new=>H η σ.1 σ.2 new) xs=_
    exact native_second_low_c_joint_rows_right Es D w φ qs _ _ xs
  have Hfun : (fun η=>nativeJointAttachmentRow w φ qi
      (nativeHighMarkedRows (exteriorPrepend mid (Es.fork D))
        ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)) ((U-pre.length)-1) ai)
      (fun σ new=>H η (exteriorPrependAssignmentEquiv mid (Es.fork D) σ).1
        (exteriorPrependAssignmentEquiv mid (Es.fork D) σ).2 new) xi)=
      fun η=>prefixTest (clockSteps mid qi) (gaussianHierarchy w φ (clockSteps tail qs))
        (fun xs=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
          (nativeHighMarkedRows D d ((U-(pre.length+mid.length))-1) astar) (H η ζ) xs) xs) xi :=
    funext Hpoint
  rw [Hfun]
  have hB (η : Ei.Assignment) : BddSmooth 0 (fun xs=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
      (nativeHighMarkedRows D d ((U-(pre.length+mid.length))-1) astar) (H η ζ) xs) xs):=by
    have HH:=native_joint_attachment_row_smooth (Es.fork D) hw φ ho.suffix_end.suffix_end qs
      (nativeHighMarkedRows (Es.fork D) (.inr d) ((U-(pre.length+mid.length))-1) astar)
      (fun σ new=>H η σ.1 σ.2 new) 0
    have HE : (fun xs=>nativeJointAttachmentRow w φ qs
        (nativeHighMarkedRows (Es.fork D) (.inr d) ((U-(pre.length+mid.length))-1) astar)
        (fun σ new=>H η σ.1 σ.2 new) xs)=
        fun xs=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
          (nativeHighMarkedRows D d ((U-(pre.length+mid.length))-1) astar) (H η ζ) xs) xs := by
      funext xs
      exact native_second_low_c_joint_rows_right Es D w φ qs _ _ xs
    rw [HE] at HH
    exact HH
  have hoG : OrderedSteps (partitionEnd aClock pre) (clockSteps mid qi++clockSteps tail qs):=by
    rw [←clockSteps_append]
    exact clockSteps_ordered ho.suffix_end qi
  have HW:=prefixTest_native_expect_swap Ei hw φ qi (clockSteps mid qi) (clockSteps tail qs) hoG
    (fun η xs=>Es.expect w φ qs (fun ζ=>nativeJointAttachmentRow w φ qs
      (nativeHighMarkedRows D d ((U-(pre.length+mid.length))-1) astar) (H η ζ) xs) xs) hB xi xi
  rw [←HW]
  rw [native_classified_star_mass_eq_nested_prefix]
  rfl

theorem native_classified_forest_tail_high_joint_rows_eq_prefix
    (mid tail : List PositiveMass) (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (d : D.Slot) (U : ℕ) (hU : mid.length < U) (a : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {aClock : ℝ} (ho : MassOrdered aClock (mid++tail))
    (q : ℕ→ι→ℝ≥0) (H : Ei.Assignment→Es.Assignment→D.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q
      (nativeHighMarkedRows (Ei.fork (exteriorPrepend mid (Es.fork D)))
        (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d))) (U-1) a)
      (fun σ new=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) σ.2;H σ.1 u.1 u.2 new) x=
      prefixTest (clockSteps mid q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (mid.length+j))))
        (nativeClassifiedHighJointMean Ei Es D d (U-mid.length) (partitionPoint a (mid++tail) mid.length)
          w φ q (fun j=>q (mid.length+j)) H x) x := by
  have HH:=native_classified_forest_high_joint_rows_eq_prefix [] mid tail Ei Es D d U
    (by simpa only [List.length_nil,Nat.zero_add] using hU) a hw φ ho q H x
  simpa only [nativeExteriorForestTree,nativeClassifiedForestOccupiedSlot,nativeClassifiedSourceRead,
    exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,List.nil_append,List.length_nil,
    Nat.zero_add,Nat.sub_zero,clockSteps,prefixTest,Equiv.refl_symm,Equiv.refl_apply] using HH

theorem native_classified_suffix_mass_readout
    (a : ℝ) (pre tail : List PositiveMass) (U : ℕ) (hU : pre.length ≤ U) :
    partitionPoint (partitionPoint a (pre++tail) pre.length) tail (U-pre.length)=
      partitionPoint a (pre++tail) U := by
  have H0:=native_classified_partitionPoint_append_shift a pre tail 0
  simp only [Nat.add_zero,partitionPoint,partitionValues_zero,id_eq] at H0
  change partitionPoint a (pre++tail) pre.length=partitionEnd a pre at H0
  rw [H0,←native_classified_partitionPoint_append_shift,Nat.add_sub_of_le hU]

end OAI.SKFluctuations.Cavity
