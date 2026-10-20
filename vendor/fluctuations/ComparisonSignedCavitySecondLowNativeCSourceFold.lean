module

public import ComparisonSignedCavitySecondLowSharedExteriorReplacement
public import ComparisonSignedCavityHighMarkedRows
public import ComparisonSignedCavityTrunkProjection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 24000000

inductive NativeSecondLowCReader {S : Type} {as : List PositiveMass} (T : ClockTree S as)
  | fixed : S→NativeSecondLowCReader T
  | slot : T.Slot→NativeSecondLowCReader T

namespace NativeSecondLowCReader
variable {S : Type} {as : List PositiveMass}

def read {T : ClockTree S as} : NativeSecondLowCReader T→T.Assignment→S
  | .fixed s,_=>s
  | .slot s,σ=>T.atSlot σ s

def low {T : ClockTree S as} (c : T.Slot) (U : ℕ) : NativeSecondLowCReader T→Prop
  | .fixed _=>True
  | .slot s=>T.splitIndex c s<U

def left {T E : ClockTree S as} (τ : E.Assignment) :
    NativeSecondLowCReader (T.fork E)→NativeSecondLowCReader T
  | .fixed s=>.fixed s
  | .slot (.inl s)=>.slot s
  | .slot (.inr s)=>.fixed (E.atSlot τ s)

def right {T E : ClockTree S as} (σ : T.Assignment) :
    NativeSecondLowCReader (T.fork E)→NativeSecondLowCReader E
  | .fixed s=>.fixed s
  | .slot (.inl s)=>.fixed (T.atSlot σ s)
  | .slot (.inr s)=>.slot s

def unstep {T : ClockTree S as} (b : PositiveMass) :
    NativeSecondLowCReader (T.step b)→NativeSecondLowCReader T
  | .fixed s=>.fixed s
  | .slot s=>.slot s

theorem read_left {T E : ClockTree S as} (r : NativeSecondLowCReader (T.fork E))
    (σ : T.Assignment) (τ : E.Assignment) : r.read (σ,τ)=(r.left τ).read σ := by
  cases r with
  | fixed s=>rfl
  | slot s=>cases s <;> rfl

theorem read_right {T E : ClockTree S as} (r : NativeSecondLowCReader (T.fork E))
    (σ : T.Assignment) (τ : E.Assignment) : r.read (σ,τ)=(r.right σ).read τ := by
  cases r with
  | fixed s=>rfl
  | slot s=>cases s <;> rfl

theorem read_unstep {T : ClockTree S as} (b : PositiveMass)
    (r : NativeSecondLowCReader (T.step b)) (σ : T.Assignment) :
    r.read σ=(r.unstep b).read σ := by cases r <;> rfl

theorem low_left {T E : ClockTree S as} (r : NativeSecondLowCReader (T.fork E))
    (c : T.Slot) (U : ℕ) (hr : low (T:=T.fork E) (Sum.inl c) U r) (τ : E.Assignment) :
    (r.left τ).low c U := by
  cases r with
  | fixed s=>trivial
  | slot s=>cases s with
    | inl s=>exact hr
    | inr s=>trivial

theorem low_right {T E : ClockTree S as} (r : NativeSecondLowCReader (T.fork E))
    (c : E.Slot) (U : ℕ) (hr : low (T:=T.fork E) (Sum.inr c) U r) (σ : T.Assignment) :
    (r.right σ).low c U := by
  cases r with
  | fixed s=>trivial
  | slot s=>cases s with
    | inl s=>trivial
    | inr s=>exact hr

theorem low_unstep {T : ClockTree S as} (b : PositiveMass) (r : NativeSecondLowCReader (T.step b))
    (c : T.Slot) (U : ℕ) (hr : low (T:=T.step b) c (U+1) r) : (r.unstep b).low c U := by
  cases r with
  | fixed s=>trivial
  | slot s=>change 1+T.splitIndex c s<U+1 at hr;exact show T.splitIndex c s<U by omega

end NativeSecondLowCReader

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeSecondLowCSourceRows {as : List PositiveMass} (T : ClockTree S as)
    (c : T.Slot) (U : ℕ) (a : ℝ) : List (MarkedPlacement T) :=
  if U=0 then T.markedAttach a else nativeHighMarkedRows T c (U-1) a

def nativeSecondLowCReplacementValue {as : List PositiveMass} (T : ClockTree S as)
    (c : T.Slot) (U : ℕ) (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (rf rz : NativeSecondLowCReader T)
    (Q : S→S→S→ℝ) (x : ι→ℝ) : ℝ :=
  nativeJointAttachmentRow w φ q (nativeSecondLowCSourceRows T c U a)
    (fun σ s=>P σ*Q (rf.read σ) s (rz.read σ)) x-
      partitionPoint a as U*T.expect w φ q
        (fun σ=>P σ*Q (rf.read σ) (T.atSlot σ c) (rz.read σ)) x

omit [Nonempty S] in
private theorem c_source_expect_add {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P R : T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>P σ+R σ) x=T.expect w φ q P x+T.expect w φ q R x := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

omit [Nonempty S] in
private theorem c_source_expect_const_mul {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (c : ℝ) (P : T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>c*P σ) x=c*T.expect w φ q P x := by
  simp only [expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [Nonempty S] in
private theorem c_source_expect_sub {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P R : T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>P σ-R σ) x=T.expect w φ q P x-T.expect w φ q R x := by
  simp only [expect,mul_sub,Finset.sum_sub_distrib]

private theorem c_source_expect_smooth
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) : BddSmooth 0 (T.expect w φ q P) := by
  have HE:T.expect w φ q P=(T.realize q).expect w φ
      (fun σ=>P ((T.assignmentEquiv q).symm σ)):=funext (T.expect_realize w φ q P)
  rw [HE]
  exact (T.realize q).expect_smooth hw φ (clockSteps_ordered ho q) _ 0

private theorem c_source_list_smooth {α : Type}
    (ps : List α) (c : α→ℝ) (F : α→(ι→ℝ)→ℝ)
    (hF : ∀p∈ps,BddSmooth 0 (F p)) :
    BddSmooth 0 (fun x=>(ps.map (fun p=>c p*F p x)).sum) := by
  induction ps with
  | nil=>exact BddSmooth.const 0 0
  | cons p ps ih=>
    exact ((hF p List.mem_cons_self).const_mul (c p)).add
      (ih (fun r hr=>hF r (List.mem_cons_of_mem p hr)))

private theorem c_source_list_shiftedMean {α : Type}
    (ps : List α) (c : α→ℝ) (F : α→(ι→ℝ)→ℝ)
    (hF : ∀p∈ps,BddSmooth 0 (F p))
    {ν : Measure (ι→ℝ)} [IsProbabilityMeasure ν] (m : ℝ) (H : (ι→ℝ)→ℝ) (x : ι→ℝ)
    (hi : Integrable (fun z=>Real.exp (m*H (x+z))) ν) :
    shiftedMean ν m H (fun y=>(ps.map (fun p=>c p*F p y)).sum) x=
      (ps.map (fun p=>c p*shiftedMean ν m H (F p) x)).sum := by
  induction ps with
  | nil=>simp [shiftedMean,tiltedMean]
  | cons p ps ih=>
    change shiftedMean ν m H (fun y=>c p*F p y+(ps.map (fun p=>c p*F p y)).sum) x=_
    rw [shiftedMean_add ((hF p List.mem_cons_self).const_mul (c p))
      (c_source_list_smooth ps c F (fun r hr=>hF r (List.mem_cons_of_mem p hr))) hi,
      shiftedMean_const_mul,ih (fun r hr=>hF r (List.mem_cons_of_mem p hr))]
    rfl

theorem native_second_low_c_joint_rows_step
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (b : PositiveMass)
    (ho : MassOrdered b.val as) (q : ℕ→ι→ℝ≥0) (ps : List (MarkedPlacement T))
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (ps.map (MarkedPlacement.step b)) H x=
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j=>q (j+1))))
        (fun y=>nativeJointAttachmentRow w φ (fun j=>q (j+1)) ps H y) x := by
  let F:=fun p:MarkedPlacement T=>p.tree.expect w φ (fun j=>q (j+1))
    (fun σ=>H (p.restrict σ) (p.spin σ))
  have hF:∀p∈ps,BddSmooth 0 (F p):=fun p _=>c_source_expect_smooth hw φ p.tree ho _ _
  have hi:=gaussianHierarchy_integrable hw φ (clockSteps as (fun j=>q (j+1)))
    (clockSteps_ordered ho _) b.val (q 0) x
  unfold nativeJointAttachmentRow
  rw [c_source_list_shiftedMean ps (fun p=>p.coeff) F hF b.val _ x hi]
  simp only [List.map_map,Function.comp_def,MarkedPlacement.step]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [expect_step hw φ b p.tree ho]

theorem native_second_low_c_joint_rows_left
    {as : List PositiveMass} (T E : ClockTree S as) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (ps : List (MarkedPlacement T))
    (H : (T.fork E).Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (ps.map (fun p=>p.left E)) H x=
      E.expect w φ q (fun τ=>nativeJointAttachmentRow w φ q ps (fun σ s=>H (σ,τ) s) x) x := by
  unfold nativeJointAttachmentRow
  simp only [List.map_map,Function.comp_def,MarkedPlacement.left]
  have Hpoint (p:MarkedPlacement T):
      (p.tree.fork E).expect w φ q (fun σ=>H (p.restrict σ.1,σ.2) (p.spin σ.1)) x=
      E.expect w φ q (fun τ=>p.tree.expect w φ q (fun σ=>H (p.restrict σ,τ) (p.spin σ)) x) x:=
    native_fork_expect_external_left w φ p.tree E q _ x
  simp_rw [Hpoint]
  induction ps with
  | nil=>simp [expect]
  | cons p ps ih=>
    simp only [List.map_cons,List.sum_cons,c_source_expect_add,c_source_expect_const_mul,ih]

def nativeSecondLowCClusterCouplingRoot {as : List PositiveMass}
    (T : ClockTree S as) (c : T.Slot) (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (f z : S) (Q : S→S→S→ℝ) (x : ι→ℝ) : ℝ :=
  let A:=T.realize q
  let P':=fun σ=>P ((T.assignmentEquiv q).symm σ)
  let Y:=fun s=>Q f s z
  actualCutRow A w φ 0 1 P' Y x-actualCutRow A w φ 0 (a/2) P' Y x-
    (a/2)*(A.fork A).expect w φ (fun σ=>
      (P' σ.1-P' σ.2)*(Y (A.atSlot σ.1 (T.slotEquiv q c))-Y (A.atSlot σ.2 (T.slotEquiv q c)))) x

private theorem c_source_full_product_realized {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (T.markedAttach a) (fun σ s=>P σ*F s) x=
      (T.realize q).row w φ a (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x := by
  classical
  rw [nativeJointAttachmentRow_eq_realized,markedAttach_realize]
  unfold jointAttachmentRow ReplicaTree.row ReplicaTree.rowList
  rw [←(T.realize q).markedAttach_forget a]
  simp only [List.map_map,ReplicaTree.Placement.eval]
  rfl

theorem native_second_low_c_root_replacement_eq_complete_coupling
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (c : T.Slot)
    {a : ℝ} (ho : MassOrdered a as) (ha : 0<a)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (f z : S) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCReplacementValue T c 0 a w φ q P (.fixed f) (.fixed z) Q x=
      nativeSecondLowCClusterCouplingRoot T c a w φ q P f z Q x := by
  let A:=T.realize q
  let P':=fun σ=>P ((T.assignmentEquiv q).symm σ)
  let Y:=fun s=>Q f s z
  have hoA:OrderedSteps a (clockSteps as q):=clockSteps_ordered ho q
  have H:=actual_shared_exterior_replacement_eq_layer_sub_whole_covariance hw φ A A hoA ha
    hoA.bounds.2 (T.slotEquiv q c) (fun σ _=>P' σ) (fun _ s=>Y s) x
  simp only [actualSharedExteriorMarkedReplacement,actualSharedExteriorLayer,
    actualSharedExteriorWholeProductCovariance,ReplicaTree.expect_fork,
    A.expect_const hw φ hoA] at H
  unfold nativeSecondLowCReplacementValue nativeSecondLowCClusterCouplingRoot
  simp only [nativeSecondLowCSourceRows,ite_true,partitionPoint,partitionValues_zero,id_eq,
    NativeSecondLowCReader.read]
  rw [c_source_full_product_realized,T.expect_realize]
  have Hat:∀σ,(T.realize q).atSlot σ (T.slotEquiv q c)=T.atSlot ((T.assignmentEquiv q).symm σ) c:=by
    intro σ
    have HH:=T.realize_atSlot q ((T.assignmentEquiv q).symm σ) c
    simpa only [Equiv.apply_symm_apply] using HH
  simp only [←Hat]
  rw [ReplicaTree.expect_fork]
  exact H

def nativeSecondLowCClusterRoot {as : List PositiveMass} (T : ClockTree S as) (c : T.Slot)
    (a : ℝ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (rf rz : NativeSecondLowCReader T) (Q : S→S→S→ℝ) (x : ι→ℝ) : ℝ :=
  match rf,rz with
  | .fixed f,.fixed z=>nativeSecondLowCClusterCouplingRoot T c a w φ q P f z Q x
  | _,_=>nativeSecondLowCReplacementValue T c 0 a w φ q P rf rz Q x

def nativeSecondLowCCouplingFold (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    {as : List PositiveMass}→(T : ClockTree S as)→T.Slot→ℕ→ℝ→(ℕ→ι→ℝ≥0)→
      (T.Assignment→ℝ)→NativeSecondLowCReader T→NativeSecondLowCReader T→
        (S→S→S→ℝ)→(ι→ℝ)→ℝ
  | _,T,c,0,a,q,P,rf,rz,Q,x=>nativeSecondLowCClusterRoot T c a w φ q P rf rz Q x
  | _,.leaf,_,_+1,_,_,_,_,_,_,_=>0
  | _::as,.step b T,c,U+1,_,q,P,rf,rz,Q,x=>
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j=>q (j+1))))
        (nativeSecondLowCCouplingFold w φ T c U b.val (fun j=>q (j+1)) P
          (rf.unstep b) (rz.unstep b) Q) x
  | _,.fork T E,c,U+1,a,q,P,rf,rz,Q,x=>match (c:T.Slot⊕E.Slot) with
      | .inl c=>E.expect w φ q (fun τ=>nativeSecondLowCCouplingFold w φ T c (U+1) a q
          (fun σ=>P (σ,τ)) (rf.left τ) (rz.left τ) Q x) x
      | .inr c=>T.expect w φ q (fun σ=>nativeSecondLowCCouplingFold w φ E c (U+1) a q
          (fun τ=>P (σ,τ)) (rf.right σ) (rz.right σ) Q x) x

omit [Fintype S] [Nonempty S] in
theorem native_second_low_c_source_rows_step {as : List PositiveMass} (T : ClockTree S as)
    (b : PositiveMass) (c : T.Slot) (U : ℕ) (a : ℝ) :
    nativeSecondLowCSourceRows (T.step b) c (U+1) a=
      (nativeSecondLowCSourceRows T c U b.val).map (MarkedPlacement.step b) := by
  cases U
  · simp only [nativeSecondLowCSourceRows,Nat.zero_add,one_ne_zero,ite_false,Nat.sub_self,
      nativeHighMarkedRows,ite_true]
  · simp only [nativeSecondLowCSourceRows,Nat.succ_ne_zero,ite_false,nativeHighMarkedRows,
      Nat.add_sub_cancel]

theorem native_second_low_c_replacement_step
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (b : PositiveMass) (c : T.Slot) (U : ℕ) (a : ℝ)
    (ho : MassOrdered b.val as) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ)
    (rf rz : NativeSecondLowCReader (T.step b)) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCReplacementValue (T.step b) c (U+1) a w φ q P rf rz Q x=
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j=>q (j+1))))
        (fun y=>nativeSecondLowCReplacementValue T c U b.val w φ (fun j=>q (j+1)) P
          (rf.unstep b) (rz.unstep b) Q y) x := by
  unfold nativeSecondLowCReplacementValue
  rw [native_second_low_c_source_rows_step,native_second_low_c_joint_rows_step hw φ T b ho]
  rw [expect_step hw φ b T ho]
  have HR:∀σ,rf.read σ=(rf.unstep b).read σ:=rf.read_unstep b
  have HZ:∀σ,rz.read σ=(rz.unstep b).read σ:=rz.read_unstep b
  simp only [HR,HZ,atSlot,partitionPoint,partitionValues]
  let ps:=nativeSecondLowCSourceRows T c U b.val
  let H:=fun σ s=>P σ*Q ((rf.unstep b).read σ) s ((rz.unstep b).read σ)
  have hs:BddSmooth 0 (fun y=>nativeJointAttachmentRow w φ (fun j=>q (j+1)) ps H y):=by
    unfold nativeJointAttachmentRow
    exact c_source_list_smooth ps (fun p=>p.coeff) _
      (fun p _=>c_source_expect_smooth hw φ p.tree ho _ _)
  have hp:=c_source_expect_smooth hw φ T ho (fun j=>q (j+1))
    (fun σ=>P σ*Q ((rf.unstep b).read σ) (T.atSlot σ c) ((rz.unstep b).read σ))
  have hi:=gaussianHierarchy_integrable hw φ (clockSteps as (fun j=>q (j+1)))
    (clockSteps_ordered ho _) b.val (q 0) x
  rw [shiftedMean_sub hs (hp.const_mul _) hi,shiftedMean_const_mul]

omit [Nonempty S] in
theorem native_second_low_c_joint_rows_right
    {as : List PositiveMass} (T E : ClockTree S as) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (ps : List (MarkedPlacement E))
    (H : (T.fork E).Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointAttachmentRow w φ q (ps.map (fun p=>p.right T)) H x=
      T.expect w φ q (fun σ=>nativeJointAttachmentRow w φ q ps (fun τ s=>H (σ,τ) s) x) x := by
  unfold nativeJointAttachmentRow
  simp only [List.map_map,Function.comp_def,MarkedPlacement.right]
  have Hpoint (p:MarkedPlacement E):
      (T.fork p.tree).expect w φ q (fun σ=>H (σ.1,p.restrict σ.2) (p.spin σ.2)) x=
      T.expect w φ q (fun σ=>p.tree.expect w φ q (fun τ=>H (σ,p.restrict τ) (p.spin τ)) x) x:=
    expect_fork w φ T p.tree q _ x
  simp_rw [Hpoint]
  induction ps with
  | nil=>simp [expect]
  | cons p ps ih=>
    simp only [List.map_cons,List.sum_cons,c_source_expect_add,c_source_expect_const_mul,ih]

theorem native_second_low_c_replacement_left {as : List PositiveMass}
    (T E : ClockTree S as) (c : T.Slot) (U : ℕ) (a : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : (T.fork E).Assignment→ℝ) (rf rz : NativeSecondLowCReader (T.fork E))
    (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCReplacementValue (T.fork E) (Sum.inl c) (U+1) a w φ q P rf rz Q x=
      E.expect w φ q (fun τ=>nativeSecondLowCReplacementValue T c (U+1) a w φ q
        (fun σ=>P (σ,τ)) (rf.left τ) (rz.left τ) Q x) x := by
  unfold nativeSecondLowCReplacementValue
  simp only [nativeSecondLowCSourceRows,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,nativeHighMarkedRows]
  rw [native_second_low_c_joint_rows_left,native_fork_expect_external_left]
  simp_rw [rf.read_left,rz.read_left]
  rw [c_source_expect_sub,c_source_expect_const_mul]
  rfl

omit [Nonempty S] in
theorem native_second_low_c_replacement_right {as : List PositiveMass}
    (T E : ClockTree S as) (c : E.Slot) (U : ℕ) (a : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : (T.fork E).Assignment→ℝ) (rf rz : NativeSecondLowCReader (T.fork E))
    (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCReplacementValue (T.fork E) (Sum.inr c) (U+1) a w φ q P rf rz Q x=
      T.expect w φ q (fun σ=>nativeSecondLowCReplacementValue E c (U+1) a w φ q
        (fun τ=>P (σ,τ)) (rf.right σ) (rz.right σ) Q x) x := by
  unfold nativeSecondLowCReplacementValue
  simp only [nativeSecondLowCSourceRows,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,nativeHighMarkedRows]
  rw [native_second_low_c_joint_rows_right,expect_fork]
  simp_rw [rf.read_right,rz.read_right]
  rw [c_source_expect_sub,c_source_expect_const_mul]
  rfl

theorem native_second_low_c_cluster_root_eq_original
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (c : T.Slot)
    {a : ℝ} (ho : MassOrdered a as) (ha : 0<a) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (rf rz : NativeSecondLowCReader T)
    (hf : rf.low c 0) (hz : rz.low c 0) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCClusterRoot T c a w φ q P rf rz Q x=
      nativeSecondLowCReplacementValue T c 0 a w φ q P rf rz Q x := by
  cases rf with
  | fixed f=>cases rz with
    | fixed z=>exact (native_second_low_c_root_replacement_eq_complete_coupling hw φ T c ho ha q P f z Q x).symm
    | slot z=>have HH:T.splitIndex c z<0:=hz;omega
  | slot f=>have HH:T.splitIndex c f<0:=hf;omega

theorem native_second_low_c_coupling_fold_eq_original
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (c : T.Slot) (U : ℕ)
    {a : ℝ} (ho : MassOrdered a as) (hU : U≤as.length) (hroot : U=0→0<a)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (rf rz : NativeSecondLowCReader T)
    (hf : rf.low c U) (hz : rz.low c U) (Q : S→S→S→ℝ) (x : ι→ℝ) :
    nativeSecondLowCCouplingFold w φ T c U a q P rf rz Q x=
      nativeSecondLowCReplacementValue T c U a w φ q P rf rz Q x := by
  induction T generalizing U a q x with
  | leaf=>cases U with
    | zero=>exact native_second_low_c_cluster_root_eq_original hw φ .leaf c ho (hroot rfl) q P rf rz hf hz Q x
    | succ U=>simp only [List.length_nil] at hU;omega
  | step b T ih=>cases U with
    | zero=>exact native_second_low_c_cluster_root_eq_original hw φ (T.step b) c ho (hroot rfl) q P rf rz hf hz Q x
    | succ U=>
      rw [nativeSecondLowCCouplingFold,native_second_low_c_replacement_step hw φ T b c U a ho.2.2]
      congr 1
      funext y
      exact ih c U ho.2.2 (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hU)
        (fun _=>b.property) (fun j=>q (j+1)) P (rf.unstep b) (rz.unstep b)
        (rf.low_unstep b c U hf) (rz.low_unstep b c U hz) y
  | fork T E ihT ihE=>cases U with
    | zero=>exact native_second_low_c_cluster_root_eq_original hw φ (T.fork E) c ho (hroot rfl) q P rf rz hf hz Q x
    | succ U=>cases c with
      | inl c=>
        rw [nativeSecondLowCCouplingFold,native_second_low_c_replacement_left]
        congr 1
        funext τ
        exact ihT c (U+1) ho hU (by omega) q (fun σ=>P (σ,τ))
          (rf.left τ) (rz.left τ) (rf.low_left c (U+1) hf τ) (rz.low_left c (U+1) hz τ) x
      | inr c=>
        rw [nativeSecondLowCCouplingFold,native_second_low_c_replacement_right]
        congr 1
        funext σ
        exact ihE c (U+1) ho hU (by omega) q (fun τ=>P (σ,τ))
          (rf.right σ) (rz.right σ) (rf.low_right c (U+1) hf σ) (rz.low_right c (U+1) hz σ) x

end OAI.SKFluctuations.Cavity
