module

public import ComparisonSignedCavitySecondLowEightLabeledRouting
public import ComparisonSignedCavitySecondLowOccupiedGammaHighSupport

@[expose] public section

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass} {T : ClockTree (S×B) as}

def NativeSecondLowLabeledDiagram.restRead (D : NativeSecondLowLabeledDiagram T)
    (τ : D.tree.cavityLeft.Assignment) : T.cavityLeft.Assignment :=
  assignmentOfSlots T.cavityLeft (fun c=>D.tree.cavityLeft.atSlot τ
    (D.tree.cavityLeftSlot (D.embed (T.cavityLeftSlot.symm c))))

theorem NativeSecondLowLabeledDiagram.restRead_at (D : NativeSecondLowLabeledDiagram T)
    (τ : D.tree.cavityLeft.Assignment) (c : T.Slot) :
    T.cavityLeft.atSlot (D.restRead τ) (T.cavityLeftSlot c)=
      D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot (D.embed c)) := by
  simp only [restRead,atSlot_assignmentOfSlots,Equiv.symm_apply_apply]

theorem NativeSecondLowLabeledDiagram.base_restRead (a : T.Slot) (τ : T.cavityLeft.Assignment) :
    (NativeSecondLowLabeledDiagram.base T a).restRead τ=τ := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [restRead_at]
  rfl

theorem NativeSecondLowLabeledDiagram.observe_restRead (D : NativeSecondLowLabeledDiagram T)
    (i : Fin 4) (p : MarkedPlacement D.tree) (τ : p.tree.cavityLeft.Assignment) :
    (D.observe i p).restRead τ=D.restRead (p.restRestrict τ) := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [restRead_at,restRead_at]
  exact (p.restRestrict_at τ (D.embed d)).symm

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
attribute [local instance] Classical.propDecidable

def nativeSecondLowOriginalLabelVector (j : Fin 8) : Fin 4 → Fin 4 :=
  match j.val with
  | 0=>![0,1,2,3]
  | 1=>![0,1,3,2]
  | 2=>![1,0,2,3]
  | 3=>![1,0,3,2]
  | 4=>![1,3,0,2]
  | 5=>![3,1,0,2]
  | 6=>![1,3,2,0]
  | _=>![3,1,2,0]

theorem native_second_low_original_label_order_eq_vector (j : Fin 8) :
    nativeSecondLowOriginalLabelOrder j=
      [nativeSecondLowOriginalLabelVector j 0,nativeSecondLowOriginalLabelVector j 1,
        nativeSecondLowOriginalLabelVector j 2,nativeSecondLowOriginalLabelVector j 3] := by
  fin_cases j <;> rfl

theorem native_second_low_chronological_targets_eq_semantic_targets {α : Type}
    (j : Fin 8) (a v z : α) :
    nativeSecondLowChronologicalTargets j a v z=
      fun k=>![a,v,v,z] (nativeSecondLowOriginalLabelVector j k) := by
  fin_cases j
  all_goals funext k
  all_goals fin_cases k
  all_goals rfl

def nativeSecondLowLabeledFourObserve {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (a : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : NativeSecondLowLabeledDiagram T :=
  ((((NativeSecondLowLabeledDiagram.base T a).observe (nativeSecondLowOriginalLabelVector j 0) p).observe (nativeSecondLowOriginalLabelVector j 1) r).observe (nativeSecondLowOriginalLabelVector j 2) s).observe (nativeSecondLowOriginalLabelVector j 3) t

theorem native_second_low_labeled_four_observe_rest_read {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (a : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) (τ : t.tree.cavityLeft.Assignment) :
    (nativeSecondLowLabeledFourObserve a j p r s t).restRead τ=
      p.restRestrict (r.restRestrict (s.restRestrict (t.restRestrict τ))) := by
  simp only [nativeSecondLowLabeledFourObserve,NativeSecondLowLabeledDiagram.observe_restRead,
    NativeSecondLowLabeledDiagram.base_restRead]

theorem native_second_low_rest_low_kernel_symm (n U : ℕ) (b h : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n) : restLowKernel n U b h j σ τ=restLowKernel n U b h j τ σ := by
  simp only [restLowKernel,mul_comm]

def nativeSecondLowLabeledLowRow {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (U : ℕ) (b h : ℕ→ℝ)
    (D : NativeSecondLowLabeledDiagram T) (i k : Fin 4) (τ : D.tree.cavityLeft.Assignment) : ℝ :=
  restLowKernel n U b h (D.tree.splitIndex (D.marks i) (D.marks k))
    (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot (D.marks i)))
    (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot (D.marks k)))

def nativeSecondLowLabeledScalarRow {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (U : ℕ) (K : ℕ→ℝ)
    (D : NativeSecondLowLabeledDiagram T) (i k : Fin 4) : ℝ :=
  nativeSecondLowScalarValue U K (D.tree.splitIndex (D.marks i) (D.marks k))

def nativeSecondLowLabeledQQKKTest {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (U : ℕ) (b h K : ℕ→ℝ)
    (P : T.cavityLeft.Assignment→ℝ) (j : Fin 8) (D : NativeSecondLowLabeledDiagram T)
    (τ : D.tree.cavityLeft.Assignment) : ℝ :=
  P (D.restRead τ)*
    (if j.val<4 then
      nativeSecondLowLabeledLowRow U b h D 0 1 τ*nativeSecondLowLabeledLowRow U b h D 2 3 τ-
        nativeSecondLowLabeledScalarRow U K D 0 1*nativeSecondLowLabeledScalarRow U K D 2 3
    else
      nativeSecondLowLabeledLowRow U b h D 1 3 τ*nativeSecondLowLabeledLowRow U b h D 0 2 τ-
        nativeSecondLowLabeledScalarRow U K D 1 3*nativeSecondLowLabeledScalarRow U K D 0 2)

def nativeSecondLowLabeledGammaValue {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8)
    (D : NativeSecondLowLabeledDiagram T) : ℝ :=
  D.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (nativeSecondLowLabeledQQKKTest U b h K P j D) 0*
    (fullScalarCutGamma D.tree U K (D.embed a) (D.marks 0)*
      fullScalarCutGamma D.tree U K (D.marks 1) (D.marks 2)*
      fullScalarCutGamma D.tree U K (D.marks 3) (D.embed z))

theorem native_second_low_joint_rest_test_eq_labeled_QQKK
    (n U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    nativeSecondLowJointRestTest n U b h K P p r s t=
      nativeSecondLowLabeledQQKKTest U b h K P j (nativeSecondLowLabeledFourObserve a j p r s t) := by
  funext τ
  rw [native_second_low_joint_rest_test_final_slots n U b h K P p r s hs t ht]
  simp only [nativeSecondLowLabeledQQKKTest,native_second_low_labeled_four_observe_rest_read,
    nativeSecondLowOldTest]
  fin_cases j
  all_goals simp [nativeSecondLowLabeledLowRow,nativeSecondLowLabeledScalarRow,
    nativeSecondLowLabeledFourObserve,nativeSecondLowOriginalLabelVector,
    NativeSecondLowLabeledDiagram.observe,NativeSecondLowLabeledDiagram.base,
    ClockTree.splitIndex_symm,native_second_low_rest_low_kernel_symm]

theorem native_second_low_gamma_word_eq_labeled_gamma_value
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    nativeSecondLowGammaWordValue n q U b h K P a z j p r s t=
      nativeSecondLowLabeledGammaValue q U b h K P a z j (nativeSecondLowLabeledFourObserve a j p r s t) := by
  unfold nativeSecondLowGammaWordValue nativeSecondLowLabeledGammaValue
  rw [native_second_low_joint_rest_test_eq_labeled_QQKK n U b h K T P a j p r s hs t ht]
  congr 1
  fin_cases j
  all_goals simp [nativeSecondLowPathGamma,nativeSecondLowLabeledFourObserve,
    nativeSecondLowOriginalLabelVector,NativeSecondLowLabeledDiagram.observe,
    NativeSecondLowLabeledDiagram.base,fullScalarCutGamma_symm]

end OAI.SKFluctuations.Cavity
