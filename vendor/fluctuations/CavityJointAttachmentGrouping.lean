module

public import CavityAllocationForest

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] [DecidableEq S]

def jointAttachmentRow {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (ps : List (ReplicaTree.MarkedPlacement T)) (H : T.Assignment → S → ℝ)
    (x : ι → ℝ) : ℝ :=
  (ps.map (fun p => p.coeff*p.tree.expect w φ
    (fun σ => H (p.restrict σ) (p.spin σ)) x)).sum

private theorem joint_placement_eq_spin_sum {steps : List (GaussianStep ι)}
    {T : ReplicaTree ι S steps} (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (p : ReplicaTree.MarkedPlacement T) (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ (fun σ => H (p.restrict σ) (p.spin σ)) x =
      ∑ s, p.toPlacement.eval w φ (fun σ => H σ s)
        (fun τ => if τ = s then 1 else 0) x := by
  classical
  simp only [ReplicaTree.Placement.eval,ReplicaTree.expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp

theorem jointAttachmentRow_eq_spin_sum {steps : List (GaussianStep ι)}
    {T : ReplicaTree ι S steps} (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (ps : List (ReplicaTree.MarkedPlacement T)) (H : T.Assignment → S → ℝ) (x : ι → ℝ) :
    jointAttachmentRow w φ ps H x =
      ∑ s, ReplicaTree.rowList w φ (ps.map ReplicaTree.MarkedPlacement.toPlacement)
        (fun σ => H σ s) (fun τ => if τ = s then 1 else 0) x := by
  classical
  induction ps with
  | nil => simp [jointAttachmentRow,ReplicaTree.rowList]
  | cons p ps ih =>
    change p.coeff*p.tree.expect w φ (fun σ => H (p.restrict σ) (p.spin σ)) x +
      jointAttachmentRow w φ ps H x = _
    rw [joint_placement_eq_spin_sum, Finset.mul_sum, ih, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rfl

namespace ChildForest
variable {st : GaussianStep ι} {tail : List (GaussianStep ι)}

def groupedAttach (A : ChildForest (S := S) st tail) (a : ℝ) :
    List (ReplicaTree.MarkedPlacement A.tree) :=
  ReplicaTree.MarkedPlacement.fresh A.tree (a-(A.children:ℝ)*st.1) :: A.retained

theorem actual_binary_grouping_row {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : ChildForest (S := S) st tail)
    {a : ℝ} (ho : OrderedSteps a (st::tail))
    (P : A.tree.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    ReplicaTree.rowList w φ ((A.groupedAttach a).map
      ReplicaTree.MarkedPlacement.toPlacement) P B x = A.tree.row w φ a P B x := by
  unfold groupedAttach
  simp only [List.map_cons,ReplicaTree.rowList,List.sum_cons]
  change (a-(A.children:ℝ)*st.1)*
    (ReplicaTree.Placement.fresh A.tree (a-(A.children:ℝ)*st.1)).eval w φ P B x +
    retainedRow w φ A P B x = _
  rw [ReplicaTree.Placement.eval_fresh hw φ _ ho, A.actual_row_grouping hw φ ho]
  ring

theorem actual_binary_grouping_joint {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : ChildForest (S := S) st tail)
    {a : ℝ} (ho : OrderedSteps a (st::tail))
    (H : A.tree.Assignment → S → ℝ) (x : ι → ℝ) :
    jointAttachmentRow w φ (A.tree.markedAttach a) H x =
      jointAttachmentRow w φ (A.groupedAttach a) H x := by
  rw [jointAttachmentRow_eq_spin_sum,jointAttachmentRow_eq_spin_sum,
    A.tree.markedAttach_forget]
  apply Finset.sum_congr rfl
  intro s hs
  exact (A.actual_binary_grouping_row hw φ ho _ _ x).symm

end ChildForest
end OAI.SKFluctuations.Cavity
