module

public import CavityPlantedNodePower
public import SKFluctuationsOAI.Probability.SKFluctuations.Chain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

inductive ChildForest (st : GaussianStep ι) (tail : List (GaussianStep ι)) where
  | child (T : ReplicaTree ι S tail)
  | fork (A B : ChildForest st tail)

namespace ChildForest
variable {st : GaussianStep ι} {tail : List (GaussianStep ι)}

@[reducible] def tree : ChildForest (S := S) st tail → ReplicaTree ι S (st::tail)
  | .child T => T.step st
  | .fork A B => A.tree.fork B.tree

def children : ChildForest (S := S) st tail → ℕ
  | .child _ => 1
  | .fork A B => A.children+B.children

def retained : (A : ChildForest (S := S) st tail) → List (ReplicaTree.MarkedPlacement A.tree)
  | .child T => (T.markedAttach st.1).map (ReplicaTree.MarkedPlacement.step st)
  | .fork A B =>
      (A.retained.map (ReplicaTree.MarkedPlacement.left B.tree)) ++
      (B.retained.map (ReplicaTree.MarkedPlacement.right A.tree))

def retainedRow (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : ChildForest (S := S) st tail) (P : A.tree.Assignment → ℝ) (B : S → ℝ)
    (x : ι → ℝ) : ℝ :=
  ReplicaTree.rowList w φ (A.retained.map ReplicaTree.MarkedPlacement.toPlacement) P B x

private theorem retained_child {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (T : ReplicaTree ι S tail)
    (ho : OrderedSteps st.1 tail) (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    retainedRow w φ (.child (st := st) T) P B x =
      shiftedMean (Measure.pi fun j => gaussianReal 0 (st.2 j)) st.1
        (gaussianHierarchy w φ tail) (T.row w φ st.1 P B) x := by
  unfold retainedRow retained
  rw [List.map_map]
  have he : (fun p : ReplicaTree.MarkedPlacement T =>
      (p.step st).toPlacement) = ReplicaTree.Placement.step st ∘
        ReplicaTree.MarkedPlacement.toPlacement := rfl
  simp only [Function.comp_def]
  rw [he, ← List.map_map, T.markedAttach_forget, ReplicaTree.rowList_map_step hw φ _
    st.1 st.2 ho]
  rfl

private theorem retained_fork (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A D : ChildForest (S := S) st tail)
    (P : (A.tree.fork D.tree).Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    retainedRow w φ (.fork A D) P B x =
      D.tree.expect w φ (fun τ => retainedRow w φ A (fun σ => P (σ,τ)) B x) x +
      A.tree.expect w φ (fun σ => retainedRow w φ D (fun τ => P (σ,τ)) B x) x := by
  change ReplicaTree.rowList w φ
      (((A.retained.map (ReplicaTree.MarkedPlacement.left D.tree)) ++
      (D.retained.map (ReplicaTree.MarkedPlacement.right A.tree))).map
      ReplicaTree.MarkedPlacement.toPlacement) P B x = _
  simp only [List.map_append, List.map_map]
  have he {T : ReplicaTree ι S (st::tail)} (ps qs : List (ReplicaTree.Placement T))
      (Q : T.Assignment → ℝ) :
      ReplicaTree.rowList w φ (ps++qs) Q B x =
        ReplicaTree.rowList w φ ps Q B x+ReplicaTree.rowList w φ qs Q B x := by
    simp only [ReplicaTree.rowList,List.map_append,List.sum_append]
  rw [he]
  simp only [Function.comp_def]
  have hl : (fun p : ReplicaTree.MarkedPlacement A.tree =>
      (p.left D.tree).toPlacement) =
      (ReplicaTree.Placement.left D.tree ∘ ReplicaTree.MarkedPlacement.toPlacement) := rfl
  have hr : (fun p : ReplicaTree.MarkedPlacement D.tree =>
      (p.right A.tree).toPlacement) =
      (ReplicaTree.Placement.right A.tree ∘ ReplicaTree.MarkedPlacement.toPlacement) := rfl
  rw [hl,hr,← List.map_map,← List.map_map]
  change ReplicaTree.rowList w φ
      ((A.retained.map ReplicaTree.MarkedPlacement.toPlacement).map
        (ReplicaTree.Placement.left D.tree)) P B x +
      ReplicaTree.rowList w φ
      ((D.retained.map ReplicaTree.MarkedPlacement.toPlacement).map
        (ReplicaTree.Placement.right A.tree)) P B x = _
  rw [ReplicaTree.rowList_map_left, ReplicaTree.rowList_map_right]
  rfl

theorem actual_row_grouping {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : ChildForest (S := S) st tail)
    {a : ℝ} (ho : OrderedSteps a (st::tail))
    (P : A.tree.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    A.tree.row w φ a P B x =
      (a-(A.children:ℝ)*st.1)*A.tree.expect w φ P x*
        gaussianHierarchyMean w φ B (st::tail) x + retainedRow w φ A P B x := by
  induction A with
  | child T =>
    rw [retained_child hw φ T ho.2.2.2]
    simpa only [tree, children, Nat.cast_one, one_mul] using
      ReplicaTree.row_step hw φ T st.1 st.2 ho P B x
  | fork A D ihA ihD =>
    change (A.tree.fork D.tree).row w φ a P B x = _
    rw [ReplicaTree.row_fork hw φ A.tree D.tree ho,
      retained_fork, children, Nat.cast_add]
    have ha : D.tree.expect w φ
        (fun τ => A.tree.row w φ a (fun σ => P (σ,τ)) B x) x =
      (a-(A.children:ℝ)*st.1)*(A.tree.fork D.tree).expect w φ P x*
        gaussianHierarchyMean w φ B (st::tail) x +
      D.tree.expect w φ (fun τ => retainedRow w φ A (fun σ => P (σ,τ)) B x) x := by
      simp_rw [ihA]
      rw [D.tree.expect_add]
      have h : D.tree.expect w φ
          (fun τ => (a-(A.children:ℝ)*st.1)*
            A.tree.expect w φ (fun σ => P (σ,τ)) x*
            gaussianHierarchyMean w φ B (st::tail) x) x =
          (a-(A.children:ℝ)*st.1)*(A.tree.fork D.tree).expect w φ P x*
            gaussianHierarchyMean w φ B (st::tail) x := by
        rw [ReplicaTree.expect_fork]
        simp only [ReplicaTree.expect, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro σ hσ
        apply Finset.sum_congr rfl
        intro τ hτ
        ring
      rw [h]
    have hd : A.tree.expect w φ
        (fun σ => D.tree.row w φ a (fun τ => P (σ,τ)) B x) x =
      (a-(D.children:ℝ)*st.1)*(A.tree.fork D.tree).expect w φ P x*
        gaussianHierarchyMean w φ B (st::tail) x +
      A.tree.expect w φ (fun σ => retainedRow w φ D (fun τ => P (σ,τ)) B x) x := by
      simp_rw [ihD]
      rw [A.tree.expect_add, ReplicaTree.expect_fork]
      simp only [ReplicaTree.expect, Finset.mul_sum, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro σ hσ
      apply Finset.sum_congr rfl
      intro τ hτ
      ring
    rw [ha,hd]
    ring

end ChildForest
end OAI.SKFluctuations.Cavity
