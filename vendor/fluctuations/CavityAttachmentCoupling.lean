module

public import CavityScalarRowBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem actual_attachment_new_marginal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (p : ReplicaTree.MarkedPlacement T) (F : S → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ (fun σ => F (p.spin σ)) x =
      gaussianHierarchyMean w φ F steps x := by
  simp only [p.spin_at]
  exact p.tree.expect_atSlot hw φ ho p.mark F x

theorem actual_attachment_centered_product {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (p : ReplicaTree.MarkedPlacement T) (hp : p ∈ T.markedAttach a)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    p.toPlacement.eval w φ P F x -
        T.expect w φ P x*gaussianHierarchyMean w φ F steps x =
      p.tree.expect w φ (fun σ =>
        (P (p.restrict σ)-T.expect w φ P x)*
        (F (p.spin σ)-gaussianHierarchyMean w φ F steps x)) x := by
  let mP := T.expect w φ P x
  let mF := gaussianHierarchyMean w φ F steps x
  have hP := T.markedAttach_preserves hw φ ho p hp P x
  have hF := actual_attachment_new_marginal hw φ T ho p F x
  have hfun : (fun σ => (P (p.restrict σ)-mP)*(F (p.spin σ)-mF)) =
      fun σ => P (p.restrict σ)*F (p.spin σ)+(-mF)*P (p.restrict σ)+
        (-mP)*F (p.spin σ)+mP*mF := by
    funext σ
    ring
  change p.toPlacement.eval w φ P F x-mP*mF = _
  rw [hfun]
  simp only [ReplicaTree.expect_add, ReplicaTree.expect_const_mul,
    p.tree.expect_const hw φ ho, hP, hF]
  change p.toPlacement.eval w φ P F x-mP*mF =
    p.toPlacement.eval w φ P F x+(-mF)*mP+(-mP)*mF+mP*mF
  ring

theorem actual_attachment_constant_collapse {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (a z : ℝ) :
    ((T.markedAttach a).map (fun p => p.coeff*z)).sum = a*z := by
  rw [List.sum_map_mul_right, T.markedAttach_mass]

end OAI.SKFluctuations.Cavity
