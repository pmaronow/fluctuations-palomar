module

public import CavityAttachmentCoupling
public import CavityMomentAllocation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem actual_preserving_attachment_centered_product {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (p : ReplicaTree.MarkedPlacement T)
    (hp : p.toPlacement.Preserves w φ)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    p.toPlacement.eval w φ P F x -
        T.expect w φ P x*gaussianHierarchyMean w φ F steps x =
      p.tree.expect w φ (fun σ =>
        (P (p.restrict σ)-T.expect w φ P x)*
        (F (p.spin σ)-gaussianHierarchyMean w φ F steps x)) x := by
  let mP := T.expect w φ P x
  let mF := gaussianHierarchyMean w φ F steps x
  have hP := hp P x
  have hF := actual_attachment_new_marginal hw φ T ho p F x
  have hfun : (fun σ => (P (p.restrict σ)-mP)*(F (p.spin σ)-mF)) =
      fun σ => P (p.restrict σ)*F (p.spin σ)+(-mF)*P (p.restrict σ)+
        (-mP)*F (p.spin σ)+mP*mF := by funext σ; ring
  change p.toPlacement.eval w φ P F x-mP*mF = _
  rw [hfun]
  simp only [ReplicaTree.expect_add, ReplicaTree.expect_const_mul,
    p.tree.expect_const hw φ ho, hP, hF]
  change p.toPlacement.eval w φ P F x-mP*mF =
    p.toPlacement.eval w φ P F x+(-mF)*mP+(-mP)*mF+mP*mF
  ring

theorem actual_preserving_attachment_covariance_sq_le {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (p : ReplicaTree.MarkedPlacement T)
    (hp : p.toPlacement.Preserves w φ)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    (p.toPlacement.eval w φ P F x -
        T.expect w φ P x*gaussianHierarchyMean w φ F steps x)^2 ≤
      T.expect w φ (fun σ => (P σ-T.expect w φ P x)^2) x *
        gaussianHierarchyMean w φ
          (fun σ => (F σ-gaussianHierarchyMean w φ F steps x)^2) steps x := by
  rw [actual_preserving_attachment_centered_product hw φ T ho p hp]
  have h := p.tree.expect_mul_sq_le hw φ ho
    (fun σ => P (p.restrict σ)-T.expect w φ P x)
    (fun σ => F (p.spin σ)-gaussianHierarchyMean w φ F steps x) x
  rw [hp (fun σ => (P σ-T.expect w φ P x)^2) x,
    actual_attachment_new_marginal hw φ T ho p
      (fun σ => (F σ-gaussianHierarchyMean w φ F steps x)^2) x] at h
  exact h

theorem actual_fork_resampling_eq_twice_variance {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (T.fork T).expect w φ (fun σ => (P σ.1-P σ.2)^2) x =
      2*T.expect w φ (fun σ => (P σ-T.expect w φ P x)^2) x := by
  let m := T.expect w φ P x
  have hfun : (fun σ : (T.fork T).Assignment => (P σ.1-P σ.2)^2) =
      fun σ => (P σ.1)^2*1+(-2)*(P σ.1*P σ.2)+1*(P σ.2)^2 := by
    funext σ; ring
  have hvar : (fun σ => (P σ-m)^2) =
      fun σ => (P σ)^2+(-2*m)*P σ+m^2 := by funext σ; ring
  rw [hfun, hvar]
  have hleft : (T.fork T).expect w φ (fun σ => (P σ.1)^2*1) x =
      T.expect w φ (fun σ => (P σ)^2) x := by
    rw [ReplicaTree.expect_fork]
    simp only [T.expect_const hw φ ho, mul_one]
  have hright : (T.fork T).expect w φ (fun σ => (P σ.2)^2) x =
      T.expect w φ (fun σ => (P σ)^2) x := by
    rw [ReplicaTree.expect_fork]
    simp only [T.expect_const hw φ ho]
  simp only [ReplicaTree.expect_add, ReplicaTree.expect_const_mul,
    hleft, hright, ReplicaTree.expect_fork_product, T.expect_const hw φ ho]
  dsimp only [m]
  ring

end OAI.SKFluctuations.Cavity
