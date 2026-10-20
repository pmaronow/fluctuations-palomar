module

public import SKConstants.GaussianProposalEndpointStability
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

@[expose] public section
noncomputable section
open NormedSpace InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.GaussianProposal

theorem toEuclideanCLM_vecMulVec_apply {n : ℕ}
    (u v x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.vecMulVec (fun i=>u i) (fun i=>v i)) x =
      ⟪v,x⟫_ℝ • u := by
  have h := congrArg (Matrix.toEuclideanLin (𝕜 := ℝ))
    (InnerProductSpace.symm_toEuclideanLin_rankOne u v)
  simp only [LinearEquiv.apply_symm_apply,star_trivial] at h
  change Matrix.toEuclideanLin _ x = _
  rw [←h]
  rfl

def directionRemainingProjection {n d : ℕ}
    (u : Fin d → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  1-∑ i, Matrix.vecMulVec (fun j=>u i j) (fun j=>u i j)

theorem directionRemainingProjection_apply {n d : ℕ}
    (u : Fin d → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (directionRemainingProjection u) x =
      x-familyProjection u x := by
  unfold directionRemainingProjection familyProjection
  simp only [map_sub,map_one,map_sum,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.sum_apply,
    toEuclideanCLM_vecMulVec_apply]

theorem directionRemainingProjection_difference_le {n d : ℕ}
    (u v : Fin d → EuclideanSpace ℝ (Fin n))
    (hu : ∀ i, ‖u i‖=1) (hv : ∀ i, ‖v i‖=1) :
    ‖directionRemainingProjection u-directionRemainingProjection v‖≤
      2*∑ i, ‖u i-v i‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [map_sub,ContinuousLinearMap.sub_apply,
    directionRemainingProjection_apply,directionRemainingProjection_apply]
  have he : (x-familyProjection u x)-(x-familyProjection v x) =
      -(familyProjection u x-familyProjection v x) := by abel
  rw [he,norm_neg]
  have h := unit_family_projection_difference_le u v hu hv x x
  simp only [sub_self,norm_zero,mul_zero,zero_add] at h
  exact h.trans_eq (by ring)

theorem unit_vecMulVec_difference_norm_le {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖Matrix.vecMulVec (fun i=>u i) (fun i=>u i)-
      Matrix.vecMulVec (fun i=>v i) (fun i=>v i)‖≤2*‖u-v‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [map_sub,ContinuousLinearMap.sub_apply,
    toEuclideanCLM_vecMulVec_apply,toEuclideanCLM_vecMulVec_apply]
  have h := unit_rankOne_difference_le u v x x hu hv
  simp only [sub_self,norm_zero,zero_add] at h
  exact h.trans_eq (by ring)

theorem directionSetRemainingProjection_difference_le {n : ℕ} {ι : Type*}
    (I : Finset ι) (u v : ι → EuclideanSpace ℝ (Fin n))
    (hu : ∀ i∈I, ‖u i‖=1) (hv : ∀ i∈I, ‖v i‖=1) :
    ‖(1-∑ i∈I, Matrix.vecMulVec (fun j=>u i j) (fun j=>u i j))-
      (1-∑ i∈I, Matrix.vecMulVec (fun j=>v i j) (fun j=>v i j))‖≤
      2*∑ i∈I, ‖u i-v i‖ := by
  have he : (1-∑ i∈I, Matrix.vecMulVec (fun j=>u i j) (fun j=>u i j))-
      (1-∑ i∈I, Matrix.vecMulVec (fun j=>v i j) (fun j=>v i j)) =
      -(∑ i∈I, (Matrix.vecMulVec (fun j=>u i j) (fun j=>u i j)-
        Matrix.vecMulVec (fun j=>v i j) (fun j=>v i j))) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [he,norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i∈I, 2*‖u i-v i‖ := Finset.sum_le_sum (fun i hi =>
      unit_vecMulVec_difference_norm_le (u i) (v i) (hu i hi) (hv i hi))
    _ = _ := by rw [Finset.mul_sum]

end SKConstants.GaussianProposal
