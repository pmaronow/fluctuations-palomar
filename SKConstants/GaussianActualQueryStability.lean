module

public import SKConstants.GaussianProposalTraceSteps
public import SKConstants.GaussianDirectionProjectionStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open NormedSpace InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.GaussianProposal
variable {Past : Type*}

theorem actualPaper_directionTrace_norm (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0<c)
    (hGram : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))-1‖≤(3/4 : ℝ))
    (j : Fin K) :
    ‖WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)‖=1 := by
  rw [actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z c hc hGram]
  exact gramSchmidtNormed_norm_of_small_Gram _ hGram j

theorem actualPaper_remainingProjection_apply_norm_le (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (j : Fin (K+1))
    (x : EuclideanSpace ℝ (Fin (r+K))) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j) x‖≤‖x‖ := by
  apply paperRemainingProjectionTrace_apply_norm_le
  intro i j
  have hId : (1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)=canonicalBasis := by
    ext i j
    exact Matrix.one_apply
  rw [hId]
  exact canonicalBasis_orthogonal i j

theorem actualPaper_remainingProjection_eq_queries_Iic (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (j : Fin K) :
    paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.succ =
      1-∑ i∈Finset.Iic j, Matrix.vecMulVec
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i)
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i) := by
  rw [actualPaper_remainingProjection_eq_past_queries r K 1 (by norm_num)]
  simp only [inv_one,one_smul]
  rw [←Finset.sum_filter]
  have hI : Finset.univ.filter (fun i : Fin K => i.val<j.succ.val)=Finset.Iic j := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic,Fin.le_def,Fin.val_succ]
    omega
  rw [hI]

theorem actualPaper_remainingProjection_difference_le (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a b : Past) (z w : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0<c)
    (hA : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))-1‖≤(3/4 : ℝ))
    (hB : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (b,1) w j))-1‖≤(3/4 : ℝ))
    (j : Fin K) :
    ‖paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.succ-
      paperRemainingProjectionTrace r (r+K) target update K (b,1) w j.succ‖≤
      2*∑ i∈Finset.Iic j, ‖WithLp.toLp 2
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i)-
        WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w i)‖ := by
  rw [actualPaper_remainingProjection_eq_queries_Iic,actualPaper_remainingProjection_eq_queries_Iic]
  simpa only [WithLp.ofLp_toLp] using directionSetRemainingProjection_difference_le
    (Finset.Iic j)
    (fun i => WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i))
    (fun i => WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w i))
    (fun i _ => actualPaper_directionTrace_norm r K target update a z c hc hA i)
    (fun i _ => actualPaper_directionTrace_norm r K target update b w c hc hB i)

theorem actualPaper_completedEndpoint_difference_le (r K : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a b : Past) (z w : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0<c)
    (hA : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))-1‖≤(3/4 : ℝ))
    (hB : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (b,1) w j))-1‖≤(3/4 : ℝ))
    (W W' : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)
    (g g' : EuclideanSpace ℝ (Fin (r+K))) (j : Fin K) :
    ‖completedMatrixEndpoint
        (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.succ) W
        (WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) N target update K (a,1) z j)) g-
      completedMatrixEndpoint
        (paperRemainingProjectionTrace r (r+K) target update K (b,1) w j.succ) W'
        (WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) N target update K (b,1) w j)) g'‖≤
      Real.sqrt N*‖W-W'‖+
      Real.sqrt N*‖W'‖*‖WithLp.toLp 2
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)-
        WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w j)‖+
      (2*∑ i∈Finset.Iic j, ‖WithLp.toLp 2
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i)-
        WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w i)‖)*
        (Real.sqrt N*‖W'‖+‖g‖)+2*‖g-g'‖ := by
  have h := completedMatrixEndpoint_difference_with_completion_le
    (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.succ)
    (paperRemainingProjectionTrace r (r+K) target update K (b,1) w j.succ) W W'
    (WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) N target update K (a,1) z j))
    (WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) N target update K (b,1) w j)) g g'
    (actualPaper_remainingProjection_apply_norm_le r K target update a z j.succ)
    (actualPaper_remainingProjection_apply_norm_le r K target update b w j.succ)
  have hu : ‖WithLp.toLp 2
      (paperQueryDirectionTrace r (r+K) N target update K (a,1) z j)‖=Real.sqrt N := by
    rw [paperQueryDirectionTrace_scale,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg N),actualPaper_directionTrace_norm r K target update a z c hc hA,mul_one]
  have hv : ‖WithLp.toLp 2
      (paperQueryDirectionTrace r (r+K) N target update K (b,1) w j)‖=Real.sqrt N := by
    rw [paperQueryDirectionTrace_scale,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg N),actualPaper_directionTrace_norm r K target update b w c hc hB,mul_one]
  have hd : ‖WithLp.toLp 2
      (paperQueryDirectionTrace r (r+K) N target update K (a,1) z j)-
      WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) N target update K (b,1) w j)‖=
      Real.sqrt N*‖WithLp.toLp 2
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)-
        WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w j)‖ := by
    rw [paperQueryDirectionTrace_scale r (r+K) N target update K (a,1) z j,
      paperQueryDirectionTrace_scale r (r+K) N target update K (b,1) w j,
      ←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg N)]
  rw [hu,hv,hd] at h
  have hp := actualPaper_remainingProjection_difference_le r K target update a b z w c hc hA hB j
  have hp' := mul_le_mul_of_nonneg_right hp
    (add_nonneg (mul_nonneg (norm_nonneg W') (Real.sqrt_nonneg N)) (norm_nonneg g))
  nlinarith

end SKConstants.GaussianProposal
