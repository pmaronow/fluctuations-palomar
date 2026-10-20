module

public import SKConstants.GramSchmidtStability
public import SKConstants.GaussianProposalQueryTrace
import Mathlib.Tactic

@[expose] public section
noncomputable section
open NormedSpace InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.GaussianProposal

lemma euclidean_norm_sq_dot {n : ℕ} (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 v‖^2 = dot v v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dot, WithLp.ofLp_toLp, pow_two]

lemma euclidean_norm_paper_row {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    ‖WithLp.toLp 2 (paperFrame E t 0)‖ = 1 := by
  have h := paperFrame_orthogonal E t hE 0 0
  have hs := euclidean_norm_sq_dot (paperFrame E t 0)
  simp only [ite_true] at h
  rw [h] at hs
  nlinarith [norm_nonneg (WithLp.toLp 2 (paperFrame E t 0))]

theorem paperFrame_eq_normalized_residual {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (hres : WithLp.toLp 2 (frameProjection E *ᵥ t) ≠ 0) :
    WithLp.toLp 2 (paperFrame E t 0) =
      NormedSpace.normalize (WithLp.toLp 2 (frameProjection E *ᵥ t)) := by
  have ht : E *ᵥ t ≠ 0 := by
    intro hz
    apply hres
    simp only [frameProjection, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero,
      WithLp.toLp_zero]
  have hd : 0 < dot (E *ᵥ t) (E *ᵥ t) :=
    lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm (by
      intro h; exact ht ((dot_self_eq_zero_iff _).mp h)))
  let a : ℝ := (Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hd)
  have he : WithLp.toLp 2 (paperFrame E t 0) =
      a • WithLp.toLp 2 (frameProjection E *ᵥ t) := by
    rw [paperFrame_projected_target E t hE ht]
    rfl
  have hn := euclidean_norm_paper_row E t hE
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hn
  have hp : ‖WithLp.toLp 2 (frameProjection E *ᵥ t)‖ ≠ 0 := norm_ne_zero_iff.mpr hres
  have hai : a = ‖WithLp.toLp 2 (frameProjection E *ᵥ t)‖⁻¹ := by
    apply (mul_right_cancel₀ hp)
    rw [hn, inv_mul_cancel₀ hp]
  rw [he, hai]
  rfl

variable {Past : Type*}

def paperTargetTrace (r n : ℕ) (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K → Fin K → Fin n → ℝ
  | 0, _, _ => fun j => Fin.elim0 j
  | K+1, s, z =>
    let F := paperFrame s.2 (target K s.1)
    Fin.cases (target K s.1) (paperTargetTrace r n target update K
      (update K s.1 z.1,tailRows F) z.2)

theorem paperDirectionTrace_eq_normalized_projection (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (z : StoppedNoise (Fin n) K) (j : Fin K)
    (hres : WithLp.toLp 2
      (paperRemainingProjectionTrace r n target update K s z j.castSucc *ᵥ
       paperTargetTrace r n target update K s z j) ≠ 0) :
    WithLp.toLp 2 (paperQueryDirectionTrace r n 1 target update K s z j) =
      NormedSpace.normalize (WithLp.toLp 2
        (paperRemainingProjectionTrace r n target update K s z j.castSucc *ᵥ
         paperTargetTrace r n target update K s z j)) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    revert hres
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hres
      simp only [paperQueryDirectionTrace, Fin.cases_zero, normalizedQuery,
        Real.sqrt_one, one_smul]
      apply paperFrame_eq_normalized_residual s.2 (target K s.1) horth
      simpa [paperRemainingProjectionTrace,paperTargetTrace] using hres

    · intro hres
      apply ih (update K s.1 z.1,tailRows F) (tailRows_orthogonal F
        (paperFrame_orthogonal s.2 (target K s.1) horth)) z.2 j
      simpa [paperRemainingProjectionTrace,paperTargetTrace] using hres

lemma sum_ite_lt_eq_sum_Iio {d : ℕ} {F : Type*} [AddCommMonoid F]
    (f : Fin d → F) (k : Fin d) :
    (∑ i : Fin d, if i < k then f i else 0) = ∑ i ∈ Finset.Iio k, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem actualPaper_residual_eq_normalized_direction_sum (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (j : Fin K) :
    WithLp.toLp 2
      (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.castSucc *ᵥ
        paperTargetTrace r (r+K) target update K (a,1) z j) =
    WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (a,1) z j) -
      ∑ i ∈ Finset.Iio j,
        ⟪WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i),
          WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (a,1) z j)⟫_ℝ •
          WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i) := by
  rw [actualPaper_remainingProjection_eq_past_queries r K 1 (by norm_num)]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  ext l
  simp only [WithLp.ofLp_toLp, WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul,
    smul_eq_mul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Matrix.mulVec,
    dotProduct, Matrix.vecMulVec_apply, inv_one, one_smul,
    EuclideanSpace.inner_toLp_toLp, Pi.star_apply, star_trivial]
  congr 1
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.vecMulVec_apply, Matrix.zero_apply, ite_mul, zero_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← sum_ite_lt_eq_sum_Iio]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : i < j
  · simp only [Fin.lt_def] at hij
    simp only [Fin.lt_def, Fin.val_castSucc, hij, ite_true]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  · simp only [Fin.lt_def] at hij
    simp only [Fin.lt_def, Fin.val_castSucc, hij, ite_false, zero_mul, Finset.sum_const_zero]

theorem actualPaper_directionTrace_eq_gramSchmidtNormed (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0 < c)
    (hGram : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j)) - 1‖ ≤ (3/4 : ℝ))
    (j : Fin K) :
    WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j) =
      gramSchmidtNormed ℝ (fun j => c • WithLp.toLp 2
        (paperTargetTrace r (r+K) target update K (a,1) z j)) j := by
  let T : Fin K → EuclideanSpace ℝ (Fin (r+K)) := fun j => c • WithLp.toLp 2
    (paperTargetTrace r (r+K) target update K (a,1) z j)
  let U : Fin K → EuclideanSpace ℝ (Fin (r+K)) := fun j => WithLp.toLp 2
    (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
  have horth : ∀ i j : Fin (r+K),
      dot ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) i)
        ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) j) = if i=j then 1 else 0 := by
    intro i j
    have hId : (1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) = canonicalBasis := by
      ext i j
      exact Matrix.one_apply
    rw [hId]
    exact canonicalBasis_orthogonal i j
  have hall : ∀ v : ℕ, ∀ j : Fin K, j.val=v → U j = gramSchmidtNormed ℝ T j := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro j hj
      let R := WithLp.toLp 2
        (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.castSucc *ᵥ
          paperTargetTrace r (r+K) target update K (a,1) z j)
      have hR : c • R = gramSchmidt ℝ T j := by
        dsimp only [R]
        rw [actualPaper_residual_eq_normalized_direction_sum]
        rw [smul_sub, Finset.smul_sum]
        rw [gramSchmidt_eq_normalized_residual]
        change T j - ∑ i ∈ Finset.Iio j,
          c • (⟪U i, WithLp.toLp 2
            (paperTargetTrace r (r+K) target update K (a,1) z j)⟫_ℝ • U i) = _
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i.val < v := by simpa [← hj] using Finset.mem_Iio.mp hi
        rw [ih i.val hij i rfl]
        dsimp only [T]
        rw [real_inner_smul_right, smul_smul]
      have hl := gramSchmidt_norm_lower_of_small_Gram T hGram j
      have hres : R ≠ 0 := by
        intro hz
        rw [hz, smul_zero] at hR
        rw [← hR, norm_zero] at hl
        norm_num at hl
      calc
        U j = NormedSpace.normalize R :=
          paperDirectionTrace_eq_normalized_projection r (r+K) target update K
            (a,1) horth z j hres
        _ = NormedSpace.normalize (c • R) := (normalize_smul_of_pos hc R).symm
        _ = gramSchmidtNormed ℝ T j := by rw [hR]; rfl
  exact hall j.val j rfl

theorem actualPaper_scaled_residual_lower (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0 < c)
    (hGram : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j)) - 1‖ ≤ (3/4 : ℝ))
    (j : Fin K) :
    (1/2 : ℝ) ≤ c * ‖WithLp.toLp 2
      (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.castSucc *ᵥ
        paperTargetTrace r (r+K) target update K (a,1) z j)‖ := by
  let T : Fin K → EuclideanSpace ℝ (Fin (r+K)) := fun j => c • WithLp.toLp 2
    (paperTargetTrace r (r+K) target update K (a,1) z j)
  have hR : c • WithLp.toLp 2
      (paperRemainingProjectionTrace r (r+K) target update K (a,1) z j.castSucc *ᵥ
        paperTargetTrace r (r+K) target update K (a,1) z j) = gramSchmidt ℝ T j := by
    rw [actualPaper_residual_eq_normalized_direction_sum, smul_sub, Finset.smul_sum,
      gramSchmidt_eq_normalized_residual]
    change T j - ∑ i ∈ Finset.Iio j, c •
      (⟪WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i),
          WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (a,1) z j)⟫_ℝ •
        WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z c hc hGram]
    dsimp only [T]
    rw [real_inner_smul_right, smul_smul]
  have hl := gramSchmidt_norm_lower_of_small_Gram T hGram j
  rw [←hR, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hl
  exact hl

theorem actualPaper_directionTrace_difference_recursive_le (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a b : Past) (z w : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0<c)
    (hA : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))-1‖≤(3/4 : ℝ))
    (hB : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (b,1) w j))-1‖≤(3/4 : ℝ))
    (j : Fin K) :
    ‖WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)-
        WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w j)‖≤
      4*((1+(K : ℝ))*‖c • WithLp.toLp 2
          (paperTargetTrace r (r+K) target update K (a,1) z j)-
        c • WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (b,1) w j)‖+
        2*‖c • WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (b,1) w j)‖*
        ∑ i ∈ Finset.Iio j, ‖WithLp.toLp 2
          (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i)-
          WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w i)‖) := by
  simp_rw [actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z c hc hA,
    actualPaper_directionTrace_eq_gramSchmidtNormed r K target update b w c hc hB]
  exact gramSchmidtNormed_difference_le _ _ hA hB j

theorem actualPaper_directionTrace_difference_le (r K : ℕ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a b : Past) (z w : StoppedNoise (Fin (r+K)) K) (c : ℝ) (hc : 0 < c)
    (hA : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j)) - 1‖ ≤ (3/4 : ℝ))
    (hB : ‖familyGram (fun j => c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (b,1) w j)) - 1‖ ≤ (3/4 : ℝ))
    (M eta : ℝ) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hBound : ∀ i, ‖c • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (b,1) w i)‖ ≤ M)
    (hDiff : ∀ i, ‖c • WithLp.toLp 2
        (paperTargetTrace r (r+K) target update K (a,1) z i) -
      c • WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (b,1) w i)‖ ≤ eta)
    (j : Fin K) :
    ‖WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j) -
      WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (b,1) w j)‖ ≤
    eta * (4*(1+(K : ℝ))+8*M*(K : ℝ))^(j.val+1) := by
  rw [actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z c hc hA,
    actualPaper_directionTrace_eq_gramSchmidtNormed r K target update b w c hc hB]
  exact gramSchmidtNormed_uniform_difference_le _ _ hA hB M eta hM heta hBound hDiff j

end SKConstants.GaussianProposal
