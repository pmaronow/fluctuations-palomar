module

public import SKConstants.EmpiricalCovariance
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section
noncomputable section
open Set NormedSpace InnerProductSpace Submodule
open scoped BigOperators InnerProductSpace RealInnerProductSpace Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

private theorem sum_dite_subtype {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]
    (f : ∀ a, p a → E) (g : ∀ a, ¬p a → E) :
    (∑ a, dite (p a) (f a) (g a)) =
      (∑ a : {a // p a}, f a a.2) + ∑ a : {a // ¬p a}, g a a.2 := by
  simp only [Finset.sum_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight (by simp)).sum_comp (fun x : {x // p x} => f x x.2)
  · exact (Equiv.subtypeEquivRight (by simp)).sum_comp (fun x : {x // ¬p x} => g x x.2)

def familyGram (T : Fin d → E) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ⟪T i, T j⟫_ℝ

def familySynthesis (T : Fin d → E) (c : EuclideanSpace ℝ (Fin d)) : E :=
  ∑ i, c i • T i

theorem familySynthesis_norm_sq (T : Fin d → E) (c : EuclideanSpace ℝ (Fin d)) :
    ‖familySynthesis T c‖^2 =
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (familyGram T) c, c⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, Concentration.matrix_quadratic_eq_sum]
  simp only [familySynthesis, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right, familyGram]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (T j) (T i)]
  ring

theorem familySynthesis_norm_sq_lower (T : Fin d → E) (eps : ℝ)
    (hGram : ‖familyGram T - 1‖ ≤ eps) (c : EuclideanSpace ℝ (Fin d)) :
    (1 - eps) * ‖c‖^2 ≤ ‖familySynthesis T c‖^2 := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (familyGram T - 1)
  have hA : ‖A‖ ≤ eps := by simpa only [A, Matrix.l2_opNorm_toEuclideanCLM] using hGram
  have hi : |⟪A c, c⟫_ℝ| ≤ eps * ‖c‖^2 := by
    calc
      _ ≤ ‖A c‖ * ‖c‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖c‖) * ‖c‖ := mul_le_mul_of_nonneg_right (A.le_opNorm c) (norm_nonneg c)
      _ ≤ (eps * ‖c‖) * ‖c‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA (norm_nonneg c)) (norm_nonneg c)
      _ = _ := by ring
  have he : ⟪A c, c⟫_ℝ = ‖familySynthesis T c‖^2 - ‖c‖^2 := by
    dsimp only [A]
    rw [map_sub, sub_apply, map_one]
    change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (familyGram T) c - c, c⟫_ℝ = _
    rw [inner_sub_left,
      real_inner_self_eq_norm_sq, familySynthesis_norm_sq]
  rw [he] at hi
  linarith [(neg_le_abs (‖familySynthesis T c‖^2 - ‖c‖^2)).trans hi]

theorem familySynthesis_norm_sq_upper (T : Fin d → E) (eps : ℝ)
    (hGram : ‖familyGram T-1‖≤eps) (c : EuclideanSpace ℝ (Fin d)) :
    ‖familySynthesis T c‖^2≤(1+eps)*‖c‖^2 := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (familyGram T-1)
  have hA : ‖A‖≤eps := by simpa only [A,Matrix.l2_opNorm_toEuclideanCLM] using hGram
  have hi : |⟪A c,c⟫_ℝ|≤eps*‖c‖^2 := by
    calc
      _ ≤ ‖A c‖*‖c‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖*‖c‖)*‖c‖ := mul_le_mul_of_nonneg_right (A.le_opNorm c) (norm_nonneg c)
      _ ≤ (eps*‖c‖)*‖c‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA (norm_nonneg c)) (norm_nonneg c)
      _ = _ := by ring
  have he : ⟪A c,c⟫_ℝ=‖familySynthesis T c‖^2-‖c‖^2 := by
    dsimp only [A]
    rw [map_sub,sub_apply,map_one]
    change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (familyGram T) c-c,c⟫_ℝ=_
    rw [inner_sub_left,real_inner_self_eq_norm_sq,familySynthesis_norm_sq]
  rw [he] at hi
  linarith [(le_abs_self (‖familySynthesis T c‖^2-‖c‖^2)).trans hi]

theorem familyGram_small_vector_norm_le (T : Fin d → E)
    (hGram : ‖familyGram T-1‖≤(3/4 : ℝ)) (k : Fin d) : ‖T k‖≤2 := by
  let c : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i=>if i=k then 1 else 0)
  have hc : ‖c‖^2=1 := by
    simp [EuclideanSpace.real_norm_sq_eq,c]
  have he : familySynthesis T c=T k := by
    simp [familySynthesis,c]
  have h := familySynthesis_norm_sq_upper T (3/4) hGram c
  rw [he,hc] at h
  nlinarith [norm_nonneg (T k)]

theorem familyGram_small_residual_lower (T : Fin d → E)
    (hGram : ‖familyGram T - 1‖ ≤ (3 / 4 : ℝ)) (k : Fin d)
    (y : E) (hy : y ∈ Submodule.span ℝ (T '' {i | i ≠ k})) :
    (1 / 2 : ℝ) ≤ ‖T k - y‖ := by
  obtain ⟨a, ha⟩ := (Fintype.mem_span_image_iff_exists_fun ℝ).mp hy
  let c : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
    (fun i => if h : i = k then 1 else -a ⟨i, h⟩)
  have hc : c k = 1 := by simp [c]
  have he : familySynthesis T c = T k - y := by
    rw [← ha]
    unfold familySynthesis c
    simp only [WithLp.ofLp_toLp, dite_smul, neg_smul]
    rw [sum_dite_subtype]
    simp only [one_smul, Finset.sum_neg_distrib]
    simp only [Fintype.sum_unique]
    have hdk : (default : {i : Fin d // i = k}).val = k :=
      (default : {i : Fin d // i = k}).property
    rw [hdk]
    simp only [sub_eq_add_neg, Subtype.eta]
    congr 2
  have hn : 1 ≤ ‖c‖^2 := by
    have hp := Finset.single_le_sum (f := fun i : Fin d => (c i)^2)
      (fun i _ => sq_nonneg (c i)) (Finset.mem_univ k)
    simpa only [hc, one_pow, EuclideanSpace.real_norm_sq_eq] using hp
  have h := familySynthesis_norm_sq_lower T (3 / 4) hGram c
  rw [he] at h
  nlinarith [norm_nonneg (T k - y)]

theorem normalize_difference_le (x y : E) (c : ℝ) (hc : 0 < c)
    (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖normalize x - normalize y‖ ≤ (2 / c) * ‖x - y‖ := by
  have hyn : y ≠ 0 := norm_pos_iff.mp (hc.trans_le hy)
  have hunit : ‖normalize y‖ = 1 := norm_normalize hyn
  have hs : ‖x‖ * ‖normalize x - normalize y‖ =
      ‖x - ‖x‖ • normalize y‖ := by
    rw [← norm_smul_of_nonneg (norm_nonneg x), smul_sub, norm_smul_normalize]
  have hsecond : ‖y - ‖x‖ • normalize y‖ = |‖y‖ - ‖x‖| := by
    calc
      _ = ‖‖y‖ • normalize y - ‖x‖ • normalize y‖ := by
        rw [norm_smul_normalize]
      _ = _ := by
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, hunit, mul_one]
  have hb : ‖x‖ * ‖normalize x - normalize y‖ ≤ 2 * ‖x - y‖ := by
    rw [hs]
    have ht : ‖x - ‖x‖ • normalize y‖ ≤ ‖x - y‖ + ‖y - ‖x‖ • normalize y‖ := by
      simpa only [dist_eq_norm] using dist_triangle x y (‖x‖ • normalize y)
    rw [hsecond] at ht
    have ha := abs_norm_sub_norm_le y x
    rw [norm_sub_rev] at ha
    linarith
  have hl := mul_le_mul_of_nonneg_right hx (norm_nonneg (normalize x - normalize y))
  have h : c * ‖normalize x - normalize y‖ ≤ 2 * ‖x - y‖ := hl.trans hb
  rw [mul_comm c] at h
  rw [← le_div_iff₀ hc] at h
  convert h using 1 <;> ring

def familyProjection (u : Fin d → E) (x : E) : E := ∑ i, ⟪u i, x⟫_ℝ • u i

theorem unit_rankOne_difference_le (u v x y : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖⟪u, x⟫_ℝ • u - ⟪v, y⟫_ℝ • v‖ ≤
      ‖x - y‖ + 2 * ‖y‖ * ‖u - v‖ := by
  have he : ⟪u, x⟫_ℝ • u - ⟪v, y⟫_ℝ • v =
      ⟪u, x - y⟫_ℝ • u + ⟪u - v, y⟫_ℝ • u + ⟪v, y⟫_ℝ • (u - v) := by
    simp only [inner_sub_right, inner_sub_left]
    module
  rw [he]
  have ht := (norm_add_le (⟪u, x - y⟫_ℝ • u + ⟪u - v, y⟫_ℝ • u)
    (⟪v, y⟫_ℝ • (u - v))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  simp only [norm_smul, Real.norm_eq_abs, hu, hv, mul_one] at ht
  have h1 := abs_real_inner_le_norm u (x - y)
  have h2 := abs_real_inner_le_norm (u - v) y
  have h3 := abs_real_inner_le_norm v y
  rw [hu, one_mul] at h1
  rw [hv, one_mul] at h3
  have h3' := mul_le_mul_of_nonneg_right h3 (norm_nonneg (u - v))
  nlinarith

theorem unit_family_projection_difference_le (u v : Fin d → E)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (x y : E) :
    ‖familyProjection u x - familyProjection v y‖ ≤
      (d : ℝ) * ‖x - y‖ + 2 * ‖y‖ * ∑ i, ‖u i - v i‖ := by
  unfold familyProjection
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin d, (‖x - y‖ + 2 * ‖y‖ * ‖u i - v i‖) :=
      Finset.sum_le_sum (fun i _ => unit_rankOne_difference_le (u i) (v i) x y (hu i) (hv i))
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem unit_family_residual_difference_le (u v : Fin d → E)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (x y : E) :
    ‖(x - familyProjection u x) - (y - familyProjection v y)‖ ≤
      (1 + (d : ℝ)) * ‖x - y‖ + 2 * ‖y‖ * ∑ i, ‖u i - v i‖ := by
  have he : (x - familyProjection u x) - (y - familyProjection v y) =
      (x - y) - (familyProjection u x - familyProjection v y) := by abel
  rw [he]
  have ht := norm_sub_le (x - y) (familyProjection u x - familyProjection v y)
  have hp := unit_family_projection_difference_le u v hu hv x y
  linarith

theorem gramSchmidt_correction_mem_span (T : Fin d → E) (k : Fin d) :
    T k - gramSchmidt ℝ T k ∈ Submodule.span ℝ (T '' {i | i ≠ k}) := by
  rw [gramSchmidt_def]
  simp only [sub_sub_cancel]
  apply Submodule.sum_mem
  intro i hi
  rw [starProjection_singleton]
  apply Submodule.smul_mem
  apply Submodule.span_mono (Set.image_mono ?_)
    (gramSchmidt_mem_span ℝ T (le_refl i))
  intro j hj
  exact ne_of_lt (hj.trans_lt (Finset.mem_Iio.mp hi))

theorem gramSchmidt_norm_lower_of_small_Gram (T : Fin d → E)
    (hGram : ‖familyGram T - 1‖ ≤ (3 / 4 : ℝ)) (k : Fin d) :
    (1 / 2 : ℝ) ≤ ‖gramSchmidt ℝ T k‖ := by
  have h := familyGram_small_residual_lower T hGram k
    (T k - gramSchmidt ℝ T k) (gramSchmidt_correction_mem_span T k)
  simpa only [sub_sub_cancel] using h

theorem gramSchmidtNormed_norm_of_small_Gram (T : Fin d → E)
    (hGram : ‖familyGram T - 1‖ ≤ (3 / 4 : ℝ)) (k : Fin d) :
    ‖gramSchmidtNormed ℝ T k‖ = 1 := by
  apply norm_normalize
  have h := gramSchmidt_norm_lower_of_small_Gram T hGram k
  exact norm_pos_iff.mp (by linarith)

theorem starProjection_singleton_eq_normalized (w x : E) :
    (ℝ ∙ w).starProjection x = ⟪normalize w, x⟫_ℝ • normalize w := by
  rw [starProjection_singleton]
  simp only [NormedSpace.normalize, real_inner_smul_left, smul_smul, div_eq_mul_inv,
    inv_pow, RCLike.ofReal_real_eq_id, id_eq]
  congr 1
  ring

theorem gramSchmidt_eq_normalized_residual (T : Fin d → E) (k : Fin d) :
    gramSchmidt ℝ T k = T k - ∑ i ∈ Finset.Iio k,
      ⟪gramSchmidtNormed ℝ T i, T k⟫_ℝ • gramSchmidtNormed ℝ T i := by
  rw [gramSchmidt_def]
  simp only [starProjection_singleton_eq_normalized]
  rfl

theorem gramSchmidtNormed_difference_le (T S : Fin d → E)
    (hT : ‖familyGram T - 1‖ ≤ (3 / 4 : ℝ))
    (hS : ‖familyGram S - 1‖ ≤ (3 / 4 : ℝ)) (k : Fin d) :
    ‖gramSchmidtNormed ℝ T k - gramSchmidtNormed ℝ S k‖ ≤
      4 * ((1 + (d : ℝ)) * ‖T k - S k‖ + 2 * ‖S k‖ *
        ∑ i ∈ Finset.Iio k, ‖gramSchmidtNormed ℝ T i - gramSchmidtNormed ℝ S i‖) := by
  have hn := normalize_difference_le (gramSchmidt ℝ T k) (gramSchmidt ℝ S k)
    (1/2) (by norm_num) (gramSchmidt_norm_lower_of_small_Gram T hT k)
    (gramSchmidt_norm_lower_of_small_Gram S hS k)
  change ‖gramSchmidtNormed ℝ T k - gramSchmidtNormed ℝ S k‖ ≤
    (2 / (1/2 : ℝ)) * ‖gramSchmidt ℝ T k - gramSchmidt ℝ S k‖ at hn
  norm_num only at hn
  refine hn.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [gramSchmidt_eq_normalized_residual, gramSchmidt_eq_normalized_residual]
  have he : (T k - ∑ i ∈ Finset.Iio k,
      ⟪gramSchmidtNormed ℝ T i,T k⟫_ℝ • gramSchmidtNormed ℝ T i) -
    (S k - ∑ i ∈ Finset.Iio k,
      ⟪gramSchmidtNormed ℝ S i,S k⟫_ℝ • gramSchmidtNormed ℝ S i) =
    (T k - S k) - ∑ i ∈ Finset.Iio k,
      (⟪gramSchmidtNormed ℝ T i,T k⟫_ℝ • gramSchmidtNormed ℝ T i -
       ⟪gramSchmidtNormed ℝ S i,S k⟫_ℝ • gramSchmidtNormed ℝ S i) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  have hs := norm_sum_le (Finset.Iio k) (fun i =>
    ⟪gramSchmidtNormed ℝ T i,T k⟫_ℝ • gramSchmidtNormed ℝ T i -
    ⟪gramSchmidtNormed ℝ S i,S k⟫_ℝ • gramSchmidtNormed ℝ S i)
  have hb := Finset.sum_le_sum (s := Finset.Iio k) (fun i _ =>
    unit_rankOne_difference_le (gramSchmidtNormed ℝ T i) (gramSchmidtNormed ℝ S i)
      (T k) (S k) (gramSchmidtNormed_norm_of_small_Gram T hT i)
      (gramSchmidtNormed_norm_of_small_Gram S hS i))
  have hc : ((Finset.Iio k).card : ℝ) ≤ d := by
    exact_mod_cast (show (Finset.Iio k).card ≤ d by
      simpa using Finset.card_le_card (Finset.subset_univ (Finset.Iio k)))
  have hb' : ‖∑ i ∈ Finset.Iio k,
      (⟪gramSchmidtNormed ℝ T i,T k⟫_ℝ • gramSchmidtNormed ℝ T i -
       ⟪gramSchmidtNormed ℝ S i,S k⟫_ℝ • gramSchmidtNormed ℝ S i)‖ ≤
    (d : ℝ)*‖T k-S k‖ + 2*‖S k‖*
      ∑ i ∈ Finset.Iio k, ‖gramSchmidtNormed ℝ T i-gramSchmidtNormed ℝ S i‖ := by
    apply (hs.trans hb).trans
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    gcongr
  linarith

theorem gramSchmidtNormed_uniform_difference_le (T S : Fin d → E)
    (hT : ‖familyGram T - 1‖ ≤ (3 / 4 : ℝ))
    (hS : ‖familyGram S - 1‖ ≤ (3 / 4 : ℝ))
    (M eta : ℝ) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hBound : ∀ i, ‖S i‖ ≤ M) (hDiff : ∀ i, ‖T i - S i‖ ≤ eta)
    (k : Fin d) :
    ‖gramSchmidtNormed ℝ T k - gramSchmidtNormed ℝ S k‖ ≤
      eta * (4 * (1 + (d : ℝ)) + 8 * M * (d : ℝ)) ^ (k.val + 1) := by
  let B : ℝ := 4 * (1 + (d : ℝ)) + 8 * M * (d : ℝ)
  have hB : 1 ≤ B := by
    dsimp [B]
    have hm : 0 ≤ 8*M*(d : ℝ) := by positivity
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have haux : ∀ a : ℕ, ∀ j : Fin d, j.val = a →
      ‖gramSchmidtNormed ℝ T j - gramSchmidtNormed ℝ S j‖ ≤ eta * B^(a+1) := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hj
      have hsum : ∑ i ∈ Finset.Iio j,
          ‖gramSchmidtNormed ℝ T i - gramSchmidtNormed ℝ S i‖ ≤
          (d : ℝ) * (eta * B^a) := by
        calc
          _ ≤ ∑ i ∈ Finset.Iio j, eta * B^a := by
            apply Finset.sum_le_sum
            intro i hi
            have hij : i.val < a := by simpa [← hj] using Finset.mem_Iio.mp hi
            apply (ih i.val hij i rfl).trans
            gcongr
            exact Nat.succ_le_of_lt hij
          _ = ((Finset.Iio j).card : ℝ) * (eta * B^a) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by
            gcongr
            exact_mod_cast (show (Finset.Iio j).card ≤ d by
              simpa using Finset.card_le_card (Finset.subset_univ (Finset.Iio j)))
      have he : eta ≤ eta * B^a := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hB) heta
      calc
        _ ≤ 4 * ((1 + (d : ℝ))*‖T j-S j‖ + 2*‖S j‖*
            ∑ i ∈ Finset.Iio j, ‖gramSchmidtNormed ℝ T i-gramSchmidtNormed ℝ S i‖) :=
          gramSchmidtNormed_difference_le T S hT hS j
        _ ≤ 4 * ((1 + (d : ℝ))*(eta*B^a) + 2*M*((d : ℝ)*(eta*B^a))) := by
          gcongr
          exact (hDiff j).trans he
          exact hBound j
        _ = eta * B^(a+1) := by rw [pow_succ]; dsimp [B]; ring
  exact haux k.val k rfl

end SKConstants
