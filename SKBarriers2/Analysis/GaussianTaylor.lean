module

public import SKBarriers2.Analysis.GaussianJets

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace SKBarriers2
namespace QBoundedJets

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {r : ℕ} {B : ℝ} {f : E → F}

theorem linear_taylor_remainder_le (hf : QBoundedJets 2 B f) (x y : E) :
    ‖f (x + y) - f x - fderiv ℝ f x y‖ ≤ B * ‖y‖ ^ 2 := by
  let R : ℝ → F := fun t => f (x + t • y) - t • fderiv ℝ f x y
  let D : ℝ → F := fun t => (fderiv ℝ f (x + t • y) - fderiv ℝ f x) y
  have hd (t : ℝ) : HasDerivAt R (D t) t := by
    have hl : HasDerivAt (fun a : ℝ => x + a • y) y t := by
      convert! (((hasDerivAt_id t).smul_const y).const_add x) using 1
      simp only [one_smul]
    have hdiff : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
    convert! ((hdiff (x + t • y)).hasFDerivAt.comp_hasDerivAt t hl).sub
      ((hasDerivAt_id t).smul_const (fderiv ℝ f x y)) using 1
    simp only [D, sub_apply, one_smul]
  have hLip : LipschitzWith ⟨B, hf.nonneg⟩ (fderiv ℝ f) := hf.derivativeJets.lipschitzWith
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (C := B * ‖y‖ ^ 2) (by
      intro t ht
      have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
      have hL : ‖fderiv ℝ f (x + t • y) - fderiv ℝ f x‖ ≤ B * (|t| * ‖y‖) := by
        have hdist := hLip.dist_le_mul (x + t • y) x
        change dist (fderiv ℝ f (x + t • y)) (fderiv ℝ f x) ≤ B * dist (x + t • y) x at hdist
        simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using hdist
      calc
        ‖D t‖ ≤ ‖fderiv ℝ f (x + t • y) - fderiv ℝ f x‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm _ y
        _ ≤ (B * (|t| * ‖y‖)) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hL (norm_nonneg y)
        _ ≤ (B * (1 * ‖y‖)) * ‖y‖ := by
          gcongr
          exact hf.nonneg
        _ = B * ‖y‖ ^ 2 := by ring)
  have he : R 1 - R 0 = f (x + y) - f x - fderiv ℝ f x y := by
    simp only [R, one_smul, zero_smul, add_zero, sub_zero]
    module
  rw [he] at h
  exact h

variable [CompleteSpace F]

theorem norm_gaussianAverage_sub_le (hf : QBoundedJets 2 B f) (v x : E) :
    ‖SKBarriers2.gaussianAverage v f x - f x‖ ≤ B * ‖v‖ ^ 2 := by
  let R : ℝ → F := fun t => f (x + t • v) - f x - t • fderiv ℝ f x v
  have hi : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable (by simp)
  have hiR : Integrable R (gaussianReal 0 1) :=
    ((hf.integrable_shift v x).sub (integrable_const _)).sub (hi.smul_const _)
  have hR (t : ℝ) : ‖R t‖ ≤ (B * ‖v‖ ^ 2) * t ^ 2 := by
    calc
      ‖R t‖ = ‖f (x + t • v) - f x - fderiv ℝ f x (t • v)‖ := by
        rw [map_smul]
      _ ≤ B * ‖t • v‖ ^ 2 := hf.linear_taylor_remainder_le x (t • v)
      _ = (B * ‖v‖ ^ 2) * t ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
  have heq : (∫ t : ℝ, R t ∂gaussianReal 0 1) = SKBarriers2.gaussianAverage v f x - f x := by
    have hi0 : Integrable (fun _ : ℝ => f x) (gaussianReal 0 1) := integrable_const _
    have hi1 : Integrable (fun t : ℝ => t • fderiv ℝ f x v) (gaussianReal 0 1) := hi.smul_const _
    dsimp only [R]
    rw [integral_sub (f := fun t : ℝ => f (x + t • v) - f x)
      (g := fun t : ℝ => t • fderiv ℝ f x v) ((hf.integrable_shift v x).sub hi0) hi1,
      integral_sub (f := fun t : ℝ => f (x + t • v)) (g := fun _ : ℝ => f x)
        (hf.integrable_shift v x) hi0, integral_const,
      integral_smul_const, integral_id_gaussianReal]
    simp only [probReal_univ, one_smul, zero_smul, sub_zero, SKBarriers2.gaussianAverage]
  rw [← heq]
  calc
    ‖∫ t : ℝ, R t ∂gaussianReal 0 1‖ ≤ ∫ t : ℝ, ‖R t‖ ∂gaussianReal 0 1 :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (B * ‖v‖ ^ 2) * t ^ 2 ∂gaussianReal 0 1 := by
      apply integral_mono hiR.norm
        ((OAI.SK.Analytic.gaussian_abs_pow_integrable 2).congr (by
          exact ae_of_all _ (fun t => by simp only [sq_abs])) |>.const_mul _)
      exact hR
    _ = B * ‖v‖ ^ 2 := by
      rw [integral_const_mul, OAI.SK.Analytic.gaussian_second_moment, mul_one]

theorem gaussianAverage_sub (hf : QBoundedJets (r + 2) B f) (v : E) :
    QBoundedJets r (B * ‖v‖ ^ 2) (fun x => SKBarriers2.gaussianAverage v f x - f x) := by
  have hfr : QBoundedJets r B f := hf.of_le (by omega)
  have hga : QBoundedJets r B (SKBarriers2.gaussianAverage v f) := hfr.gaussianAverage v
  refine ⟨mul_nonneg hf.nonneg (sq_nonneg _), hga.smooth.sub hfr.smooth, ?_⟩
  intro j hj x
  change ‖iteratedFDeriv ℝ j (SKBarriers2.gaussianAverage v f - f) x‖ ≤ B * ‖v‖ ^ 2
  rw [iteratedFDeriv_sub (hga.smooth.of_le (by exact_mod_cast hj))
    (hfr.smooth.of_le (by exact_mod_cast hj))]
  change ‖iteratedFDeriv ℝ j (SKBarriers2.gaussianAverage v f) x - iteratedFDeriv ℝ j f x‖ ≤ _
  rw [hfr.iteratedFDeriv_gaussianAverage v j hj x]
  have hjf : QBoundedJets 2 B (iteratedFDeriv ℝ j f) :=
    (hf.of_le (by omega : 2 + j ≤ r + 2)).jet j
  exact hjf.norm_gaussianAverage_sub_le v x

theorem gaussianAverage_sub_twice (hf : QBoundedJets (r + 4) B f) (v : E) :
    QBoundedJets r (B * ‖v‖ ^ 4)
      (fun x => SKBarriers2.gaussianAverage v
        (fun y => SKBarriers2.gaussianAverage v f y - f y) x -
          (SKBarriers2.gaussianAverage v f x - f x)) := by
  have hf' : QBoundedJets ((r + 2) + 2) B f := by convert hf using 1
  convert (hf'.gaussianAverage_sub v).gaussianAverage_sub v using 1
  ring

end QBoundedJets
end SKBarriers2
