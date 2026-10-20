module

public import SKBarriers2.Analysis.StepCalculus
public import OAI.Probability.SKBarriers.Scalar.ScalarSymmetricTaylor
public import OAI.Probability.SKBarriers.Calculus.StronglyConvexVariance

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)
variable {r s : ℕ} {B C : ℝ} {f ψ : E → ℝ}

def directionalJet (v : E) : ℕ → (E → ℝ) → E → ℝ
  | 0, g => g
  | n + 1, g => fun x => fderiv ℝ (directionalJet v n g) x v

theorem directionalJet_smooth (n : ℕ) (hf : QPotential (r + n + 1) B f) (v : E) :
    QBddSmooth r (B * ‖v‖ ^ (n + 1)) (directionalJet v (n + 1) f) := by
  induction n generalizing r with
  | zero => simpa only [Nat.add_zero, Nat.zero_add, directionalJet, pow_one] using hf.directional v
  | succ n ih =>
    have hi : QBddSmooth (r + 1) (B * ‖v‖ ^ (n + 1)) (directionalJet v (n + 1) f) := by
      apply ih
      convert hf using 1
      omega
    have hd := hi.potential.directional v
    simpa only [directionalJet, pow_succ, mul_assoc] using hd

private theorem line_derivative {g : E → ℝ} (hg : ContDiff ℝ 1 g) (v x : E) (t : ℝ) :
    HasDerivAt (fun a : ℝ => g (x + a • v)) (fderiv ℝ g (x + t • v) v) t := by
  have hv : HasDerivAt (fun a : ℝ => x + a • v) v t := by
    convert! (((hasDerivAt_id t).smul_const v).const_add x) using 1
    simp only [one_smul]
  exact (hg.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hv

private theorem scalar_cubic_taylor {F D₁ D₂ D₃ : ℝ → ℝ}
    (hd₁ : ∀ t, HasDerivAt F (D₁ t) t) (hd₂ : ∀ t, HasDerivAt D₁ (D₂ t) t)
    (hd₃ : ∀ t, HasDerivAt D₂ (D₃ t) t) {L : ℝ≥0} (hL : LipschitzWith L D₃)
    (x y : ℝ) :
    |F (x + y) - F x - D₁ x * y - D₂ x * y ^ 2 / 2 - D₃ x * y ^ 3 / 6| ≤
      (L : ℝ) * |y| ^ 4 := by
  let R : ℝ → ℝ := fun t => F (x + t * y) - D₁ x * (t * y) -
    D₂ x * (t * y) ^ 2 / 2 - D₃ x * (t * y) ^ 3 / 6
  have hd (t : ℝ) : HasDerivAt R
      ((D₁ (x + t * y) - D₁ x - D₂ x * (t * y) - D₃ x * (t * y) ^ 2 / 2) * y) t := by
    convert! ((((hd₁ (x + t * y)).comp t (((hasDerivAt_id t).mul_const y).const_add x)).sub
      (((hasDerivAt_id t).mul_const y).const_mul (D₁ x))).sub
      (((((hasDerivAt_id t).mul_const y).pow 2).const_mul (D₂ x)).div_const 2)).sub
      (((((hasDerivAt_id t).mul_const y).pow 3).const_mul (D₃ x)).div_const 6) using 1
    simp only [id_eq]
    ring_nf
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (C := (L : ℝ) * |y| ^ 4) (by
      intro t ht
      rw [Real.norm_eq_abs, abs_mul]
      have h := lipschitz_second_derivative_taylor hd₂ hd₃ hL x (t * y)
      have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
      calc
        _ ≤ ((L : ℝ) * |t * y| ^ 3) * |y| := mul_le_mul_of_nonneg_right h (abs_nonneg y)
        _ ≤ ((L : ℝ) * (1 * |y|) ^ 3) * |y| := by
          rw [abs_mul]
          gcongr
        _ = _ := by ring_nf)
  have he : R 1 - R 0 = F (x + y) - F x - D₁ x * y - D₂ x * y ^ 2 / 2 - D₃ x * y ^ 3 / 6 := by
    dsimp only [R]
    ring_nf
  rw [he, Real.norm_eq_abs] at H
  exact H

theorem spatial_cubic_taylor_le (hψ : QPotential s C ψ) (hs : 4 ≤ s)
    (v x : E) (t : ℝ) :
    |ψ (x + t • v) - ψ x - directionalJet v 1 ψ x * t -
        directionalJet v 2 ψ x * t ^ 2 / 2 - directionalJet v 3 ψ x * t ^ 3 / 6| ≤
      C * ‖v‖ ^ 4 * t ^ 4 := by
  have hψ' := hψ.of_le hs
  have h₁ : QBddSmooth 3 (C * ‖v‖) (directionalJet v 1 ψ) := by
    simpa only [Nat.zero_add, pow_one] using directionalJet_smooth (r := 3) 0 hψ' v
  have h₂ : QBddSmooth 2 (C * ‖v‖ ^ 2) (directionalJet v 2 ψ) := directionalJet_smooth 1 hψ' v
  have h₃ : QBddSmooth 1 (C * ‖v‖ ^ 3) (directionalJet v 3 ψ) := directionalJet_smooth 2 hψ' v
  have hline : LipschitzWith ‖v‖₊ (fun t : ℝ => x + t • v) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm]
    have he : x + a • v - (x + b • v) = (a - b) • v := by module
    rw [he, norm_smul, Real.norm_eq_abs, Real.dist_eq, coe_nnnorm, mul_comm]
  have hL := (h₃.potential.lipschitzWith le_rfl).comp hline
  have h := scalar_cubic_taylor
    (line_derivative (hψ.smooth.of_le (by exact_mod_cast (show 1 ≤ s by omega))) v x)
    (line_derivative (h₁.smooth.of_le (by norm_num)) v x)
    (line_derivative (h₂.smooth.of_le (by norm_num)) v x) hL 0 t
  simp only [zero_add, zero_smul, add_zero] at h
  change |ψ (x + t • v) - ψ x - directionalJet v 1 ψ x * t -
      directionalJet v 2 ψ x * t ^ 2 / 2 - directionalJet v 3 ψ x * t ^ 3 / 6| ≤
    (C * ‖v‖ ^ 3) * ‖v‖ * |t| ^ 4 at h
  refine h.trans_eq ?_
  rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)]
  ring

private theorem noise_id_growth : HasExpGrowth (fun t : ℝ => t) :=
  HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)

private theorem integrable_spatial_test (hf : QPotential r B f) (hr : 2 ≤ r)
    (hψ : QPotential s C ψ) (hs : 2 ≤ s) (m : ℝ) (v x : E) :
    Integrable (fun t : ℝ => ψ (x + t • v)) (stepLaw m v f x) := by
  exact ((hψ.boundedDerivs hs).hasExpGrowth.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    ((hf.boundedDerivs hr).compCLM (vectorTranslation v))
    (hψ.smooth.continuous.comp (vectorTranslation v).continuous) m x

theorem abs_noiseMean_linear_remainder_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (hψ : QPotential s C ψ) (hs : 2 ≤ s) (m : ℝ) (v x : E) :
    |noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
        fderiv ℝ ψ x v * noiseMean m v f x (fun t => t)| ≤
      C * ‖v‖ ^ 2 * noiseMean m v f x (fun t => t ^ 2) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let R : ℝ → ℝ := fun t => ψ (x + t • v) - ψ x - fderiv ℝ ψ x v * t
  have hiψ := integrable_spatial_test hf hr hψ hs m v x
  have hi := integrable_noise hf hr m v x noise_id_growth continuous_id
  have hi₂ : Integrable (fun t : ℝ => t ^ 2) μ := by
    simpa only [pow_two] using integrable_noise hf hr m v x
      (noise_id_growth.mul noise_id_growth) (continuous_id.mul continuous_id)
  have he : noiseMean m v f x R = noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
      fderiv ℝ ψ x v * noiseMean m v f x (fun t => t) := by
    unfold noiseMean
    dsimp only [R]
    have h₀ : (∫ t, ψ (x + t • v) - ψ x ∂μ) = (∫ t, ψ (x + t • v) ∂μ) - ψ x := by
      calc
        _ = (∫ t, ψ (x + t • v) ∂μ) - ∫ _ : ℝ, ψ x ∂μ :=
          integral_sub hiψ (integrable_const (ψ x))
        _ = _ := by rw [integral_const, probReal_univ, one_smul]
    calc
      _ = (∫ t, ψ (x + t • v) - ψ x ∂μ) - ∫ t : ℝ, fderiv ℝ ψ x v * t ∂μ :=
        integral_sub (hiψ.sub (integrable_const (ψ x))) (hi.const_mul _)
      _ = _ := by rw [h₀, integral_const_mul]
  have hR (t : ℝ) : |R t| ≤ C * ‖v‖ ^ 2 * t ^ 2 := by
    calc
      |R t| = |ψ (x + t • v) - ψ x - fderiv ℝ ψ x (t • v)| := by
        rw [map_smul, smul_eq_mul]
        congr 1
        dsimp only [R]
        ring
      _ ≤ C * ‖t • v‖ ^ 2 := hψ.taylor_linear_remainder_le hs x (t • v)
      _ = C * ‖v‖ ^ 2 * t ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
  rw [← he]
  calc
    |noiseMean m v f x R| ≤ ∫ t, |R t| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, C * ‖v‖ ^ 2 * t ^ 2 ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun t => abs_nonneg _)) (hi₂.const_mul _)
        (ae_of_all _ hR)
    _ = _ := integral_const_mul _ _

theorem noise_second_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    noiseMean m v f x (fun t => t ^ 2) ≤ 1 + B + B ^ 2 := by
  have h := (abs_le.mp (abs_noise_second_sub_one_le hf hr m v x)).2
  rw [abs_of_nonneg hm.1] at h
  have hmn : m ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  have hvn : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hcoef : m * B + m ^ 2 * B ^ 2 ≤ B + B ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hm.2 hf.nonneg
    have h₂ := mul_le_mul_of_nonneg_right hmn (sq_nonneg B)
    nlinarith
  have hprod := mul_le_mul hcoef hvn (sq_nonneg ‖v‖)
    (add_nonneg hf.nonneg (sq_nonneg B))
  nlinarith

theorem abs_noiseMean_sub_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (hψ : QPotential s C ψ) (hs : 2 ≤ s) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v x : E) (hv : ‖v‖ ≤ 1) :
    |noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x| ≤
      C * (1 + B) ^ 2 * ‖v‖ ^ 2 := by
  have hlin := abs_noiseMean_linear_remainder_le hf hr hψ hs m v x
  have hfirst := abs_noise_first_le hf hr m v x
  rw [abs_of_nonneg hm.1] at hfirst
  have hfirst' : |noiseMean m v f x (fun t => t)| ≤ B * ‖v‖ := by
    exact hfirst.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hm.2 hf.nonneg] : m * B ≤ B) (norm_nonneg v))
  have hD := hψ.directional_le (by omega) x v
  have hterm : |fderiv ℝ ψ x v * noiseMean m v f x (fun t => t)| ≤ C * B * ‖v‖ ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (C * ‖v‖) * (B * ‖v‖) :=
        mul_le_mul hD hfirst' (abs_nonneg _) (mul_nonneg hψ.nonneg (norm_nonneg v))
      _ = _ := by ring
  have he (a d : ℝ) : a = (a - d) + d := by ring
  rw [he (noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x)
    (fderiv ℝ ψ x v * noiseMean m v f x (fun t => t))]
  calc
    _ ≤ |noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
        fderiv ℝ ψ x v * noiseMean m v f x (fun t => t)| +
        |fderiv ℝ ψ x v * noiseMean m v f x (fun t => t)| := abs_add_le _ _
    _ ≤ C * ‖v‖ ^ 2 * (1 + B + B ^ 2) + C * B * ‖v‖ ^ 2 :=
      add_le_add (hlin.trans (mul_le_mul_of_nonneg_left (noise_second_le hf hr hm v x hv)
        (mul_nonneg hψ.nonneg (sq_nonneg _)))) hterm
    _ = _ := by ring

theorem abs_noise_first_sub_local_le (hf : QPotential r B f) (hr : 3 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |noiseMean m v f x (fun t => t) - m * fderiv ℝ f x v| ≤
      B * (1 + B) ^ 2 * ‖v‖ ^ 3 := by
  have hB : 0 ≤ B := hf.nonneg
  have hd : QBddSmooth 2 (B * ‖v‖) (fun y => fderiv ℝ f y v) :=
    (hf.of_le hr).directional v
  have h := abs_noiseMean_sub_le hf (by omega) hd.potential (by omega) hm v x hv
  rw [noise_first hf (by omega)]
  rw [← mul_sub, abs_mul, abs_of_nonneg hm.1]
  calc
    _ ≤ m * (B * ‖v‖ * (1 + B) ^ 2 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left h hm.1
    _ ≤ B * ‖v‖ * (1 + B) ^ 2 * ‖v‖ ^ 2 :=
      mul_le_of_le_one_left (by positivity) hm.2
    _ = _ := by ring

private theorem noise_pow_growth (n : ℕ) : HasExpGrowth (fun t : ℝ => t ^ n) := by
  induction n with
  | zero => exact HasExpGrowth.of_bounded zero_le_one (fun _ => by norm_num)
  | succ n ih => simpa only [pow_succ] using ih.mul noise_id_growth

theorem integrable_noise_pow (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) (stepLaw m v f x) := by
  exact integrable_noise hf hr m v x (noise_pow_growth n) (continuous_id.pow n)

theorem noise_moment_succ (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) (n : ℕ) :
    noiseMean m v f x (fun t => t ^ (n + 1)) =
      (n : ℝ) * noiseMean m v f x (fun t => t ^ (n - 1)) +
      m * noiseMean m v f x (fun t => t ^ n * fderiv ℝ f (x + t • v) v) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * t ^ (n - 1)) t := by
    convert! (hasDerivAt_id t).pow n using 1
    simp only [id_eq, mul_one]
  have hconst : HasExpGrowth (fun _ : ℝ => (n : ℝ)) :=
    HasExpGrowth.of_bounded (Nat.cast_nonneg n) (fun _ => by simp only [Real.norm_eq_abs, Nat.abs_cast, le_refl])
  have H := tilted_integration_by_parts hf hr m v x hd
    (continuous_const.mul (continuous_id.pow (n - 1))) (noise_pow_growth n)
    (hconst.mul (noise_pow_growth (n - 1)))
  simpa only [← pow_succ', noiseMean, integral_const_mul] using H

private theorem abs_noiseMean_weighted_le (m : ℝ) (v x : E) {w A : ℝ → ℝ} {K : ℝ}
    (hw : ∀ t, 0 ≤ w t) (hiw : Integrable w (stepLaw m v f x))
    (hA : ∀ t, |A t| ≤ K) :
    |noiseMean m v f x (fun t => w t * A t)| ≤ K * noiseMean m v f x w := by
  calc
    _ ≤ ∫ t, |w t * A t| ∂stepLaw m v f x := abs_integral_le_integral_abs
    _ ≤ ∫ t, K * w t ∂stepLaw m v f x := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun t => abs_nonneg _)) (hiw.const_mul K)
      apply ae_of_all
      intro t
      change |w t * A t| ≤ K * w t
      rw [abs_mul, abs_of_nonneg (hw t), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hA t) (hw t)
    _ = _ := integral_const_mul _ _

theorem abs_noise_third_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |noiseMean m v f x (fun t => t ^ 3)| ≤ B * (3 + B + B ^ 2) * ‖v‖ := by
  have hB : 0 ≤ B := hf.nonneg
  have hfirst := abs_noise_first_le hf hr m v x
  rw [abs_of_nonneg hm.1] at hfirst
  have hfirst' : |noiseMean m v f x (fun t => t)| ≤ B * ‖v‖ := by
    calc
      _ ≤ m * B * ‖v‖ := hfirst
      _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hB hm.2) (norm_nonneg v)
  have hw := abs_noiseMean_weighted_le (f := f) m v x (fun t => sq_nonneg t)
    (integrable_noise_pow hf hr m v x 2)
    (fun t => hf.directional_le (by omega) (x + t • v) v)
  have hw' : |noiseMean m v f x (fun t => t ^ 2 * fderiv ℝ f (x + t • v) v)| ≤
      B * ‖v‖ * (1 + B + B ^ 2) := hw.trans
    (mul_le_mul_of_nonneg_left (noise_second_le hf hr hm v x hv) (by positivity))
  have H := noise_moment_succ hf hr m v x 2
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, pow_one] at H
  rw [H]
  calc
    _ ≤ |2 * noiseMean m v f x (fun t => t)| +
        |m * noiseMean m v f x (fun t => t ^ 2 * fderiv ℝ f (x + t • v) v)| := abs_add_le _ _
    _ ≤ 2 * (B * ‖v‖) + B * ‖v‖ * (1 + B + B ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm.1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst' (by norm_num))
        ((mul_le_mul_of_nonneg_left hw' hm.1).trans (mul_le_of_le_one_left (by positivity) hm.2))
    _ = _ := by ring

private theorem young_cubic (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z) :
    a * z ^ 3 ≤ (3 * z ^ 4 + a ^ 4) / 4 := by
  have h := mul_nonneg (sq_nonneg (z - a))
    (by positivity : 0 ≤ 3 * z ^ 2 + 2 * a * z + a ^ 2)
  nlinarith

theorem noise_fourth_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    noiseMean m v f x (fun t => t ^ 4) ≤ 12 * (1 + B + B ^ 2) + B ^ 4 := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let a := m * B * ‖v‖
  have hB : 0 ≤ B := hf.nonneg
  have hm0 : 0 ≤ m := hm.1
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have haB : a ≤ B := by
    calc
      a ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hB hm.2) (norm_nonneg v)
      _ ≤ B := mul_le_of_le_one_right hB hv
  have ha₄ : a ^ 4 ≤ B ^ 4 := by gcongr
  have H := noise_moment_succ hf hr m v x 3
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat] at H
  have hi₄ := integrable_noise_pow hf hr m v x 4
  have hb : m * noiseMean m v f x (fun t => t ^ 3 * fderiv ℝ f (x + t • v) v) ≤
      (3 * noiseMean m v f x (fun t => t ^ 4) + a ^ 4) / 4 := by
    calc
      _ ≤ |m * noiseMean m v f x (fun t => t ^ 3 * fderiv ℝ f (x + t • v) v)| := le_abs_self _
      _ = |∫ t, m * (t ^ 3 * fderiv ℝ f (x + t • v) v) ∂μ| := by rw [integral_const_mul]; rfl
      _ ≤ ∫ t, |m * (t ^ 3 * fderiv ℝ f (x + t • v) v)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ t : ℝ, (3 * t ^ 4 + a ^ 4) / 4 ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun t => abs_nonneg _))
          (((hi₄.const_mul 3).add (integrable_const (a ^ 4))).div_const 4)
        apply ae_of_all
        intro t
        change |m * (t ^ 3 * fderiv ℝ f (x + t • v) v)| ≤ (3 * t ^ 4 + a ^ 4) / 4
        calc
          _ = m * |t| ^ 3 * |fderiv ℝ f (x + t • v) v| := by
            rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hm.1]; ring
          _ ≤ m * |t| ^ 3 * (B * ‖v‖) :=
            mul_le_mul_of_nonneg_left (hf.directional_le (by omega) (x + t • v) v) (by positivity)
          _ = a * |t| ^ 3 := by dsimp only [a]; ring
          _ ≤ (3 * |t| ^ 4 + a ^ 4) / 4 := young_cubic a |t| ha (abs_nonneg t)
          _ = _ := by rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)]
      _ = _ := by
        rw [integral_div, integral_add (hi₄.const_mul 3) (integrable_const (a ^ 4)),
          integral_const_mul, integral_const, probReal_univ, one_smul]
        rfl
  have hs := noise_second_le hf hr hm v x hv
  nlinarith

theorem abs_noiseMean_cubic_remainder_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (hψ : QPotential s C ψ) (hs : 4 ≤ s) (m : ℝ) (v x : E) :
    |noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
        directionalJet v 1 ψ x * noiseMean m v f x (fun t => t) -
        (directionalJet v 2 ψ x / 2) * noiseMean m v f x (fun t => t ^ 2) -
        (directionalJet v 3 ψ x / 6) * noiseMean m v f x (fun t => t ^ 3)| ≤
      C * ‖v‖ ^ 4 * noiseMean m v f x (fun t => t ^ 4) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let d₁ := directionalJet v 1 ψ x
  let d₂ := directionalJet v 2 ψ x / 2
  let d₃ := directionalJet v 3 ψ x / 6
  let R : ℝ → ℝ := fun t => ψ (x + t • v) - ψ x - d₁ * t - d₂ * t ^ 2 - d₃ * t ^ 3
  have hiψ := integrable_spatial_test hf hr hψ (by omega) m v x
  have hi₁ := integrable_noise_pow hf hr m v x 1
  simp only [pow_one] at hi₁
  have hi₂ := integrable_noise_pow hf hr m v x 2
  have hi₃ := integrable_noise_pow hf hr m v x 3
  have hi₄ := integrable_noise_pow hf hr m v x 4
  have hc := integrable_const (μ := μ) (ψ x)
  have h₀ := integral_sub hiψ hc
  have h₁ := integral_sub (hiψ.sub hc) (hi₁.const_mul d₁)
  have h₂ := integral_sub ((hiψ.sub hc).sub (hi₁.const_mul d₁)) (hi₂.const_mul d₂)
  have h₃ := integral_sub (((hiψ.sub hc).sub (hi₁.const_mul d₁)).sub (hi₂.const_mul d₂))
    (hi₃.const_mul d₃)
  simp only [Pi.sub_apply] at h₀ h₁ h₂ h₃
  have he : noiseMean m v f x R = noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
      d₁ * noiseMean m v f x (fun t => t) - d₂ * noiseMean m v f x (fun t => t ^ 2) -
      d₃ * noiseMean m v f x (fun t => t ^ 3) := by
    unfold noiseMean
    dsimp only [R]
    rw [h₃, h₂, h₁, h₀, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have hR (t : ℝ) : |R t| ≤ C * ‖v‖ ^ 4 * t ^ 4 := by
    convert! spatial_cubic_taylor_le hψ hs v x t using 1
    congr 1
    dsimp only [R, d₁, d₂, d₃]
    ring
  change |noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
      d₁ * noiseMean m v f x (fun t => t) - d₂ * noiseMean m v f x (fun t => t ^ 2) -
      d₃ * noiseMean m v f x (fun t => t ^ 3)| ≤ _
  rw [← he]
  calc
    _ ≤ ∫ t, |R t| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, C * ‖v‖ ^ 4 * t ^ 4 ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun t => abs_nonneg _)) (hi₄.const_mul _)
        (ae_of_all _ hR)
    _ = _ := integral_const_mul _ _

def pathExpansionConstant (B : ℝ) : ℝ :=
  B * (1 + B) ^ 2 + (B + B ^ 2) + B * (3 + B + B ^ 2) +
    12 * (1 + B + B ^ 2) + B ^ 4

theorem pathExpansionConstant_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ pathExpansionConstant B := by
  unfold pathExpansionConstant
  positivity

private theorem abs_four_add_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    _ ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := add_le_add (abs_add_le (a + b) c) le_rfl
    _ ≤ _ := add_le_add (add_le_add (abs_add_le a b) le_rfl) le_rfl

theorem abs_noiseMean_generator_remainder_le (hf : QPotential r B f) (hr : 3 ≤ r)
    (hψ : QPotential s C ψ) (hs : 4 ≤ s) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v x : E) (hv : ‖v‖ ≤ 1) :
    |noiseMean m v f x (fun t => ψ (x + t • v)) - ψ x -
        m * fderiv ℝ f x v * fderiv ℝ ψ x v - directionalJet v 2 ψ x / 2| ≤
      C * pathExpansionConstant B * ‖v‖ ^ 4 := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hψ.nonneg
  let M (n : ℕ) := noiseMean m v f x (fun t => t ^ n)
  let A := noiseMean m v f x (fun t => ψ (x + t • v))
  let d₁ := directionalJet v 1 ψ x
  let d₂ := directionalJet v 2 ψ x / 2
  let d₃ := directionalJet v 3 ψ x / 6
  let R := A - ψ x - d₁ * M 1 - d₂ * M 2 - d₃ * M 3
  have hR : |R| ≤ C * ‖v‖ ^ 4 * (12 * (1 + B + B ^ 2) + B ^ 4) := by
    have h := abs_noiseMean_cubic_remainder_le hf (by omega) hψ hs m v x
    dsimp only [R, M]
    simp only [pow_one]
    exact h.trans (mul_le_mul_of_nonneg_left (noise_fourth_le hf (by omega) hm v x hv) (by positivity))
  have h₁ : |d₁| ≤ C * ‖v‖ := hψ.directional_le (by omega) x v
  have hjet₂ : |directionalJet v 2 ψ x| ≤ C * ‖v‖ ^ 2 :=
    (directionalJet_smooth (r := 0) 1 (hψ.of_le (by omega)) v).abs_le x
  have hjet₃ : |directionalJet v 3 ψ x| ≤ C * ‖v‖ ^ 3 :=
    (directionalJet_smooth (r := 0) 2 (hψ.of_le (by omega)) v).abs_le x
  have h₂ : |d₂| ≤ C * ‖v‖ ^ 2 := by
    dsimp only [d₂]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [mul_nonneg hC (sq_nonneg ‖v‖)]
  have h₃ : |d₃| ≤ C * ‖v‖ ^ 3 := by
    dsimp only [d₃]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    linarith [mul_nonneg hC (pow_nonneg (norm_nonneg v) 3)]
  have he₁ : |M 1 - m * fderiv ℝ f x v| ≤ B * (1 + B) ^ 2 * ‖v‖ ^ 3 := by
    simpa only [M, pow_one] using abs_noise_first_sub_local_le hf hr hm v x hv
  have he₂ : |M 2 - 1| ≤ (B + B ^ 2) * ‖v‖ ^ 2 := by
    have h := abs_noise_second_sub_one_le hf (by omega) m v x
    rw [abs_of_nonneg hm.1] at h
    have hmn : m ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
    have hc : m * B + m ^ 2 * B ^ 2 ≤ B + B ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hm.2 hB, mul_le_mul_of_nonneg_right hmn (sq_nonneg B)]
    exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  have he₃ : |M 3| ≤ B * (3 + B + B ^ 2) * ‖v‖ := abs_noise_third_le hf (by omega) hm v x hv
  have ht₁ : |d₁ * (M 1 - m * fderiv ℝ f x v)| ≤ C * B * (1 + B) ^ 2 * ‖v‖ ^ 4 := by
    rw [abs_mul]
    exact (mul_le_mul h₁ he₁ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have ht₂ : |d₂ * (M 2 - 1)| ≤ C * (B + B ^ 2) * ‖v‖ ^ 4 := by
    rw [abs_mul]
    exact (mul_le_mul h₂ he₂ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have ht₃ : |d₃ * M 3| ≤ C * (B * (3 + B + B ^ 2)) * ‖v‖ ^ 4 := by
    rw [abs_mul]
    exact (mul_le_mul h₃ he₃ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have he : A - ψ x - m * fderiv ℝ f x v * fderiv ℝ ψ x v - d₂ =
      R + d₁ * (M 1 - m * fderiv ℝ f x v) + d₂ * (M 2 - 1) + d₃ * M 3 := by
    dsimp only [R, d₁, directionalJet]
    ring
  change |A - ψ x - m * fderiv ℝ f x v * fderiv ℝ ψ x v - d₂| ≤ _
  rw [he]
  exact (abs_four_add_le _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add hR ht₁) ht₂) ht₃).trans_eq (by
      unfold pathExpansionConstant
      ring))

theorem hasDerivAt_lineCGF (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) :
    HasDerivAt (cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1))
      (noiseMean m v f x (fun t => f (x + t • v))) m := by
  have ht := ((hf.boundedDerivs hr).compCLM (vectorTranslation v)).mem_interior_integrableExpSet_section x m
  have H := (analyticAt_cgf ht).differentiableAt.hasDerivAt
  rw [← integral_tilted_mul_self ht] at H
  exact H

theorem continuous_noiseMean_mass (hf : QPotential r B f) (hr : 2 ≤ r) (v x : E) :
    Continuous (fun m : ℝ => noiseMean m v f x (fun t => f (x + t • v))) := by
  have he : (fun m : ℝ => noiseMean m v f x (fun t => f (x + t • v))) =
      deriv (cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)) := by
    funext m
    exact (hasDerivAt_lineCGF hf hr m v x).deriv.symm
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro m
  have ht := ((hf.boundedDerivs hr).compCLM (vectorTranslation v)).mem_interior_integrableExpSet_section x m
  exact (analyticAt_cgf ht).deriv.continuousAt

private theorem lineCGF_eq_mul_step (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (v x : E) :
    cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1) m = m * vectorStep m v f x := by
  have H := congrArg Real.log (exp_gaussianStep ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) m x)
  rw [Real.log_exp] at H
  exact H.symm

theorem step_eq_integral_noiseMean (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) :
    vectorStep m v f x = ∫ θ : ℝ in 0..1,
      noiseMean (θ * m) v f x (fun t => f (x + t • v)) := by
  by_cases hm : m = 0
  · subst m
    simp only [mul_zero, noiseMean, stepLaw, gaussianStepLaw_zero, vectorStep, gaussianStep,
      ite_true, intervalIntegral.integral_const, sub_zero, one_smul]
  · let c := cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)
    have hd (θ : ℝ) : HasDerivAt (fun θ : ℝ => c (θ * m))
        (m * noiseMean (θ * m) v f x (fun t => f (x + t • v))) θ := by
      convert! (hasDerivAt_lineCGF hf hr (θ * m) v x).comp θ ((hasDerivAt_id θ).mul_const m) using 1
      ring
    have hc : Continuous (fun θ : ℝ => noiseMean (θ * m) v f x (fun t => f (x + t • v))) :=
      (continuous_noiseMean_mass hf hr v x).comp (continuous_id.mul continuous_const)
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
      ((continuous_const.mul hc).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul] at H
    simp only [one_mul, zero_mul, c, cgf_zero, sub_zero] at H
    rw [lineCGF_eq_mul_step hf hr] at H
    exact (mul_left_cancel₀ hm H).symm

theorem abs_step_generator_remainder_le (hf : QPotential r B f) (hr : 4 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |vectorStep m v f x - f x - m * (fderiv ℝ f x v) ^ 2 / 2 -
        directionalJet v 2 f x / 2| ≤ B * pathExpansionConstant B * ‖v‖ ^ 4 := by
  let d := fderiv ℝ f x v
  let H := directionalJet v 2 f x
  let P : ℝ → ℝ := fun θ => f x + θ * m * d ^ 2 + H / 2
  have hc : Continuous (fun θ : ℝ => noiseMean (θ * m) v f x (fun t => f (x + t • v))) :=
    (continuous_noiseMean_mass hf (by omega) v x).comp (continuous_id.mul continuous_const)
  have hp : Continuous P := by unfold P; fun_prop
  have hdP (θ : ℝ) : HasDerivAt (fun θ : ℝ => θ * f x + θ ^ 2 * (m * d ^ 2) / 2 + θ * H / 2)
      (P θ) θ := by
    convert! (((hasDerivAt_id θ).mul_const (f x)).add
      ((((hasDerivAt_id θ).pow 2).mul_const (m * d ^ 2)).div_const 2)).add
      (((hasDerivAt_id θ).mul_const H).div_const 2) using 1
    dsimp only [P, id_eq]
    ring
  have hP : (∫ θ : ℝ in 0..1, P θ) = f x + m * d ^ 2 / 2 + H / 2 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hdP θ) (hp.intervalIntegrable 0 1)
    simpa only [one_mul, zero_mul, one_pow, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, sub_zero] using h
  have he : vectorStep m v f x - f x - m * d ^ 2 / 2 - H / 2 =
      ∫ θ : ℝ in 0..1, noiseMean (θ * m) v f x (fun t => f (x + t • v)) - P θ := by
    have hsub := intervalIntegral.integral_sub (μ := volume)
      (hc.intervalIntegrable 0 1) (hp.intervalIntegrable 0 1)
    rw [hsub, ← step_eq_integral_noiseMean hf (by omega), hP]
    ring
  change |vectorStep m v f x - f x - m * d ^ 2 / 2 - H / 2| ≤ _
  rw [he]
  have hbound (θ : ℝ) (hθ : θ ∈ Set.uIoc (0 : ℝ) 1) :
      ‖noiseMean (θ * m) v f x (fun t => f (x + t • v)) - P θ‖ ≤
        B * pathExpansionConstant B * ‖v‖ ^ 4 := by
    rw [Set.uIoc_of_le zero_le_one] at hθ
    have hupper : θ * m ≤ m := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ.2 hm.1
    have hmθ : θ * m ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hθ.1.le hm.1, hupper.trans hm.2⟩
    convert! abs_noiseMean_generator_remainder_le hf (by omega) hf hr hmθ v x hv using 1
    rw [Real.norm_eq_abs]
    congr 1
    dsimp only [P, d, H]
    ring
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem abs_mass_sensitivity_remainder_le (hf : QPotential r B f) (hr : 4 ≤ r)
    {a₀ m : ℝ} (ha₀ : 0 < a₀) (hm : m ∈ Icc a₀ 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |stepEntropy m v f x / m ^ 2 - (fderiv ℝ f x v) ^ 2 / 2| ≤
      (2 * B * pathExpansionConstant B / a₀) * ‖v‖ ^ 4 := by
  have hm0 : 0 < m := ha₀.trans_le hm.1
  have hm' : m ∈ Icc (0 : ℝ) 1 := ⟨hm0.le, hm.2⟩
  let d := fderiv ℝ f x v
  let H := directionalJet v 2 f x
  let A := noiseMean m v f x (fun t => f (x + t • v))
  let T := vectorStep m v f x
  let R₁ := A - f x - m * d ^ 2 - H / 2
  let R₂ := T - f x - m * d ^ 2 / 2 - H / 2
  have h₁ : |R₁| ≤ B * pathExpansionConstant B * ‖v‖ ^ 4 := by
    convert! abs_noiseMean_generator_remainder_le hf (by omega) hf hr hm' v x hv using 1
    congr 1
    dsimp only [R₁, A, d, H]
    ring
  have h₂ : |R₂| ≤ B * pathExpansionConstant B * ‖v‖ ^ 4 := abs_step_generator_remainder_le hf hr hm' v x hv
  have he : stepEntropy m v f x / m ^ 2 - d ^ 2 / 2 = (R₁ - R₂) / m := by
    dsimp only [stepEntropy, R₁, R₂, A, T]
    field_simp
    ring
  change |stepEntropy m v f x / m ^ 2 - d ^ 2 / 2| ≤ _
  rw [he, abs_div, abs_of_pos hm0]
  calc
    _ ≤ (|R₁| + |R₂|) / m := div_le_div_of_nonneg_right (abs_sub _ _) hm0.le
    _ ≤ (2 * B * pathExpansionConstant B * ‖v‖ ^ 4) / m := by
      apply div_le_div_of_nonneg_right _ hm0.le
      linarith
    _ ≤ (2 * B * pathExpansionConstant B * ‖v‖ ^ 4) / a₀ :=
      div_le_div_of_nonneg_left (by
        have hB := hf.nonneg
        have hP := pathExpansionConstant_nonneg hB
        positivity) ha₀ hm.1
    _ = _ := by ring

theorem abs_mass_deriv_remainder_le (hf : QPotential r B f) (hr : 4 ≤ r)
    {a₀ m : ℝ} (ha₀ : 0 < a₀) (hm : m ∈ Icc a₀ 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |deriv (fun a : ℝ => vectorStep a v f x) m - (fderiv ℝ f x v) ^ 2 / 2| ≤
      (2 * B * pathExpansionConstant B / a₀) * ‖v‖ ^ 4 := by
  rw [(hasDerivAt_mass hf (by omega) (ne_of_gt (ha₀.trans_le hm.1)) v x).deriv]
  exact abs_mass_sensitivity_remainder_le hf hr ha₀ hm v x hv

theorem hasDerivAt_terminal_tilt (hf : QPotential r B f) (hr : 2 ≤ r)
    (hψ : QBddSmooth s C ψ) (hs : 2 ≤ s) {m : ℝ} (hm : m ≠ 0) (v x : E) :
    HasDerivAt (fun a : ℝ => vectorStep m v (fun y => f y + a * ψ y) x)
      (noiseMean m v f x (fun t => ψ (x + t • v))) 0 := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let A : ℝ → ℝ := fun t => ψ (x + t • v)
  have hAc : Continuous A := hψ.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hi (a : ℝ) : Integrable (fun t => Real.exp (a * A t)) μ := by
    apply Integrable.of_bound (Real.continuous_exp.comp (continuous_const.mul hAc)).aestronglyMeasurable
      (Real.exp (|a| * C))
    apply ae_of_all
    intro t
    change ‖Real.exp (a * A t)‖ ≤ Real.exp (|a| * C)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      a * A t ≤ |a * A t| := le_abs_self _
      _ = |a| * |A t| := abs_mul _ _
      _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hψ.abs_le (x + t • v)) (abs_nonneg a)
  have hset : integrableExpSet A μ = univ := by
    ext a
    simp only [mem_univ, iff_true]
    exact hi a
  have ht : (0 : ℝ) ∈ interior (integrableExpSet A μ) := by rw [hset, interior_univ]; exact mem_univ 0
  have hb := (hf.boundedDerivs hr).compCLM (vectorTranslation v)
  have he (a : ℝ) : cgf A μ (m * a) =
      m * (vectorStep m v (fun y => f y + a * ψ y) x - vectorStep m v f x) := by
    have hp := ((hf.boundedDerivs hr).add ((hψ.potential.boundedDerivs hs).const_mul a)).compCLM
      (vectorTranslation v)
    change Real.log (∫ t : ℝ, Real.exp ((m * a) * A t)
      ∂(gaussianReal 0 1).tilted (fun t => m * f (x + t • v))) = _
    rw [integral_tilted_real_eq_div]
    have he' (t : ℝ) : Real.exp ((m * a) * A t) * Real.exp (m * f (x + t • v)) =
        Real.exp (m * (f (x + t • v) + a * ψ (x + t • v))) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [A]
      ring
    simp_rw [he']
    have hZ : (∫ t : ℝ, Real.exp (m * f (x + t • v)) ∂gaussianReal 0 1) =
        Real.exp (m * vectorStep m v f x) := (exp_gaussianStep hb m x).symm
    have hZ' : (∫ t : ℝ, Real.exp (m * (f (x + t • v) + a * ψ (x + t • v))) ∂gaussianReal 0 1) =
        Real.exp (m * vectorStep m v (fun y => f y + a * ψ y) x) := (exp_gaussianStep hp m x).symm
    rw [hZ', hZ, ← Real.exp_sub, Real.log_exp]
    ring
  have hfun : (fun a : ℝ => vectorStep m v (fun y => f y + a * ψ y) x) =
      fun a : ℝ => vectorStep m v f x + cgf A μ (m * a) / m := by
    funext a
    rw [he]
    field_simp
    ring
  have hd := (analyticAt_cgf ht).differentiableAt.hasDerivAt
  rw [deriv_cgf_zero ht, probReal_univ, div_one] at hd
  have harg : HasDerivAt (fun a : ℝ => m * a) m 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).const_mul m using 1
    ring
  have H := ((hd.comp_of_eq 0 harg (by ring)).div_const m).const_add (vectorStep m v f x)
  rw [hfun]
  convert! H using 1
  field_simp
  rfl

theorem abs_terminal_tilt_deriv_remainder_le (hf : QPotential r B f) (hr : 3 ≤ r)
    (hψ : QBddSmooth s C ψ) (hs : 4 ≤ s) {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1)
    (v x : E) (hv : ‖v‖ ≤ 1) :
    |deriv (fun a : ℝ => vectorStep m v (fun y => f y + a * ψ y) x) 0 - ψ x -
        m * fderiv ℝ f x v * fderiv ℝ ψ x v - directionalJet v 2 ψ x / 2| ≤
      C * pathExpansionConstant B * ‖v‖ ^ 4 := by
  rw [(hasDerivAt_terminal_tilt hf (by omega) hψ (by omega) hm.1.ne' v x).deriv]
  exact abs_noiseMean_generator_remainder_le hf hr hψ.potential hs ⟨hm.1.le, hm.2⟩ v x hv

private theorem step_prefixGradient (hf : QPotential r B f) (hr : 2 ≤ r)
    (v w x : E) (t : ℝ) :
    prefixGradient (f ∘ vectorTranslation v) w (x,t) = fderiv ℝ f (x + t • v) w := by
  have hd := ((hf.boundedDerivs hr).1.differentiable (by norm_num)
    ((vectorTranslation v) (x,t))).hasFDerivAt.comp (x,t) (vectorTranslation v).hasFDerivAt
  rw [prefixGradient, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, vectorTranslation, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, zero_smul, add_zero]

private theorem step_prefixHessian (hf : QPotential r B f) (hr : 2 ≤ r)
    (v w u x : E) (t : ℝ) :
    prefixHessian (f ∘ vectorTranslation v) w u (x,t) =
      fderiv ℝ (fderiv ℝ f) (x + t • v) w u := by
  have H := hessian_comp_linear f (hf.boundedDerivs hr).1 (vectorTranslation v) (x,t) (w,0) (u,0)
  convert! H using 1
  simp only [Hessian, vectorTranslation, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, zero_smul, add_zero]

theorem fderiv_fderiv_step_apply (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x w u : E) :
    fderiv ℝ (fderiv ℝ (vectorStep m v f)) x w u =
      noiseMean m v f x (fun t => fderiv ℝ (fderiv ℝ f) (x + t • v) w u) + m *
        (noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w * fderiv ℝ f (x + t • v) u) -
          noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w) *
            noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) u)) := by
  have H := fderiv_fderiv_gaussianStep_apply ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) m x w u
  change fderiv ℝ (fderiv ℝ (vectorStep m v f)) x w u =
    noiseMean m v f x (fun t => prefixHessian (f ∘ vectorTranslation v) w u (x,t)) + m *
      (noiseMean m v f x (fun t => prefixGradient (f ∘ vectorTranslation v) w (x,t) *
        prefixGradient (f ∘ vectorTranslation v) u (x,t)) -
        noiseMean m v f x (fun t => prefixGradient (f ∘ vectorTranslation v) w (x,t)) *
          noiseMean m v f x (fun t => prefixGradient (f ∘ vectorTranslation v) u (x,t))) at H
  simp only [step_prefixGradient hf hr, step_prefixHessian hf hr] at H
  exact H

private theorem abs_covariance_le_mean_variance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {A D : ℝ → ℝ} (hA : MemLp A 2 μ) (hD : MemLp D 2 μ) :
    |covariance A D μ| ≤ (variance A μ + variance D μ) / 2 := by
  have hplus := variance_nonneg (X := fun t => A t + D t) (μ := μ)
  have hminus := variance_nonneg (X := fun t => A t - D t) (μ := μ)
  rw [variance_fun_add hA hD] at hplus
  rw [variance_fun_sub hA hD] at hminus
  apply abs_le.mpr
  constructor <;> linarith

private theorem gradient_memLp (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x w : E) :
    MemLp (fun t : ℝ => fderiv ℝ f (x + t • v) w) 2 (stepLaw m v f x) := by
  let _ := stepLaw_probability hf hr m v x
  have hd : QBddSmooth 1 (B * ‖w‖) (fun y => fderiv ℝ f y w) := (hf.of_le hr).directional w
  exact MemLp.of_bound (hd.smooth.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable (B * ‖w‖)
    (ae_of_all _ (fun t => hf.directional_le (by omega) (x + t • v) w))

theorem abs_gradient_covariance_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v x w u : E) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    |noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w * fderiv ℝ f (x + t • v) u) -
        noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w) *
          noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) u)| ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  have hgap : 0 < 1 - m * (B * ‖v‖ ^ 2) := by linarith
  have hvar (z : E) (hz : ‖z‖ = 1) :
      variance (fun t : ℝ => fderiv ℝ f (x + t • v) z) μ ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by
    have hd : QBddSmooth 1 (B * ‖z‖) (fun y => fderiv ℝ f y z) := (hf.of_le hr).directional z
    have H := spatial_variance_le hf hr hm v x (by linarith) (hd.potential.lipschitzWith le_rfl)
    change variance (fun t : ℝ => fderiv ℝ f (x + t • v) z) μ ≤
      (B * ‖z‖) ^ 2 * ‖v‖ ^ 2 / (1 - m * (B * ‖v‖ ^ 2)) at H
    rw [hz, mul_one] at H
    refine H.trans ((div_le_iff₀ hgap).mpr ?_)
    have hnon : 0 ≤ B ^ 2 * ‖v‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hsmall hnon]
  have hA := gradient_memLp hf hr m v x w
  have hD := gradient_memLp hf hr m v x u
  have H := abs_covariance_le_mean_variance hA hD
  rw [covariance_eq_sub hA hD] at H
  change |(∫ t, fderiv ℝ f (x + t • v) w * fderiv ℝ f (x + t • v) u ∂μ) -
      (∫ t, fderiv ℝ f (x + t • v) w ∂μ) * (∫ t, fderiv ℝ f (x + t • v) u ∂μ)| ≤ _
  exact H.trans (by linarith [hvar w hw, hvar u hu])

theorem norm_second_step_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v x : E) (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    ‖fderiv ℝ (fderiv ℝ (vectorStep m v f)) x‖ ≤ B + 2 * m * B ^ 2 * ‖v‖ ^ 2 := by
  have hB : 0 ≤ B := hf.nonneg
  have hbound : 0 ≤ B + 2 * m * B ^ 2 * ‖v‖ ^ 2 := by positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hbound
  intro w hw
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hbound
  intro u hu
  have hbase := abs_noiseMean_le hf hr m v x (fun t => hf.second_directional_le hr (x + t • v) w u)
  rw [hw, hu, mul_one, mul_one] at hbase
  have hcov := abs_gradient_covariance_le hf hr hm v x w u hw hu hsmall
  rw [Real.norm_eq_abs, fderiv_fderiv_step_apply hf hr]
  calc
    _ ≤ |noiseMean m v f x (fun t => fderiv ℝ (fderiv ℝ f) (x + t • v) w u)| +
        |m * (noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w * fderiv ℝ f (x + t • v) u) -
          noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w) *
            noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) u))| := abs_add_le _ _
    _ ≤ B + m * (2 * B ^ 2 * ‖v‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg hm]
      exact add_le_add hbase (mul_le_mul_of_nonneg_left hcov hm)
    _ = _ := by ring

theorem qbddSmooth_two_step (hf : QBddSmooth r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBddSmooth 2 (B + 2 * B ^ 2 * ‖v‖ ^ 2) (vectorStep m v f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hgain : 0 ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by positivity
  refine ⟨by positivity, (vectorStep_regular (hf.potential.boundedDerivs hr) m v).1, ?_⟩
  intro j hj x
  interval_cases j
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      (abs_step_le hf hr hm.1 v x).trans (le_add_of_nonneg_right hgain)
  · simpa only [norm_iteratedFDeriv_one] using
      (norm_fderiv_step_le hf.potential hr m v x).trans (le_add_of_nonneg_right hgain)
  · have H := norm_second_step_le hf.potential hr hm.1 v x hsmall
    have hmB : 2 * m * B ^ 2 * ‖v‖ ^ 2 ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hm.2 hgain]
    have h := H.trans (add_le_add le_rfl hmB)
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    exact h

end SKBarriers2.StepCalculus
