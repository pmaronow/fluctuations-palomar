module

public import SKBarriers2.Corner.FrozenDiffChain
public import OAI.Probability.SKBarriers.Gaussian.GaussianMassStability

@[expose] public section

noncomputable section
open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def gaussianTiltPolynomialConstant (L : ℝ) (p : ℕ) : ℝ :=
  (∫ t : ℝ, Real.exp ((L + p) * |t|) ∂gaussianReal 0 1) /
    (∫ t : ℝ, Real.exp (-L * |t|) ∂gaussianReal 0 1)

theorem gaussianTiltPolynomialConstant_pos (L : ℝ) (p : ℕ) :
    0 < gaussianTiltPolynomialConstant L p := by
  exact div_pos (integral_exp_pos (integrable_exp_mul_abs_gaussian _))
    (integral_exp_pos (integrable_exp_mul_abs_gaussian _))

private theorem polynomial_noise_le_exp (p : ℕ) (t : ℝ) :
    (1 + |t|) ^ p ≤ Real.exp ((p : ℝ) * |t|) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by positivity)
  simpa only [add_comm] using Real.add_one_le_exp |t|

theorem gaussian_centered_tilt_polynomial_bound {g : ℝ → ℝ} {L : ℝ}
    (hg : Continuous g) (hL : 0 ≤ L) (hbound : ∀ t, |g t| ≤ L * |t|) (p : ℕ) :
    Integrable (fun t => (1 + |t|) ^ p) ((gaussianReal 0 1).tilted g) ∧
      (∫ t, (1 + |t|) ^ p ∂(gaussianReal 0 1).tilted g) ≤ gaussianTiltPolynomialConstant L p := by
  let ν := gaussianReal 0 1
  let Z := ∫ t, Real.exp (g t) ∂ν
  let D := ∫ t : ℝ, Real.exp (-L * |t|) ∂ν
  let A := ∫ t : ℝ, Real.exp ((L + p) * |t|) ∂ν
  have hi : Integrable (fun t => Real.exp (g t)) ν := by
    apply (integrable_exp_mul_abs_gaussian L).mono' (Real.continuous_exp.comp hg).aestronglyMeasurable
    exact ae_of_all _ (fun t => by
      change ‖Real.exp (g t)‖ ≤ Real.exp (L * |t|)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound t)))
  have hD : 0 < D := integral_exp_pos (integrable_exp_mul_abs_gaussian (-L))
  have hDZ : D ≤ Z := by
    have H := gaussian_exp_integral_bounds g hg (A := 0) hL
      (fun t => by simpa only [zero_add] using hbound t)
    simpa only [neg_zero, Real.exp_zero, one_mul] using H.1
  have hZ : 0 < Z := hD.trans_le hDZ
  have hA : 0 ≤ A := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hb (t : ℝ) : Real.exp (g t) * (1 + |t|) ^ p ≤ Real.exp ((L + p) * |t|) := by
    calc
      _ ≤ Real.exp (L * |t|) * Real.exp ((p : ℝ) * |t|) :=
        mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound t)))
          (polynomial_noise_le_exp p t) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnum : Integrable (fun t => Real.exp (g t) * (1 + |t|) ^ p) ν := by
    apply (integrable_exp_mul_abs_gaussian (L + p)).mono' (by fun_prop)
    exact ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.exp (g t) * (1 + |t|) ^ p)]
      exact hb t)
  refine ⟨(integrable_tilted_iff hi _).mpr (by simpa only [smul_eq_mul] using hnum), ?_⟩
  have hn : (∫ t, Real.exp (g t) * (1 + |t|) ^ p ∂ν) ≤ A :=
    integral_mono hnum (integrable_exp_mul_abs_gaussian (L + p)) hb
  calc
    _ = (∫ t, Real.exp (g t) * (1 + |t|) ^ p ∂ν) / Z := by
      rw [integral_tilted]
      simp only [smul_eq_mul]
      rw [← integral_div]
      congr 1
      funext t
      dsimp only [Z]
      ring
    _ ≤ A / Z := div_le_div_of_nonneg_right hn hZ.le
    _ ≤ A / D := div_le_div_of_nonneg_left hA hD hDZ
    _ = _ := rfl

theorem gaussian_tilt_polynomial_bound {g : ℝ → ℝ} {L : ℝ}
    (hg : Continuous g) (hL : 0 ≤ L) (hbound : ∀ t, |g t - g 0| ≤ L * |t|) (p : ℕ) :
    Integrable (fun t => (1 + |t|) ^ p) ((gaussianReal 0 1).tilted g) ∧
      (∫ t, (1 + |t|) ^ p ∂(gaussianReal 0 1).tilted g) ≤ gaussianTiltPolynomialConstant L p := by
  have he : (gaussianReal 0 1).tilted g =
      (gaussianReal 0 1).tilted (fun t => g t - g 0) := by
    have H := tilted_add_constant (gaussianReal 0 1) g (-g 0)
    simpa only [sub_eq_add_neg] using H.symm
  rw [he]
  exact gaussian_centered_tilt_polynomial_bound (hg.sub continuous_const) hL hbound p

theorem log_integral_exp_sub_le {f g : ℝ → ℝ} {C : ℝ}
    (hf : Integrable (fun t => Real.exp (f t)) (gaussianReal 0 1))
    (hg : Integrable (fun t => Real.exp (g t)) (gaussianReal 0 1))
    (hfg : ∀ t, f t ≤ g t + C) :
    Real.log (∫ t, Real.exp (f t) ∂gaussianReal 0 1) -
      Real.log (∫ t, Real.exp (g t) ∂gaussianReal 0 1) ≤ C := by
  have hp := integral_exp_pos hf
  have hq := integral_exp_pos hg
  have hle : (∫ t, Real.exp (f t) ∂gaussianReal 0 1) ≤
      Real.exp C * ∫ t, Real.exp (g t) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    apply integral_mono hf (hg.const_mul _)
    intro t
    change Real.exp (f t) ≤ Real.exp C * Real.exp (g t)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr ((hfg t).trans_eq (add_comm _ _))
  have H := Real.log_le_log hp hle
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hq), Real.log_exp] at H
  linarith

theorem abs_log_integral_exp_sub_le {f g : ℝ → ℝ} {C : ℝ}
    (hf : Integrable (fun t => Real.exp (f t)) (gaussianReal 0 1))
    (hg : Integrable (fun t => Real.exp (g t)) (gaussianReal 0 1))
    (hfg : ∀ t, |f t - g t| ≤ C) :
    |Real.log (∫ t, Real.exp (f t) ∂gaussianReal 0 1) -
      Real.log (∫ t, Real.exp (g t) ∂gaussianReal 0 1)| ≤ C := by
  apply abs_le.mpr
  constructor
  · have H := log_integral_exp_sub_le hg hf (fun t => by linarith [(abs_le.mp (hfg t)).1])
    linarith
  · exact log_integral_exp_sub_le hf hg (fun t => by linarith [(abs_le.mp (hfg t)).2])

theorem quadraticGaussian_eq_map {D : ℝ} (hD : 0 < D) (L : ℝ) :
    quadraticGaussian D L = (gaussianReal 0 1).map
      (fun t => L / D + Real.sqrt D⁻¹ * t) := by
  have hv : NNReal.mk ((Real.sqrt D⁻¹) ^ 2) (sq_nonneg _) = Real.toNNReal D⁻¹ := by
    ext
    change (Real.sqrt D⁻¹) ^ 2 = (Real.toNNReal D⁻¹ : ℝ)
    rw [Real.sq_sqrt (inv_nonneg.mpr hD.le), Real.coe_toNNReal _ (inv_nonneg.mpr hD.le)]
  have he : (fun t => L / D + Real.sqrt D⁻¹ * t) =
      (fun t => L / D + t) ∘ (fun t => Real.sqrt D⁻¹ * t) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero, zero_add, mul_one, hv, quadraticGaussian]

theorem integral_quadraticGaussian_standard {D : ℝ} (hD : 0 < D) (L : ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t, g t ∂quadraticGaussian D L) =
      ∫ t, g (L / D + Real.sqrt D⁻¹ * t) ∂gaussianReal 0 1 := by
  rw [quadraticGaussian_eq_map hD L]
  exact integral_map (by fun_prop) hg.aestronglyMeasurable

theorem quadraticAverage_eq_standard (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (hD : 0 < Q.precision m v) {g : Vec3 → ℝ} (hg : Continuous g) :
    quadraticAverage Q m v g x = ∫ t,
      g (quadraticMeanTransition Q m v x +
        t • ((Real.sqrt (Q.precision m v)⁻¹) • v)) ∂gaussianReal 0 1 := by
  rw [quadraticAverage, integral_quadraticGaussian_standard hD _
    (g := fun t => g (x + t • v)) (hg.comp (by fun_prop))]
  apply integral_congr_ae
  refine ae_of_all _ (fun t => ?_)
  apply congrArg g
  unfold quadraticMeanTransition
  simp only [add_smul, smul_smul]
  rw [mul_comm (Real.sqrt (Q.precision m v)⁻¹) t, add_assoc]

theorem integrable_exp_lipschitz_line {f : Vec3 → ℝ} {L : ℝ}
    (hf : Continuous f) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (m : ℝ) (a w : Vec3) :
    Integrable (fun t => Real.exp (m * f (a + t • w))) (gaussianReal 0 1) := by
  let C : ℝ := |m| * L * ‖w‖
  apply ((integrable_exp_mul_abs_gaussian C).const_mul (Real.exp (m * f a))).mono' (by fun_prop)
  refine ae_of_all _ (fun t => ?_)
  change ‖Real.exp (m * f (a + t • w))‖ ≤ Real.exp (m * f a) * Real.exp (C * |t|)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have H := mul_le_mul_of_nonneg_left (hLip (a + t • w) a) (abs_nonneg m)
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
  have hs : m * (f (a + t • w) - f a) ≤ |m| * |f (a + t • w) - f a| := by
    rw [← abs_mul]
    exact le_abs_self _
  dsimp only [C]
  nlinarith

theorem affine_tilt_polynomial_moment {f ψ : Vec3 → ℝ} {L M : ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (p : ℕ) (hbound : ∀ y, |ψ y| ≤ M * (1 + ‖y‖) ^ p) (m : ℝ) (a w : Vec3) :
    let ν := (gaussianReal 0 1).tilted (fun t => m * f (a + t • w))
    Integrable (fun t => ψ (a + t • w)) ν ∧
      |∫ t, ψ (a + t • w) ∂ν| ≤
        (M * (1 + ‖a‖ + ‖w‖) ^ p) * gaussianTiltPolynomialConstant (|m| * L * ‖w‖) p := by
  let ν := (gaussianReal 0 1).tilted (fun t => m * f (a + t • w))
  have hnoise (t : ℝ) :
      |m * f (a + t • w) - m * f (a + (0 : ℝ) • w)| ≤ (|m| * L * ‖w‖) * |t| := by
    rw [zero_smul, add_zero, ← mul_sub, abs_mul]
    have H := mul_le_mul_of_nonneg_left (hLip (a + t • w) a) (abs_nonneg m)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
    exact H.trans_eq (by ring)
  have hpoly := gaussian_tilt_polynomial_bound (g := fun t => m * f (a + t • w))
    (by fun_prop) (by positivity : 0 ≤ |m| * L * ‖w‖) hnoise p
  have htest (t : ℝ) : |ψ (a + t • w)| ≤
      (M * (1 + ‖a‖ + ‖w‖) ^ p) * (1 + |t|) ^ p := by
    have hn : 1 + ‖a + t • w‖ ≤ (1 + ‖a‖ + ‖w‖) * (1 + |t|) := by
      have H := norm_add_le a (t • w)
      rw [norm_smul, Real.norm_eq_abs] at H
      nlinarith [mul_nonneg (norm_nonneg a) (abs_nonneg t), norm_nonneg w, abs_nonneg t]
    calc
      _ ≤ M * (1 + ‖a + t • w‖) ^ p := hbound _
      _ ≤ M * ((1 + ‖a‖ + ‖w‖) * (1 + |t|)) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn p) hM
      _ = _ := by rw [mul_pow]; ring
  have hmeas : AEStronglyMeasurable (fun t => ψ (a + t • w)) ν :=
    (hψ.comp (by fun_prop)).aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  have hi : Integrable (fun t => ψ (a + t • w)) ν :=
    (hpoly.1.const_mul (M * (1 + ‖a‖ + ‖w‖) ^ p)).mono' hmeas
      (ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using htest t))
  refine ⟨hi, ?_⟩
  calc
    _ = ‖∫ t, ψ (a + t • w) ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖ψ (a + t • w)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ t, (M * (1 + ‖a‖ + ‖w‖) ^ p) * (1 + |t|) ^ p ∂ν :=
      integral_mono hi.norm (hpoly.1.const_mul _) (fun t => by
        simpa only [Real.norm_eq_abs] using htest t)
    _ = (M * (1 + ‖a‖ + ‖w‖) ^ p) * ∫ t, (1 + |t|) ^ p ∂ν := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly.2 (by positivity)

theorem log_affine_gaussian_lipschitz {f : Vec3 → ℝ} {L S m : ℝ}
    (hf : Continuous f) (hL : 0 ≤ L) (hm : 0 < m)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (a : Vec3 → Vec3) (ha : ∀ x y, ‖a x - a y‖ ≤ S * ‖x - y‖) (w : Vec3) (x y : Vec3) :
    |Real.log (∫ t, Real.exp (m * f (a x + t • w)) ∂gaussianReal 0 1) / m -
      Real.log (∫ t, Real.exp (m * f (a y + t • w)) ∂gaussianReal 0 1) / m| ≤ L * S * ‖x - y‖ := by
  have hbound (t : ℝ) : |m * f (a x + t • w) - m * f (a y + t • w)| ≤
      m * L * S * ‖x - y‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos hm]
    have H := mul_le_mul_of_nonneg_left (hLip (a x + t • w) (a y + t • w)) hm.le
    rw [add_sub_add_right_eq_sub] at H
    calc
      _ ≤ m * (L * ‖a x - a y‖) := H
      _ ≤ m * (L * (S * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ha x y) hL) hm.le
      _ = _ := by ring
  have H := abs_log_integral_exp_sub_le (integrable_exp_lipschitz_line hf hLip m (a x) w)
    (integrable_exp_lipschitz_line hf hLip m (a y) w) hbound
  rw [← sub_div, abs_div, abs_of_pos hm]
  calc
    _ ≤ (m * L * S * ‖x - y‖) / m := div_le_div_of_nonneg_right H hm.le
    _ = _ := by field_simp

theorem quadraticMeanTransition_lipschitz (Q : QuadraticTerminal) {B m : ℝ}
    (hB : 0 ≤ B) (hQ : ∀ i j, |Q.hessian i j| ≤ B) (hm : 0 ≤ m)
    (v : Vec3) (hD : 0 < Q.precision m v) (x y : Vec3) :
    ‖quadraticMeanTransition Q m v x - quadraticMeanTransition Q m v y‖ ≤
      (1 + 3 * m * B * directionEnergy v / Q.precision m v) * ‖x - y‖ := by
  have hslope : |Q.slope v x - Q.slope v y| ≤
      (3 * B * directionSize v) * ‖x - y‖ := by
    have he : Q.slope v x - Q.slope v y = ∑ i, (x i - y i) * Q.hessianDirection v i := by
      simp only [QuadraticTerminal.slope, Fin.sum_univ_succ]
      ring
    rw [he]
    calc
      _ ≤ ∑ i, |(x i - y i) * Q.hessianDirection v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, ‖x - y‖ * (B * directionSize v) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        apply mul_le_mul _ (QuadraticTerminal.hessianDirection_abs_le hB hQ v i)
          (abs_nonneg _) (norm_nonneg _)
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - y) i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring
  have hv : ‖v‖ ≤ directionSize v := by
    apply (pi_norm_le_iff_of_nonneg (directionSize_nonneg v)).mpr
    intro i
    change |v i| ≤ ∑ j, |v j|
    exact Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
  have he : quadraticMeanTransition Q m v x - quadraticMeanTransition Q m v y =
      (x - y) + (m / Q.precision m v * (Q.slope v x - Q.slope v y)) • v := by
    ext i
    simp only [quadraticMeanTransition, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ‖x - y‖ + ‖(m / Q.precision m v * (Q.slope v x - Q.slope v y)) • v‖ := norm_add_le _ _
    _ = ‖x - y‖ + (m / Q.precision m v) * |Q.slope v x - Q.slope v y| * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg hm hD.le)]
    _ ≤ ‖x - y‖ + (m / Q.precision m v) *
        ((3 * B * directionSize v) * ‖x - y‖) * directionSize v := by
      gcongr
      positivity [directionSize_nonneg v]
    _ = _ := by unfold directionEnergy; ring

theorem vectorStep_quadratic_lipschitz_decomposition (Q : QuadraticTerminal)
    {B L m : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (hm : 0 < m) (v : Vec3) (hD : 0 < Q.precision m v)
    {f : Vec3 → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) :
    ∃ g : Vec3 → ℝ, Continuous g ∧
      (∀ x y, |g x - g y| ≤
        (L * (1 + 3 * m * B * directionEnergy v / Q.precision m v)) * ‖x - y‖) ∧
      vectorStep m v (fun x => Q.value x + f x) = fun x => (Q.update m v).value x + g x := by
  let S : ℝ := 1 + 3 * m * B * directionEnergy v / Q.precision m v
  let w := (Real.sqrt (Q.precision m v)⁻¹) • v
  let g : Vec3 → ℝ := fun x =>
    Real.log (∫ t, Real.exp (m * f (quadraticMeanTransition Q m v x + t • w)) ∂gaussianReal 0 1) / m
  have hS : 0 ≤ S := by dsimp only [S]; positivity [directionEnergy_nonneg v]
  have hg (x y : Vec3) : |g x - g y| ≤ (L * S) * ‖x - y‖ :=
    log_affine_gaussian_lipschitz hf hL hm hLip (quadraticMeanTransition Q m v)
      (quadraticMeanTransition_lipschitz Q hB hQ hm.le v hD) w x y
  have hgc : Continuous g := by
    have hlip : LipschitzWith (NNReal.mk (L * S) (mul_nonneg hL hS)) g := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change |g x - g y| ≤ (L * S) * ‖x - y‖
      exact hg x y
    exact hlip.continuous
  refine ⟨g, hgc, hg, ?_⟩
  funext x
  have hpos : 0 < quadraticAverage Q m v (fun y => Real.exp (m * f y)) x := by
    rw [quadraticAverage_eq_standard Q m v x hD (by fun_prop)]
    exact integral_exp_pos (integrable_exp_lipschitz_line hf hLip m (quadraticMeanTransition Q m v x) w)
  rw [Q.vectorStep_add_correction m v x f (ne_of_gt hm) hD hpos,
    quadraticAverage_eq_standard Q m v x hD (by fun_prop)]

theorem vectorIncrementChain_quadratic_lipschitz_decomposition
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) {B L : ℝ}
    (hB : 0 < B) (hL : 0 ≤ L) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (hm : ∀ u ∈ l, 0 < u.1 ∧ u.1 ≤ 1)
    (hv : ∀ u ∈ l, 6 * (2 ^ l.length * B) * directionEnergy u.2 ≤ 1)
    {f : Vec3 → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) :
    ∃ g : Vec3 → ℝ, Continuous g ∧
      (∀ x y, |g x - g y| ≤ (2 ^ l.length * L) * ‖x - y‖) ∧
      vectorIncrementChain l (fun x => Q.value x + f x) =
        fun x => (riccatiRecursion l Q).value x + g x := by
  induction l with
  | nil =>
    refine ⟨f, hf, ?_, rfl⟩
    simpa only [List.length_nil, pow_zero, one_mul] using hLip
  | cons u l ih =>
    have ht (w : Vec3) : 6 * (2 ^ l.length * B) * directionEnergy w ≤
        6 * (2 ^ (u :: l).length * B) * directionEnergy w := by
      have hnonneg : 0 ≤ (2 : ℝ) ^ l.length * B * directionEnergy w := by
        positivity [directionEnergy_nonneg w]
      simp only [List.length_cons, pow_succ]
      nlinarith only [hnonneg]
    have hm' : ∀ w ∈ l, 0 < w.1 ∧ w.1 ≤ 1 := fun w hw => hm w (List.mem_cons_of_mem u hw)
    have hv' : ∀ w ∈ l, 6 * (2 ^ l.length * B) * directionEnergy w.2 ≤ 1 :=
      fun w hw => (ht w.2).trans (hv w (List.mem_cons_of_mem u hw))
    rcases ih hm' hv' with ⟨g, hgc, hglip, hgeq⟩
    have hv₂ (w : ℝ × Vec3) (hw : w ∈ l) : 2 * (2 ^ l.length * B) * directionEnergy w.2 ≤ 1 := by
      have H := hv' w hw
      nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ l.length * B by positivity) (directionEnergy_nonneg w.2)]
    have hR := (riccatiAdmissible_of_small_directions l Q hB hQ hm' hv₂).2
    have hB' : 0 < (2 : ℝ) ^ l.length * B := by positivity
    have hL' : 0 ≤ (2 : ℝ) ^ l.length * L := by positivity
    have hu := hm u List.mem_cons_self
    have hvu : 6 * (2 ^ l.length * B) * directionEnergy u.2 ≤ 1 :=
      (ht u.2).trans (hv u List.mem_cons_self)
    have hvu₂ : 2 * (2 ^ l.length * B) * directionEnergy u.2 ≤ 1 := by
      nlinarith [mul_nonneg hB'.le (directionEnergy_nonneg u.2)]
    have hD := (QuadraticTerminal.update_small hB' hR ⟨hu.1.le, hu.2⟩ u.2 hvu₂).1
    have hDpos : 0 < (riccatiRecursion l Q).precision u.1 u.2 := by linarith
    rcases vectorStep_quadratic_lipschitz_decomposition (riccatiRecursion l Q)
      hB'.le hL' hR hu.1 u.2 hDpos hgc hglip with ⟨g', hg'c, hg'lip, hg'eq⟩
    have hgain : 1 + 3 * u.1 * (2 ^ l.length * B) * directionEnergy u.2 /
        (riccatiRecursion l Q).precision u.1 u.2 ≤ 2 := by
      have hmB := mul_le_of_le_one_left
        (mul_nonneg hB'.le (directionEnergy_nonneg u.2)) hu.2
      have hnum : 3 * u.1 * (2 ^ l.length * B) * directionEnergy u.2 ≤
          (riccatiRecursion l Q).precision u.1 u.2 := by nlinarith
      have H := (div_le_one hDpos).mpr hnum
      linarith
    refine ⟨g', hg'c, ?_, ?_⟩
    · intro x y
      calc
        _ ≤ ((2 ^ l.length * L) * (1 + 3 * u.1 * (2 ^ l.length * B) * directionEnergy u.2 /
            (riccatiRecursion l Q).precision u.1 u.2)) * ‖x - y‖ := hg'lip x y
        _ ≤ ((2 ^ l.length * L) * 2) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgain hL') (norm_nonneg _)
        _ = _ := by rw [List.length_cons, pow_succ]; ring
    · change vectorStep u.1 u.2 (vectorIncrementChain l (fun x => Q.value x + f x)) = _
      rw [hgeq]
      exact hg'eq

def QuadraticTerminal.scale (Q : QuadraticTerminal) (c : ℝ) : QuadraticTerminal where
  constant := c * Q.constant
  linear := fun i => c * Q.linear i
  hessian := fun i j => c * Q.hessian i j
  symmetric := fun i j => by rw [Q.symmetric i j]

theorem QuadraticTerminal.scale_value (Q : QuadraticTerminal) (c : ℝ) (x : Vec3) :
    (Q.scale c).value x = c * Q.value x := by
  simp only [QuadraticTerminal.value, QuadraticTerminal.scale, Fin.sum_univ_succ]
  ring

theorem epsilonChain_alternative_split (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (G : Vec3 → ℝ) (ε : ℝ) :
    epsilonChain l Q (fun x => G x - Q.value x) ε =
      vectorIncrementChain l (fun x => (Q.scale (1 - ε)).value x + ε * G x) := by
  apply congrArg (vectorIncrementChain l)
  funext x
  rw [Q.scale_value]
  ring

theorem scalarData_frozen_suffix_lipschitz_frames {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ t : List (ℝ × Vec3),
      t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z
      RiccatiAdmissible t (Q.scale (1 - ε)) ∧
        (∀ P ∈ riccatiPrecisions t (Q.scale (1 - ε)), 1 / 2 ≤ P) ∧
        ∃ g : Vec3 → ℝ, Continuous g ∧ (∀ x y, |g x - g y| ≤ C * ‖x - y‖) ∧
          epsilonChain t Q (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) ε =
            fun x => (riccatiRecursion t (Q.scale (1 - ε))).value x + g x := by
  let B : ℝ := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let R : ℝ := 72 * (2 ^ 12 * (6 * B)) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨min (l / 2) (min ((D.q - u) / 6) R⁻¹), 2 ^ 12 * (6 * B),
    lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hR)), by positivity, ?_⟩
  intro r hr h hh hh₀ k hk z ε hε t ht
  have hhl : h ≤ l / 2 := hh₀.trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhR : h ≤ R⁻¹ := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  have hmfull := frozenSchedule_masses β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hm : ∀ w ∈ t, 0 < w.1 ∧ w.1 ≤ 1 := fun w hw => hmfull w (ht.subset hw)
  have hlen : t.length ≤ 12 := by simpa only [frozenSchedule_length] using ht.length_le
  have hsmall : 72 * (2 ^ 12 * (6 * B)) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ R * h := by dsimp only [R]; nlinarith
      _ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left hhR hR.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  have hvfull (w : ℝ × Vec3)
      (hw : w ∈ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k) :
      6 * (2 ^ 12 * (2 * B)) * directionEnergy w.2 ≤ 1 := by
    have H := frozenSchedule_small_directions β _ h k (B := 6 * B) (by positivity) hh.le hk hsmall w hw
    rw [frozenSchedule_length] at H
    convert H using 1
    ring
  have hv (w : ℝ × Vec3) (hw : w ∈ t) : 6 * (2 ^ t.length * (2 * B)) * directionEnergy w.2 ≤ 1 := by
    apply le_trans _ (hvfull w (ht.subset hw))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
          (by positivity : 0 ≤ 2 * B)) (by norm_num : 0 ≤ (6 : ℝ)))
      (directionEnergy_nonneg w.2)
  have hv₂ (w : ℝ × Vec3) (hw : w ∈ t) : 2 * (2 ^ t.length * (2 * B)) * directionEnergy w.2 ≤ 1 := by
    have H := hv w hw
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ t.length * (2 * B) by positivity) (directionEnergy_nonneg w.2)]
  let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z
  let G := frozenTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h
  have hQ : ∀ i j, |(Q.scale (1 - ε)).hessian i j| ≤ 2 * B := by
    have hχ : |jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z| ≤ B :=
      (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z).trans (by dsimp only [B]; linarith)
    have hb := terminalTaylorQuadratic_hessian_bound β _ (r - h) h z B hB.le hχ
    intro i j
    change |(1 - ε) * Q.hessian i j| ≤ 2 * B
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith [hε.2], by linarith [hε.1]⟩)
      (hb i j) (abs_nonneg _) (by norm_num)
  have hG := scalarData_frozenTerminal_qPotential D 2 htime
  have hGLip (x y : Vec3) : |G x - G y| ≤ (3 * scalarTerminalJetBound D 2) * ‖x - y‖ := by
    have H := (hG.lipschitzWith (by norm_num)).norm_sub_le x y
    change |G x - G y| ≤ (3 * scalarTerminalJetBound D 2) * ‖x - y‖ at H
    exact H
  have hfLip (x y : Vec3) : |ε * G x - ε * G y| ≤ (6 * B) * ‖x - y‖ := by
    rw [← mul_sub, abs_mul]
    have he : |ε| ≤ 2 := abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
    calc
      _ ≤ 2 * ((3 * scalarTerminalJetBound D 2) * ‖x - y‖) :=
        mul_le_mul he (hGLip x y) (abs_nonneg _) (by norm_num)
      _ ≤ _ := by dsimp only [B]; nlinarith [norm_nonneg (x - y)]
  have hstart := riccatiAdmissible_of_small_directions t (Q.scale (1 - ε))
    (by positivity : 0 < 2 * B) hQ hm hv₂
  refine ⟨hstart.1, riccatiPrecisions_ge_half t (Q.scale (1 - ε))
    (by positivity : 0 < 2 * B) hQ hm hv₂, ?_⟩
  rcases vectorIncrementChain_quadratic_lipschitz_decomposition t (Q.scale (1 - ε))
    (by positivity : 0 < 2 * B) (by positivity : 0 ≤ 6 * B) hQ hm hv
    (continuous_const.mul hG.smooth.continuous) hfLip with ⟨g, hgc, hglip, hgeq⟩
  refine ⟨g, hgc, ?_, ?_⟩
  · intro x y
    exact (hglip x y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
        (by positivity : 0 ≤ 6 * B)) (norm_nonneg _))
  · rw [show terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z = fun x => G x - Q.value x from rfl,
      epsilonChain_alternative_split]
    exact hgeq

theorem integrable_exp_quadratic_lipschitz_line (Q : QuadraticTerminal)
    {f : Vec3 → ℝ} {L m : ℝ} (hf : Continuous f)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (v x : Vec3)
    (hD : 0 < Q.precision m v) :
    Integrable (fun t => Real.exp (m * (Q.value (x + t • v) + f (x + t • v))))
      (gaussianReal 0 1) := by
  have hi : Integrable (fun t => Real.exp (m * f (x + t • v)))
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    rw [quadraticGaussian_eq_map hD]
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    have H := integrable_exp_lipschitz_line hf hLip m
      (x + (m * Q.slope v x / Q.precision m v) • v)
      ((Real.sqrt (Q.precision m v)⁻¹) • v)
    have he (t : ℝ) : x + (m * Q.slope v x / Q.precision m v +
        Real.sqrt (Q.precision m v)⁻¹ * t) • v =
        (x + (m * Q.slope v x / Q.precision m v) • v) +
          t • ((Real.sqrt (Q.precision m v)⁻¹) • v) := by module
    simpa only [Function.comp_def, he] using H
  have H := (Q.integrable_weighted_iff m v x hD _).mp hi
  simpa only [mul_add, Real.exp_add] using H

theorem vectorStep_equal_mass_merge_of_integrable {f : Vec3 → ℝ}
    (hf : Continuous f) {m : ℝ} (hm : m ≠ 0) (v w x : Vec3)
    (hi : ∀ y, Integrable (fun t => Real.exp (m * f (y + t • w))) (gaussianReal 0 1))
    (ho : Integrable (fun t => Real.exp (m * vectorStep m w f (x + t • v)))
      (gaussianReal 0 1)) :
    vectorStep m v (vectorStep m w f) x =
      Real.log (∫ y : ℝ × ℝ, Real.exp (m * f (x + y.1 • v + y.2 • w))
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) / m := by
  have he (y : Vec3) : Real.exp (m * vectorStep m w f y) =
      ∫ t, Real.exp (m * f (y + t • w)) ∂gaussianReal 0 1 := by
    simp only [vectorStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep]
    rw [mul_div_cancel₀ _ hm, Real.exp_log (integral_exp_pos (hi y))]
  have hj : Integrable (fun y : ℝ × ℝ => Real.exp (m * f (x + y.1 • v + y.2 • w)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply (integrable_prod_iff (show Continuous
      (fun y : ℝ × ℝ => Real.exp (m * f (x + y.1 • v + y.2 • w))) by fun_prop).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun s => hi (x + s • v)), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← he] using ho
  simp only [vectorStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep] at he ⊢
  simp_rw [he]
  rw [integral_prod _ hj]

theorem vectorStep_equal_mass_comm_quadratic_lipschitz (Q : QuadraticTerminal)
    {B L m : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (hm : 0 < m) (hm₁ : m ≤ 1) (v w : Vec3)
    (hv : 4 * B * directionEnergy v ≤ 1) (hw : 4 * B * directionEnergy w ≤ 1)
    {f : Vec3 → ℝ} (hf : Continuous f) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) :
    vectorStep m v (vectorStep m w (fun y => Q.value y + f y)) =
      vectorStep m w (vectorStep m v (fun y => Q.value y + f y)) := by
  have hsmall (u : Vec3) (hu : 4 * B * directionEnergy u ≤ 1) :
      2 * B * directionEnergy u ≤ 1 := by nlinarith [directionEnergy_nonneg u]
  have hV := Q.update_small hB hQ ⟨hm.le, hm₁⟩ v (hsmall v hv)
  have hW := Q.update_small hB hQ ⟨hm.le, hm₁⟩ w (hsmall w hw)
  have hVW := (Q.update m w).update_small (by positivity : 0 < 2 * B) hW.2
    ⟨hm.le, hm₁⟩ v (by nlinarith only [hv])
  have hWV := (Q.update m v).update_small (by positivity : 0 < 2 * B) hV.2
    ⟨hm.le, hm₁⟩ w (by nlinarith only [hw])
  have hD (a : ℝ) (ha : 1 / 2 ≤ a) : 0 < a := by linarith
  rcases vectorStep_quadratic_lipschitz_decomposition Q hB.le hL hQ hm w (hD _ hW.1) hf hLip with
    ⟨gW, hgW, hLipW, hEqW⟩
  rcases vectorStep_quadratic_lipschitz_decomposition Q hB.le hL hQ hm v (hD _ hV.1) hf hLip with
    ⟨gV, hgV, hLipV, hEqV⟩
  funext x
  rw [vectorStep_equal_mass_merge_of_integrable (by unfold QuadraticTerminal.value; fun_prop)
    (ne_of_gt hm) v w x
    (fun y => integrable_exp_quadratic_lipschitz_line Q hf hLip w y (hD _ hW.1))
    (by rw [hEqW]; exact integrable_exp_quadratic_lipschitz_line (Q.update m w) hgW hLipW v x (hD _ hVW.1)),
    vectorStep_equal_mass_merge_of_integrable (by unfold QuadraticTerminal.value; fun_prop)
    (ne_of_gt hm) w v x
    (fun y => integrable_exp_quadratic_lipschitz_line Q hf hLip v y (hD _ hV.1))
    (by rw [hEqV]; exact integrable_exp_quadratic_lipschitz_line (Q.update m v) hgV hLipV w x (hD _ hWV.1))]
  rw [← integral_prod_swap]
  congr 2
  apply integral_congr_ae
  refine ae_of_all _ (fun y => ?_)
  dsimp only [Prod.swap]
  rw [add_right_comm x (y.2 • v) (y.1 • w)]

theorem vectorIncrementChain_equal_mass_perm_quadratic_lipschitz
    (Q : QuadraticTerminal) {B L m : ℝ} (hB : 0 < B) (hL : 0 ≤ L)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (hm : 0 < m) (hm₁ : m ≤ 1)
    {f : Vec3 → ℝ} (hf : Continuous f) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    {vs ws : List Vec3} (hp : vs.Perm ws)
    (hv : ∀ v ∈ vs, 6 * (2 ^ vs.length * B) * directionEnergy v ≤ 1) :
    vectorIncrementChain (vs.map (fun v => (m, v))) (fun x => Q.value x + f x) =
      vectorIncrementChain (ws.map (fun v => (m, v))) (fun x => Q.value x + f x) := by
  have hmono (n d : ℕ) (hnd : n ≤ d) (v : Vec3) :
      6 * (2 ^ n * B) * directionEnergy v ≤ 6 * (2 ^ d * B) * directionEnergy v := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnd) hB.le)
        (by norm_num : 0 ≤ (6 : ℝ))) (directionEnergy_nonneg v)
  induction hp with
  | nil => rfl
  | cons v hp ih =>
    simp only [List.map_cons, vectorIncrementChain]
    rw [ih (fun w hw => (hmono _ _ (by simp only [List.length_cons]; omega) w).trans
      (hv w (List.mem_cons_of_mem v hw)))]
  | swap v w vs =>
    let t := vs.map (fun u => (m, u))
    have hvt (u : Vec3) (hu : u ∈ vs) : 6 * (2 ^ vs.length * B) * directionEnergy u ≤ 1 :=
      (hmono _ _ (by simp only [List.length_cons]; omega) u).trans
        (hv u (by simp only [List.mem_cons]; exact Or.inr (Or.inr hu)))
    have hmt : ∀ u ∈ t, 0 < u.1 ∧ u.1 ≤ 1 := by
      intro u hu
      rcases List.mem_map.mp hu with ⟨v, _, rfl⟩
      exact ⟨hm, hm₁⟩
    have ht : ∀ u ∈ t, 6 * (2 ^ t.length * B) * directionEnergy u.2 ≤ 1 := by
      intro u hu
      rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
      simpa only [t, List.length_map] using hvt v hv
    have ht₂ : ∀ u ∈ t, 2 * (2 ^ t.length * B) * directionEnergy u.2 ≤ 1 := by
      intro u hu
      have H := ht u hu
      nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ t.length * B by positivity) (directionEnergy_nonneg u.2)]
    rcases vectorIncrementChain_quadratic_lipschitz_decomposition t Q hB hL hQ hmt ht hf hLip with
      ⟨g, hgc, hglip, hgeq⟩
    have hR := (riccatiAdmissible_of_small_directions t Q hB hQ hmt ht₂).2
    have hhead (u : Vec3) (hu : u ∈ w :: v :: vs) :
        4 * (2 ^ t.length * B) * directionEnergy u ≤ 1 := by
      have H := hv u hu
      simp only [List.length_cons, pow_succ, t, List.length_map] at H ⊢
      nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ vs.length * B by positivity) (directionEnergy_nonneg u)]
    simp only [List.map_cons, vectorIncrementChain]
    change vectorStep m w (vectorStep m v (vectorIncrementChain t (fun x => Q.value x + f x))) = _
    rw [hgeq]
    exact vectorStep_equal_mass_comm_quadratic_lipschitz (riccatiRecursion t Q)
      (by positivity : 0 < 2 ^ t.length * B) (by positivity) hR hm hm₁ w v
      (hhead w List.mem_cons_self) (hhead v (List.mem_cons_of_mem w List.mem_cons_self)) hgc hglip
  | trans hp hq ihp ihq =>
    exact (ihp hv).trans (ihq (fun v hv' => by
      rw [← hp.length_eq]
      exact hv v (hp.mem_iff.mpr hv')))

private def frozenInnerDirections (β p h k : ℝ) : List Vec3 :=
  [(β * Real.sqrt (h * p)) • rampVector p k,
    (β * Real.sqrt (h * (1 - p))) • rampVector p k,
    (β * Real.sqrt (h * (1 - p))) • postXVector p k,
    (β * Real.sqrt (h * (1 - p))) • postYVector p k,
    (β * (k * Real.sqrt (h * (4 * varianceCoefficient p)))) • rampVector p 0,
    (β * (k * Real.sqrt (h * (4 * varianceCoefficient p)))) • ((1 / Real.sqrt 2) • sharedVector p 0),
    (β * (k * Real.sqrt (h * (4 * varianceCoefficient p)))) • ((1 / 2 : ℝ) • contrast),
    (β * Real.sqrt (h * (2 - OW.repairLength p k))) • Pi.single 0 1,
    (β * Real.sqrt (h * (2 - OW.repairLength p k))) • Pi.single 1 1,
    (β * Real.sqrt (h * (2 - OW.repairLength p k))) • Pi.single 2 1]

private theorem frozenInner_eq_directions (β a p h k : ℝ) :
    frozenInner β a p h k = (frozenInnerDirections β p h k).map (fun v => (a, v)) := by
  rfl

private theorem swap_frozen_vectors (p k : ℝ) :
    OW.swap23 (commonVector p k) = commonVector p (-k) ∧
    OW.swap23 (sharedVector p k) = sharedVector p (-k) ∧
    OW.swap23 (rampVector p k) = rampVector p (-k) ∧
    OW.swap23 (postXVector p k) = postYVector p (-k) ∧
    OW.swap23 (postYVector p k) = postXVector p (-k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals ext i; fin_cases i <;>
    simp [OW.swap23_apply, commonVector, sharedVector, rampVector, postXVector, postYVector] <;> ring

private theorem swap_frozen_axes :
    OW.swap23 (contrast) = -contrast ∧
    OW.swap23 (Pi.single 0 (1 : ℝ)) = Pi.single 0 1 ∧
    OW.swap23 (Pi.single 1 (1 : ℝ)) = Pi.single 2 1 ∧
    OW.swap23 (Pi.single 2 (1 : ℝ)) = Pi.single 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals ext i; fin_cases i <;> simp [OW.swap23_apply, contrast]

theorem directionEnergy_swap23 (v : Vec3) : directionEnergy (OW.swap23 v) = directionEnergy v := by
  simp [directionEnergy, directionSize, Fin.sum_univ_succ, OW.swap23_apply]
  ring

theorem frozenInner_swap_quadratic_lipschitz (Q : QuadraticTerminal)
    {B L a : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (ha : 0 < a) (ha₁ : a ≤ 1) (β p h k : ℝ)
    {f : Vec3 → ℝ} (hf : Continuous f) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (hv : ∀ u ∈ frozenInner β a p h k, 6 * (2 ^ 10 * B) * directionEnergy u.2 ≤ 1) :
    vectorIncrementChain (frozenInner β a p h (-k)) (fun x => Q.value x + f x) =
      vectorIncrementChain ((frozenInner β a p h k).map (fun u => (u.1, OW.swap23 u.2)))
        (fun x => Q.value x + f x) := by
  let c := β * Real.sqrt (h * p)
  let d := β * Real.sqrt (h * (1 - p))
  let b := β * (k * Real.sqrt (h * (4 * varianceCoefficient p)))
  let e := β * Real.sqrt (h * (2 - OW.repairLength p k))
  let vs := (frozenInnerDirections β p h k).map OW.swap23
  let ws : List Vec3 := [c • rampVector p (-k), d • rampVector p (-k),
    d • postXVector p (-k), d • postYVector p (-k),
    b • rampVector p 0, b • ((1 / Real.sqrt 2) • sharedVector p 0),
    -(b • ((1 / 2 : ℝ) • contrast)), e • Pi.single 0 1, e • Pi.single 1 1, e • Pi.single 2 1]
  have hp : vs.Perm ws := by
    have hr := (swap_frozen_vectors p 0).2.2.1
    have hs := (swap_frozen_vectors p 0).2.1
    simp only [neg_zero] at hr hs
    dsimp only [vs, ws, frozenInnerDirections, c, d, b, e]
    simp only [List.map_cons, List.map_nil, map_smul, (swap_frozen_vectors p k).2.2.1,
      (swap_frozen_vectors p k).2.2.2.1, (swap_frozen_vectors p k).2.2.2.2, hr, hs,
      swap_frozen_axes.1, swap_frozen_axes.2.1, swap_frozen_axes.2.2.1,
      swap_frozen_axes.2.2.2, smul_neg]
    refine List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap' _ _ ?_))
    exact (List.Perm.swap _ _ []).cons _ |>.cons _ |>.cons _ |>.cons _
  have hvs (v : Vec3) (hv' : v ∈ vs) : 6 * (2 ^ vs.length * B) * directionEnergy v ≤ 1 := by
    rcases List.mem_map.mp hv' with ⟨w, hw, rfl⟩
    have H := hv (a, w) (by rw [frozenInner_eq_directions]; exact List.mem_map.mpr ⟨w, hw, rfl⟩)
    simpa only [vs, List.length_map, frozenInnerDirections, List.length_cons, List.length_nil,
      directionEnergy_swap23] using H
  have heq := vectorIncrementChain_equal_mass_perm_quadratic_lipschitz Q hB hL hQ ha ha₁ hf hLip hp hvs
  have hn : vectorIncrementChain (frozenInner β a p h (-k)) (fun x => Q.value x + f x) =
      vectorIncrementChain (ws.map (fun v => (a, v))) (fun x => Q.value x + f x) := by
    simp only [frozenInner, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      vectorIncrementChain, OW.repairLength_neg, mul_neg, neg_mul, neg_smul, vectorStep_neg,
      ws, c, d, b, e]
  rw [hn, ← heq, frozenInner_eq_directions, List.map_map, List.map_map]
  rfl

theorem frozenSchedule_even_quadratic_lipschitz (Q : QuadraticTerminal)
    {B L a : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (ha : 0 < a) (ha₁ : a ≤ 1) (β p h k z : ℝ)
    {f : Vec3 → ℝ} (hf : Continuous f) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (hsym : (fun x => Q.value x + f x) ∘ OW.swap23 = fun x => Q.value x + f x)
    (hv : ∀ u ∈ frozenInner β a p h k, 6 * (2 ^ 10 * B) * directionEnergy u.2 ≤ 1) :
    vectorIncrementChain (frozenSchedule β a p h (-k)) (fun x => Q.value x + f x) (fun _ => z) =
      vectorIncrementChain (frozenSchedule β a p h k) (fun x => Q.value x + f x) (fun _ => z) := by
  have hi := frozenInner_swap_quadratic_lipschitz Q hB hL hQ ha ha₁ β p h k hf hLip hv
  have he : vectorIncrementChain (frozenSchedule β a p h (-k)) (fun x => Q.value x + f x) =
      vectorIncrementChain ((frozenSchedule β a p h k).map (fun u => (u.1, OW.swap23 u.2)))
        (fun x => Q.value x + f x) := by
    simp only [frozenSchedule, List.map_append, vectorIncrementChain_append, frozenCommon, frozenShared,
      List.map_cons, List.map_nil, vectorIncrementChain, map_smul,
      (swap_frozen_vectors p k).1, (swap_frozen_vectors p k).2.1]
    rw [hi]
  have hp := congrFun (vectorIncrementChain_pullback OW.swap23
    (frozenSchedule β a p h k) (fun x => Q.value x + f x)) (fun _ => z)
  rw [hsym] at hp
  simp only [Function.comp_apply, OW.swap23_diagonal] at hp
  exact (congrFun he (fun _ => z)).trans hp.symm

theorem QuadraticTerminal.scale_one (Q : QuadraticTerminal) : Q.scale 1 = Q := by
  cases Q
  simp only [scale, one_mul]

theorem scalarData_frozen_uniform_riccati {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ, ∀ t : List (ℝ × Vec3),
      t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      RiccatiAdmissible t (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z) ∧
        ∀ P ∈ riccatiPrecisions t (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z),
          1 / 2 ≤ P := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨h₀, C, hh₀, _, H⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z t ht
  have H₀ := H r hr h hh hhsmall k hk z 0 ⟨by norm_num, by norm_num⟩ t ht
  simp only [sub_zero, QuadraticTerminal.scale_one] at H₀
  exact ⟨H₀.1, H₀.2.1⟩

theorem scalarData_frozen_epsilon_even {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ, ∀ ε ∈ Icc (-1 : ℝ) 2,
      frozenTerminalTheta β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h))
          (r - h) h (-k) z ε =
        frozenTerminalTheta β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h))
          (r - h) h k z ε := by
  let B : ℝ := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let R : ℝ := 72 * (2 ^ 12 * (6 * B)) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨min (l / 2) (min ((D.q - u) / 6) R⁻¹),
    lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hR)), ?_⟩
  intro r hr h hh hh₀ k hk z ε hε
  have hhl : h ≤ l / 2 := hh₀.trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhR : h ≤ R⁻¹ := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  have hsmall : 72 * (2 ^ 12 * (6 * B)) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ R * h := by dsimp only [R]; nlinarith
      _ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left hhR hR.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z
  let G := frozenTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h
  have hQ : ∀ i j, |(Q.scale (1 - ε)).hessian i j| ≤ 2 * B := by
    have hχ : |jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z| ≤ B :=
      (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z).trans (by dsimp only [B]; linarith)
    have hb := terminalTaylorQuadratic_hessian_bound β _ (r - h) h z B hB.le hχ
    intro i j
    change |(1 - ε) * Q.hessian i j| ≤ 2 * B
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith [hε.2], by linarith [hε.1]⟩)
      (hb i j) (abs_nonneg _) (by norm_num)
  have hG := scalarData_frozenTerminal_qPotential D 2 htime
  have hGLip (x y : Vec3) : |G x - G y| ≤ (3 * scalarTerminalJetBound D 2) * ‖x - y‖ := by
    have H := (hG.lipschitzWith (by norm_num)).norm_sub_le x y
    change |G x - G y| ≤ (3 * scalarTerminalJetBound D 2) * ‖x - y‖ at H
    exact H
  have hfLip (x y : Vec3) : |ε * G x - ε * G y| ≤ (6 * B) * ‖x - y‖ := by
    rw [← mul_sub, abs_mul]
    have he : |ε| ≤ 2 := abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
    calc
      _ ≤ 2 * ((3 * scalarTerminalJetBound D 2) * ‖x - y‖) :=
        mul_le_mul he (hGLip x y) (abs_nonneg _) (by norm_num)
      _ ≤ _ := by dsimp only [B]; nlinarith [norm_nonneg (x - y)]
  have hsym : (fun x => (Q.scale (1 - ε)).value x + ε * G x) ∘ OW.swap23 =
      fun x => (Q.scale (1 - ε)).value x + ε * G x := by
    funext x
    dsimp only [Function.comp_def]
    rw [Q.scale_value, Q.scale_value]
    have hQsym : Q.value (OW.swap23 x) = Q.value x := by
      simp only [Q, terminalTaylorQuadratic_value]
      simp [OW.swap23_apply, Fin.sum_univ_succ]
      ring
    have hGsym : G (OW.swap23 x) = G x :=
      congrFun (frozenTerminal_swap β (cdf (D.μ : Measure ℝ)) (r - h) h) x
    rw [hQsym, hGsym]
  have hv (w : ℝ × Vec3) (hw : w ∈ frozenInner β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k) :
      6 * (2 ^ 10 * (2 * B)) * directionEnergy w.2 ≤ 1 := by
    have hmem : w ∈ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k :=
      List.mem_append_right _ hw
    have H := frozenSchedule_small_directions β _ h k (B := 6 * B) (by positivity) hh.le hk hsmall w hmem
    rw [frozenSchedule_length] at H
    have he : 0 ≤ directionEnergy w.2 := directionEnergy_nonneg _
    norm_num at H ⊢
    nlinarith
  have He := frozenSchedule_even_quadratic_lipschitz (Q.scale (1 - ε))
    (by positivity : 0 < 2 * B) (by positivity : 0 ≤ 6 * B) hQ
    (scalarData_cdf_pos_of_pos D hs) (cdf_le_one _ _) β (1 / 2) h k z
    (continuous_const.mul hG.smooth.continuous) hfLip hsym hv
  change epsilonChain _ Q (fun x => G x - Q.value x) ε _ = epsilonChain _ Q (fun x => G x - Q.value x) ε _
  rw [epsilonChain_alternative_split, epsilonChain_alternative_split]
  exact He

theorem scalarData_frozen_epsilon_derivatives_even {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ, ∀ n : ℕ, ∀ ε ∈ Icc (0 : ℝ) 1,
      iteratedDeriv n (frozenThetaDifference β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h (-k) z) ε =
      iteratedDeriv n (frozenThetaDifference β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z) ε := by
  rcases scalarData_frozen_epsilon_even D hl hu with ⟨h₀, hh₀, H⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z n ε hε
  have He : Set.EqOn
      (frozenThetaDifference β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h (-k) z)
      (frozenThetaDifference β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z)
      (Ioo (-1 : ℝ) 2) := by
    intro e he
    unfold frozenThetaDifference
    rw [H r hr h hh hhsmall k hk z e ⟨he.1.le, he.2.le⟩]
  exact He.iteratedDeriv_of_isOpen isOpen_Ioo n ⟨by linarith [hε.1], by linarith [hε.2]⟩

theorem scalarData_thetaThirdInTilt_even {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1, ∀ k ∈ Icc (-(1 / 2 : ℝ)) (1 / 2),
      thetaThirdInTilt β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h))
          (r - h) h z ε (-k) =
        thetaThirdInTilt β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h))
          (r - h) h z ε k := by
  rcases scalarData_frozen_epsilon_derivatives_even D hl hu with ⟨h₀, hh₀, H⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall z ε hε k hk
  exact H r hr h hh hhsmall k (abs_le.mpr hk) z 3 ε hε

theorem completedSquare_normalized_moment (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (hD : 0 < Q.precision m v) {f ψ : Vec3 → ℝ} {L : ℝ}
    (hf : Continuous f) (hψ : Continuous ψ)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) :
    (∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) * ψ (x + t • v)
      ∂gaussianReal 0 1) /
      (∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) ∂gaussianReal 0 1) =
    let a := quadraticMeanTransition Q m v x
    let w := (Real.sqrt (Q.precision m v)⁻¹) • v
    ∫ t, ψ (a + t • w) ∂(gaussianReal 0 1).tilted (fun t => m * f (a + t • w)) := by
  let a := quadraticMeanTransition Q m v x
  let w := (Real.sqrt (Q.precision m v)⁻¹) • v
  have hnum : (∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) * ψ (x + t • v)
      ∂gaussianReal 0 1) = quadraticPartition Q m v x *
      (∫ t, Real.exp (m * f (a + t • w)) * ψ (a + t • w) ∂gaussianReal 0 1) := by
    simp_rw [mul_add, Real.exp_add, mul_assoc]
    rw [quadratic_weighted_moment Q m v x hD (fun y => Real.exp (m * f y) * ψ y),
      quadraticAverage_eq_standard Q m v x hD (by fun_prop)]
  have hden : (∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) ∂gaussianReal 0 1) =
      quadraticPartition Q m v x * (∫ t, Real.exp (m * f (a + t • w)) ∂gaussianReal 0 1) := by
    simp_rw [mul_add, Real.exp_add]
    rw [quadratic_weighted_moment Q m v x hD (fun y => Real.exp (m * f y)),
      quadraticAverage_eq_standard Q m v x hD (by fun_prop)]
  have hP := ne_of_gt (quadraticPartition_pos Q m v x hD)
  have hZ := ne_of_gt (integral_exp_pos (integrable_exp_lipschitz_line hf hLip m a w))
  rw [hnum, hden, integral_tilted]
  simp only [smul_eq_mul]
  change _ = ∫ t, Real.exp (m * f (a + t • w)) /
    (∫ s, Real.exp (m * f (a + s • w)) ∂gaussianReal 0 1) * ψ (a + t • w) ∂gaussianReal 0 1
  have he (t : ℝ) : Real.exp (m * f (a + t • w)) * ψ (a + t • w) /
      (∫ t, Real.exp (m * f (a + t • w)) ∂gaussianReal 0 1) =
      Real.exp (m * f (a + t • w)) /
        (∫ t, Real.exp (m * f (a + t • w)) ∂gaussianReal 0 1) * ψ (a + t • w) := by ring
  simp_rw [← he]
  rw [integral_div]
  field_simp [hP, hZ]

theorem completedSquare_polynomial_moment_bound (Q : QuadraticTerminal)
    {B L M m : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (hm : 0 ≤ m) (v : Vec3) (hD : 0 < Q.precision m v)
    {f ψ : Vec3 → ℝ} (hf : Continuous f) (hψ : Continuous ψ)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (p : ℕ) (hbound : ∀ y, |ψ y| ≤ M * (1 + ‖y‖) ^ p) (x : Vec3) :
    let S := 1 + 3 * m * B * directionEnergy v / Q.precision m v
    let w := (Real.sqrt (Q.precision m v)⁻¹) • v
    |(∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) * ψ (x + t • v)
      ∂gaussianReal 0 1) /
      (∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) ∂gaussianReal 0 1)| ≤
      (M * (1 + ‖quadraticMeanTransition Q m v 0‖ + S + ‖w‖) ^ p *
        gaussianTiltPolynomialConstant (|m| * L * ‖w‖) p) * (1 + ‖x‖) ^ p := by
  let S := 1 + 3 * m * B * directionEnergy v / Q.precision m v
  let w := (Real.sqrt (Q.precision m v)⁻¹) • v
  have hS : 0 ≤ S := by dsimp only [S]; positivity [directionEnergy_nonneg v]
  have ha : ‖quadraticMeanTransition Q m v x‖ ≤
      ‖quadraticMeanTransition Q m v 0‖ + S * ‖x‖ := by
    have H := quadraticMeanTransition_lipschitz Q hB hQ hm v hD x 0
    rw [sub_zero] at H
    have H' := norm_add_le (quadraticMeanTransition Q m v x - quadraticMeanTransition Q m v 0)
      (quadraticMeanTransition Q m v 0)
    rw [sub_add_cancel] at H'
    linarith
  have hpoly : 1 + ‖quadraticMeanTransition Q m v x‖ + ‖w‖ ≤
      (1 + ‖quadraticMeanTransition Q m v 0‖ + S + ‖w‖) * (1 + ‖x‖) := by
    nlinarith [norm_nonneg (quadraticMeanTransition Q m v 0), norm_nonneg w, norm_nonneg x]
  rw [completedSquare_normalized_moment Q m v x hD hf hψ hLip]
  have H := (affine_tilt_polynomial_moment hf hψ hL hM hLip p hbound m
    (quadraticMeanTransition Q m v x) w).2
  refine H.trans ?_
  calc
    _ ≤ (M * ((1 + ‖quadraticMeanTransition Q m v 0‖ + S + ‖w‖) * (1 + ‖x‖)) ^ p) *
        gaussianTiltPolynomialConstant (|m| * L * ‖w‖) p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpoly p) hM) (gaussianTiltPolynomialConstant_pos _ _).le
    _ = _ := by rw [mul_pow]; ring

end SKBarriers2.Corner
