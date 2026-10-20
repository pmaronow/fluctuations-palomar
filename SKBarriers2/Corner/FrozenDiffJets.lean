module

public import SKBarriers2.Corner.FrozenDiffEps

@[expose] public section

noncomputable section
open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def UniformPolynomialGrowth (U : Set ℝ) (f : ℝ → Vec3 → ℝ) : Prop :=
  ∃ M : ℝ, ∃ p : ℕ, 0 ≤ M ∧ ∀ e ∈ U, ∀ x, |f e x| ≤ M * (1 + ‖x‖) ^ p

namespace UniformPolynomialGrowth

theorem const (U : Set ℝ) (c : ℝ) : UniformPolynomialGrowth U (fun _ _ => c) := by
  exact ⟨|c|, 0, abs_nonneg _, fun _ _ _ => by rw [pow_zero, mul_one]⟩

theorem mono {U : Set ℝ} {f g : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f)
    (hfg : ∀ e ∈ U, ∀ x, |g e x| ≤ |f e x|) : UniformPolynomialGrowth U g := by
  rcases hf with ⟨M, p, hM, hf⟩
  exact ⟨M, p, hM, fun e he x => (hfg e he x).trans (hf e he x)⟩

theorem congr {U : Set ℝ} {f g : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f)
    (hfg : ∀ e ∈ U, ∀ x, g e x = f e x) : UniformPolynomialGrowth U g := by
  exact hf.mono (fun e he x => le_of_eq (congrArg abs (hfg e he x)))

theorem abs {U : Set ℝ} {f : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f) :
    UniformPolynomialGrowth U (fun e x => |f e x|) := by
  exact hf.mono (fun _ _ _ => by rw [abs_abs])

theorem add {U : Set ℝ} {f g : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f)
    (hg : UniformPolynomialGrowth U g) : UniformPolynomialGrowth U (fun e x => f e x + g e x) := by
  rcases hf with ⟨M, p, hM, hf⟩
  rcases hg with ⟨N, q, hN, hg⟩
  refine ⟨M + N, p + q, add_nonneg hM hN, ?_⟩
  intro e he x
  have hp : (1 + ‖x‖) ^ p ≤ (1 + ‖x‖) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  have hq : (1 + ‖x‖) ^ q ≤ (1 + ‖x‖) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  calc
    _ ≤ |f e x| + |g e x| := abs_add_le _ _
    _ ≤ M * (1 + ‖x‖) ^ p + N * (1 + ‖x‖) ^ q := add_le_add (hf e he x) (hg e he x)
    _ ≤ M * (1 + ‖x‖) ^ (p + q) + N * (1 + ‖x‖) ^ (p + q) :=
      add_le_add (mul_le_mul_of_nonneg_left hp hM) (mul_le_mul_of_nonneg_left hq hN)
    _ = _ := by ring

theorem mul {U : Set ℝ} {f g : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f)
    (hg : UniformPolynomialGrowth U g) : UniformPolynomialGrowth U (fun e x => f e x * g e x) := by
  rcases hf with ⟨M, p, hM, hf⟩
  rcases hg with ⟨N, q, hN, hg⟩
  refine ⟨M * N, p + q, mul_nonneg hM hN, ?_⟩
  intro e he x
  rw [abs_mul]
  exact (mul_le_mul (hf e he x) (hg e he x) (abs_nonneg _) (by positivity)).trans_eq
    (by rw [pow_add]; ring)

theorem const_mul {U : Set ℝ} {f : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f) (c : ℝ) :
    UniformPolynomialGrowth U (fun e x => c * f e x) := (const U c).mul hf

theorem neg {U : Set ℝ} {f : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f) :
    UniformPolynomialGrowth U (fun e x => -f e x) := by
  exact hf.mono (fun _ _ _ => by rw [abs_neg])

theorem sub {U : Set ℝ} {f g : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f)
    (hg : UniformPolynomialGrowth U g) : UniformPolynomialGrowth U (fun e x => f e x - g e x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem pow {U : Set ℝ} {f : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f) (n : ℕ) :
    UniformPolynomialGrowth U (fun e x => f e x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const U 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem noise {U : Set ℝ} {f : ℝ → Vec3 → ℝ} (hf : UniformPolynomialGrowth U f) (x v : Vec3) :
    ∃ M : ℝ, ∃ p : ℕ, 0 ≤ M ∧ ∀ e ∈ U, ∀ t, |f e (x + t • v)| ≤ M * (1 + t ^ 2) ^ p := by
  rcases hf with ⟨M, p, hM, hf⟩
  refine ⟨M * (2 * (1 + ‖x‖ + ‖v‖)) ^ p, p, by positivity, ?_⟩
  intro e he t
  have ht : 1 + |t| ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  have hn : 1 + ‖x + t • v‖ ≤ (2 * (1 + ‖x‖ + ‖v‖)) * (1 + t ^ 2) := by
    have H := norm_add_le x (t • v)
    rw [norm_smul, Real.norm_eq_abs] at H
    calc
      _ ≤ (1 + ‖x‖ + ‖v‖) * (1 + |t|) := by
        nlinarith [norm_nonneg v, abs_nonneg t, mul_nonneg (norm_nonneg x) (abs_nonneg t)]
      _ ≤ (1 + ‖x‖ + ‖v‖) * (2 * (1 + t ^ 2)) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  exact (hf e he _).trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hn p) hM).trans_eq (by rw [mul_pow]; ring))

end UniformPolynomialGrowth

theorem gaussianTiltPolynomialConstant_mono {L R : ℝ} (hLR : L ≤ R) (p : ℕ) :
    gaussianTiltPolynomialConstant L p ≤ gaussianTiltPolynomialConstant R p := by
  have hn : (∫ t : ℝ, Real.exp ((L + p) * |t|) ∂gaussianReal 0 1) ≤
      (∫ t : ℝ, Real.exp ((R + p) * |t|) ∂gaussianReal 0 1) :=
    integral_mono (integrable_exp_mul_abs_gaussian _) (integrable_exp_mul_abs_gaussian _)
      (fun t => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)))
  have hd : (∫ t : ℝ, Real.exp (-R * |t|) ∂gaussianReal 0 1) ≤
      (∫ t : ℝ, Real.exp (-L * |t|) ∂gaussianReal 0 1) :=
    integral_mono (integrable_exp_mul_abs_gaussian _) (integrable_exp_mul_abs_gaussian _)
      (fun t => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)))
  exact div_le_div₀ (integral_nonneg (fun _ => (Real.exp_pos _).le)) hn
    (integral_exp_pos (integrable_exp_mul_abs_gaussian _)) hd

structure QuadraticFamilyContinuousOn (Q : ℝ → QuadraticTerminal) (S : Set ℝ) : Prop where
  constant : ContinuousOn (fun e => (Q e).constant) S
  linear : ContinuousOn (fun e => (Q e).linear) S
  hessian : ContinuousOn (fun e => (Q e).hessian) S

namespace QuadraticFamilyContinuousOn

theorem precision {Q : ℝ → QuadraticTerminal} {S : Set ℝ} (H : QuadraticFamilyContinuousOn Q S)
    (m : ℝ) (v : Vec3) : ContinuousOn (fun e => (Q e).precision m v) S := by
  have hH (i j : Fin 3) : ContinuousOn (fun e => (Q e).hessian i j) S :=
    continuousOn_pi.mp (continuousOn_pi.mp H.hessian i) j
  simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature,
    QuadraticTerminal.hessianDirection, Fin.sum_univ_succ]
  fun_prop

theorem slope {Q : ℝ → QuadraticTerminal} {S : Set ℝ} (H : QuadraticFamilyContinuousOn Q S)
    (v x : Vec3) : ContinuousOn (fun e => (Q e).slope v x) S := by
  have hH (i j : Fin 3) : ContinuousOn (fun e => (Q e).hessian i j) S :=
    continuousOn_pi.mp (continuousOn_pi.mp H.hessian i) j
  have hL (i : Fin 3) : ContinuousOn (fun e => (Q e).linear i) S := continuousOn_pi.mp H.linear i
  simp only [QuadraticTerminal.slope, QuadraticTerminal.linearDirection,
    QuadraticTerminal.hessianDirection, Fin.sum_univ_succ]
  fun_prop

theorem update {Q : ℝ → QuadraticTerminal} {S : Set ℝ} (H : QuadraticFamilyContinuousOn Q S)
    (m : ℝ) (v : Vec3) (hp : ∀ e ∈ S, 0 < (Q e).precision m v) :
    QuadraticFamilyContinuousOn (fun e => (Q e).update m v) S := by
  have hH (i j : Fin 3) : ContinuousOn (fun e => (Q e).hessian i j) S :=
    continuousOn_pi.mp (continuousOn_pi.mp H.hessian i) j
  have hL (i : Fin 3) : ContinuousOn (fun e => (Q e).linear i) S := continuousOn_pi.mp H.linear i
  have hC := H.constant
  have hD := H.precision m v
  have hInv : ContinuousOn (fun e => ((Q e).precision m v)⁻¹) S :=
    hD.inv₀ (fun e he => ne_of_gt (hp e he))
  have hLog : ContinuousOn (fun e => Real.log ((Q e).precision m v)) S :=
    hD.log (fun e he => ne_of_gt (hp e he))
  constructor
  · simp only [QuadraticTerminal.update, QuadraticTerminal.linearDirection, Fin.sum_univ_succ, div_eq_mul_inv, mul_inv]
    fun_prop
  · apply continuousOn_pi.mpr
    intro i
    simp only [QuadraticTerminal.update, QuadraticTerminal.linearDirection,
      QuadraticTerminal.hessianDirection, Fin.sum_univ_succ, div_eq_mul_inv]
    fun_prop
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simp only [QuadraticTerminal.update, QuadraticTerminal.hessianDirection, Fin.sum_univ_succ, div_eq_mul_inv]
    fun_prop

theorem riccati {Q : ℝ → QuadraticTerminal} {S : Set ℝ} (H : QuadraticFamilyContinuousOn Q S)
    (l : List (ℝ × Vec3)) (hp : ∀ e ∈ S, RiccatiAdmissible l (Q e)) :
    QuadraticFamilyContinuousOn (fun e => riccatiRecursion l (Q e)) S := by
  induction l with
  | nil => exact H
  | cons w t ih => exact (ih (fun e he => (hp e he).1)).update w.1 w.2 (fun e he => (hp e he).2.2)

end QuadraticFamilyContinuousOn

theorem quadraticFamilyContinuousOn_scale (Q : QuadraticTerminal) (S : Set ℝ) :
    QuadraticFamilyContinuousOn (fun e => Q.scale (1 - e)) S := by
  constructor
  · change ContinuousOn (fun e => (1 - e) * Q.constant) S
    fun_prop
  · apply continuousOn_pi.mpr
    intro i
    change ContinuousOn (fun e => (1 - e) * Q.linear i) S
    fun_prop
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    change ContinuousOn (fun e => (1 - e) * Q.hessian i j) S
    fun_prop

def epsilonMoment (m : ℝ) (v : Vec3) (F ψ : ℝ → Vec3 → ℝ) (e : ℝ) (x : Vec3) : ℝ :=
  (∫ t, Real.exp (m * F e (x + t • v)) * ψ e (x + t • v) ∂gaussianReal 0 1) /
    (∫ t, Real.exp (m * F e (x + t • v)) ∂gaussianReal 0 1)

theorem uniformPolynomialGrowth_epsilonMoment {U S : Set ℝ} (hS : IsCompact S) (hUS : U ⊆ S)
    {Q : ℝ → QuadraticTerminal} (hQ : QuadraticFamilyContinuousOn Q S)
    {m L : ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L) (v : Vec3)
    (hD : ∀ e ∈ S, 0 < (Q e).precision m v)
    {F ψ : ℝ → Vec3 → ℝ}
    (hframe : ∀ e ∈ U, ∃ g : Vec3 → ℝ, Continuous g ∧
      (∀ x y, |g x - g y| ≤ L * ‖x - y‖) ∧ F e = fun x => (Q e).value x + g x)
    (hψ : ContinuousOn (fun p : ℝ × Vec3 => ψ p.1 p.2) (U ×ˢ univ))
    (hψgrowth : UniformPolynomialGrowth U ψ) :
    UniformPolynomialGrowth U (epsilonMoment m v F ψ) := by
  rcases hψgrowth with ⟨M, p, hM, hψbound⟩
  rcases hS.exists_bound_of_continuousOn hQ.hessian with ⟨B₀, hB₀⟩
  let B := |B₀|
  have hB : 0 ≤ B := abs_nonneg _
  have hH (e : ℝ) (he : e ∈ S) (i j : Fin 3) : |(Q e).hessian i j| ≤ B := by
    have H₁ := norm_le_pi_norm ((Q e).hessian i) j
    have H₂ := norm_le_pi_norm (Q e).hessian i
    exact (H₁.trans H₂).trans ((hB₀ e he).trans (le_abs_self _))
  have hDc := hQ.precision m v
  have hInv : ContinuousOn (fun e => ((Q e).precision m v)⁻¹) S :=
    hDc.inv₀ (fun e he => ne_of_gt (hD e he))
  have hMean : ContinuousOn (fun e => quadraticMeanTransition (Q e) m v 0) S := by
    have hs := hQ.slope v 0
    unfold quadraticMeanTransition
    simp only [div_eq_mul_inv]
    fun_prop
  let w : ℝ → Vec3 := fun e => (Real.sqrt ((Q e).precision m v)⁻¹) • v
  have hw : ContinuousOn w S := by dsimp only [w]; fun_prop
  let A : ℝ → ℝ := fun e => 1 + ‖quadraticMeanTransition (Q e) m v 0‖ +
    (1 + 3 * m * B * directionEnergy v / (Q e).precision m v) + ‖w e‖
  have hA : ContinuousOn A S := by dsimp only [A]; simp only [div_eq_mul_inv]; fun_prop
  rcases hS.exists_bound_of_continuousOn hA with ⟨A₀, hA₀⟩
  have hR : ContinuousOn (fun e => |m| * L * ‖w e‖) S := by fun_prop
  rcases hS.exists_bound_of_continuousOn hR with ⟨R₀, hR₀⟩
  let R := |R₀|
  let Amax := |A₀| + 1
  refine ⟨M * Amax ^ p * gaussianTiltPolynomialConstant R p, p, by
    exact mul_nonneg (mul_nonneg hM (by dsimp only [Amax]; positivity))
      (gaussianTiltPolynomialConstant_pos _ _).le, ?_⟩
  intro e he x
  rcases hframe e he with ⟨g, hg, hLip, heq⟩
  have hψc : Continuous (ψ e) := hψ.comp_continuous
    (show Continuous (fun x : Vec3 => (e, x)) by fun_prop) (fun _ => ⟨he, mem_univ _⟩)
  have H := completedSquare_polynomial_moment_bound (Q e) hB hL hM (hH e (hUS he)) hm v
    (hD e (hUS he)) hg hψc hLip p (hψbound e he) x
  change |epsilonMoment m v F ψ e x| ≤ _
  unfold epsilonMoment
  rw [heq]
  refine H.trans (mul_le_mul_of_nonneg_right ?_ (by positivity : 0 ≤ (1 + ‖x‖) ^ p))
  have hAe : A e ≤ Amax :=
    (le_abs_self _).trans ((hA₀ e (hUS he)).trans (by dsimp only [Amax]; linarith [le_abs_self A₀]))
  have hAnonneg : 0 ≤ A e := by dsimp only [A]; positivity [directionEnergy_nonneg v, (hD e (hUS he)).le]
  have hRe : |m| * L * ‖w e‖ ≤ R :=
    (le_abs_self _).trans ((hR₀ e (hUS he)).trans (le_abs_self _))
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hAnonneg hAe p) hM)
    (gaussianTiltPolynomialConstant_mono hRe p) (gaussianTiltPolynomialConstant_pos _ _).le
    (mul_nonneg hM (by dsimp only [Amax]; positivity))

def epsilonSpatialJet (F : ℝ → Vec3 → ℝ) (n : ℕ) (e : ℝ) (x : Vec3) : ℝ :=
  iteratedDeriv n (fun a => F a x) e

structure EpsilonJetControl (F : ℝ → Vec3 → ℝ) (U : Set ℝ) : Prop where
  continuous : ∀ n ≤ 3, ContinuousOn (fun p : ℝ × Vec3 => epsilonSpatialJet F n p.1 p.2) (U ×ˢ univ)
  growth : ∀ n, 1 ≤ n → n ≤ 3 → UniformPolynomialGrowth U (epsilonSpatialJet F n)
  regular : ∀ e ∈ U, ∀ x, EpsilonRegularAt (fun a => F a x) e

theorem EpsilonJetControl.noise_bounds {F : ℝ → Vec3 → ℝ} {U : Set ℝ}
    (H : EpsilonJetControl F U) (x v : Vec3) :
    ∃ M : ℝ, ∃ p : ℕ, 0 ≤ M ∧
      (∀ n ≤ 3, ∀ e ∈ U, Continuous (fun t : ℝ => epsilonSpatialJet F n e (x + t • v))) ∧
      (∀ n, 1 ≤ n → n ≤ 3 → ∀ e ∈ U, ∀ t : ℝ,
        |epsilonSpatialJet F n e (x + t • v)| ≤ M * (1 + t ^ 2) ^ p) := by
  have hg := (((H.growth 1 (by norm_num) (by norm_num)).abs).add
    ((H.growth 2 (by norm_num) (by norm_num)).abs)).add
      ((H.growth 3 (by norm_num) (by norm_num)).abs)
  rcases hg.noise x v with ⟨M, p, hM, hb⟩
  refine ⟨M, p, hM, ?_, ?_⟩
  · intro n hn e he
    exact (H.continuous n hn).comp_continuous
      (show Continuous (fun t : ℝ => (e, x + t • v)) by fun_prop) (fun _ => ⟨he, mem_univ _⟩)
  · intro n hn hn₃ e he t
    have H' := hb e he t
    rw [abs_of_nonneg (by positivity)] at H'
    interval_cases n <;> linarith [abs_nonneg (epsilonSpatialJet F 1 e (x + t • v)),
      abs_nonneg (epsilonSpatialJet F 2 e (x + t • v)), abs_nonneg (epsilonSpatialJet F 3 e (x + t • v))]

theorem logPartition_jet_values {Z Z₁ Z₂ Z₃ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {m e : ℝ} (hm : m ≠ 0) (he : e ∈ U)
    (h₀ : ∀ a ∈ U, HasDerivAt Z (Z₁ a) a)
    (h₁ : ∀ a ∈ U, HasDerivAt Z₁ (Z₂ a) a)
    (h₂ : ∀ a ∈ U, HasDerivAt Z₂ (Z₃ a) a) (hZ : Z e ≠ 0) :
    iteratedDeriv 1 (fun a => Real.log (Z a) / m) e = Z₁ e / (m * Z e) ∧
    iteratedDeriv 2 (fun a => Real.log (Z a) / m) e =
      Z₂ e / (m * Z e) - m * (Z₁ e / (m * Z e)) ^ 2 ∧
    iteratedDeriv 3 (fun a => Real.log (Z a) / m) e =
      Z₃ e / (m * Z e) - 3 * m * (Z₁ e / (m * Z e)) * (Z₂ e / (m * Z e)) +
        2 * m ^ 2 * (Z₁ e / (m * Z e)) ^ 3 := by
  have hder : HasDerivAt (deriv Z) (Z₂ e) e := by
    apply (h₁ e he).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds he] with a ha
    exact (h₀ a ha).deriv
  have hnear : ∀ᶠ a in 𝓝 e, DifferentiableAt ℝ Z a := by
    filter_upwards [hU.mem_nhds he] with a ha
    exact (h₀ a ha).differentiableAt
  have H₁ := (logPartition_hasDerivAt (m := m) (h₀ e he) hZ).deriv
  have H₂ := (logPartition_second (m := m) (h₀ e he) hder hnear hZ).deriv
  have H₃ := (logPartition_third_of_tower hU hm he h₀ h₁ h₂ hZ).deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at *
  rw [H₁, H₂, H₃]
  constructor
  · field_simp
  · constructor <;> field_simp

theorem EpsilonJetControl.integral_controls {F : ℝ → Vec3 → ℝ} {U : Set ℝ}
    (H : EpsilonJetControl F U) (hU : IsOpen U) (P : QuadraticTerminal) {m : ℝ}
    (hm : 0 ≤ m) (v : Vec3) (hP : 1 / 2 ≤ P.precision m v)
    (hmajor : ∀ e ∈ U, ∀ y, F e y ≤ P.value y) (x : Vec3) {e : ℝ} (he : e ∈ U) :
    IntegralDerivativeControl (gaussianReal 0 1)
      (NonlinearEpsilonStep.weight m (fun a t => F a (x + t • v)))
      (NonlinearEpsilonStep.weightFirst m (fun a t => F a (x + t • v))
        (fun a t => epsilonSpatialJet F 1 a (x + t • v))) e ∧
    IntegralDerivativeControl (gaussianReal 0 1)
      (NonlinearEpsilonStep.weightFirst m (fun a t => F a (x + t • v))
        (fun a t => epsilonSpatialJet F 1 a (x + t • v)))
      (NonlinearEpsilonStep.weightSecond m (fun a t => F a (x + t • v))
        (fun a t => epsilonSpatialJet F 1 a (x + t • v)) (fun a t => epsilonSpatialJet F 2 a (x + t • v))) e ∧
    IntegralDerivativeControl (gaussianReal 0 1)
      (NonlinearEpsilonStep.weightSecond m (fun a t => F a (x + t • v))
        (fun a t => epsilonSpatialJet F 1 a (x + t • v)) (fun a t => epsilonSpatialJet F 2 a (x + t • v)))
      (NonlinearEpsilonStep.weightThird m (fun a t => F a (x + t • v))
        (fun a t => epsilonSpatialJet F 1 a (x + t • v)) (fun a t => epsilonSpatialJet F 2 a (x + t • v))
        (fun a t => epsilonSpatialJet F 3 a (x + t • v))) e := by
  rcases H.noise_bounds x v with ⟨M, p, hM, hc, hb⟩
  rcases P.noise_envelope v x hP with ⟨A, hA⟩
  apply NonlinearEpsilonStep.integral_controls_of_polynomial_bounds hU (A := A)
    (B := 3 / 8) (M := M) (p := p) (by norm_num) (by norm_num) hM _ _ _ _ he
  · intro a ha
    exact ⟨hc 0 (by norm_num) a ha, hc 1 (by norm_num) a ha,
      hc 2 (by norm_num) a ha, hc 3 (by norm_num) a ha⟩
  · intro a ha t
    simpa only [EpsilonRegularAt, epsilonSpatialJet, iteratedDeriv_one] using H.regular a ha (x + t • v)
  · intro a ha t
    exact (mul_le_mul_of_nonneg_left (hmajor a ha _) hm).trans (hA t)
  · intro a ha t
    exact ⟨hb 1 (by norm_num) (by norm_num) a ha t, hb 2 (by norm_num) (by norm_num) a ha t,
      hb 3 (by norm_num) (by norm_num) a ha t⟩

theorem EpsilonJetControl.step {F : ℝ → Vec3 → ℝ} {U : Set ℝ}
    (H : EpsilonJetControl F U) (hU : IsOpen U) (P : QuadraticTerminal) {m : ℝ}
    (hm : 0 < m) (v : Vec3) (hP : 1 / 2 ≤ P.precision m v)
    (hmajor : ∀ e ∈ U, ∀ y, F e y ≤ P.value y)
    (hmoment : ∀ ψ : ℝ → Vec3 → ℝ,
      ContinuousOn (fun p : ℝ × Vec3 => ψ p.1 p.2) (U ×ˢ univ) →
      UniformPolynomialGrowth U ψ → UniformPolynomialGrowth U (epsilonMoment m v F ψ)) :
    EpsilonJetControl (fun e => vectorStep m v (F e)) U := by
  let f₁ := epsilonSpatialJet F 1
  let f₂ := epsilonSpatialJet F 2
  let f₃ := epsilonSpatialJet F 3
  let ψ₁ := f₁
  let ψ₂ : ℝ → Vec3 → ℝ := fun e x => f₂ e x + m * f₁ e x ^ 2
  let ψ₃ : ℝ → Vec3 → ℝ := fun e x => f₃ e x + 3 * m * f₁ e x * f₂ e x + m ^ 2 * f₁ e x ^ 3
  have hc₀ : ContinuousOn (fun p : ℝ × Vec3 => F p.1 p.2) (U ×ˢ univ) := H.continuous 0 (by norm_num)
  have hc₁ : ContinuousOn (fun p : ℝ × Vec3 => f₁ p.1 p.2) (U ×ˢ univ) := H.continuous 1 (by norm_num)
  have hc₂ : ContinuousOn (fun p : ℝ × Vec3 => f₂ p.1 p.2) (U ×ˢ univ) := H.continuous 2 (by norm_num)
  have hc₃ : ContinuousOn (fun p : ℝ × Vec3 => f₃ p.1 p.2) (U ×ˢ univ) := H.continuous 3 (by norm_num)
  have hg₁ : UniformPolynomialGrowth U f₁ := H.growth 1 (by norm_num) (by norm_num)
  have hg₂ : UniformPolynomialGrowth U f₂ := H.growth 2 (by norm_num) (by norm_num)
  have hg₃ : UniformPolynomialGrowth U f₃ := H.growth 3 (by norm_num) (by norm_num)
  have hψ₂c : ContinuousOn (fun p : ℝ × Vec3 => ψ₂ p.1 p.2) (U ×ˢ univ) :=
    hc₂.add (continuousOn_const.mul (hc₁.pow 2))
  have hψ₃c : ContinuousOn (fun p : ℝ × Vec3 => ψ₃ p.1 p.2) (U ×ˢ univ) :=
    (hc₃.add (((continuousOn_const.mul hc₁).mul hc₂))).add (continuousOn_const.mul (hc₁.pow 3))
  have hψ₂g : UniformPolynomialGrowth U ψ₂ := hg₂.add ((hg₁.pow 2).const_mul m)
  have hψ₃g : UniformPolynomialGrowth U ψ₃ :=
    (hg₃.add ((hg₁.const_mul (3 * m)).mul hg₂)).add ((hg₁.pow 3).const_mul (m ^ 2))
  let Z : ℝ → Vec3 → ℝ := fun e x => ∫ t, Real.exp (m * F e (x + t • v)) ∂gaussianReal 0 1
  let Z₁ : ℝ → Vec3 → ℝ := fun e x => m * ∫ t, Real.exp (m * F e (x + t • v)) * ψ₁ e (x + t • v) ∂gaussianReal 0 1
  let Z₂ : ℝ → Vec3 → ℝ := fun e x => m * ∫ t, Real.exp (m * F e (x + t • v)) * ψ₂ e (x + t • v) ∂gaussianReal 0 1
  let Z₃ : ℝ → Vec3 → ℝ := fun e x => m * ∫ t, Real.exp (m * F e (x + t • v)) * ψ₃ e (x + t • v) ∂gaussianReal 0 1
  have hd (x : Vec3) (e : ℝ) (he : e ∈ U) : HasDerivAt (fun a => Z a x) (Z₁ e x) e ∧
      HasDerivAt (fun a => Z₁ a x) (Z₂ e x) e ∧ HasDerivAt (fun a => Z₂ a x) (Z₃ e x) e := by
    have H' := H.integral_controls hU P hm.le v hP hmajor x he
    simpa only [NonlinearEpsilonStep.weight, NonlinearEpsilonStep.weightFirst,
      NonlinearEpsilonStep.weightSecond, NonlinearEpsilonStep.weightThird, integral_const_mul] using
      And.intro H'.1.hasDerivAt (And.intro H'.2.1.hasDerivAt H'.2.2.hasDerivAt)
  have hZ (e : ℝ) (he : e ∈ U) (x : Vec3) : Z e x ≠ 0 :=
    ne_of_gt (integral_exp_pos (H.integral_controls hU P hm.le v hP hmajor x he).1.integrable)
  have hZc : ContinuousOn (fun p : ℝ × Vec3 => Z p.1 p.2) (U ×ˢ univ) := by
    simpa only [mul_one] using continuousOn_quadratic_dominated_moment (ψ := fun _ _ => (1 : ℝ)) P hm.le (by norm_num : (0 : ℝ) ≤ 1)
      v hP hc₀ (show ContinuousOn (fun _ : ℝ × Vec3 => (1 : ℝ)) (U ×ˢ univ) from continuousOn_const)
      hmajor 0 (fun _ _ _ => by norm_num)
  have hmc (ψ : ℝ → Vec3 → ℝ) (hc : ContinuousOn (fun p : ℝ × Vec3 => ψ p.1 p.2) (U ×ˢ univ))
      (hg : UniformPolynomialGrowth U ψ) :
      ContinuousOn (fun p : ℝ × Vec3 => epsilonMoment m v F ψ p.1 p.2) (U ×ˢ univ) := by
    rcases hg with ⟨M, p, hM, hb⟩
    exact (continuousOn_quadratic_dominated_moment P hm.le hM v hP hc₀ hc hmajor p hb).div hZc
      (fun a ha => hZ a.1 ha.1 a.2)
  let A₁ := epsilonMoment m v F ψ₁
  let A₂ := epsilonMoment m v F ψ₂
  let A₃ := epsilonMoment m v F ψ₃
  have hA₁c := hmc ψ₁ hc₁ hg₁
  have hA₂c := hmc ψ₂ hψ₂c hψ₂g
  have hA₃c := hmc ψ₃ hψ₃c hψ₃g
  have hA₁g := hmoment ψ₁ hc₁ hg₁
  have hA₂g := hmoment ψ₂ hψ₂c hψ₂g
  have hA₃g := hmoment ψ₃ hψ₃c hψ₃g
  let G : ℝ → Vec3 → ℝ := fun e => vectorStep m v (F e)
  have hfun (x : Vec3) : (fun e => G e x) = fun e => Real.log (Z e x) / m := by
    funext e
    simp only [G, vectorStep, gaussianStep, ite_eq_right (ne_of_gt hm), positiveGaussianLogStep, Z]
  have hids (e : ℝ) (he : e ∈ U) (x : Vec3) :
      epsilonSpatialJet G 1 e x = A₁ e x ∧
      epsilonSpatialJet G 2 e x = A₂ e x - m * A₁ e x ^ 2 ∧
      epsilonSpatialJet G 3 e x = A₃ e x - 3 * m * A₁ e x * A₂ e x + 2 * m ^ 2 * A₁ e x ^ 3 := by
    have H' := logPartition_jet_values hU (ne_of_gt hm) he
      (fun a ha => (hd x a ha).1) (fun a ha => (hd x a ha).2.1) (fun a ha => (hd x a ha).2.2) (hZ e he x)
    have h₁ : Z₁ e x / (m * Z e x) = A₁ e x := by dsimp only [Z₁, A₁, epsilonMoment, Z]; field_simp
    have h₂ : Z₂ e x / (m * Z e x) = A₂ e x := by dsimp only [Z₂, A₂, epsilonMoment, Z]; field_simp
    have h₃ : Z₃ e x / (m * Z e x) = A₃ e x := by dsimp only [Z₃, A₃, epsilonMoment, Z]; field_simp
    rw [h₁, h₂, h₃] at H'
    simpa only [epsilonSpatialJet, hfun x] using H'
  constructor
  · intro n hn
    interval_cases n
    · simpa only [epsilonSpatialJet, iteratedDeriv_zero, G, vectorStep, gaussianStep,
        ite_eq_right (ne_of_gt hm), positiveGaussianLogStep] using
        (hZc.log (fun a ha => hZ a.1 ha.1 a.2)).div_const m
    · exact hA₁c.congr (fun a ha => (hids a.1 ha.1 a.2).1)
    · exact (hA₂c.sub (continuousOn_const.mul (hA₁c.pow 2))).congr
        (fun a ha => (hids a.1 ha.1 a.2).2.1)
    · exact ((hA₃c.sub ((continuousOn_const.mul hA₁c).mul hA₂c)).add
        (continuousOn_const.mul (hA₁c.pow 3))).congr (fun a ha => (hids a.1 ha.1 a.2).2.2)
  · intro n hn hn₃
    interval_cases n
    · exact hA₁g.congr (fun e he x => (hids e he x).1)
    · exact (hA₂g.sub ((hA₁g.pow 2).const_mul m)).congr (fun e he x => (hids e he x).2.1)
    · exact ((hA₃g.sub ((hA₁g.const_mul (3 * m)).mul hA₂g)).add
        ((hA₁g.pow 3).const_mul (2 * m ^ 2))).congr (fun e he x => (hids e he x).2.2)
  · intro e he x
    rw [EpsilonRegularAt, hfun x]
    exact logPartition_regular_of_tower hU (ne_of_gt hm) he
      (fun a ha => (hd x a ha).1) (fun a ha => (hd x a ha).2.1) (fun a ha => (hd x a ha).2.2) (hZ e he x)

theorem epsilonJetControl_affine (Q : QuadraticTerminal) (K : Vec3 → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hK : Continuous K) (hg : UniformPolynomialGrowth U (fun _ => K)) :
    EpsilonJetControl (fun e x => Q.value x + e * K x) U := by
  let F : ℝ → Vec3 → ℝ := fun e x => Q.value x + e * K x
  change EpsilonJetControl F U
  have hd (e : ℝ) (x : Vec3) : HasDerivAt (fun a => F a x) (K x) e :=
    by simpa only [F, id_eq, one_mul] using ((hasDerivAt_id e).mul_const (K x)).const_add (Q.value x)
  have h₁ (x : Vec3) : deriv (fun e => F e x) = fun _ => K x := funext (fun e => (hd e x).deriv)
  have h₂ (x : Vec3) : iteratedDeriv 2 (fun e => F e x) = fun _ => 0 := by
    funext e
    rw [iteratedDeriv_succ, iteratedDeriv_one, h₁]
    exact deriv_const e (K x)
  have h₃ (x : Vec3) : iteratedDeriv 3 (fun e => F e x) = fun _ => 0 := by
    funext e
    rw [iteratedDeriv_succ, h₂]
    exact deriv_const e 0
  have hKc : Continuous (fun p : ℝ × Vec3 => K p.2) := hK.comp continuous_snd
  constructor
  · intro n hn
    interval_cases n
    · change ContinuousOn (fun p : ℝ × Vec3 => Q.value p.2 + p.1 * K p.2) (U ×ˢ univ)
      have hQ : Continuous Q.value := by unfold QuadraticTerminal.value; fun_prop
      exact ((hQ.comp continuous_snd).add (continuous_fst.mul hKc)).continuousOn
    · simpa only [epsilonSpatialJet, iteratedDeriv_one, h₁] using hKc.continuousOn
    · simpa only [epsilonSpatialJet, h₂] using (continuousOn_const : ContinuousOn (fun _ : ℝ × Vec3 => (0 : ℝ)) (U ×ˢ univ))
    · simpa only [epsilonSpatialJet, h₃] using (continuousOn_const : ContinuousOn (fun _ : ℝ × Vec3 => (0 : ℝ)) (U ×ˢ univ))
  · intro n hn hn₃
    interval_cases n
    · exact hg.congr (fun e _ x => by
        simpa only [epsilonSpatialJet, iteratedDeriv_one] using congrFun (h₁ x) e)
    · exact (UniformPolynomialGrowth.const U 0).congr (fun e _ x => congrFun (h₂ x) e)
    · exact (UniformPolynomialGrowth.const U 0).congr (fun e _ x => congrFun (h₃ x) e)
  · intro e he x
    exact (show EpsilonChainDominationOn [] Q K U from True.intro).regular hU
      (fun _ hw => by cases hw) x he

theorem epsilonJetControl_chain (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    {U S : Set ℝ} (hU : IsOpen U) (hS : IsCompact S) (hUS : U ⊆ S) {L : ℝ} (hL : 0 ≤ L)
    (hK : Continuous K) (hKg : UniformPolynomialGrowth U (fun _ => K))
    (hm : ∀ w ∈ l, 0 < w.1)
    (hf : ∀ t, t <:+ l → ∀ e ∈ S,
      RiccatiAdmissible t (Q.scale (1 - e)) ∧ ∃ g : Vec3 → ℝ, Continuous g ∧
        (∀ x y, |g x - g y| ≤ L * ‖x - y‖) ∧
        epsilonChain t Q K e = fun x => (riccatiRecursion t (Q.scale (1 - e))).value x + g x)
    (hmajor : ∀ w t, w :: t <:+ l → ∃ P : QuadraticTerminal,
      1 / 2 ≤ P.precision w.1 w.2 ∧ ∀ e ∈ U, ∀ x, epsilonChain t Q K e x ≤ P.value x) :
    EpsilonJetControl (fun e => epsilonChain l Q K e) U := by
  induction l with
  | nil => exact epsilonJetControl_affine Q K hU hK hKg
  | cons w t ih =>
    have ht := List.suffix_cons w t
    have Ht := ih (fun v hv => hm v (List.mem_cons_of_mem w hv))
      (fun j hj => hf j (hj.trans ht)) (fun v j hj => hmajor v j (hj.trans ht))
    rcases hmajor w t (List.suffix_refl _) with ⟨P, hP, hbound⟩
    apply Ht.step hU P (hm w List.mem_cons_self) w.2 hP hbound
    intro ψ hψ hψg
    apply uniformPolynomialGrowth_epsilonMoment hS hUS
      ((quadraticFamilyContinuousOn_scale Q S).riccati t (fun e he => (hf t ht e he).1))
      (hm w List.mem_cons_self).le hL w.2 (fun e he => (hf (w :: t) (List.suffix_refl _) e he).1.2.2)
      (fun e he => (hf t ht e (hUS he)).2) hψ hψg

theorem epsilonChain_common_majorant (l : List (ℝ × Vec3)) (Q P : QuadraticTerminal)
    (K : Vec3 → ℝ) {U S : Set ℝ} (hUS : U ⊆ S) {L : ℝ}
    (hP : RiccatiAdmissible l P) (hm : ∀ w ∈ l, 0 < w.1)
    (hf : ∀ t, t <:+ l → ∀ e ∈ S,
      RiccatiAdmissible t (Q.scale (1 - e)) ∧ ∃ g : Vec3 → ℝ, Continuous g ∧
        (∀ x y, |g x - g y| ≤ L * ‖x - y‖) ∧
        epsilonChain t Q K e = fun x => (riccatiRecursion t (Q.scale (1 - e))).value x + g x)
    (hbase : ∀ e ∈ U, ∀ x, Q.value x + e * K x ≤ P.value x) :
    ∀ e ∈ U, ∀ x, epsilonChain l Q K e x ≤ (riccatiRecursion l P).value x := by
  intro e he
  apply epsilonChain_le_quadratic l Q P K e hP hm _ (hbase e he)
  intro w t ht x
  have hD := (hf (w :: t) ht e (hUS he)).1.2.2
  rcases (hf t ((List.suffix_cons w t).trans ht) e (hUS he)).2 with ⟨g, hg, hLip, heq⟩
  rw [heq]
  exact integrable_exp_quadratic_lipschitz_line _ hg hLip w.2 x hD

theorem epsilonSuffixPolynomialBounds_of_controls (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) {U : Set ℝ} (hm : ∀ w ∈ l, 0 ≤ w.1)
    (H : ∀ t, t <:+ l → EpsilonJetControl (fun e => epsilonChain t Q K e) U)
    (hmajor : ∀ w t, w :: t <:+ l → ∃ P : QuadraticTerminal,
      1 / 2 ≤ P.precision w.1 w.2 ∧ ∀ e ∈ U, ∀ x, epsilonChain t Q K e x ≤ P.value x) :
    EpsilonSuffixPolynomialBounds l Q K U := by
  apply epsilonSuffixPolynomialBounds_of_jet_bounds
  · intro w t ht x
    have Ht := H t ((List.suffix_cons w t).trans ht)
    rcases Ht.noise_bounds x w.2 with ⟨M, p, hM, hc, _⟩
    rcases hmajor w t ht with ⟨P, hP, hb⟩
    rcases P.noise_envelope w.2 x hP with ⟨A, hA⟩
    refine ⟨A, hc 0 (by norm_num), ?_⟩
    intro e he s
    exact (mul_le_mul_of_nonneg_left (hb e he _) (hm w (ht.subset List.mem_cons_self))).trans (hA s)
  · intro w t ht x
    rcases (H t ((List.suffix_cons w t).trans ht)).noise_bounds x w.2 with ⟨M, p, hM, hc, hb⟩
    exact ⟨M, p, hM, fun e he => ⟨hc 1 (by norm_num) e he, hc 2 (by norm_num) e he, hc 3 (by norm_num) e he⟩,
      fun e he s => ⟨hb 1 (by norm_num) (by norm_num) e he s, hb 2 (by norm_num) (by norm_num) e he s,
        hb 3 (by norm_num) (by norm_num) e he s⟩⟩

theorem terminalResidual_uniformPolynomialGrowth (β : ℝ) (α : ℝ → ℝ) (s h z B : ℝ)
    (hB : 0 ≤ B) (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B) (U : Set ℝ) :
    UniformPolynomialGrowth U (fun _ => terminalResidual β α s h z) := by
  let A := 6 * B + 12 * B * z ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A + 12 * B, 2, by positivity, ?_⟩
  intro e he x
  have H := terminalResidual_growth β α s h z B hB hΦ h₁ h₂ (0 : Vec3) x 1
  simp only [one_smul, zero_add, Pi.zero_apply, zero_sub, neg_sq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, one_pow, mul_one] at H
  have hs : squaredLength x ≤ 3 * ‖x‖ ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin 3, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have Hi := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at Hi
        nlinarith [sq_abs (x i), norm_nonneg x, abs_nonneg (x i)]
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hbase : |terminalResidual β α s h z x| ≤ A + 12 * B * ‖x‖ ^ 2 := by
    have H' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * B)
    dsimp only [A]
    nlinarith only [H, H']
  have hn₀ : 1 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hn₂ : ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  calc
    _ ≤ A + 12 * B * ‖x‖ ^ 2 := hbase
    _ ≤ A * (1 + ‖x‖) ^ 2 + 12 * B * (1 + ‖x‖) ^ 2 :=
      add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn₀ hA)
        (mul_le_mul_of_nonneg_left hn₂ (by positivity))
    _ = _ := by ring

theorem scalarData_frozen_suffix_polynomial_bounds {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ l / 2 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      EpsilonSuffixPolynomialBounds
        (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k)
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) (Ioo (-1 : ℝ) 2) := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨hF, C, hhF, hC, HF⟩
  let B : ℝ := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let R : ℝ := 72 * (2 ^ 12 * (20 * B)) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp only [R]; positivity
  let h₀ := min hF (min (l / 2) (min ((D.q - u) / 6) R⁻¹))
  have hh₀ : 0 < h₀ := lt_min hhF (lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hR)))
  have hhl₀ : h₀ ≤ l / 2 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨h₀, hh₀, hhl₀, ?_⟩
  intro r hr h hh hhsmall k hk z
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := hhsmall.trans hhl₀
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhR : h ≤ R⁻¹ :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  let P := terminalUpperQuadratic β α (r - h) h z B
  have hUS : Ioo (-1 : ℝ) 2 ⊆ Icc (-1 : ℝ) 2 := fun _ he => ⟨he.1.le, he.2.le⟩
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hsmall : 72 * (2 ^ 12 * (20 * B)) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ R * h := by dsimp only [R]; nlinarith
      _ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left hhR hR.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  have hstartup (j : List (ℝ × Vec3)) (hj : j <:+ full) :
      RiccatiAdmissible j P ∧ ∀ d ∈ riccatiPrecisions j P, 1 / 2 ≤ d := by
    have hlen : j.length ≤ 12 := by simpa only [full, frozenSchedule_length] using hj.length_le
    have hmass : ∀ v ∈ j, 0 < v.1 ∧ v.1 ≤ 1 := fun v hv => hm v (hj.subset hv)
    have hv (v : ℝ × Vec3) (hv : v ∈ j) : 2 * (2 ^ j.length * (20 * B)) * directionEnergy v.2 ≤ 1 := by
      have H := frozenSchedule_small_directions β _ h k (B := 20 * B) (by positivity)
        hh.le hk hsmall v (hj.subset hv)
      rw [frozenSchedule_length] at H
      refine le_trans ?_ H
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
          (by positivity : 0 ≤ 20 * B)) (by norm_num : 0 ≤ (2 : ℝ))) (directionEnergy_nonneg _)
    exact ⟨(riccatiAdmissible_of_small_directions j P (by positivity : 0 < 20 * B)
      (terminalUpperQuadratic_hessian hB.le) hmass hv).1,
      riccatiPrecisions_ge_half j P (by positivity : 0 < 20 * B)
        (terminalUpperQuadratic_hessian hB.le) hmass hv⟩
  have hf (j : List (ℝ × Vec3)) (hj : j <:+ full) (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 2) :
      RiccatiAdmissible j (Q.scale (1 - e)) ∧ ∃ g : Vec3 → ℝ, Continuous g ∧
        (∀ x y, |g x - g y| ≤ C * ‖x - y‖) ∧
        epsilonChain j Q K e = fun x => (riccatiRecursion j (Q.scale (1 - e))).value x + g x := by
    have H := HF r hr h hh hhF' k hk z e he j hj
    exact ⟨H.1, H.2.2⟩
  have h₁ (y : ℝ) : |jet β α 1 ((r - h) + 4 * h) y| ≤ B :=
    (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) ht y).trans (by dsimp only [B]; linarith)
  have h₂ : |jet β α 2 ((r - h) + 4 * h) z| ≤ B :=
    (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) ht z).trans (by dsimp only [B]; linarith)
  have hbase (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) 2) (x : Vec3) : Q.value x + e * K x ≤ P.value x :=
    terminal_epsilon_le_upper_quadratic β α (r - h) h z B hB.le (scalarData_phi_regular D ht) h₁ h₂
      (abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩) x
  have hmajor (w : ℝ × Vec3) (j : List (ℝ × Vec3)) (hj : w :: j <:+ full) :
      ∃ Pj : QuadraticTerminal, 1 / 2 ≤ Pj.precision w.1 w.2 ∧
        ∀ e ∈ Ioo (-1 : ℝ) 2, ∀ x, epsilonChain j Q K e x ≤ Pj.value x := by
    have hj' := (List.suffix_cons w j).trans hj
    refine ⟨riccatiRecursion j P, (hstartup (w :: j) hj).2 _ List.mem_cons_self, ?_⟩
    exact epsilonChain_common_majorant j Q P K hUS (hstartup j hj').1
      (fun v hv => (hm v (hj'.subset hv)).1) (fun t ht => hf t (ht.trans hj')) hbase
  have hKc : Continuous K := terminalResidual_continuous β α (r - h) h z (scalarData_phi_regular D ht)
  have hKg : UniformPolynomialGrowth (Ioo (-1 : ℝ) 2) (fun _ => K) :=
    terminalResidual_uniformPolynomialGrowth β α (r - h) h z B hB.le (scalarData_phi_regular D ht) h₁ h₂ _
  have Hcontrols (j : List (ℝ × Vec3)) (hj : j <:+ full) :
      EpsilonJetControl (fun e => epsilonChain j Q K e) (Ioo (-1 : ℝ) 2) :=
    epsilonJetControl_chain j Q K isOpen_Ioo isCompact_Icc hUS hC.le hKc hKg
      (fun v hv => (hm v (hj.subset hv)).1)
      (fun t ht => hf t (ht.trans hj)) (fun w t ht => hmajor w t (ht.trans hj))
  exact epsilonSuffixPolynomialBounds_of_controls full Q K (fun w hw => (hm w hw).1.le) Hcontrols hmajor

theorem scalarData_terminalChainDifferentiation {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      TerminalChainDifferentiation β (cdf (D.μ : Measure ℝ)) (Icc l u) h₀ (1 / 2) := by
  rcases scalarData_frozen_suffix_polynomial_bounds D hl hu with ⟨h₀, hh₀, hhl, H⟩
  exact ⟨h₀, hh₀, scalarData_terminalChainDifferentiation_of_polynomial_bounds D hl hhl isOpen_Ioo
    (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by constructor <;> norm_num) H⟩

theorem scalarData_frozen_epsilon_regular {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      EpsilonRegularAt (frozenThetaDifference β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z) ε := by
  rcases scalarData_frozen_suffix_polynomial_bounds D hl hu with ⟨h₀, hh₀, hhl, H⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε
  have hs : 0 < r - h := by linarith [hr.1]
  exact frozenThetaDifference_regular_of_polynomial_bounds β (cdf (D.μ : Measure ℝ))
    (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩ isOpen_Ioo
    (H r hr h hh hhsmall k hk z) (H r hr h hh hhsmall 0 (by norm_num) z)
    ⟨by linarith [hε.1], by linarith [hε.2]⟩

theorem scalarData_terminalMixedThirdControl_of_kRegularity
    {β C h₀ κ l u : ℝ} (D : ScalarData β) (hl : 0 < l) (hu : u < D.q)
    (hh₀ : 0 < h₀) (hκ : κ < 1 / 2)
    (HK : FrozenKRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ κ) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ ≤ h₀ ∧
      TerminalMixedThirdControl β (cdf (D.μ : Measure ℝ)) (Icc l u) (6 * C) h₁ κ := by
  rcases scalarData_frozen_suffix_polynomial_bounds D hl hu with ⟨hP, hhP, _, H⟩
  have H' : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ min h₀ hP → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      EpsilonSuffixPolynomialBounds
        (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k)
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) (Ioo (-1 : ℝ) 2) :=
    fun r hr h hh hhsmall => H r hr h hh (hhsmall.trans (min_le_right _ _))
  have HK' : FrozenKRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) C (min h₀ hP) κ := by
    intro r hr h hh hhsmall
    exact HK r hr h hh (hhsmall.trans (min_le_left _ _))
  rcases scalarData_terminalMixedThirdControl_of_polynomial_bounds_and_kRegularity
    D hl hu (lt_min hh₀ hhP) hκ H' HK' with ⟨h₁, hh₁, hh₁₀, Hmixed⟩
  exact ⟨h₁, hh₁, hh₁₀.trans (min_le_left _ _), Hmixed⟩

end SKBarriers2.Corner
