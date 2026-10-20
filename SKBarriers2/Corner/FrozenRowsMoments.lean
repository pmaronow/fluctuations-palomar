module

public import SKBarriers2.Corner.FrozenRows
public import SKBarriers2.Analysis.ParamChain

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem scalarTaylorPolynomial_two (f : ℝ → ℝ) (z y : ℝ) :
    scalarTaylorPolynomial f 2 z y = f z + deriv f z * (y - z) +
      iteratedDeriv 2 f z / 2 * (y - z) ^ 2 := by
  simp only [scalarTaylorPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial, Nat.cast_mul, Nat.cast_one]
  ring

def centeredScalarEpsilon (f : ℝ → ℝ) (z ε y : ℝ) : ℝ :=
  (1 - ε) * (deriv f z * (y - z) + iteratedDeriv 2 f z / 2 * (y - z) ^ 2) +
    ε * (f y - f z)

theorem centeredScalarEpsilon_eq (f : ℝ → ℝ) (z ε y : ℝ) :
    scalarTaylorPolynomial f 2 z y + ε * quadraticTaylorTail f z y =
      f z + centeredScalarEpsilon f z ε y := by
  rw [quadraticTaylorTail, scalarTaylorPolynomial_two]
  unfold centeredScalarEpsilon
  ring

theorem centeredScalarEpsilon_bound {f : ℝ → ℝ} {B z ε y : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : |iteratedDeriv 2 f z| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) :
    |centeredScalarEpsilon f z ε y| ≤ B * |y - z| + B / 2 * |y - z| ^ 2 := by
  have hLip : |f y - f z| ≤ B * |y - z| := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (s := (univ : Set ℝ)) (fun x _ => hf.differentiable (by simp) x)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hb₁ x) convex_univ (mem_univ z) (mem_univ y)
  have hlinear : |deriv f z * (y - z)| ≤ B * |y - z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb₁ z) (abs_nonneg _)
  have hquad : |iteratedDeriv 2 f z / 2 * (y - z) ^ 2| ≤ B / 2 * |y - z| ^ 2 := by
    rw [abs_mul, abs_div, abs_pow]
    rw [abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb₂ (by norm_num)) (by positivity)
  unfold centeredScalarEpsilon
  calc
    _ ≤ |(1 - ε) * (deriv f z * (y - z) + iteratedDeriv 2 f z / 2 * (y - z) ^ 2)| +
        |ε * (f y - f z)| := abs_add_le _ _
    _ ≤ (1 - ε) * (B * |y - z| + B / 2 * |y - z| ^ 2) + ε * (B * |y - z|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hε.2), abs_of_nonneg hε.1]
      exact add_le_add (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
        (add_le_add hlinear hquad)) (sub_nonneg.mpr hε.2))
        (mul_le_mul_of_nonneg_left hLip hε.1)
    _ ≤ _ := by
      have H := mul_nonneg hε.1
        (mul_nonneg (div_nonneg hB (by norm_num : 0 ≤ (2 : ℝ))) (sq_nonneg |y - z|))
      nlinarith

def gaussianQuadraticLower (S T : ℝ) : ℝ :=
  ∫ g : ℝ, Real.exp (-S * |g| - T * g ^ 2) ∂gaussianReal 0 1

theorem gaussianQuadraticLower_integrable {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    Integrable (fun g : ℝ => Real.exp (-S * |g| - T * g ^ 2)) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  refine ae_of_all _ (fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hS (abs_nonneg g), mul_nonneg hT (sq_nonneg g)])

theorem gaussianQuadraticLower_pos {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    0 < gaussianQuadraticLower S T :=
  integral_exp_pos (gaussianQuadraticLower_integrable hS hT)

def gaussianQuadraticMoment (S : ℝ) (p : ℕ) : ℝ :=
  ∫ g : ℝ, (1 + g ^ 2) ^ p * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2) ∂gaussianReal 0 1

theorem gaussianQuadraticMoment_integrable (S : ℝ) (p : ℕ) :
    Integrable (fun g : ℝ => (1 + g ^ 2) ^ p * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))
      (gaussianReal 0 1) :=
  integrable_polynomial_exp_square (by norm_num) (by norm_num) (2 * S ^ 2) p

theorem gaussianQuadraticMoment_nonneg (S : ℝ) (p : ℕ) : 0 ≤ gaussianQuadraticMoment S p := by
  exact integral_nonneg (fun g => by positivity)

theorem centeredScalarEpsilon_gaussian_envelope
    {f : ℝ → ℝ} {B R h z ε m v : ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : |iteratedDeriv 2 f z| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v| ≤ R * Real.sqrt h) (hsmall : 4 * B * R ^ 2 * h ≤ 1) (g : ℝ) :
    Real.exp (-(B * R) * |g| - (B * R ^ 2 / 2) * g ^ 2) ≤
        Real.exp (m * centeredScalarEpsilon f z ε (z + v * g)) ∧
      Real.exp (m * centeredScalarEpsilon f z ε (z + v * g)) ≤
        Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2) := by
  have H := centeredScalarEpsilon_bound hf hB hb₁ hb₂ hε (y := z + v * g)
  have hvg : |z + v * g - z| ≤ R * Real.sqrt h * |g| := by
    rw [add_sub_cancel_left, abs_mul]
    exact mul_le_mul_of_nonneg_right hv (abs_nonneg g)
  have hval : |m * centeredScalarEpsilon f z ε (z + v * g)| ≤
      B * R * Real.sqrt h * |g| + B * R ^ 2 * h / 2 * g ^ 2 := by
    rw [abs_mul, abs_of_nonneg hm.1]
    calc
      _ ≤ B * |z + v * g - z| + B / 2 * |z + v * g - z| ^ 2 :=
        (mul_le_mul_of_nonneg_left H hm.1).trans (mul_le_of_le_one_left (by positivity) hm.2)
      _ ≤ B * (R * Real.sqrt h * |g|) + B / 2 * (R * Real.sqrt h * |g|) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hh, sq_abs]; ring
  have hs : Real.sqrt h ≤ 1 := (Real.sqrt_le_one).mpr hh₁
  have hcoarse : |m * centeredScalarEpsilon f z ε (z + v * g)| ≤
      (B * R) * |g| + (B * R ^ 2 / 2) * g ^ 2 := by
    refine hval.trans ?_
    exact add_le_add (by nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ B * R * |g|)])
      (by nlinarith [mul_le_mul_of_nonneg_left hh₁ (by positivity : 0 ≤ B * R ^ 2 / 2 * g ^ 2)])
  constructor
  · apply Real.exp_le_exp.mpr
    have Hlower := (abs_le.mp hcoarse).1
    linarith
  · apply Real.exp_le_exp.mpr
    have hyoung : B * R * |g| ≤ 2 * (B * R) ^ 2 + g ^ 2 / 8 := by
      nlinarith [sq_nonneg (|g| - 4 * (B * R)), sq_abs g]
    have hquad : B * R ^ 2 * h / 2 * g ^ 2 ≤ g ^ 2 / 8 := by
      nlinarith [mul_le_mul_of_nonneg_right hsmall (sq_nonneg g)]
    have hlin : B * R * Real.sqrt h * |g| ≤ B * R * |g| := by
      nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ B * R * |g|)]
    linarith [le_abs_self (m * centeredScalarEpsilon f z ε (z + v * g))]

theorem scalar_cubic_gaussian_moment_bound
    {f : ℝ → ℝ} {B R h z ε m v : ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : |iteratedDeriv 2 f z| ≤ B)
    (hb₃ : ∀ x, |iteratedDeriv 3 f x| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v| ≤ R * Real.sqrt h) (hsmall : 4 * B * R ^ 2 * h ≤ 1) (n : ℕ) :
    let W := fun g => Real.exp (m * centeredScalarEpsilon f z ε (z + v * g))
    let K := fun g => quadraticTaylorTail f z (z + v * g)
    Integrable (fun g => W g * K g ^ n) (gaussianReal 0 1) ∧
      |(∫ g, W g * K g ^ n ∂gaussianReal 0 1) / (∫ g, W g ∂gaussianReal 0 1)| ≤
        ((B * R ^ 3 / 6) ^ n * gaussianQuadraticMoment (B * R) (3 * n) /
          gaussianQuadraticLower (B * R) (B * R ^ 2 / 2)) * (Real.sqrt h * h) ^ n := by
  let W := fun g => Real.exp (m * centeredScalarEpsilon f z ε (z + v * g))
  let K := fun g => quadraticTaylorTail f z (z + v * g)
  let A := (B * R ^ 3 / 6) ^ n * (Real.sqrt h * h) ^ n
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hfc : Continuous f := hf.continuous
  have hWc : Continuous W := by dsimp only [W, centeredScalarEpsilon]; fun_prop
  have hKc : Continuous K := by dsimp only [K, quadraticTaylorTail, scalarTaylorPolynomial]; fun_prop
  have henv := centeredScalarEpsilon_gaussian_envelope hf hB hR hh hh₁ hb₁ hb₂ hε hm hv hsmall
  have hK (g : ℝ) : |K g| ≤ (B * R ^ 3 / 6) * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3 := by
    have H := (quadraticTaylorTail_bounds hf hb₃ z (z + v * g)).1
    have hv' : |z + v * g - z| ≤ R * Real.sqrt h * |g| := by
      rw [add_sub_cancel_left, abs_mul]
      exact mul_le_mul_of_nonneg_right hv (abs_nonneg g)
    have hg : |g| ≤ 1 + g ^ 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
    have hs : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
      calc
        _ = Real.sqrt h * (Real.sqrt h) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hh]
    calc
      _ ≤ B * (R * Real.sqrt h * |g|) ^ 3 / 6 := H.trans (by gcongr)
      _ = (B * R ^ 3 / 6) * (Real.sqrt h * h) * |g| ^ 3 := by rw [mul_pow, mul_pow, hs]; ring
      _ ≤ _ := by gcongr
  have hbound (g : ℝ) : |W g * K g ^ n| ≤
      A * ((1 + g ^ 2) ^ (3 * n) * Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2)) := by
    rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2) *
          ((B * R ^ 3 / 6) * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3) ^ n := by
        gcongr
        · exact Real.exp_le_exp.mp (henv g).2
        · exact hK g
      _ = _ := by dsimp only [A]; rw [mul_pow, mul_pow, ← pow_mul]; ring
  have hi : Integrable (fun g => W g * K g ^ n) (gaussianReal 0 1) := by
    apply ((gaussianQuadraticMoment_integrable (B * R) (3 * n)).const_mul A).mono' ?_
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hbound g))
    exact (hWc.mul (hKc.pow n)).aestronglyMeasurable
  have hiW : Integrable W (gaussianReal 0 1) := by
    apply (gaussianQuadraticMoment_integrable (B * R) 0).mono' hWc.aestronglyMeasurable
    refine ae_of_all _ (fun g => ?_)
    change |Real.exp (m * centeredScalarEpsilon f z ε (z + v * g))| ≤ _
    simpa only [pow_zero, one_mul, abs_of_pos (Real.exp_pos _)] using (henv g).2
  have hD : 0 < gaussianQuadraticLower (B * R) (B * R ^ 2 / 2) :=
    gaussianQuadraticLower_pos (by positivity) (by positivity)
  have hDZ : gaussianQuadraticLower (B * R) (B * R ^ 2 / 2) ≤ ∫ g, W g ∂gaussianReal 0 1 :=
    integral_mono (gaussianQuadraticLower_integrable (by positivity) (by positivity)) hiW
      (fun g => (henv g).1)
  have hn : |∫ g, W g * K g ^ n ∂gaussianReal 0 1| ≤ A * gaussianQuadraticMoment (B * R) (3 * n) := by
    calc
      _ ≤ ∫ g, |W g * K g ^ n| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
      _ ≤ _ := (integral_mono hi.abs ((gaussianQuadraticMoment_integrable (B * R) (3 * n)).const_mul A)
        hbound).trans_eq (integral_const_mul _ _)
  refine ⟨hi, ?_⟩
  rw [abs_div, abs_of_pos (hD.trans_le hDZ)]
  calc
    _ ≤ (A * gaussianQuadraticMoment (B * R) (3 * n)) / (∫ g, W g ∂gaussianReal 0 1) :=
      div_le_div_of_nonneg_right hn (hD.trans_le hDZ).le
    _ ≤ (A * gaussianQuadraticMoment (B * R) (3 * n)) /
        gaussianQuadraticLower (B * R) (B * R ^ 2 / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hA (gaussianQuadraticMoment_nonneg _ _)) hD hDZ
    _ = _ := by dsimp only [A]; ring

theorem scalarData_scalar_cubic_gaussian_moment_bound
    {β s h R z ε m v : ℝ} (D : ScalarData β) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v| ≤ R * Real.sqrt h)
    (hsmall : 4 * scalarTerminalJetBound D 3 * R ^ 2 * h ≤ 1) (n : ℕ) :
    let f := Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)
    let B := scalarTerminalJetBound D 3
    let W := fun g => Real.exp (m * centeredScalarEpsilon f z ε (z + v * g))
    let K := fun g => quadraticTaylorTail f z (z + v * g)
    Integrable (fun g => W g * K g ^ n) (gaussianReal 0 1) ∧
      |(∫ g, W g * K g ^ n ∂gaussianReal 0 1) / (∫ g, W g ∂gaussianReal 0 1)| ≤
        ((B * R ^ 3 / 6) ^ n * gaussianQuadraticMoment (B * R) (3 * n) /
          gaussianQuadraticLower (B * R) (B * R ^ 2 / 2)) * (Real.sqrt h * h) ^ n := by
  apply scalar_cubic_gaussian_moment_bound (scalarData_phi_contDiff D ht)
    (scalarTerminalJetBound_nonneg D 3) hR hh hh₁
    (fun x => by simpa only [jet, iteratedDeriv_one] using
      scalarData_jet_le D (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 3) ht x)
    (scalarData_jet_le D (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 3) ht z)
    (fun x => scalarData_jet_le D (by norm_num : 1 ≤ 3) le_rfl ht x) hε hm hv hsmall n

private theorem epsilon_nil_first (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
  funext ε
  simpa only [epsilonChain, vectorIncrementChain, id_eq, one_mul] using
    (((hasDerivAt_id ε).mul_const (K x)).const_add (Q.value x)).deriv

private theorem epsilon_nil_second (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext ε
  rw [iteratedDeriv_succ, iteratedDeriv_one, epsilon_nil_first]
  exact deriv_const ε (K x)

private theorem epsilon_nil_third (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 3 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext ε
  rw [iteratedDeriv_succ, epsilon_nil_second]
  exact deriv_const ε 0

theorem epsilonPartitionWeight_singleton (m ε : ℝ) (v x : Vec3)
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (n : Fin 4) (g : ℝ) :
    epsilonPartitionWeight [(m, v)] Q K x ε n g =
      m ^ n.val * (Real.exp (m * (Q.value (x + g • v) + ε * K (x + g • v))) *
        K (x + g • v) ^ n.val) := by
  fin_cases n <;>
    simp only [epsilonPartitionWeight, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals
    dsimp only [epsilonSuffixNoiseJet, NonlinearEpsilonStep.weight,
      NonlinearEpsilonStep.weightFirst, NonlinearEpsilonStep.weightSecond, NonlinearEpsilonStep.weightThird]
    simp only [iteratedDeriv_zero, iteratedDeriv_one, epsilon_nil_first, epsilon_nil_second,
      epsilon_nil_third, pow_zero, pow_one, zero_add, add_zero, mul_zero, one_mul, mul_one]
    simp only [epsilonChain, vectorIncrementChain]
  all_goals ring

private theorem scalar_axis_point (z v g : ℝ) :
    (fun _ : Fin 3 => z) + g • (v • (Pi.single 2 1 : Vec3)) = ![z, z, z + v * g] := by
  ext i
  fin_cases i <;> simp [mul_comm]

theorem terminalResidual_scalar_axis (β : ℝ) (α : ℝ → ℝ) (s h z v g : ℝ) :
    terminalResidual β α s h z ((fun _ => z) + g • (v • (Pi.single 2 1 : Vec3))) =
      quadraticTaylorTail (Phi β α (s + 4 * h)) z (z + v * g) := by
  rw [scalar_axis_point, terminalResidual_eq_quadraticTaylorTails]
  have hself : quadraticTaylorTail (Phi β α (s + 4 * h)) z z = 0 := by
    rw [quadraticTaylorTail, scalarTaylorPolynomial_two]
    ring
  simp [Fin.sum_univ_succ, hself]

theorem terminalEpsilon_scalar_axis (β : ℝ) (α : ℝ → ℝ) (s h z ε v g : ℝ) :
    (terminalTaylorQuadratic β α s h z).value
        ((fun _ => z) + g • (v • (Pi.single 2 1 : Vec3))) +
      ε * terminalResidual β α s h z ((fun _ => z) + g • (v • (Pi.single 2 1 : Vec3))) =
      3 * Phi β α (s + 4 * h) z +
        centeredScalarEpsilon (Phi β α (s + 4 * h)) z ε (z + v * g) := by
  rw [terminalResidual_scalar_axis, scalar_axis_point, terminalTaylorQuadratic_value]
  simp [Fin.sum_univ_succ, quadraticTaylorTail, scalarTaylorPolynomial_two,
    centeredScalarEpsilon, jet, iteratedDeriv_one]
  ring

theorem epsilonPartitionMoment_scalar_axis_ratio (β : ℝ) (α : ℝ → ℝ)
    (s h z ε m v : ℝ) (n : Fin 4) :
    epsilonPartitionMoment [(m, v • (Pi.single 2 1 : Vec3))]
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) (fun _ => z) ε n /
      epsilonPartitionMoment [(m, v • (Pi.single 2 1 : Vec3))]
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) (fun _ => z) ε 0 =
      m ^ n.val *
        ((∫ g, Real.exp (m * centeredScalarEpsilon (Phi β α (s + 4 * h)) z ε (z + v * g)) *
            quadraticTaylorTail (Phi β α (s + 4 * h)) z (z + v * g) ^ n.val ∂gaussianReal 0 1) /
          (∫ g, Real.exp (m * centeredScalarEpsilon (Phi β α (s + 4 * h)) z ε (z + v * g))
            ∂gaussianReal 0 1)) := by
  let E := Real.exp (m * (3 * Phi β α (s + 4 * h) z))
  let W := fun g => Real.exp (m * centeredScalarEpsilon (Phi β α (s + 4 * h)) z ε (z + v * g))
  let K := fun g => quadraticTaylorTail (Phi β α (s + 4 * h)) z (z + v * g)
  have heq (j : Fin 4) :
      epsilonPartitionMoment [(m, v • (Pi.single 2 1 : Vec3))]
          (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) (fun _ => z) ε j =
        E * (m ^ j.val * (∫ g, W g * K g ^ j.val ∂gaussianReal 0 1)) := by
    unfold epsilonPartitionMoment
    have hf (g : ℝ) : epsilonPartitionWeight [(m, v • (Pi.single 2 1 : Vec3))]
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) (fun _ => z) ε j g =
        E * (m ^ j.val * (W g * K g ^ j.val)) := by
      rw [epsilonPartitionWeight_singleton, terminalEpsilon_scalar_axis, terminalResidual_scalar_axis]
      dsimp only [E, W, K]
      rw [mul_add, Real.exp_add]
      ring
    simp_rw [hf]
    rw [integral_const_mul, integral_const_mul]
  rw [heq n, heq 0]
  simp only [Fin.val_zero, pow_zero, one_mul, mul_one]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _), mul_div_assoc]

theorem scalarData_axis_singleton_partition_bound {β s h R z ε m v : ℝ}
    (D : ScalarData β) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v| ≤ R * Real.sqrt h)
    (hsmall : 4 * scalarTerminalJetBound D 3 * R ^ 2 * h ≤ 1) (n : Fin 4) :
    let B := scalarTerminalJetBound D 3
    |epsilonPartitionMoment [(m, v • (Pi.single 2 1 : Vec3))]
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z) ε n /
      epsilonPartitionMoment [(m, v • (Pi.single 2 1 : Vec3))]
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z) ε 0| ≤
      ((B * R ^ 3 / 6) ^ n.val * gaussianQuadraticMoment (B * R) (3 * n.val) /
        gaussianQuadraticLower (B * R) (B * R ^ 2 / 2)) * (Real.sqrt h * h) ^ n.val := by
  rw [epsilonPartitionMoment_scalar_axis_ratio, abs_mul, abs_pow, abs_of_nonneg hm.1]
  have H := (scalarData_scalar_cubic_gaussian_moment_bound (z := z) D ht hR hh hh₁ hε hm hv hsmall n.val).2
  exact (mul_le_mul_of_nonneg_left H (pow_nonneg hm.1 _)).trans
    (mul_le_of_le_one_left ((abs_nonneg _).trans H) (pow_le_one₀ hm.1 hm.2))

theorem frozen_last_direction_bound {β h k : ℝ} (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    |β * Real.sqrt (h * (2 - OW.repairLength (1 / 2) k))| ≤
      (2 * (|β| + 1)) * Real.sqrt h := by
  have hlen := OW.repairLength_mem (p := (1 / 2 : ℝ)) ⟨by norm_num, le_rfl⟩ hk
  have hs : Real.sqrt (2 - OW.repairLength (1 / 2) k) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith [hlen.1]⟩
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul hh]
  calc
    _ ≤ |β| * (Real.sqrt h * 2) := by gcongr
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg h]

theorem scalarData_frozen_last_raw_moment_bound {β s h z ε k : ℝ}
    (D : ScalarData β) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (hh : 0 ≤ h) (hh₁ : h ≤ 1) (hε : ε ∈ Icc (0 : ℝ) 1) (hk : |k| ≤ 1 / 2)
    (hsmall : 4 * scalarTerminalJetBound D 3 * (2 * (|β| + 1)) ^ 2 * h ≤ 1) (n : Fin 4) :
    let B := scalarTerminalJetBound D 3
    let R := 2 * (|β| + 1)
    |partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) s) s h z ε 11) n k /
      partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) s) s h z ε 11) 0 k| ≤
      ((B * R ^ 3 / 6) ^ n.val * gaussianQuadraticMoment (B * R) (3 * n.val) /
        gaussianQuadraticLower (B * R) (B * R ^ 2 / 2)) * (Real.sqrt h * h) ^ n.val := by
  exact scalarData_axis_singleton_partition_bound D ht (by positivity) hh hh₁ hε
    ⟨cdf_nonneg _ _, cdf_le_one _ _⟩ (frozen_last_direction_bound hh hk) hsmall n

theorem scalarData_frozen_last_raw_moments {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ B h₀ : ℝ, 1 ≤ B ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
        ∀ ε ∈ Icc (0 : ℝ) 1, ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ n : Fin 4,
          |partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11) n k /
            partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11) 0 k| ≤
              B * (Real.sqrt h * h) ^ n.val := by
  let J := scalarTerminalJetBound D 3
  let R := 2 * (|β| + 1)
  let A : Fin 4 → ℝ := fun n =>
    (J * R ^ 3 / 6) ^ n.val * gaussianQuadraticMoment (J * R) (3 * n.val) /
      gaussianQuadraticLower (J * R) (J * R ^ 2 / 2)
  have hJ : 0 ≤ J := scalarTerminalJetBound_nonneg D 3
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hA (n : Fin 4) : 0 ≤ A n := by
    exact div_nonneg (mul_nonneg (pow_nonneg (by positivity) _)
      (gaussianQuadraticMoment_nonneg _ _))
      (gaussianQuadraticLower_pos (by positivity) (by positivity)).le
  let B := 1 + ∑ n : Fin 4, A n
  have hB : 1 ≤ B := by
    have H := Finset.sum_nonneg (fun n (_ : n ∈ (Finset.univ : Finset (Fin 4))) => hA n)
    dsimp only [B]
    linarith
  have hAB (n : Fin 4) : A n ≤ B := by
    have H := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hA i)
      (Finset.mem_univ n)
    dsimp only [B]
    linarith
  let Q := 1 + 4 * J * R ^ 2
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let h₀ := min 1 (min (l / 2) (min ((D.q - u) / 6) Q⁻¹))
  have hh₀ : 0 < h₀ := lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (inv_pos.mpr hQ)))
  refine ⟨B, h₀, hB, hh₀, ?_⟩
  intro r hr h hh hhsmall z ε hε k hk n
  have hh₁ : h ≤ 1 := hhsmall.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhQ : h ≤ Q⁻¹ :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hsmall : 4 * J * R ^ 2 * h ≤ 1 := by
    calc
      _ ≤ Q * h := by dsimp only [Q]; nlinarith
      _ ≤ Q * Q⁻¹ := mul_le_mul_of_nonneg_left hhQ hQ.le
      _ = 1 := mul_inv_cancel₀ hQ.ne'
  exact (scalarData_frozen_last_raw_moment_bound D ht hh.le hh₁ hε hk hsmall n).trans
    (mul_le_mul_of_nonneg_right (hAB n) (pow_nonneg (by positivity) _))

theorem quadratic_gaussian_integral_k_controls
    {F F₁ F₂ : ℝ → ℝ → ℝ} {U : Set ℝ} {k A C b : ℝ} {p : ℕ}
    (hU : U ∈ 𝓝 k) (hb : 0 ≤ b) (hbsmall : 2 * b < 1)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (F x) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (F₁ x) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (F₂ x) (gaussianReal 0 1))
    (hd : ∀ g : ℝ, ∀ x ∈ U, HasDerivAt (fun y => F y g) (F₁ x g) x ∧
      HasDerivAt (fun y => F₁ y g) (F₂ x g) x)
    (hbound : ∀ x ∈ U, ∀ g : ℝ,
      |F x g| ≤ C * ((1 + g ^ 2) ^ p * Real.exp (A + b * g ^ 2)) ∧
      |F₁ x g| ≤ C * ((1 + g ^ 2) ^ p * Real.exp (A + b * g ^ 2)) ∧
      |F₂ x g| ≤ C * ((1 + g ^ 2) ^ p * Real.exp (A + b * g ^ 2))) :
    IntegralDerivativeControl (gaussianReal 0 1) F F₁ k ∧
      IntegralDerivativeControl (gaussianReal 0 1) F₁ F₂ k := by
  let G : ℝ → ℝ := fun g => C * ((1 + g ^ 2) ^ p * Real.exp (A + b * g ^ 2))
  have hG : Integrable G (gaussianReal 0 1) :=
    (integrable_polynomial_exp_square hb hbsmall A p).const_mul C
  have hk : k ∈ U := mem_of_mem_nhds hU
  have hi₀ : Integrable (F k) (gaussianReal 0 1) :=
    hG.mono' (hmeas k hk).1 (ae_of_all _ (fun g => by
      simpa only [Real.norm_eq_abs] using (hbound k hk g).1))
  have hi₁ : Integrable (F₁ k) (gaussianReal 0 1) :=
    hG.mono' (hmeas k hk).2.1 (ae_of_all _ (fun g => by
      simpa only [Real.norm_eq_abs] using (hbound k hk g).2.1))
  constructor
  · exact ⟨U, hU, G, Filter.mem_of_superset hU (fun x hx => (hmeas x hx).1), hi₀,
      (hmeas k hk).2.1, hG,
      ae_of_all _ (fun g x hx => by simpa only [Real.norm_eq_abs] using (hbound x hx g).2.1),
      ae_of_all _ (fun g x hx => (hd g x hx).1)⟩
  · exact ⟨U, hU, G, Filter.mem_of_superset hU (fun x hx => (hmeas x hx).2.1), hi₁,
      (hmeas k hk).2.2, hG,
      ae_of_all _ (fun g x hx => by simpa only [Real.norm_eq_abs] using (hbound x hx g).2.2),
      ae_of_all _ (fun g x hx => (hd g x hx).2)⟩

end SKBarriers2.Corner
