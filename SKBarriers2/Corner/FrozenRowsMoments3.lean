module

public import SKBarriers2.Corner.FrozenRowsMoments2

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def powerMoment (n : Fin 4) (r : ℝ) : ℝ := ![1, r, r ^ 2, r ^ 3] n

def powerMomentFirst (n : Fin 4) (r r₁ : ℝ) : ℝ :=
  ![0, r₁, 2 * r * r₁, 3 * r ^ 2 * r₁] n

def powerMomentSecond (n : Fin 4) (r r₁ r₂ : ℝ) : ℝ :=
  ![0, r₂, 2 * r₁ ^ 2 + 2 * r * r₂, 6 * r * r₁ ^ 2 + 3 * r ^ 2 * r₂] n

theorem powerMoment_eq_pow (n : Fin 4) (r : ℝ) : powerMoment n r = r ^ n.val := by
  fin_cases n <;> simp [powerMoment]

theorem powerMoment_derivatives {r r₁ r₂ : ℝ → ℝ} {k : ℝ}
    (hr : HasDerivAt r (r₁ k) k) (hr₁ : HasDerivAt r₁ (r₂ k) k) (n : Fin 4) :
    HasDerivAt (fun a => powerMoment n (r a)) (powerMomentFirst n (r k) (r₁ k)) k ∧
      HasDerivAt (fun a => powerMomentFirst n (r a) (r₁ a))
        (powerMomentSecond n (r k) (r₁ k) (r₂ k)) k := by
  fin_cases n
  · exact ⟨hasDerivAt_const k 1, hasDerivAt_const k 0⟩
  · exact ⟨hr, hr₁⟩
  · constructor
    · change HasDerivAt (fun a => r a ^ 2) (2 * r k * r₁ k) k
      convert hr.pow 2 using 1
      norm_num
    · change HasDerivAt (fun a => 2 * r a * r₁ a) (2 * r₁ k ^ 2 + 2 * r k * r₂ k) k
      convert ((hr.const_mul 2).mul hr₁) using 1
      ring
  · constructor
    · change HasDerivAt (fun a => r a ^ 3) (3 * r k ^ 2 * r₁ k) k
      exact hr.pow 3
    · change HasDerivAt (fun a => 3 * r a ^ 2 * r₁ a) (6 * r k * r₁ k ^ 2 + 3 * r k ^ 2 * r₂ k) k
      convert (((hr.pow 2).const_mul 3).mul hr₁) using 1
      norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.pow_apply]
      ring

def exponentialMoment (n : Fin 4) (a r : ℝ) : ℝ := Real.exp a * powerMoment n r

def exponentialMomentFirst (n : Fin 4) (a a₁ r r₁ : ℝ) : ℝ :=
  Real.exp a * (a₁ * powerMoment n r + powerMomentFirst n r r₁)

def exponentialMomentSecond (n : Fin 4) (a a₁ a₂ r r₁ r₂ : ℝ) : ℝ :=
  Real.exp a * ((a₂ + a₁ ^ 2) * powerMoment n r + 2 * a₁ * powerMomentFirst n r r₁ +
    powerMomentSecond n r r₁ r₂)

theorem exponentialMoment_derivatives {a a₁ a₂ r r₁ r₂ : ℝ → ℝ} {k : ℝ}
    (ha : HasDerivAt a (a₁ k) k) (ha₁ : HasDerivAt a₁ (a₂ k) k)
    (hr : HasDerivAt r (r₁ k) k) (hr₁ : HasDerivAt r₁ (r₂ k) k) (n : Fin 4) :
    HasDerivAt (fun x => exponentialMoment n (a x) (r x))
        (exponentialMomentFirst n (a k) (a₁ k) (r k) (r₁ k)) k ∧
      HasDerivAt (fun x => exponentialMomentFirst n (a x) (a₁ x) (r x) (r₁ x))
        (exponentialMomentSecond n (a k) (a₁ k) (a₂ k) (r k) (r₁ k) (r₂ k)) k := by
  have hp := powerMoment_derivatives hr hr₁ n
  constructor
  · convert ha.exp.mul hp.1 using 1 <;>
      dsimp only [exponentialMoment, exponentialMomentFirst]
    all_goals first | rfl | ring
  · convert ha.exp.mul ((ha₁.mul hp.1).add hp.2) using 1 <;>
      dsimp only [exponentialMomentFirst, exponentialMomentSecond]
    all_goals
      first | rfl | (simp only [Pi.mul_apply, Pi.add_apply]; ring)

def residualCurveFirst (f : ℝ → ℝ) (z : ℝ) (y y₁ : Vec3) : ℝ :=
  ∑ i, quadraticTaylorTailFirst f z (y i) * y₁ i

def residualCurveSecond (f : ℝ → ℝ) (z : ℝ) (y y₁ y₂ : Vec3) : ℝ :=
  ∑ i, (quadraticTaylorTailSecond f z (y i) * y₁ i ^ 2 + quadraticTaylorTailFirst f z (y i) * y₂ i)

theorem terminalResidual_curve_derivatives {β s h z k : ℝ} {α : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Phi β α (s + 4 * h))) {y y₁ y₂ : ℝ → Vec3}
    (hy : ∀ i, HasDerivAt (fun a => y a i) (y₁ k i) k)
    (hy₁ : ∀ i, HasDerivAt (fun a => y₁ a i) (y₂ k i) k) :
    HasDerivAt (fun a => terminalResidual β α s h z (y a))
        (residualCurveFirst (Phi β α (s + 4 * h)) z (y k) (y₁ k)) k ∧
      HasDerivAt (fun a => residualCurveFirst (Phi β α (s + 4 * h)) z (y a) (y₁ a))
        (residualCurveSecond (Phi β α (s + 4 * h)) z (y k) (y₁ k) (y₂ k)) k := by
  have H (i : Fin 3) := quadraticTaylorTail_comp_derivatives (z := z) (y := fun a => y a i)
    (y₁ := fun a => y₁ a i) (y₂ := fun a => y₂ a i) hf (hy i) (hy₁ i)
  constructor
  · simp_rw [terminalResidual_eq_quadraticTaylorTails]
    exact HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => (H i).1)
  · exact HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => (H i).2)

theorem scalarData_terminalResidual_curve_bounds {β s h z R : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h) (hR : 0 ≤ R) (y y₁ y₂ : Vec3)
    (hy : ∀ i, |y i - z| ≤ R * Real.sqrt h)
    (hy₁ : ∀ i, |y₁ i| ≤ R * Real.sqrt h) (hy₂ : ∀ i, |y₂ i| ≤ R * Real.sqrt h) :
    let C := (6 * scalarTerminalJetBound D 3 * R ^ 3) * (Real.sqrt h * h)
    |terminalResidual β (cdf (D.μ : Measure ℝ)) s h z y| ≤ C ∧
      |residualCurveFirst (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z y y₁| ≤ C ∧
      |residualCurveSecond (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z y y₁ y₂| ≤ C := by
  let B := scalarTerminalJetBound D 3
  have hB : 0 ≤ B := scalarTerminalJetBound_nonneg D 3
  have H (i : Fin 3) := quadraticTaylorTail_comp_bounds (scalarData_phi_contDiff D ht)
    (fun x => scalarData_jet_le D (by norm_num : 1 ≤ 3) le_rfl ht x)
    hB (mul_nonneg hR (Real.sqrt_nonneg _)) (hy i) (hy₁ i) (hy₂ i)
  have hs : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
    calc
      _ = Real.sqrt h * (Real.sqrt h) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hh]
  have Hsum (G : Fin 3 → ℝ) (hG : ∀ i, |G i| ≤ 2 * B * (R * Real.sqrt h) ^ 3) :
      |∑ i, G i| ≤ (6 * B * R ^ 3) * (Real.sqrt h * h) := by
    calc
      _ ≤ ∑ i, |G i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, 2 * B * (R * Real.sqrt h) ^ 3 := Finset.sum_le_sum (fun i _ => hG i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_pow, hs]; ring
  rw [terminalResidual_eq_quadraticTaylorTails]
  exact ⟨Hsum _ (fun i => (H i).1), Hsum _ (fun i => (H i).2.1), Hsum _ (fun i => (H i).2.2)⟩

private theorem abs_mul_le_mul {a b A B : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

theorem powerMoment_bounds {r r₁ r₂ R : ℝ} (hR : 0 ≤ R)
    (hr : |r| ≤ R) (hr₁ : |r₁| ≤ R) (hr₂ : |r₂| ≤ R) (n : Fin 4) :
    |powerMoment n r| ≤ R ^ n.val ∧ |powerMomentFirst n r r₁| ≤ 3 * R ^ n.val ∧
      |powerMomentSecond n r r₁ r₂| ≤ 9 * R ^ n.val := by
  have hrpow (p : ℕ) : |r ^ p| ≤ R ^ p := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hr p
  have hrr₁ : |r * r₁| ≤ R ^ 2 := (abs_mul_le_mul hR hr hr₁).trans_eq (by ring)
  have hrr₂ : |r * r₂| ≤ R ^ 2 := (abs_mul_le_mul hR hr hr₂).trans_eq (by ring)
  have hr₁sq : |r₁ ^ 2| ≤ R ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hr₁ 2
  have hsq₁ : |r ^ 2 * r₁| ≤ R ^ 3 := (abs_mul_le_mul (sq_nonneg _) (hrpow 2) hr₁).trans_eq (by ring)
  have hsq₂ : |r ^ 2 * r₂| ≤ R ^ 3 := (abs_mul_le_mul (sq_nonneg _) (hrpow 2) hr₂).trans_eq (by ring)
  have hsq₃ : |r * r₁ ^ 2| ≤ R ^ 3 := (abs_mul_le_mul hR hr hr₁sq).trans_eq (by ring)
  fin_cases n
  · norm_num [powerMoment, powerMomentFirst, powerMomentSecond]
  · simpa only [powerMoment, powerMomentFirst, powerMomentSecond, Matrix.cons_val_zero', Matrix.cons_val_succ',
      pow_one] using And.intro hr (And.intro (hr₁.trans (by nlinarith)) (hr₂.trans (by nlinarith)))
  · simp only [powerMoment, powerMomentFirst, powerMomentSecond, Matrix.cons_val_zero', Matrix.cons_val_succ']
    refine ⟨hrpow 2, ?_, ?_⟩
    · calc
        _ = 2 * |r * r₁| := by rw [mul_assoc, abs_mul]; norm_num
        _ ≤ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hrr₁ (by norm_num)
        _ ≤ _ := by nlinarith [sq_nonneg R]
    · calc
        _ ≤ |2 * r₁ ^ 2| + |2 * r * r₂| := abs_add_le _ _
        _ = 2 * |r₁ ^ 2| + 2 * |r * r₂| := by rw [mul_assoc]; simp only [abs_mul]; norm_num
        _ ≤ 2 * R ^ 2 + 2 * R ^ 2 := by gcongr
        _ ≤ _ := by nlinarith [sq_nonneg R]
  · simp only [powerMoment, powerMomentFirst, powerMomentSecond, Matrix.cons_val_zero', Matrix.cons_val_succ']
    refine ⟨hrpow 3, ?_, ?_⟩
    · calc
        _ = 3 * |r ^ 2 * r₁| := by rw [mul_assoc, abs_mul]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq₁ (by norm_num)
    · calc
        _ ≤ |6 * r * r₁ ^ 2| + |3 * r ^ 2 * r₂| := abs_add_le _ _
        _ = 6 * |r * r₁ ^ 2| + 3 * |r ^ 2 * r₂| := by simp only [mul_assoc, abs_mul]; norm_num
        _ ≤ 6 * R ^ 3 + 3 * R ^ 3 := by gcongr
        _ = _ := by ring

theorem exponentialMoment_bounds {a a₁ a₂ r r₁ r₂ E L q R : ℝ}
    (hE : Real.exp a ≤ E) (hL : 0 ≤ L) (hq : 1 ≤ q) (hR : 0 ≤ R)
    (ha₁ : |a₁| ≤ L * q) (ha₂ : |a₂| ≤ L * q)
    (hr : |r| ≤ R) (hr₁ : |r₁| ≤ R) (hr₂ : |r₂| ≤ R) (n : Fin 4) :
    let C := 10 * (L + 1) ^ 2 * q ^ 2 * R ^ n.val * E
    |exponentialMoment n a r| ≤ C ∧ |exponentialMomentFirst n a a₁ r r₁| ≤ C ∧
      |exponentialMomentSecond n a a₁ a₂ r r₁ r₂| ≤ C := by
  have hq₀ : 0 ≤ q := by linarith
  have hE₀ : 0 ≤ E := (Real.exp_pos a).le.trans hE
  have hP := powerMoment_bounds hR hr hr₁ hr₂ n
  have hRpow : 0 ≤ R ^ n.val := pow_nonneg hR _
  have hq₂ : q ≤ q ^ 2 := by nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq)]
  have hq₂one : 1 ≤ q ^ 2 := hq.trans hq₂
  have hC₀ : 1 ≤ 10 * (L + 1) ^ 2 * q ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hq₂one (sq_nonneg (L + 1))]
  have hC₁ : L * q + 3 ≤ 10 * (L + 1) ^ 2 * q ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hq₂ hL
    have H' := mul_le_mul_of_nonneg_right (show L + 3 ≤ 10 * (L + 1) ^ 2 by nlinarith) (sq_nonneg q)
    nlinarith
  have hC₂ : L * q + (L * q) ^ 2 + 6 * L * q + 9 ≤ 10 * (L + 1) ^ 2 * q ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hq₂ hL
    have H' := mul_le_mul_of_nonneg_right (show L ^ 2 + 7 * L + 9 ≤ 10 * (L + 1) ^ 2 by nlinarith)
      (sq_nonneg q)
    nlinarith
  have H₀ : |powerMoment n r| ≤ 10 * (L + 1) ^ 2 * q ^ 2 * R ^ n.val :=
    hP.1.trans (by nlinarith [mul_le_mul_of_nonneg_right hC₀ hRpow])
  have H₁ : |a₁ * powerMoment n r + powerMomentFirst n r r₁| ≤
      10 * (L + 1) ^ 2 * q ^ 2 * R ^ n.val := by
    calc
      _ ≤ (L * q) * R ^ n.val + 3 * R ^ n.val :=
        (abs_add_le _ _).trans (add_le_add (abs_mul_le_mul (mul_nonneg hL hq₀) ha₁ hP.1) hP.2.1)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hC₁ hRpow]
  have H₂ : |(a₂ + a₁ ^ 2) * powerMoment n r + 2 * a₁ * powerMomentFirst n r r₁ +
      powerMomentSecond n r r₁ r₂| ≤ 10 * (L + 1) ^ 2 * q ^ 2 * R ^ n.val := by
    have ha : |a₂ + a₁ ^ 2| ≤ L * q + (L * q) ^ 2 := by
      exact (abs_add_le _ _).trans (add_le_add ha₂ (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ha₁ 2))
    have hb : |2 * a₁ * powerMomentFirst n r r₁| ≤ (2 * (L * q)) * (3 * R ^ n.val) := by
      rw [mul_assoc]
      calc
        _ = 2 * |a₁ * powerMomentFirst n r r₁| := by rw [abs_mul]; norm_num
        _ ≤ 2 * ((L * q) * (3 * R ^ n.val)) :=
          mul_le_mul_of_nonneg_left (abs_mul_le_mul (mul_nonneg hL hq₀) ha₁ hP.2.1) (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ (L * q + (L * q) ^ 2) * R ^ n.val + (2 * (L * q)) * (3 * R ^ n.val) + 9 * R ^ n.val :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_mul_le_mul (by positivity) ha hP.1) hb)) hP.2.2)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hC₂ hRpow]
  have Hmul (b : ℝ) (hb : |b| ≤ 10 * (L + 1) ^ 2 * q ^ 2 * R ^ n.val) :
      |Real.exp a * b| ≤ 10 * (L + 1) ^ 2 * q ^ 2 * R ^ n.val * E := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul hE hb (abs_nonneg _) hE₀).trans_eq (by ring)
  exact ⟨Hmul _ H₀, Hmul _ H₁, Hmul _ H₂⟩

def centeredScalarEpsilonFirst (f : ℝ → ℝ) (z ε y : ℝ) : ℝ :=
  (1 - ε) * (deriv f z + iteratedDeriv 2 f z * (y - z)) + ε * deriv f y

def centeredScalarEpsilonSecond (f : ℝ → ℝ) (z ε y : ℝ) : ℝ :=
  (1 - ε) * iteratedDeriv 2 f z + ε * iteratedDeriv 2 f y

theorem centeredScalarEpsilon_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z ε y : ℝ) :
    HasDerivAt (centeredScalarEpsilon f z ε) (centeredScalarEpsilonFirst f z ε y) y ∧
      HasDerivAt (centeredScalarEpsilonFirst f z ε) (centeredScalarEpsilonSecond f z ε y) y := by
  have hf₁ := (hf.differentiable (by simp) y).hasDerivAt
  have hf₂ := ((contDiff_deriv_infty hf).differentiable (by simp) y).hasDerivAt
  have hd := (hasDerivAt_id y).sub_const z
  constructor
  · convert (((hd.const_mul (deriv f z)).add ((hd.pow 2).const_mul (iteratedDeriv 2 f z / 2))).const_mul
      (1 - ε)).add ((hf₁.sub_const (f z)).const_mul ε) using 1
    · funext x
      dsimp only [centeredScalarEpsilon]
      dsimp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    · dsimp only [centeredScalarEpsilonFirst]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      dsimp only [id_eq]
      ring
  · convert (((hd.const_mul (iteratedDeriv 2 f z)).const_add (deriv f z)).const_mul
      (1 - ε)).add (hf₂.const_mul ε) using 1
    · funext x
      dsimp only [centeredScalarEpsilonFirst]
      dsimp only [Pi.add_apply, Pi.mul_apply, id_eq]
    · dsimp only [centeredScalarEpsilonSecond]
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      ring

theorem centeredScalarEpsilon_derivative_bounds {f : ℝ → ℝ} {B z ε y : ℝ}
    (hB : 0 ≤ B) (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : ∀ x, |iteratedDeriv 2 f x| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) :
    |centeredScalarEpsilonFirst f z ε y| ≤ B + B * |y - z| ∧
      |centeredScalarEpsilonSecond f z ε y| ≤ B := by
  have hε₁ : 0 ≤ 1 - ε := sub_nonneg.mpr hε.2
  have H₁ : |deriv f z + iteratedDeriv 2 f z * (y - z)| ≤ B + B * |y - z| :=
    (abs_add_le _ _).trans (add_le_add (hb₁ z) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb₂ z) (abs_nonneg _)))
  constructor
  · calc
      _ ≤ (1 - ε) * (B + B * |y - z|) + ε * B := by
        unfold centeredScalarEpsilonFirst
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hε₁, abs_of_nonneg hε.1]
        exact add_le_add (mul_le_mul_of_nonneg_left H₁ hε₁) (mul_le_mul_of_nonneg_left (hb₁ y) hε.1)
      _ ≤ _ := by nlinarith [mul_nonneg hε.1 (mul_nonneg hB (abs_nonneg (y - z)))]
  · unfold centeredScalarEpsilonSecond
    calc
      _ ≤ (1 - ε) * B + ε * B := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hε₁, abs_of_nonneg hε.1]
        exact add_le_add (mul_le_mul_of_nonneg_left (hb₂ z) hε₁) (mul_le_mul_of_nonneg_left (hb₂ y) hε.1)
      _ = B := by ring

def scalarAxisExponent (f : ℝ → ℝ) (z ε m : ℝ) (v : ℝ → ℝ) (k g : ℝ) : ℝ :=
  m * centeredScalarEpsilon f z ε (z + v k * g)

def scalarAxisExponentFirst (f : ℝ → ℝ) (z ε m : ℝ) (v v₁ : ℝ → ℝ) (k g : ℝ) : ℝ :=
  m * (centeredScalarEpsilonFirst f z ε (z + v k * g) * (v₁ k * g))

def scalarAxisExponentSecond (f : ℝ → ℝ) (z ε m : ℝ) (v v₁ v₂ : ℝ → ℝ) (k g : ℝ) : ℝ :=
  m * (centeredScalarEpsilonSecond f z ε (z + v k * g) * (v₁ k * g) ^ 2 +
    centeredScalarEpsilonFirst f z ε (z + v k * g) * (v₂ k * g))

theorem scalarAxisExponent_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z ε m k g : ℝ} {v v₁ v₂ : ℝ → ℝ}
    (hv : HasDerivAt v (v₁ k) k) (hv₁ : HasDerivAt v₁ (v₂ k) k) :
    HasDerivAt (fun x => scalarAxisExponent f z ε m v x g)
        (scalarAxisExponentFirst f z ε m v v₁ k g) k ∧
      HasDerivAt (fun x => scalarAxisExponentFirst f z ε m v v₁ x g)
        (scalarAxisExponentSecond f z ε m v v₁ v₂ k g) k := by
  have hy := (hv.mul_const g).const_add z
  have hy₁ := hv₁.mul_const g
  constructor
  · exact (((centeredScalarEpsilon_derivatives hf z ε _).1.comp k hy).const_mul m)
  · convert ((((centeredScalarEpsilon_derivatives hf z ε _).2.comp k hy).mul hy₁).const_mul m) using 1
    · rfl
    · change m * (centeredScalarEpsilonSecond f z ε (z + v k * g) * (v₁ k * g) ^ 2 +
        centeredScalarEpsilonFirst f z ε (z + v k * g) * (v₂ k * g)) = _
      dsimp only [Function.comp_apply]
      ring

theorem scalarAxisExponent_bounds {f : ℝ → ℝ} {B R h z ε m k g : ℝ}
    {v v₁ v₂ : ℝ → ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (_hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : ∀ x, |iteratedDeriv 2 f x| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v k| ≤ R * Real.sqrt h) (hv₁ : |v₁ k| ≤ R * Real.sqrt h)
    (hv₂ : |v₂ k| ≤ R * Real.sqrt h) :
    |scalarAxisExponentFirst f z ε m v v₁ k g| ≤ (B * R + 2 * B * R ^ 2) * (1 + g ^ 2) ∧
      |scalarAxisExponentSecond f z ε m v v₁ v₂ k g| ≤ (B * R + 2 * B * R ^ 2) * (1 + g ^ 2) := by
  have hs : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr hh₁
  have harg (w : ℝ) (hw : |w| ≤ R * Real.sqrt h) : |w * g| ≤ R * |g| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hR (abs_nonneg g))])
  have hv' : |z + v k * g - z| ≤ R * |g| := by rw [add_sub_cancel_left]; exact harg _ hv
  have hF := centeredScalarEpsilon_derivative_bounds hB hb₁ hb₂ hε (z := z) (y := z + v k * g)
  have hF₁ : |centeredScalarEpsilonFirst f z ε (z + v k * g)| ≤ B + B * (R * |g|) :=
    hF.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv' hB))
  have hmass (a A : ℝ) (hA : 0 ≤ A) (ha : |a| ≤ A) : |m * a| ≤ A := by
    rw [abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left ha hm.1).trans (mul_le_of_le_one_left hA hm.2)
  have hg : |g| ≤ 1 + g ^ 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  have H₁ : |centeredScalarEpsilonFirst f z ε (z + v k * g) * (v₁ k * g)| ≤
      B * R * |g| + B * R ^ 2 * g ^ 2 := by
    exact (abs_mul_le_mul (by positivity) hF₁ (harg _ hv₁)).trans_eq (by rw [← sq_abs g]; ring)
  have H₂ : |centeredScalarEpsilonSecond f z ε (z + v k * g) * (v₁ k * g) ^ 2 +
      centeredScalarEpsilonFirst f z ε (z + v k * g) * (v₂ k * g)| ≤
      B * R * |g| + 2 * B * R ^ 2 * g ^ 2 := by
    have HA : |(v₁ k * g) ^ 2| ≤ (R * |g|) ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (harg _ hv₁) 2
    exact ((abs_add_le _ _).trans (add_le_add (abs_mul_le_mul hB hF.2 HA)
      (abs_mul_le_mul (by positivity) hF₁ (harg _ hv₂)))).trans_eq (by rw [← sq_abs g]; ring)
  have hcoarse : B * R * |g| + 2 * B * R ^ 2 * g ^ 2 ≤
      (B * R + 2 * B * R ^ 2) * (1 + g ^ 2) := by
    have H := mul_le_mul_of_nonneg_left hg (mul_nonneg hB hR)
    nlinarith [mul_nonneg hB (sq_nonneg R)]
  exact ⟨(hmass _ _ (by positivity) H₁).trans (by
    nlinarith [hcoarse, mul_nonneg (mul_nonneg hB (sq_nonneg R)) (sq_nonneg g)]),
    (hmass _ _ (by positivity) H₂).trans hcoarse⟩

def scalarAxisResidual (f : ℝ → ℝ) (z : ℝ) (v : ℝ → ℝ) (k g : ℝ) : ℝ :=
  quadraticTaylorTail f z (z + v k * g)

def scalarAxisResidualFirst (f : ℝ → ℝ) (z : ℝ) (v v₁ : ℝ → ℝ) (k g : ℝ) : ℝ :=
  quadraticTaylorTailFirst f z (z + v k * g) * (v₁ k * g)

def scalarAxisResidualSecond (f : ℝ → ℝ) (z : ℝ) (v v₁ v₂ : ℝ → ℝ) (k g : ℝ) : ℝ :=
  quadraticTaylorTailSecond f z (z + v k * g) * (v₁ k * g) ^ 2 +
    quadraticTaylorTailFirst f z (z + v k * g) * (v₂ k * g)

theorem scalarAxisResidual_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z k g : ℝ} {v v₁ v₂ : ℝ → ℝ}
    (hv : HasDerivAt v (v₁ k) k) (hv₁ : HasDerivAt v₁ (v₂ k) k) :
    HasDerivAt (fun x => scalarAxisResidual f z v x g) (scalarAxisResidualFirst f z v v₁ k g) k ∧
      HasDerivAt (fun x => scalarAxisResidualFirst f z v v₁ x g) (scalarAxisResidualSecond f z v v₁ v₂ k g) k := by
  exact quadraticTaylorTail_comp_derivatives (y := fun x => z + v x * g)
    (y₁ := fun x => v₁ x * g) (y₂ := fun x => v₂ x * g) hf ((hv.mul_const g).const_add z) (hv₁.mul_const g)

theorem scalarAxisResidual_bounds {f : ℝ → ℝ} {B R h z k g : ℝ} {v v₁ v₂ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hb : ∀ x, |iteratedDeriv 3 f x| ≤ B)
    (hv : |v k| ≤ R * Real.sqrt h) (hv₁ : |v₁ k| ≤ R * Real.sqrt h)
    (hv₂ : |v₂ k| ≤ R * Real.sqrt h) :
    let M := (2 * B * R ^ 3) * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3
    |scalarAxisResidual f z v k g| ≤ M ∧ |scalarAxisResidualFirst f z v v₁ k g| ≤ M ∧
      |scalarAxisResidualSecond f z v v₁ v₂ k g| ≤ M := by
  have harg (w : ℝ) (hw : |w| ≤ R * Real.sqrt h) : |w * g| ≤ R * Real.sqrt h * |g| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  have H := quadraticTaylorTail_comp_bounds (z := z) (y := z + v k * g)
    (y₁ := v₁ k * g) (y₂ := v₂ k * g) hf hb hB (by positivity : 0 ≤ R * Real.sqrt h * |g|)
    (by rw [add_sub_cancel_left]; exact harg _ hv) (harg _ hv₁) (harg _ hv₂)
  have hc : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
    calc
      _ = Real.sqrt h * (Real.sqrt h) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hh]
  have hg : |g| ≤ 1 + g ^ 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  have HB : 2 * B * (R * Real.sqrt h * |g|) ^ 3 ≤
      (2 * B * R ^ 3) * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3 := by
    calc
      _ = (2 * B * R ^ 3) * (Real.sqrt h * h) * |g| ^ 3 := by rw [mul_pow, mul_pow, hc]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hg 3) (by positivity)
  exact ⟨H.1.trans HB, H.2.1.trans HB, H.2.2.trans HB⟩

def scalarAxisMoment (f : ℝ → ℝ) (z ε m : ℝ) (v : ℝ → ℝ) (n : Fin 4) (k g : ℝ) : ℝ :=
  exponentialMoment n (scalarAxisExponent f z ε m v k g) (scalarAxisResidual f z v k g)

def scalarAxisMomentFirst (f : ℝ → ℝ) (z ε m : ℝ) (v v₁ : ℝ → ℝ) (n : Fin 4) (k g : ℝ) : ℝ :=
  exponentialMomentFirst n (scalarAxisExponent f z ε m v k g) (scalarAxisExponentFirst f z ε m v v₁ k g)
    (scalarAxisResidual f z v k g) (scalarAxisResidualFirst f z v v₁ k g)

def scalarAxisMomentSecond (f : ℝ → ℝ) (z ε m : ℝ) (v v₁ v₂ : ℝ → ℝ) (n : Fin 4) (k g : ℝ) : ℝ :=
  exponentialMomentSecond n (scalarAxisExponent f z ε m v k g) (scalarAxisExponentFirst f z ε m v v₁ k g)
    (scalarAxisExponentSecond f z ε m v v₁ v₂ k g) (scalarAxisResidual f z v k g)
    (scalarAxisResidualFirst f z v v₁ k g) (scalarAxisResidualSecond f z v v₁ v₂ k g)

theorem scalarAxisMoment_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z ε m k g : ℝ} {v v₁ v₂ : ℝ → ℝ}
    (hv : HasDerivAt v (v₁ k) k) (hv₁ : HasDerivAt v₁ (v₂ k) k) (n : Fin 4) :
    HasDerivAt (fun x => scalarAxisMoment f z ε m v n x g) (scalarAxisMomentFirst f z ε m v v₁ n k g) k ∧
      HasDerivAt (fun x => scalarAxisMomentFirst f z ε m v v₁ n x g) (scalarAxisMomentSecond f z ε m v v₁ v₂ n k g) k := by
  have HA := scalarAxisExponent_derivatives hf hv hv₁ (z := z) (ε := ε) (m := m) (g := g)
  have HR := scalarAxisResidual_derivatives hf hv hv₁ (z := z) (g := g)
  exact exponentialMoment_derivatives
    (a := fun x => scalarAxisExponent f z ε m v x g)
    (a₁ := fun x => scalarAxisExponentFirst f z ε m v v₁ x g)
    (a₂ := fun x => scalarAxisExponentSecond f z ε m v v₁ v₂ x g)
    (r := fun x => scalarAxisResidual f z v x g)
    (r₁ := fun x => scalarAxisResidualFirst f z v v₁ x g)
    (r₂ := fun x => scalarAxisResidualSecond f z v v₁ v₂ x g) HA.1 HA.2 HR.1 HR.2 n

theorem scalarAxisMoment_envelope {f : ℝ → ℝ} {B R h z ε m k g : ℝ}
    {v v₁ v₂ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : ∀ x, |iteratedDeriv 2 f x| ≤ B)
    (hb₃ : ∀ x, |iteratedDeriv 3 f x| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v k| ≤ R * Real.sqrt h) (hv₁ : |v₁ k| ≤ R * Real.sqrt h)
    (hv₂ : |v₂ k| ≤ R * Real.sqrt h) (hsmall : 4 * B * R ^ 2 * h ≤ 1) (n : Fin 4) :
    let L := B * R + 2 * B * R ^ 2
    let C := 10 * (L + 1) ^ 2 * (2 * B * R ^ 3) ^ n.val
    let G := C * (Real.sqrt h * h) ^ n.val *
      ((1 + g ^ 2) ^ (3 * n.val + 2) * Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2))
    |scalarAxisMoment f z ε m v n k g| ≤ G ∧ |scalarAxisMomentFirst f z ε m v v₁ n k g| ≤ G ∧
      |scalarAxisMomentSecond f z ε m v v₁ v₂ n k g| ≤ G := by
  have HA := scalarAxisExponent_bounds hB hR hh hh₁ hb₁ hb₂ hε hm hv hv₁ hv₂ (z := z) (g := g)
  have HR := scalarAxisResidual_bounds hf hB hR hh hb₃ hv hv₁ hv₂ (z := z) (g := g)
  have HE := (centeredScalarEpsilon_gaussian_envelope hf hB hR hh hh₁ hb₁ (hb₂ z) hε hm hv hsmall g).2
  have H := exponentialMoment_bounds HE (by positivity : 0 ≤ B * R + 2 * B * R ^ 2)
    (by nlinarith [sq_nonneg g] : 1 ≤ 1 + g ^ 2)
    (by positivity : 0 ≤ (2 * B * R ^ 3) * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3)
    HA.1 HA.2 HR.1 HR.2.1 HR.2.2 n
  have heq : 10 * (B * R + 2 * B * R ^ 2 + 1) ^ 2 * (1 + g ^ 2) ^ 2 *
      ((2 * B * R ^ 3) * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3) ^ n.val *
        Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2) =
      (10 * (B * R + 2 * B * R ^ 2 + 1) ^ 2 * (2 * B * R ^ 3) ^ n.val) *
        (Real.sqrt h * h) ^ n.val * ((1 + g ^ 2) ^ (3 * n.val + 2) *
          Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2)) := by
    simp only [mul_pow, pow_add, pow_mul]
    ring
  exact ⟨H.1.trans_eq heq, H.2.1.trans_eq heq, H.2.2.trans_eq heq⟩

theorem scalarAxisMoment_noise_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (z ε m : ℝ) (v v₁ v₂ : ℝ → ℝ) (n : Fin 4) (k : ℝ) :
    Continuous (scalarAxisMoment f z ε m v n k) ∧ Continuous (scalarAxisMomentFirst f z ε m v v₁ n k) ∧
      Continuous (scalarAxisMomentSecond f z ε m v v₁ v₂ n k) := by
  have hf₁ : Continuous (deriv f) := (contDiff_deriv_infty hf).continuous
  have hf₂ : Continuous (deriv (deriv f)) := (contDiff_deriv_infty (contDiff_deriv_infty hf)).continuous
  have hi₂ : Continuous (iteratedDeriv 2 f) := by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hf₂
  have hK : Continuous (quadraticTaylorTail f z) := by unfold quadraticTaylorTail scalarTaylorPolynomial; fun_prop
  have hK₁ : Continuous (quadraticTaylorTailFirst f z) := by unfold quadraticTaylorTailFirst scalarTaylorPolynomial; fun_prop
  have hK₂ : Continuous (quadraticTaylorTailSecond f z) := by unfold quadraticTaylorTailSecond scalarTaylorPolynomial; fun_prop
  change Continuous (fun g => scalarAxisMoment f z ε m v n k g) ∧
    Continuous (fun g => scalarAxisMomentFirst f z ε m v v₁ n k g) ∧
    Continuous (fun g => scalarAxisMomentSecond f z ε m v v₁ v₂ n k g)
  fin_cases n <;>
    dsimp only [scalarAxisMoment, scalarAxisMomentFirst, scalarAxisMomentSecond,
      exponentialMoment, exponentialMomentFirst, exponentialMomentSecond,
      powerMoment, powerMomentFirst, powerMomentSecond, Matrix.cons_val_zero', Matrix.cons_val_succ',
      scalarAxisExponent, scalarAxisExponentFirst, scalarAxisExponentSecond,
      centeredScalarEpsilon, centeredScalarEpsilonFirst, centeredScalarEpsilonSecond,
      scalarAxisResidual, scalarAxisResidualFirst, scalarAxisResidualSecond]
  all_goals
    exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

theorem scalarAxisMoment_k_controls {f : ℝ → ℝ} {B R h z ε m k : ℝ}
    {v v₁ v₂ : ℝ → ℝ} {U : Set ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : ∀ x, |iteratedDeriv 2 f x| ≤ B)
    (hb₃ : ∀ x, |iteratedDeriv 3 f x| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1) (hU : U ∈ 𝓝 k)
    (hd : ∀ x ∈ U, HasDerivAt v (v₁ x) x ∧ HasDerivAt v₁ (v₂ x) x)
    (hv : ∀ x ∈ U, |v x| ≤ R * Real.sqrt h ∧ |v₁ x| ≤ R * Real.sqrt h ∧ |v₂ x| ≤ R * Real.sqrt h)
    (hsmall : 4 * B * R ^ 2 * h ≤ 1) (n : Fin 4) :
    IntegralDerivativeControl (gaussianReal 0 1) (scalarAxisMoment f z ε m v n)
        (scalarAxisMomentFirst f z ε m v v₁ n) k ∧
      IntegralDerivativeControl (gaussianReal 0 1) (scalarAxisMomentFirst f z ε m v v₁ n)
        (scalarAxisMomentSecond f z ε m v v₁ v₂ n) k := by
  apply quadratic_gaussian_integral_k_controls (A := 2 * (B * R) ^ 2) (b := 1 / 4)
    (C := (10 * (B * R + 2 * B * R ^ 2 + 1) ^ 2 * (2 * B * R ^ 3) ^ n.val) *
      (Real.sqrt h * h) ^ n.val) (p := 3 * n.val + 2) hU (by norm_num) (by norm_num)
  · intro x _
    have H := scalarAxisMoment_noise_continuous hf z ε m v v₁ v₂ n x
    exact ⟨H.1.aestronglyMeasurable, H.2.1.aestronglyMeasurable, H.2.2.aestronglyMeasurable⟩
  · intro g x hx
    exact scalarAxisMoment_derivatives hf (hd x hx).1 (hd x hx).2 n
  · intro x hx g
    exact scalarAxisMoment_envelope hf hB hR hh hh₁ hb₁ hb₂ hb₃ hε hm (hv x hx).1
      (hv x hx).2.1 (hv x hx).2.2 hsmall n

def frozenLastLength (k : ℝ) : ℝ := 2 - (44 / 9 : ℝ) * k ^ 2

def frozenLastAmplitude (β h k : ℝ) : ℝ := β * Real.sqrt h * Real.sqrt (frozenLastLength k)

def frozenLastAmplitudeFirst (β h k : ℝ) : ℝ :=
  β * Real.sqrt h * (-(44 / 9 : ℝ) * k / Real.sqrt (frozenLastLength k))

def frozenLastAmplitudeSecond (β h k : ℝ) : ℝ :=
  β * Real.sqrt h * (-(88 / 9 : ℝ) / Real.sqrt (frozenLastLength k) ^ 3)

theorem frozenLastLength_bounds {k : ℝ} (hk : |k| ≤ 1 / 3) :
    1 ≤ frozenLastLength k ∧ frozenLastLength k ≤ 2 := by
  have H := pow_le_pow_left₀ (abs_nonneg k) hk 2
  rw [sq_abs] at H
  unfold frozenLastLength
  constructor <;> nlinarith [sq_nonneg k]

theorem frozenLastAmplitude_eq (β : ℝ) {h : ℝ} (hh : 0 ≤ h) (k : ℝ) :
    frozenLastAmplitude β h k = β * Real.sqrt (h * (2 - OW.repairLength (1 / 2) k)) := by
  have heq : 2 - OW.repairLength (1 / 2) k = frozenLastLength k := by
    norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight, frozenLastLength]
    ring
  rw [heq, Real.sqrt_mul hh]
  unfold frozenLastAmplitude
  ring

theorem frozenLastAmplitude_derivatives (β h : ℝ) {k : ℝ} (hk : |k| ≤ 1 / 3) :
    HasDerivAt (frozenLastAmplitude β h) (frozenLastAmplitudeFirst β h k) k ∧
      HasDerivAt (frozenLastAmplitudeFirst β h) (frozenLastAmplitudeSecond β h k) k := by
  have hdpos : 0 < frozenLastLength k := by linarith [(frozenLastLength_bounds hk).1]
  have hspos : 0 < Real.sqrt (frozenLastLength k) := Real.sqrt_pos.mpr hdpos
  have hd : HasDerivAt frozenLastLength (-(88 / 9 : ℝ) * k) k := by
    convert (((hasDerivAt_id k).pow 2).const_mul (44 / 9 : ℝ)).const_sub 2 using 1
    · funext x
      dsimp only [frozenLastLength, Pi.pow_apply, id_eq]
    · norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]
      ring
  have hs : HasDerivAt (fun x => Real.sqrt (frozenLastLength x))
      (-(44 / 9 : ℝ) * k / Real.sqrt (frozenLastLength k)) k :=
    (hd.sqrt hdpos.ne').congr_deriv (by ring)
  have hnum : HasDerivAt (fun x : ℝ => -(44 / 9 : ℝ) * x) (-(44 / 9 : ℝ)) k := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id k).const_mul (-(44 / 9 : ℝ))
  have hrat : ((-(44 / 9 : ℝ)) * Real.sqrt (frozenLastLength k) -
      (-(44 / 9 : ℝ) * k) * (-(44 / 9 : ℝ) * k / Real.sqrt (frozenLastLength k))) /
      Real.sqrt (frozenLastLength k) ^ 2 = -(88 / 9 : ℝ) / Real.sqrt (frozenLastLength k) ^ 3 := by
    have H := Real.sq_sqrt hdpos.le
    change Real.sqrt (frozenLastLength k) ^ 2 = 2 - (44 / 9 : ℝ) * k ^ 2 at H
    field_simp [hspos.ne']
    nlinarith
  exact ⟨hs.const_mul (β * Real.sqrt h), ((hnum.div hs hspos.ne').congr_deriv hrat).const_mul (β * Real.sqrt h)⟩

theorem frozenLastAmplitude_bounds (β : ℝ) {h k : ℝ} (_hh : 0 ≤ h) (hk : |k| ≤ 1 / 3) :
    |frozenLastAmplitude β h k| ≤ (20 * (|β| + 1)) * Real.sqrt h ∧
      |frozenLastAmplitudeFirst β h k| ≤ (20 * (|β| + 1)) * Real.sqrt h ∧
      |frozenLastAmplitudeSecond β h k| ≤ (20 * (|β| + 1)) * Real.sqrt h := by
  have hd := frozenLastLength_bounds hk
  have hs : 1 ≤ Real.sqrt (frozenLastLength k) := Real.one_le_sqrt.mpr hd.1
  have hs₂ : Real.sqrt (frozenLastLength k) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith [hd.2]⟩
  have hfac : 0 ≤ |β| * Real.sqrt h := by positivity
  have H₁ : |-(44 / 9 : ℝ) * k / Real.sqrt (frozenLastLength k)| ≤ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 44 / 9)]
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (frozenLastLength k))).mpr
    nlinarith
  have H₂ : |-(88 / 9 : ℝ) / Real.sqrt (frozenLastLength k) ^ 3| ≤ 10 := by
    rw [abs_div, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 88 / 9)]
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < Real.sqrt (frozenLastLength k)) 3)).mpr
    have H := one_le_pow₀ hs (n := 3)
    linarith
  have hscale : 10 * (|β| * Real.sqrt h) ≤ (20 * (|β| + 1)) * Real.sqrt h := by
    nlinarith [Real.sqrt_nonneg h, mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg h)]
  simp only [frozenLastAmplitude, frozenLastAmplitudeFirst, frozenLastAmplitudeSecond,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg h), abs_of_nonneg (Real.sqrt_nonneg (frozenLastLength k))]
  exact ⟨(mul_le_mul_of_nonneg_left hs₂ hfac).trans (by nlinarith),
    (mul_le_mul_of_nonneg_left H₁ hfac).trans (by nlinarith),
    (mul_le_mul_of_nonneg_left H₂ hfac).trans (by nlinarith [hscale])⟩

theorem IntegralDerivativeControl.const_mul {μ : Measure ℝ} {F F₁ : ℝ → ℝ → ℝ} {k : ℝ}
    (H : IntegralDerivativeControl μ F F₁ k) (c : ℝ) :
    IntegralDerivativeControl μ (fun x g => c * F x g) (fun x g => c * F₁ x g) k := by
  rcases H with ⟨S, hS, b, hm, hi, hm₁, hb, hbound, hd⟩
  refine ⟨S, hS, fun g => |c| * b g, hm.mono (fun _ hx => hx.const_mul c), hi.const_mul c,
    hm₁.const_mul c, hb.const_mul |c|, ?_, ?_⟩
  · filter_upwards [hbound] with g hg
    intro x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hg x hx) (abs_nonneg c)
  · filter_upwards [hd] with g hg
    intro x hx
    exact (hg x hx).const_mul c

private theorem gaussian_envelope_normalized_bound {F Z : ℝ → ℝ} {S T C t : ℝ} {p n : ℕ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hF : AEStronglyMeasurable F (gaussianReal 0 1))
    (hiZ : Integrable Z (gaussianReal 0 1))
    (hZ : ∀ g, Real.exp (-S * |g| - T * g ^ 2) ≤ Z g)
    (hb : ∀ g, |F g| ≤ C * t ^ n * ((1 + g ^ 2) ^ p * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))) :
    |(∫ g, F g ∂gaussianReal 0 1) / (∫ g, Z g ∂gaussianReal 0 1)| ≤
      (C * gaussianQuadraticMoment S p / gaussianQuadraticLower S T) * t ^ n := by
  have hscale : 0 ≤ C * t ^ n := mul_nonneg hC (pow_nonneg ht _)
  have hiF : Integrable F (gaussianReal 0 1) :=
    ((gaussianQuadraticMoment_integrable S p).const_mul (C * t ^ n)).mono' hF
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  have hD := gaussianQuadraticLower_pos hS hT
  have hDZ : gaussianQuadraticLower S T ≤ ∫ g, Z g ∂gaussianReal 0 1 :=
    integral_mono (gaussianQuadraticLower_integrable hS hT) hiZ hZ
  have H : |∫ g, F g ∂gaussianReal 0 1| ≤ (C * t ^ n) * gaussianQuadraticMoment S p := by
    calc
      _ ≤ ∫ g, |F g| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
      _ ≤ _ := (integral_mono hiF.abs ((gaussianQuadraticMoment_integrable S p).const_mul (C * t ^ n)) hb).trans_eq
        (integral_const_mul _ _)
  rw [abs_div, abs_of_pos (hD.trans_le hDZ)]
  calc
    _ ≤ ((C * t ^ n) * gaussianQuadraticMoment S p) / (∫ g, Z g ∂gaussianReal 0 1) :=
      div_le_div_of_nonneg_right H (hD.trans_le hDZ).le
    _ ≤ ((C * t ^ n) * gaussianQuadraticMoment S p) / gaussianQuadraticLower S T :=
      div_le_div_of_nonneg_left (mul_nonneg hscale (gaussianQuadraticMoment_nonneg _ _)) hD hDZ
    _ = _ := by ring

theorem scalarAxisMoment_normalized_bounds {f : ℝ → ℝ} {B R h z ε m k : ℝ}
    {v v₁ v₂ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hb₁ : ∀ x, |deriv f x| ≤ B) (hb₂ : ∀ x, |iteratedDeriv 2 f x| ≤ B)
    (hb₃ : ∀ x, |iteratedDeriv 3 f x| ≤ B)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v k| ≤ R * Real.sqrt h) (hv₁ : |v₁ k| ≤ R * Real.sqrt h)
    (hv₂ : |v₂ k| ≤ R * Real.sqrt h) (hsmall : 4 * B * R ^ 2 * h ≤ 1) (n : Fin 4) :
    let C := (10 * (B * R + 2 * B * R ^ 2 + 1) ^ 2 * (2 * B * R ^ 3) ^ n.val) *
      gaussianQuadraticMoment (B * R) (3 * n.val + 2) / gaussianQuadraticLower (B * R) (B * R ^ 2 / 2)
    let Z := ∫ g, scalarAxisMoment f z ε m v 0 k g ∂gaussianReal 0 1
    |(∫ g, scalarAxisMoment f z ε m v n k g ∂gaussianReal 0 1) / Z| ≤ C * (Real.sqrt h * h) ^ n.val ∧
      |(∫ g, scalarAxisMomentFirst f z ε m v v₁ n k g ∂gaussianReal 0 1) / Z| ≤ C * (Real.sqrt h * h) ^ n.val ∧
      |(∫ g, scalarAxisMomentSecond f z ε m v v₁ v₂ n k g ∂gaussianReal 0 1) / Z| ≤ C * (Real.sqrt h * h) ^ n.val := by
  have HE (g : ℝ) := scalarAxisMoment_envelope (z := z) (g := g) hf hB hR hh hh₁ hb₁ hb₂ hb₃ hε hm hv hv₁ hv₂ hsmall n
  have Hc := scalarAxisMoment_noise_continuous hf z ε m v v₁ v₂ n k
  have hiZ := (scalar_cubic_gaussian_moment_bound hf hB hR hh hh₁ hb₁ (hb₂ z) hb₃ hε hm hv hsmall 0).1
  simp only [pow_zero, mul_one] at hiZ
  have hZ (g : ℝ) : Real.exp (-(B * R) * |g| - (B * R ^ 2 / 2) * g ^ 2) ≤
      scalarAxisMoment f z ε m v 0 k g := by
    simpa only [scalarAxisMoment, exponentialMoment, powerMoment, Matrix.cons_val_zero, mul_one, scalarAxisExponent]
      using (centeredScalarEpsilon_gaussian_envelope hf hB hR hh hh₁ hb₁ (hb₂ z) hε hm hv hsmall g).1
  have hiZ' : Integrable (scalarAxisMoment f z ε m v 0 k) (gaussianReal 0 1) := by
    change Integrable (fun g => scalarAxisMoment f z ε m v 0 k g) (gaussianReal 0 1)
    simpa only [scalarAxisMoment, exponentialMoment, powerMoment, Matrix.cons_val_zero, mul_one, scalarAxisExponent] using hiZ
  have Hbound (F : ℝ → ℝ) (hc : Continuous F)
      (hb : ∀ g, |F g| ≤ (10 * (B * R + 2 * B * R ^ 2 + 1) ^ 2 * (2 * B * R ^ 3) ^ n.val) *
        (Real.sqrt h * h) ^ n.val * ((1 + g ^ 2) ^ (3 * n.val + 2) *
          Real.exp (2 * (B * R) ^ 2 + (1 / 4 : ℝ) * g ^ 2))) :
      |(∫ g, F g ∂gaussianReal 0 1) / (∫ g, scalarAxisMoment f z ε m v 0 k g ∂gaussianReal 0 1)| ≤
      ((10 * (B * R + 2 * B * R ^ 2 + 1) ^ 2 * (2 * B * R ^ 3) ^ n.val) *
        gaussianQuadraticMoment (B * R) (3 * n.val + 2) / gaussianQuadraticLower (B * R) (B * R ^ 2 / 2)) *
        (Real.sqrt h * h) ^ n.val := by
    exact gaussian_envelope_normalized_bound (by positivity) (by positivity) (by positivity) (by positivity)
      hc.aestronglyMeasurable hiZ' hZ hb
  exact ⟨Hbound _ Hc.1 (fun g => (HE g).1), Hbound _ Hc.2.1 (fun g => (HE g).2.1),
    Hbound _ Hc.2.2 (fun g => (HE g).2.2)⟩

def frozenLastWeightFirst (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (n : Fin 4) (k g : ℝ) : ℝ :=
  (Real.exp (a * (3 * Phi β α (s + 4 * h) z)) * a ^ n.val) *
    scalarAxisMomentFirst (Phi β α (s + 4 * h)) z ε a
      (frozenLastAmplitude β h) (frozenLastAmplitudeFirst β h) n k g

def frozenLastWeightSecond (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (n : Fin 4) (k g : ℝ) : ℝ :=
  (Real.exp (a * (3 * Phi β α (s + 4 * h) z)) * a ^ n.val) *
    scalarAxisMomentSecond (Phi β α (s + 4 * h)) z ε a
      (frozenLastAmplitude β h) (frozenLastAmplitudeFirst β h) (frozenLastAmplitudeSecond β h) n k g

theorem frozenLastWeight_eq (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ) (hh : 0 ≤ h) :
    frozenPartitionWeight β α a s h z ε 11 = fun n k g =>
      (Real.exp (a * (3 * Phi β α (s + 4 * h) z)) * a ^ n.val) *
        scalarAxisMoment (Phi β α (s + 4 * h)) z ε a (frozenLastAmplitude β h) n k g := by
  funext n k g
  change epsilonPartitionWeight [(a, (β * Real.sqrt (h * (2 - OW.repairLength (1 / 2) k))) •
    (Pi.single 2 1 : Vec3))] (terminalTaylorQuadratic β α s h z)
    (terminalResidual β α s h z) (fun _ => z) ε n g = _
  rw [← frozenLastAmplitude_eq β hh k, epsilonPartitionWeight_singleton,
    terminalEpsilon_scalar_axis, terminalResidual_scalar_axis]
  dsimp only [scalarAxisMoment, scalarAxisExponent, scalarAxisResidual, exponentialMoment]
  rw [powerMoment_eq_pow, mul_add, Real.exp_add]
  ring

private theorem weighted_partition_ratio (E m : ℝ) (hE : E ≠ 0)
    (F G : Fin 4 → ℝ → ℝ → ℝ) (n : Fin 4) (k : ℝ) :
    partitionIntegral (fun j x g => (E * m ^ j.val) * F j x g) n k /
      partitionIntegral (fun j x g => (E * m ^ j.val) * G j x g) 0 k =
        m ^ n.val * (partitionIntegral F n k / partitionIntegral G 0 k) := by
  simp only [partitionIntegral, integral_const_mul, Fin.val_zero, pow_zero, mul_one]
  rw [mul_assoc, mul_div_mul_left _ _ hE, mul_div_assoc]

theorem scalarData_frozen_last_partition_k_control {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ B h₀ : ℝ, 1 ≤ B ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
        PartitionIntegralKControl
          (frozenPartitionWeight β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11)
          (frozenLastWeightFirst β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε)
          (frozenLastWeightSecond β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε)
          (Icc (-(1 / 4 : ℝ)) (1 / 4)) B (Real.sqrt h * h) := by
  rcases scalarData_frozen_partition_pos D hl hu with ⟨hP, hhP, HP⟩
  let J := scalarTerminalJetBound D 3
  let R := 20 * (|β| + 1)
  have hJ : 0 ≤ J := scalarTerminalJetBound_nonneg D 3
  have hR : 0 < R := by dsimp only [R]; positivity
  let A : Fin 4 → ℝ := fun n =>
    (10 * (J * R + 2 * J * R ^ 2 + 1) ^ 2 * (2 * J * R ^ 3) ^ n.val) *
      gaussianQuadraticMoment (J * R) (3 * n.val + 2) / gaussianQuadraticLower (J * R) (J * R ^ 2 / 2)
  have hA (n : Fin 4) : 0 ≤ A n := by
    exact div_nonneg (mul_nonneg (by positivity) (gaussianQuadraticMoment_nonneg _ _))
      (gaussianQuadraticLower_pos (by positivity) (by positivity)).le
  let B := 1 + ∑ n : Fin 4, A n
  have hB : 1 ≤ B := by
    have H := Finset.sum_nonneg (fun n (_ : n ∈ (Finset.univ : Finset (Fin 4))) => hA n)
    dsimp only [B]
    linarith
  have hAB (n : Fin 4) : A n ≤ B := by
    have H := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hA i) (Finset.mem_univ n)
    dsimp only [B]
    linarith
  let S := 1 + 4 * J * R ^ 2
  have hS : 0 < S := by dsimp only [S]; positivity
  let h₀ := min hP (min 1 (min (l / 2) (min ((D.q - u) / 6) S⁻¹)))
  have hh₀ : 0 < h₀ := lt_min hhP (lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (inv_pos.mpr hS))))
  refine ⟨B, h₀, hB, hh₀, ?_⟩
  intro r hr h hh hhsmall z ε hε
  have hhP' : h ≤ hP := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hhS : h ≤ S⁻¹ := (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hsmall : 4 * J * R ^ 2 * h ≤ 1 := by
    calc
      _ ≤ S * h := by dsimp only [S]; nlinarith
      _ ≤ S * S⁻¹ := mul_le_mul_of_nonneg_left hhS hS.le
      _ = 1 := mul_inv_cancel₀ hS.ne'
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let f := Phi β α ((r - h) + 4 * h)
  let E := Real.exp (a * (3 * f z))
  let v := frozenLastAmplitude β h
  let v₁ := frozenLastAmplitudeFirst β h
  let v₂ := frozenLastAmplitudeSecond β h
  have hE : E ≠ 0 := Real.exp_ne_zero _
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hf : ContDiff ℝ ∞ f := scalarData_phi_contDiff D ht
  have hb₁ (x : ℝ) : |deriv f x| ≤ J := by
    simpa only [jet, iteratedDeriv_one] using scalarData_jet_le D (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 3) ht x
  have hb₂ (x : ℝ) : |iteratedDeriv 2 f x| ≤ J := scalarData_jet_le D (by norm_num) (by norm_num) ht x
  have hb₃ (x : ℝ) : |iteratedDeriv 3 f x| ≤ J := scalarData_jet_le D (by norm_num) le_rfl ht x
  have hW := frozenLastWeight_eq β α a (r - h) h z ε hh.le
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact ne_of_gt (HP r hr h hh hhP' k (by rw [abs_le]; constructor <;> linarith [hk.1, hk.2]) z ε hε 11 (by norm_num))
  · intro k hk n
    have hU : Ioo (-(1 / 3 : ℝ)) (1 / 3) ∈ 𝓝 k :=
      Ioo_mem_nhds (by linarith [hk.1]) (by linarith [hk.2])
    have HC := scalarAxisMoment_k_controls (z := z) hf hJ hR.le hh.le hh₁ hb₁ hb₂ hb₃ hε ha hU
      (fun x hx => frozenLastAmplitude_derivatives β h (abs_le.mpr ⟨hx.1.le, hx.2.le⟩))
      (fun x hx => frozenLastAmplitude_bounds β hh.le (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)) hsmall n
    rw [hW]
    exact ⟨HC.1.const_mul (E * a ^ n.val), HC.2.const_mul (E * a ^ n.val)⟩
  · intro k hk n
    have hk' : |k| ≤ 1 / 3 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have hv := frozenLastAmplitude_bounds β hh.le hk'
    have HC := scalarAxisMoment_normalized_bounds (z := z) hf hJ hR.le hh.le hh₁ hb₁ hb₂ hb₃ hε ha hv.1 hv.2.1 hv.2.2 hsmall n
    have Hlift (x : ℝ) (hx : |x| ≤ A n * (Real.sqrt h * h) ^ n.val) :
        |a ^ n.val * x| ≤ B * (Real.sqrt h * h) ^ n.val := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg ha.1 _)]
      calc
        _ ≤ |x| := mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ha.1 ha.2)
        _ ≤ A n * (Real.sqrt h * h) ^ n.val := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right (hAB n) (by positivity)
    rw [hW]
    change
      |partitionIntegral (fun j x g => (E * a ^ j.val) * scalarAxisMoment f z ε a v j x g) n k /
        partitionIntegral (fun j x g => (E * a ^ j.val) * scalarAxisMoment f z ε a v j x g) 0 k| ≤ _ ∧
      |partitionIntegral (fun j x g => (E * a ^ j.val) * scalarAxisMomentFirst f z ε a v v₁ j x g) n k /
        partitionIntegral (fun j x g => (E * a ^ j.val) * scalarAxisMoment f z ε a v j x g) 0 k| ≤ _ ∧
      |partitionIntegral (fun j x g => (E * a ^ j.val) * scalarAxisMomentSecond f z ε a v v₁ v₂ j x g) n k /
        partitionIntegral (fun j x g => (E * a ^ j.val) * scalarAxisMoment f z ε a v j x g) 0 k| ≤ _
    rw [weighted_partition_ratio E a hE, weighted_partition_ratio E a hE, weighted_partition_ratio E a hE]
    exact ⟨Hlift _ HC.1, Hlift _ HC.2.1, Hlift _ HC.2.2⟩

theorem scalarData_frozen_last_rows_k_regular {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
        ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
          (∀ i : Fin 3, ∀ k ∈ Icc (-(1 / 4 : ℝ)) (1 / 4),
            HasDerivAt (frozenThirdPartitionRow β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11 i) (d₁ i k) k ∧
              HasDerivAt (d₁ i) (d₂ i k) k) ∧
          (∀ i : Fin 3, ∀ k ∈ Icc (-(1 / 4 : ℝ)) (1 / 4), |d₂ i k| ≤ C * Real.sqrt h * h ^ 3) := by
  rcases scalarData_frozen_last_partition_k_control D hl hu with ⟨B, hK, hB, hhK, HK⟩
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity : 0 < l / 2)
  let R := (6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3
  have hR : 0 < R := by dsimp only [R]; positivity
  let C := 3 * R / a₀
  let h₀ := min hK (min 1 (l / 2))
  refine ⟨C, h₀, div_pos (mul_pos (by norm_num) hR) ha₀,
    lt_min hhK (lt_min (by norm_num) (by positivity)), ?_⟩
  intro r hr h hh hhsmall z ε hε
  have hhK' : h ≤ hK := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hamass : a₀ ≤ cdf (D.μ : Measure ℝ) (r - h) :=
    monotone_cdf (D.μ : Measure ℝ) (by linarith [hr.1])
  let m := frozenPartitionMass (cdf (D.μ : Measure ℝ) (r - h)) 11
  have hm : a₀ / 3 ≤ m := frozenPartitionMass_lower ha₀ hamass 11
  have hmpos : 0 < m := (div_pos ha₀ (by norm_num)).trans_le hm
  have HW := HK r hr h hh hhK' z ε hε
  rcases HW.rows (m := m) hB (by positivity) hmpos with ⟨d₁, d₂, hd, hb⟩
  refine ⟨d₁, d₂, ?_, ?_⟩
  · intro i k hk
    have heq : frozenThirdPartitionRow β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11 i =
      thirdPartitionRows m (partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11)) i :=
      funext (frozenThirdPartitionRow_eq_moments β _ _ _ h z ε (by norm_num : 11 < 12) i)
    rw [heq]
    exact hd i k hk
  · intro i k hk
    have hcoeff : R / m ≤ 3 * R / a₀ := by
      calc
        _ ≤ R / (a₀ / 3) := div_le_div_of_nonneg_left hR.le (div_pos ha₀ (by norm_num)) hm
        _ = _ := by ring
    calc
      _ ≤ (R / m) * (Real.sqrt h * h) ^ 3 := hb i k hk
      _ ≤ (3 * R / a₀) * (Real.sqrt h * h ^ 3) :=
        mul_le_mul hcoeff (cubic_residual_scale_le hh.le hh₁) (by positivity) (by positivity)
      _ = _ := by ring

end SKBarriers2.Corner
