module

public import Mathlib

@[expose] public section

namespace SKOptimized.Overshoot

noncomputable section
open scoped BigOperators

def c2 (p : ℝ) : ℝ := ((2 : ℕ) : ℝ) * p * (p - 1) / (p - ((2 : ℕ) : ℝ)) ^ 2
def c4 (p : ℝ) : ℝ :=
  (p - 1) * (((3 : ℕ) : ℝ) * p ^ 2 + ((6 : ℕ) : ℝ) * p + ((4 : ℕ) : ℝ)) /
    (((3 : ℕ) : ℝ) * (p - ((2 : ℕ) : ℝ)) ^ 4)
def c6 (p : ℝ) : ℝ :=
  (((3 : ℕ) : ℝ) * p + ((4 : ℕ) : ℝ)) *
    (((9 : ℕ) : ℝ) * p ^ 2 + ((15 : ℕ) : ℝ) * p + ((10 : ℕ) : ℝ)) /
      (((27 : ℕ) : ℝ) * (p - ((2 : ℕ) : ℝ)) ^ 6)

def riccati2 (p : ℝ) : ℝ :=
  ((2 : ℕ) : ℝ) * (p - 1) * (p ^ 2 + ((2 : ℕ) : ℝ)) / (p - ((2 : ℕ) : ℝ)) ^ 2
def riccati4 (p : ℝ) : ℝ :=
  (((12 : ℕ) : ℝ) * p ^ 3 + ((6 : ℕ) : ℝ) * p ^ 2 + p + ((8 : ℕ) : ℝ)) /
    (((3 : ℕ) : ℝ) * (p - ((2 : ℕ) : ℝ)) ^ 4)
def wick2 (p : ℝ) : ℝ :=
  -(p - 1) * (p ^ 2 - p + ((2 : ℕ) : ℝ)) / (p - ((2 : ℕ) : ℝ)) ^ 2
def wick4 (p : ℝ) : ℝ :=
  -(((3 : ℕ) : ℝ) * p ^ 3 + p ^ 2 + p + ((4 : ℕ) : ℝ)) /
    (((2 : ℕ) : ℝ) * (p - ((2 : ℕ) : ℝ)) ^ 4)

def tentWeight (p : ℝ) : ℝ := 1 / (((2 : ℕ) : ℝ) - p)
def rampWeight (p : ℝ) : ℝ := (1 - p) / (((2 : ℕ) : ℝ) - p)
def gain (p : ℝ) : ℝ := ((2 : ℕ) : ℝ) * (1 - p) / (((2 : ℕ) : ℝ) - p) ^ 2
def pressurePolynomial (p k : ℝ) : ℝ := c2 p * k ^ 2 + c4 p * k ^ 4 + c6 p * k ^ 6
def bandGain (p E : ℝ) : ℝ := gain p - c4 p * E ^ 2 * p - c6 p * E ^ 4 * p ^ 3

theorem sub_two_ne_zero {p : ℝ} (hp : p ≤ 1 / 2) : p - 2 ≠ 0 := by linarith
theorem two_sub_ne_zero {p : ℝ} (hp : p ≤ 1 / 2) : 2 - p ≠ 0 := by linarith

theorem riccati2_add_twice_wick2 (p : ℝ) (hp : p ≠ 2) :
    riccati2 p + 2 * wick2 p = c2 p := by
  unfold riccati2 wick2 c2
  have h : p - 2 ≠ 0 := sub_ne_zero.mpr hp
  field_simp
  <;> ring

theorem riccati4_add_twice_wick4 (p : ℝ) (hp : p ≠ 2) :
    riccati4 p + 2 * wick4 p = c4 p := by
  unfold riccati4 wick4 c4
  have h : p - 2 ≠ 0 := sub_ne_zero.mpr hp
  field_simp
  <;> ring

theorem contact_reduction (p k a b D N : ℝ) (hp : p ≠ 2) (hcontact : N = 2 * a * D) :
    a ^ 2 * b ^ 3 * D *
        (riccati2 p * k ^ 2 + riccati4 p * k ^ 4 + c6 p * k ^ 6) +
      a * b ^ 3 * N * (wick2 p * k ^ 2 + wick4 p * k ^ 4) =
    a ^ 2 * b ^ 3 * D * pressurePolynomial p k := by
  rw [hcontact]
  unfold pressurePolynomial
  rw [← riccati2_add_twice_wick2 p hp, ← riccati4_add_twice_wick4 p hp]
  ring

theorem c2_nonpos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) : c2 p ≤ 0 := by
  unfold c2
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  · positivity

theorem c2_neg {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) : c2 p < 0 := by
  unfold c2
  have hden : 0 < (p - 2) ^ 2 := sq_pos_of_ne_zero (sub_two_ne_zero hp1)
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith)) hden

theorem c4_neg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) : c4 p < 0 := by
  unfold c4
  have hnum : 0 < 3 * p ^ 2 + 6 * p + 4 := by positivity
  have hden : 0 < 3 * (p - 2) ^ 4 := by
    have h := pow_pos (sq_pos_of_ne_zero (sub_two_ne_zero hp1)) 2
    nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hnum) hden

theorem c6_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) : 0 < c6 p := by
  unfold c6
  have hden : 0 < 27 * (p - 2) ^ 6 := by
    have h := pow_pos (sq_pos_of_ne_zero (sub_two_ne_zero hp1)) 3
    nlinarith
  exact div_pos (by positivity) hden

@[simp] theorem c2_half : c2 (1 / 2) = -2 / 9 := by norm_num [c2]
@[simp] theorem c4_half : c4 (1 / 2) = -62 / 243 := by norm_num [c4]
@[simp] theorem c6_half : c6 (1 / 2) = 6952 / 19683 := by norm_num [c6]
@[simp] theorem c2_zero : c2 0 = 0 := by norm_num [c2]
@[simp] theorem c4_zero : c4 0 = -1 / 12 := by norm_num [c4]
@[simp] theorem c6_zero : c6 0 = 5 / 216 := by norm_num [c6]

theorem weights_sum (p : ℝ) (hp : p ≠ 2) : tentWeight p + rampWeight p = 1 := by
  unfold tentWeight rampWeight
  simp only [Nat.cast_ofNat]
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  field_simp
  <;> ring

theorem ramp_tune (p : ℝ) : rampWeight p = tentWeight p * (1 - p) := by
  unfold rampWeight tentWeight
  ring

theorem c2_eq_neg_p_gain (p : ℝ) : c2 p = -p * gain p := by
  unfold c2 gain
  simp only [Nat.cast_ofNat]
  have hsq : (p - 2) ^ 2 = (2 - p) ^ 2 := by ring
  rw [hsq]
  ring

theorem gain_square_identity (p : ℝ) (hp : p ≠ 2) :
    gain p = 1 / 2 - p ^ 2 / (2 * (2 - p) ^ 2) := by
  unfold gain
  simp only [Nat.cast_ofNat]
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  field_simp
  <;> ring

theorem gain_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) : 0 < gain p := by
  unfold gain
  simp only [Nat.cast_ofNat]
  exact div_pos (by linarith) (sq_pos_of_ne_zero (two_sub_ne_zero hp1))

theorem gain_le_half {p : ℝ} (hp1 : p ≤ 1 / 2) : gain p ≤ 1 / 2 := by
  rw [gain_square_identity p (by linarith)]
  have h : 0 ≤ p ^ 2 / (2 * (2 - p) ^ 2) := by positivity
  linarith

@[simp] theorem gain_half : gain (1 / 2) = 4 / 9 := by norm_num [gain]
@[simp] theorem gain_zero : gain 0 = 1 / 2 := by norm_num [gain]

theorem half_polynomial_bound {k : ℝ} (hk : |k| ≤ 1 / 2) :
    pressurePolynomial (1 / 2) k ≤ -(1 / 5) * k ^ 2 := by
  have hk2 : k ^ 2 ≤ 1 / 4 := by
    have H := mul_self_le_mul_self (abs_nonneg k) hk
    nlinarith [sq_abs k]
  have hk4 : k ^ 4 ≤ 1 / 16 := by
    have H := pow_le_pow_left₀ (sq_nonneg k) hk2 2
    nlinarith
  have hk6 : k ^ 6 ≤ k ^ 2 / 16 := by
    have H := mul_le_mul_of_nonneg_right hk4 (sq_nonneg k)
    nlinarith
  simp only [pressurePolynomial, c2_half, c4_half, c6_half]
  nlinarith [sq_nonneg k, pow_nonneg (sq_nonneg k) 2]

theorem local_gain_of_expansion_bound
    (pressure base m C h k : ℝ) (hm : 0 < m) (hC : 0 ≤ C) (hh : 0 < h)
    (hk : |k| ≤ 1 / 2) (hsmall : C * h ≤ m / 10)
    (hexpansion : pressure ≤ base + m * h ^ 3 * pressurePolynomial (1 / 2) k +
      C * h ^ 4 * k ^ 2) :
    pressure ≤ base - m * h ^ 3 * k ^ 2 / 10 := by
  have H := mul_le_mul_of_nonneg_left (half_polynomial_bound hk)
    (by positivity : 0 ≤ m * h ^ 3)
  have HC := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ h ^ 3 * k ^ 2)
  nlinarith

theorem local_gain_in_original_variables
    (pressure base m C h k δ d : ℝ) (hm : 0 < m) (hC : 0 ≤ C) (hh : 0 < h)
    (hk : |k| ≤ 1 / 2) (hsmall : C * h ≤ m / 10)
    (hexpansion : pressure ≤ base + m * h ^ 3 * pressurePolynomial (1 / 2) k +
      C * h ^ 4 * k ^ 2) (hδ : δ = h * k) (hd : d = h / 2) :
    pressure ≤ base - m * δ ^ 2 * d / 5 := by
  have H := local_gain_of_expansion_bound pressure base m C h k hm hC hh hk hsmall hexpansion
  rw [hδ, hd]
  convert H using 1 <;> ring

theorem p0_frozen_contact_reduction (a a1 b D V CW C4 : ℝ)
    (hcontact : b * (V - 12 * a * CW + 6 * a ^ 2 * C4) = 2 * a1 * D) :
    b ^ 4 * (3 * a ^ 3 * C4 / 2 - 3 * a ^ 2 * CW + a * V / 4) =
      a * a1 * b ^ 3 * D / 2 := by
  have H := congrArg (fun x : ℝ => a * b ^ 3 * x / 4) hcontact
  nlinarith only [H]

theorem p0_slope_contact_reduction (a a1 b D N : ℝ) (hcontact : N = 2 * a * D) :
    -17 * a * a1 * b ^ 3 * D / 24 + 13 * a1 * b ^ 3 * N / 96 =
      -7 * a * a1 * b ^ 3 * D / 16 := by
  rw [hcontact]
  ring

theorem p0_frozen_plus_slope (a a1 b D V CW C4 N : ℝ)
    (hcontact3 : b * (V - 12 * a * CW + 6 * a ^ 2 * C4) = 2 * a1 * D)
    (hcontact2 : N = 2 * a * D) :
    b ^ 4 * (3 * a ^ 3 * C4 / 2 - 3 * a ^ 2 * CW + a * V / 4) +
      (-17 * a * a1 * b ^ 3 * D / 24 + 13 * a1 * b ^ 3 * N / 96) =
        a * a1 * b ^ 3 * D / 16 := by
  rw [p0_frozen_contact_reduction a a1 b D V CW C4 hcontact3,
    p0_slope_contact_reduction a a1 b D N hcontact2]
  ring

theorem p0_ramp_contact_square (θ : ℝ) :
    (8 * θ ^ 2 - 12 * θ + 3) + 2 * (-2 * θ ^ 2 + 4 * θ - 1) = (2 * θ - 1) ^ 2 := by
  ring

def p0FourthCoefficient (a a1 b D F T : ℝ) : ℝ :=
  a * a1 * b ^ 3 * D / ((16 : ℕ) : ℝ) +
    b ^ 2 * F * (((2 : ℕ) : ℝ) * a * T - a1 / ((2 : ℕ) : ℝ)) ^ 2

theorem p0_fourth_nonnegative (a a1 b D F T : ℝ)
    (ha : 0 ≤ a) (ha1 : 0 ≤ a1) (hb : 0 ≤ b) (hD : 0 ≤ D) (hF : 0 ≤ F) :
    0 ≤ p0FourthCoefficient a a1 b D F T := by
  unfold p0FourthCoefficient
  positivity

theorem p0_fourth_lower_bound (a a1 b D F T : ℝ) (hF : 0 ≤ F) :
    a * a1 * b ^ 3 * D / 16 ≤ p0FourthCoefficient a a1 b D F T := by
  unfold p0FourthCoefficient
  have H : 0 ≤ b ^ 2 * F * (2 * a * T - a1 / 2) ^ 2 := by positivity
  linarith

theorem p0_fourth_optimal_ramp (a a1 b D F : ℝ) (ha : a ≠ 0) :
    p0FourthCoefficient a a1 b D F (a1 / (4 * a)) = a * a1 * b ^ 3 * D / 16 := by
  unfold p0FourthCoefficient
  simp only [Nat.cast_ofNat]
  have H : 2 * a * (a1 / (4 * a)) - a1 / 2 = 0 := by field_simp; ring
  rw [H]
  ring

theorem p0_fourth_has_minimizer (a a1 b D F : ℝ) (ha : a ≠ 0) (hF : 0 ≤ F) :
    ∃ T : ℝ, ∀ S : ℝ, p0FourthCoefficient a a1 b D F T ≤
      p0FourthCoefficient a a1 b D F S := by
  refine ⟨a1 / (4 * a), ?_⟩
  intro S
  rw [p0_fourth_optimal_ramp a a1 b D F ha]
  exact p0_fourth_lower_bound a a1 b D F S hF

abbrev Vec3 := Fin 3 → ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def ones : Vec3 := ![1, 1, 1]
def contrast : Vec3 := ![0, 1, -1]
def outer (v : Vec3) : Mat3 := fun i j => v i * v j
def contrastMatrix : Mat3 := outer contrast
def repairMatrix : Mat3 := 1 - (1 / ((4 : ℕ) : ℝ)) • contrastMatrix

def commonVector (p k : ℝ) : Vec3 :=
  ![1, 1 + tentWeight p * k, 1 - tentWeight p * k]
def sharedVector (p k : ℝ) : Vec3 :=
  ![0, 1 - tentWeight p * k, 1 + tentWeight p * k]
def rampVector (p k : ℝ) : Vec3 := ![1, rampWeight p * k, -rampWeight p * k]
def postXVector (p k : ℝ) : Vec3 := ![0, 1 - tentWeight p * k, tentWeight p * k]
def postYVector (p k : ℝ) : Vec3 := ![0, -tentWeight p * k, 1 + tentWeight p * k]
def varianceCoefficient (p : ℝ) : ℝ :=
  (tentWeight p) ^ 2 * (((3 : ℕ) : ℝ) - p) + (rampWeight p) ^ 2

def q0 (p k : ℝ) : Mat3 := outer (commonVector p k)
def q1 (p k : ℝ) : Mat3 := p • outer (sharedVector p k)
def q2 (p k : ℝ) : Mat3 :=
  !![-1, rampWeight p * k, -rampWeight p * k;
      rampWeight p * k,
        -1 - p - ((2 : ℕ) : ℝ) * rampWeight p * k - (1 + p) * (tentWeight p) ^ 2 * k ^ 2,
        (1 + p) * (tentWeight p) ^ 2 * k ^ 2;
      -rampWeight p * k,
        (1 + p) * (tentWeight p) ^ 2 * k ^ 2,
        -1 - p + ((2 : ℕ) : ℝ) * rampWeight p * k - (1 + p) * (tentWeight p) ^ 2 * k ^ 2]

theorem q2_physical_decomposition (p k : ℝ) (hp : p ≠ 2) :
    q2 p k = outer (rampVector p k) - (2 : ℝ) • (1 : Mat3) +
      (1 - p) • (outer (postXVector p k) + outer (postYVector p k)) -
      (k ^ 2 * varianceCoefficient p) • contrastMatrix := by
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q2, outer, rampVector, postXVector, postYVector, varianceCoefficient,
      contrastMatrix, contrast, tentWeight, rampWeight, Matrix.one_apply, Matrix.ofNat_apply]
      <;> field_simp [h] <;> ring

theorem outer_posSemidef (v : Vec3) : (outer v).PosSemidef := by
  have H : outer v = Matrix.vecMulVec v (star v) := by
    ext i j
    simp [outer, Matrix.vecMulVec]
  rw [H]
  exact Matrix.posSemidef_vecMulVec_self_star v

def rawLocalCovariance (p k : ℝ) : Mat3 :=
  q0 p k + q1 p k + outer (rampVector p k) +
    (1 - p) • (outer (postXVector p k) + outer (postYVector p k))

theorem raw_local_covariance_posSemidef (p k : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (rawLocalCovariance p k).PosSemidef := by
  unfold rawLocalCovariance q0 q1
  exact (((outer_posSemidef _).add ((outer_posSemidef _).smul hp0)).add
    (outer_posSemidef _)).add
    (((outer_posSemidef _).add (outer_posSemidef _)).smul (by linarith : 0 ≤ 1 - p))

theorem raw_local_covariance_excess (p k : ℝ) (hp : p ≠ 2) :
    rawLocalCovariance p k = q0 p k + q1 p k + q2 p k + (2 : ℝ) • (1 : Mat3) +
      (k ^ 2 * varianceCoefficient p) • contrastMatrix := by
  rw [q2_physical_decomposition p k hp]
  unfold rawLocalCovariance
  abel

theorem contrastMatrix_squared : contrastMatrix * contrastMatrix = (2 : ℝ) • contrastMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contrastMatrix, outer, contrast, Matrix.mul_apply, Fin.sum_univ_succ]

theorem contrastMatrix_mul_ones : Matrix.mulVec contrastMatrix ones = 0 := by
  ext i
  fin_cases i <;> norm_num [contrastMatrix, outer, contrast, ones, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem repair_endpoint (z : ℝ) :
    z • contrastMatrix + (4 * z) • repairMatrix = (4 * z) • (1 : Mat3) := by
  ext i j
  simp only [repairMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

def quadraticForm (Q : Mat3) (x : Vec3) : ℝ := ∑ i, ∑ j, x i * Q i j * x j

theorem repair_quadratic_form (x : Vec3) :
    quadraticForm repairMatrix x =
      x 0 ^ 2 + (x 1 + x 2) ^ 2 / 2 + (x 1 - x 2) ^ 2 / 4 := by
  simp [quadraticForm, repairMatrix, contrastMatrix, outer, contrast, Fin.sum_univ_succ,
    Matrix.one_apply]
  ring

theorem repair_quadratic_nonnegative (x : Vec3) : 0 ≤ quadraticForm repairMatrix x := by
  rw [repair_quadratic_form]
  positivity

theorem repair_posSemidef : repairMatrix.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [repairMatrix, contrastMatrix, outer, contrast, Matrix.conjTranspose_apply,
        Matrix.one_apply]
  · intro x
    simpa [quadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
      using repair_quadratic_nonnegative x

theorem covariance_total (p k : ℝ) (hp : p ≠ 2) :
    q0 p k + q1 p k + q2 p k =
      !![0, 1 + k, 1 - k; 1 + k, 0, 1 + p; 1 - k, 1 + p, 0] := by
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight]
      <;> field_simp [h] <;> ring

theorem covariance_total_diagonal (p k : ℝ) (hp : p ≠ 2) (i : Fin 3) :
    (q0 p k + q1 p k + q2 p k) i i = 0 := by
  rw [covariance_total p k hp]
  fin_cases i <;> simp

theorem repaired_local_covariance_endpoint (p k : ℝ) (hp : p ≠ 2) :
    rawLocalCovariance p k + (4 * (k ^ 2 * varianceCoefficient p)) • repairMatrix =
      !![2, 1 + k, 1 - k; 1 + k, 2, 1 + p; 1 - k, 1 + p, 2] +
        (4 * (k ^ 2 * varianceCoefficient p)) • (1 : Mat3) := by
  have H : q0 p k + q1 p k + q2 p k + (2 : ℝ) • (1 : Mat3) =
      !![2, 1 + k, 1 - k; 1 + k, 2, 1 + p; 1 - k, 1 + p, 2] := by
    rw [covariance_total p k hp]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply, Matrix.ofNat_apply]
  calc
    rawLocalCovariance p k + (4 * (k ^ 2 * varianceCoefficient p)) • repairMatrix =
        (q0 p k + q1 p k + q2 p k + (2 : ℝ) • (1 : Mat3)) +
          ((k ^ 2 * varianceCoefficient p) • contrastMatrix +
            (4 * (k ^ 2 * varianceCoefficient p)) • repairMatrix) := by
              rw [raw_local_covariance_excess p k hp]
              abel
    _ = _ := by rw [H, repair_endpoint]

theorem varianceCoefficient_pos {p : ℝ} (hp1 : p ≤ 1 / 2) : 0 < varianceCoefficient p := by
  have HA : 0 < tentWeight p := by
    unfold tentWeight
    simp only [Nat.cast_ofNat]
    exact div_pos (by norm_num) (by linarith)
  have H : 0 < (tentWeight p) ^ 2 * (3 - p) := mul_pos (by positivity) (by linarith)
  unfold varianceCoefficient
  simp only [Nat.cast_ofNat]
  nlinarith [sq_nonneg (rampWeight p)]

theorem weighted_covariance_annihilates_ones (p k : ℝ) (hp : p ≠ 2) :
    Matrix.mulVec ((1 / 3 : ℝ) • q0 p k + (1 / 2 : ℝ) • q1 p k + q2 p k) ones = 0 := by
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  ext i
  fin_cases i <;>
    simp [q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight,
      ones, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      <;> field_simp [h] <;> ring

theorem common_sum_preserved (p k : ℝ) : ∑ i, commonVector p k i = 3 := by
  simp [commonVector, Fin.sum_univ_succ]
  ring

theorem shared_sum_preserved (p k : ℝ) : ∑ i, sharedVector p k i = 2 := by
  simp [sharedVector, Fin.sum_univ_succ]
  ring

theorem ramp_sum_preserved (p k : ℝ) : ∑ i, rampVector p k i = 1 := by
  simp [rampVector, Fin.sum_univ_succ]

theorem q0_sum (p k : ℝ) : ∑ i, ∑ j, q0 p k i j = 9 := by
  simp [q0, outer, commonVector, Fin.sum_univ_succ]
  ring

theorem q1_sum (p k : ℝ) : ∑ i, ∑ j, q1 p k i j = 4 * p := by
  simp [q1, outer, sharedVector, Fin.sum_univ_succ]
  ring

theorem q2_sum (p k : ℝ) : ∑ i, ∑ j, q2 p k i j = -3 - 2 * p := by
  simp [q2, Fin.sum_univ_succ]
  ring

def matrixTrace (Q : Mat3) : ℝ := ∑ i, Q i i
def entryCubeSum (Q : Mat3) : ℝ := ∑ i, ∑ j, (Q i j) ^ 3

def wickJet (p k : ℝ) : ℝ :=
  (entryCubeSum (q0 p k) / ((3 : ℕ) : ℝ) +
    (entryCubeSum (q0 p k + q1 p k) - entryCubeSum (q0 p k)) / ((2 : ℕ) : ℝ) +
    (entryCubeSum (q0 p k + q1 p k + q2 p k) -
      entryCubeSum (q0 p k + q1 p k))) / ((12 : ℕ) : ℝ)

def riccatiJet (p k : ℝ) : ℝ :=
  let Q0 := q0 p k
  let Q1 := q1 p k
  let Q2 := q2 p k
  let H1 := Q2 + (1 / ((2 : ℕ) : ℝ)) • Q1
  let H2 := Q2 * Q2 + (1 / ((2 : ℕ) : ℝ)) • (Q2 * Q1 + Q1 * Q2) +
    (1 / ((4 : ℕ) : ℝ)) • (Q1 * Q1)
  matrixTrace (Q2 * Q2 * Q2) / ((6 : ℕ) : ℝ) +
    matrixTrace (Q1 * (Q2 * Q2)) / ((2 : ℕ) : ℝ) +
    matrixTrace (Q1 * Q2 * Q1) / ((4 : ℕ) : ℝ) +
    matrixTrace (Q1 * Q1 * Q1) / ((24 : ℕ) : ℝ) +
    matrixTrace (Q0 * H2) / ((2 : ℕ) : ℝ) +
    matrixTrace (Q0 * H1 * Q0) / ((6 : ℕ) : ℝ) +
    matrixTrace (Q0 * Q0 * Q0) / ((54 : ℕ) : ℝ)

set_option maxHeartbeats 2000000 in
theorem wick_jet_evaluation (p k : ℝ) (hp : p ≠ 2) :
    wickJet p k - wickJet p 0 = wick2 p * k ^ 2 + wick4 p * k ^ 4 := by
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  have h' : p - 2 ≠ 0 := sub_ne_zero.mpr hp
  simp [wickJet, entryCubeSum, q0, q1, q2, outer, commonVector, sharedVector,
    tentWeight, rampWeight, wick2, wick4, Fin.sum_univ_succ]
  field_simp [h, h']
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem riccati_jet_evaluation (p k : ℝ) (hp : p ≠ 2) :
    riccatiJet p k - riccatiJet p 0 =
      riccati2 p * k ^ 2 + riccati4 p * k ^ 4 + c6 p * k ^ 6 := by
  have h : 2 - p ≠ 0 := by intro h; apply hp; linarith
  have h' : p - 2 ≠ 0 := sub_ne_zero.mpr hp
  have H : riccatiJet p k - riccatiJet p 0 =
      2 * (p - 1) * (p ^ 2 + 2) * (tentWeight p) ^ 2 * k ^ 2 +
      (12 * p ^ 3 + 6 * p ^ 2 + p + 8) / 3 * (tentWeight p) ^ 4 * k ^ 4 +
      (3 * p + 4) * (9 * p ^ 2 + 15 * p + 10) / 27 * (tentWeight p) ^ 6 * k ^ 6 := by
    simp [riccatiJet, matrixTrace, q0, q1, q2, outer, commonVector, sharedVector,
      ramp_tune, Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  rw [H]
  unfold riccati2 riccati4 c6 tentWeight
  field_simp [h, h']
  ring

theorem finite_jet_contact_reduction (p k a b D N : ℝ)
    (hp : p ≠ 2) (hcontact : N = 2 * a * D) :
    a ^ 2 * b ^ 3 * D * (riccatiJet p k - riccatiJet p 0) +
      a * b ^ 3 * N * (wickJet p k - wickJet p 0) =
        a ^ 2 * b ^ 3 * D * pressurePolynomial p k := by
  rw [riccati_jet_evaluation p k hp, wick_jet_evaluation p k hp]
  exact contact_reduction p k a b D N hp hcontact

theorem finite_half_jet_strictly_negative (k a b D N : ℝ)
    (hk : |k| ≤ 1 / 2) (hk0 : k ≠ 0) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hcontact : N = 2 * a * D) :
    a ^ 2 * b ^ 3 * D * (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
      a * b ^ 3 * N * (wickJet (1 / 2) k - wickJet (1 / 2) 0) < 0 := by
  rw [finite_jet_contact_reduction (1 / 2) k a b D N (by norm_num) hcontact]
  have H : pressurePolynomial (1 / 2) k < 0 := by
    have Hbound := half_polynomial_bound hk
    have Hsquare := sq_pos_of_ne_zero hk0
    nlinarith
  exact mul_neg_of_pos_of_neg (by positivity) H

end
end SKOptimized.Overshoot
