module

public import SKBarriers2.Corner.FrozenCoef

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology
open Set MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def riccatiWeightedCovariance : List (ℝ × Vec3) → Mat3
  | [] => 0
  | u :: l => u.1 • Matrix.vecMulVec u.2 u.2 + riccatiWeightedCovariance l

def riccatiPrecisionMatrix (l : List (ℝ × Vec3)) (χ : ℝ) : Mat3 :=
  1 - χ • riccatiWeightedCovariance l

namespace QuadraticTerminal

def hessianMatrix (Q : QuadraticTerminal) : Mat3 := Matrix.of Q.hessian

private theorem hessian_transpose (Q : QuadraticTerminal) :
    Q.hessianMatrix.transpose = Q.hessianMatrix := by
  ext i j
  exact Q.symmetric j i

private theorem hessian_update_matrix (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) :
    (Q.update m v).hessianMatrix = Q.hessianMatrix +
      (m / Q.precision m v) • Matrix.vecMulVec (Q.hessianDirection v) (Q.hessianDirection v) := by
  ext i j
  simp only [hessianMatrix, update, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

theorem hessian_update_cancel (Q : QuadraticTerminal) (m : ℝ) (v : Vec3)
    (hp : Q.precision m v ≠ 0) :
    (Q.update m v).hessianMatrix *
      (1 - m • Matrix.vecMulVec v (Q.hessianDirection v)) = Q.hessianMatrix := by
  rw [hessian_update_matrix, add_mul, mul_sub, mul_sub, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec]
  change Q.hessianMatrix - m • Matrix.vecMulVec (Q.hessianDirection v) (Q.hessianDirection v) +
    ((m / Q.precision m v) • Matrix.vecMulVec (Q.hessianDirection v) (Q.hessianDirection v) -
      (m / Q.precision m v) • (m •
        Matrix.vecMulVec (Q.hessianDirection v) (((Q.hessianDirection v) ⬝ᵥ v) • Q.hessianDirection v))) = _
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  have hc : (Q.hessianDirection v) ⬝ᵥ v = Q.curvature v := by
    unfold curvature dotProduct
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  have hp' : 1 - m * Q.curvature v ≠ 0 := hp
  dsimp only [precision]
  field_simp
  ring

theorem precisionMatrix_factor (Q : QuadraticTerminal) (A : Mat3) (χ m : ℝ) (v : Vec3)
    (hA : Q.hessianMatrix * A = χ • (1 : Mat3)) :
    A - (χ * m) • Matrix.vecMulVec v v =
      (1 - m • Matrix.vecMulVec v (Q.hessianDirection v)) * A := by
  have hd : (Q.hessianDirection v) ᵥ* A = χ • v := by
    change (Q.hessianMatrix *ᵥ v) ᵥ* A = _
    rw [Matrix.vecMul_mulVec, hessian_transpose, hA, Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.vecMulVec_mul, hd]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem precisionMatrix_update (Q : QuadraticTerminal) (A : Mat3) (χ m : ℝ) (v : Vec3)
    (hA : Q.hessianMatrix * A = χ • (1 : Mat3)) (hp : Q.precision m v ≠ 0) :
    (Q.update m v).hessianMatrix * (A - (χ * m) • Matrix.vecMulVec v v) = χ • (1 : Mat3) := by
  rw [precisionMatrix_factor Q A χ m v hA, ← Matrix.mul_assoc, hessian_update_cancel Q m v hp]
  exact hA

theorem precisionMatrix_det_update (Q : QuadraticTerminal) (A : Mat3) (χ m : ℝ) (v : Vec3)
    (hA : Q.hessianMatrix * A = χ • (1 : Mat3)) :
    (A - (χ * m) • Matrix.vecMulVec v v).det = Q.precision m v * A.det := by
  rw [precisionMatrix_factor Q A χ m v hA, Matrix.det_mul]
  congr 1
  simp [Matrix.det_fin_three, Matrix.vecMulVec_apply,
    precision, curvature, Fin.sum_univ_succ]
  ring

end QuadraticTerminal

theorem riccatiPrecisionMatrix_cons (u : ℝ × Vec3) (l : List (ℝ × Vec3)) (χ : ℝ) :
    riccatiPrecisionMatrix (u :: l) χ =
      riccatiPrecisionMatrix l χ - (χ * u.1) • Matrix.vecMulVec u.2 u.2 := by
  ext i j
  simp only [riccatiPrecisionMatrix, riccatiWeightedCovariance, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem riccatiRecursion_precisionMatrix (l : List (ℝ × Vec3)) (c u χ z : ℝ)
    (hl : RiccatiAdmissible l (separableTaylorQuadratic c u χ z)) :
    (riccatiRecursion l (separableTaylorQuadratic c u χ z)).hessianMatrix *
      riccatiPrecisionMatrix l χ = χ • (1 : Mat3) := by
  induction l with
  | nil =>
    simp only [riccatiRecursion, riccatiPrecisionMatrix, riccatiWeightedCovariance,
      smul_zero, sub_zero, Matrix.mul_one]
    ext i j
    simp only [QuadraticTerminal.hessianMatrix, Matrix.of_apply, separableTaylorQuadratic, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  | cons v l ih =>
    rcases hl with ⟨hl, _, hp⟩
    rw [riccatiRecursion, riccatiPrecisionMatrix_cons]
    exact QuadraticTerminal.precisionMatrix_update _ _ χ v.1 v.2 (ih hl) (ne_of_gt hp)

theorem riccatiPrecisionMatrix_det_pos (l : List (ℝ × Vec3)) (c u χ z : ℝ)
    (hl : RiccatiAdmissible l (separableTaylorQuadratic c u χ z)) :
    0 < (riccatiPrecisionMatrix l χ).det := by
  induction l with
  | nil => simp [riccatiPrecisionMatrix, riccatiWeightedCovariance]
  | cons v l ih =>
    rcases hl with ⟨hl, _, hp⟩
    rw [riccatiPrecisionMatrix_cons,
      QuadraticTerminal.precisionMatrix_det_update _ _ χ v.1 v.2
        (riccatiRecursion_precisionMatrix l c u χ z hl)]
    exact mul_pos hp (ih hl)

def riccatiLogCorrection : List (ℝ × Vec3) → QuadraticTerminal → ℝ
  | [], _ => 0
  | v :: l, Q => riccatiLogCorrection l Q -
      Real.log ((riccatiRecursion l Q).precision v.1 v.2) / (2 * v.1)

theorem riccati_log_precision (v : ℝ × Vec3) (l : List (ℝ × Vec3)) (c u χ z : ℝ)
    (hl : RiccatiAdmissible (v :: l) (separableTaylorQuadratic c u χ z)) :
    Real.log ((riccatiRecursion l (separableTaylorQuadratic c u χ z)).precision v.1 v.2) =
      Real.log (riccatiPrecisionMatrix (v :: l) χ).det - Real.log (riccatiPrecisionMatrix l χ).det := by
  rcases hl with ⟨hl, _, hp⟩
  rw [riccatiPrecisionMatrix_cons,
    QuadraticTerminal.precisionMatrix_det_update _ _ χ v.1 v.2
      (riccatiRecursion_precisionMatrix l c u χ z hl),
    Real.log_mul (ne_of_gt hp) (ne_of_gt (riccatiPrecisionMatrix_det_pos l c u χ z hl))]
  ring

theorem riccatiAdmissible_suffix (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible (l ++ t) Q) : RiccatiAdmissible t Q := by
  induction l with
  | nil => exact hl
  | cons v l ih => exact ih hl.1

theorem riccatiLogCorrection_block (l t : List (ℝ × Vec3)) (c u χ z m : ℝ)
    (hm : ∀ v ∈ l, v.1 = m)
    (hl : RiccatiAdmissible (l ++ t) (separableTaylorQuadratic c u χ z)) :
    riccatiLogCorrection (l ++ t) (separableTaylorQuadratic c u χ z) -
        riccatiLogCorrection t (separableTaylorQuadratic c u χ z) =
      -(Real.log (riccatiPrecisionMatrix (l ++ t) χ).det -
          Real.log (riccatiPrecisionMatrix t χ).det) / (2 * m) := by
  induction l with
  | nil => simp only [List.nil_append, sub_self, neg_zero, zero_div]
  | cons v l ih =>
    have hm₀ : v.1 = m := hm v (List.mem_cons_self)
    have hml : ∀ w ∈ l, w.1 = m := fun w hw => hm w (List.mem_cons_of_mem v hw)
    have H := ih hml hl.1
    have hlog := riccati_log_precision v (l ++ t) c u χ z hl
    simp only [List.cons_append, riccatiLogCorrection] at H ⊢
    rw [hlog, hm₀]
    linear_combination H

theorem riccatiWeightedCovariance_append (l t : List (ℝ × Vec3)) :
    riccatiWeightedCovariance (l ++ t) = riccatiWeightedCovariance l + riccatiWeightedCovariance t := by
  induction l with
  | nil => simp only [List.nil_append, riccatiWeightedCovariance, zero_add]
  | cons v l ih =>
    simp only [List.cons_append, riccatiWeightedCovariance, ih, add_assoc]

theorem riccatiWeightedCovariance_eq (l : List (ℝ × Vec3)) (m : ℝ)
    (hm : ∀ v ∈ l, v.1 = m) :
    riccatiWeightedCovariance l = m • Matrix.of (matrixChainCovariance l) := by
  induction l with
  | nil => ext i j; simp [riccatiWeightedCovariance]
  | cons v l ih =>
    have hm₀ : v.1 = m := hm v List.mem_cons_self
    have hml : ∀ w ∈ l, w.1 = m := fun w hw => hm w (List.mem_cons_of_mem v hw)
    rw [riccatiWeightedCovariance, ih hml, hm₀]
    ext i j
    simp only [matrixChainCovariance_cons, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecMulVec_apply, Pi.add_apply, rankOneMatrix, smul_eq_mul]
    ring

theorem frozenCommon_weightedCovariance (β a h k : ℝ) (hh : 0 ≤ h) :
    riccatiWeightedCovariance (frozenCommon β a (1 / 2) h k) =
      (a * β ^ 2 * h) • ((1 / 3 : ℝ) • q0 (1 / 2) k) := by
  rw [riccatiWeightedCovariance_eq _ (a / 3) (by simp [frozenCommon]),
    frozenCommon_covariance β a (1 / 2) h k hh]
  ext i j
  simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem frozenShared_weightedCovariance (β a h k : ℝ) (hh : 0 ≤ h) :
    riccatiWeightedCovariance (frozenShared β a (1 / 2) h k) =
      (a * β ^ 2 * h) • ((1 / 2 : ℝ) • q1 (1 / 2) k) := by
  rw [riccatiWeightedCovariance_eq _ (a / 2) (by simp [frozenShared]),
    frozenShared_covariance β a (1 / 2) h k hh (by norm_num)]
  ext i j
  simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem frozenInner_weightedCovariance (β a h k : ℝ) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    riccatiWeightedCovariance (frozenInner β a (1 / 2) h k) =
      (a * β ^ 2 * h) • frozenRiccatiCovariance₂ k := by
  rw [riccatiWeightedCovariance_eq _ a (by simp [frozenInner]),
    frozenInner_covariance β a (1 / 2) 0 h k hh (by norm_num)
      (OW.repairLength_mem (by norm_num) hk)]
  ext i j
  simp only [frozenRiccatiCovariance₂, physicalInner, frozenInnerCovariance,
    Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem frozenSchedule_weightedCovariance (β a h k : ℝ) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    riccatiWeightedCovariance (frozenSchedule β a (1 / 2) h k) =
      (a * β ^ 2 * h) • frozenRiccatiCovariance₀ k := by
  rw [frozenSchedule, riccatiWeightedCovariance_append, riccatiWeightedCovariance_append,
    frozenCommon_weightedCovariance β a h k hh, frozenShared_weightedCovariance β a h k hh,
    frozenInner_weightedCovariance β a h k hh hk]
  unfold frozenRiccatiCovariance₀ frozenRiccatiCovariance₁ frozenRiccatiCovariance₂
  module

def frozenRiccatiLogDeterminant (a t k : ℝ) : ℝ :=
  (-3 * Real.log (1 - t • frozenRiccatiCovariance₀ k).det +
    Real.log (1 - t • frozenRiccatiCovariance₁ k).det +
    Real.log (1 - t • frozenRiccatiCovariance₂ k).det) / (2 * a)

theorem frozenSchedule_logCorrection (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) :
    riccatiLogCorrection (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) =
      frozenRiccatiLogDeterminant a (a * β ^ 2 * χ * h) k := by
  let Q := separableTaylorQuadratic c u χ z
  let l₀ := frozenCommon β a (1 / 2) h k
  let l₁ := frozenShared β a (1 / 2) h k
  let l₂ := frozenInner β a (1 / 2) h k
  have hfull : RiccatiAdmissible (l₀ ++ (l₁ ++ l₂)) Q := by
    simpa only [l₀, l₁, l₂, Q, frozenSchedule, List.append_assoc] using hl
  have htail : RiccatiAdmissible (l₁ ++ l₂) Q := riccatiAdmissible_suffix _ _ _ hfull
  have hinner : RiccatiAdmissible l₂ Q := riccatiAdmissible_suffix _ _ _ htail
  have H₀ := riccatiLogCorrection_block l₀ (l₁ ++ l₂) c u χ z (a / 3)
    (by simp [l₀, frozenCommon]) hfull
  have H₁ := riccatiLogCorrection_block l₁ l₂ c u χ z (a / 2)
    (by simp [l₁, frozenShared]) htail
  have H₂ := riccatiLogCorrection_block l₂ [] c u χ z a
    (by simp [l₂, frozenInner]) (by simpa only [List.append_nil] using hinner)
  have A₀ : riccatiPrecisionMatrix (l₀ ++ (l₁ ++ l₂)) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₀ k := by
    change riccatiPrecisionMatrix (frozenSchedule β a (1 / 2) h k) χ = _
    rw [riccatiPrecisionMatrix, frozenSchedule_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have A₁ : riccatiPrecisionMatrix (l₁ ++ l₂) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₁ k := by
    rw [riccatiPrecisionMatrix, riccatiWeightedCovariance_append,
      frozenShared_weightedCovariance β a h k hh, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [frozenRiccatiCovariance₁, frozenRiccatiCovariance₂, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have A₂ : riccatiPrecisionMatrix l₂ χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₂ k := by
    rw [riccatiPrecisionMatrix, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [A₀, A₁] at H₀
  rw [A₁, A₂] at H₁
  have hz : Real.log (riccatiPrecisionMatrix [] χ).det = 0 := by
    simp [riccatiPrecisionMatrix, riccatiWeightedCovariance]
  simp only [List.append_nil] at H₂
  change riccatiLogCorrection l₂ Q - 0 =
    -(Real.log (riccatiPrecisionMatrix l₂ χ).det -
        Real.log (riccatiPrecisionMatrix [] χ).det) / (2 * a) at H₂
  rw [hz, sub_zero, sub_zero] at H₂
  rw [A₂] at H₂
  change riccatiLogCorrection (l₀ ++ (l₁ ++ l₂)) Q = _
  unfold frozenRiccatiLogDeterminant
  field_simp [ha] at H₀ H₁ H₂ ⊢
  nlinarith

namespace QuadraticTerminal

def slopeVector (Q : QuadraticTerminal) (x : Vec3) : Vec3 :=
  fun i => Q.linear i + ∑ j, x j * Q.hessian j i

def hessianTotal (Q : QuadraticTerminal) : ℝ := ∑ i, ∑ j, Q.hessian i j

def AlignedSlope (Q : QuadraticTerminal) (x : Vec3) (τ : ℝ) : Prop :=
  ∀ i, Q.slopeVector x i = τ * ∑ j, Q.hessian j i

private theorem slopeVector_update (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) (i : Fin 3) :
    (Q.update m v).slopeVector x i = Q.slopeVector x i +
      m / Q.precision m v * Q.slope v x * Q.hessianDirection v i := by
  simp only [slopeVector, update, slope, linearDirection, Fin.sum_univ_succ]
  ring

private theorem hessianColumn_update (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) (i : Fin 3) :
    (∑ j, (Q.update m v).hessian j i) = (∑ j, Q.hessian j i) +
      m / Q.precision m v * (∑ j, Q.hessianDirection v j) * Q.hessianDirection v i := by
  simp only [update, Fin.sum_univ_succ]
  ring

theorem alignedSlope_slope (Q : QuadraticTerminal) (v x : Vec3) (τ : ℝ)
    (ha : Q.AlignedSlope x τ) :
    Q.slope v x = τ * ∑ i, Q.hessianDirection v i := by
  have he : Q.slope v x = ∑ i, Q.slopeVector x i * v i := by
    simp only [slope, slopeVector, linearDirection, hessianDirection, Fin.sum_univ_succ]
    ring
  rw [he]
  have hai (i : Fin 3) : Q.slopeVector x i = τ * ∑ j, Q.hessian j i := ha i
  simp_rw [hai]
  simp only [hessianDirection, Fin.sum_univ_succ]
  ring

theorem AlignedSlope.update {Q : QuadraticTerminal} {x : Vec3} {τ : ℝ}
    (ha : Q.AlignedSlope x τ) (m : ℝ) (v : Vec3) : (Q.update m v).AlignedSlope x τ := by
  intro i
  rw [slopeVector_update, hessianColumn_update, ha i, alignedSlope_slope Q v x τ ha]
  ring

theorem hessianTotal_update (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) :
    (Q.update m v).hessianTotal = Q.hessianTotal +
      m / Q.precision m v * (∑ i, Q.hessianDirection v i) ^ 2 := by
  simp only [hessianTotal, update, Fin.sum_univ_succ]
  ring

theorem aligned_value_update (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) (τ : ℝ)
    (ha : Q.AlignedSlope x τ) :
    (Q.update m v).value x = Q.value x - Real.log (Q.precision m v) / (2 * m) +
      τ ^ 2 / 2 * ((Q.update m v).hessianTotal - Q.hessianTotal) := by
  rw [update_value, hessianTotal_update, alignedSlope_slope Q v x τ ha]
  ring

end QuadraticTerminal

theorem riccatiRecursion_aligned_value (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (x : Vec3) (τ : ℝ) (ha : Q.AlignedSlope x τ) :
    (riccatiRecursion l Q).AlignedSlope x τ ∧
      (riccatiRecursion l Q).value x = Q.value x + riccatiLogCorrection l Q +
        τ ^ 2 / 2 * ((riccatiRecursion l Q).hessianTotal - Q.hessianTotal) := by
  induction l with
  | nil =>
    refine ⟨ha, ?_⟩
    simp only [riccatiRecursion, riccatiLogCorrection, add_zero, sub_self, mul_zero]
  | cons v l ih =>
    rcases ih with ⟨hal, hval⟩
    refine ⟨hal.update v.1 v.2, ?_⟩
    rw [riccatiRecursion, QuadraticTerminal.aligned_value_update _ v.1 v.2 x τ hal,
      hval, riccatiLogCorrection]
    ring

theorem separableTaylorQuadratic_aligned (c u χ z : ℝ) (hχ : χ ≠ 0) :
    (separableTaylorQuadratic c u χ z).AlignedSlope (fun _ => z) (u / χ) := by
  intro i
  simp only [QuadraticTerminal.slopeVector, separableTaylorQuadratic]
  simp_rw [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

theorem frozenRiccatiCovariance₀_ones (k : ℝ) :
    frozenRiccatiCovariance₀ k *ᵥ ones = (4 : ℝ) • ones := by
  have he : frozenRiccatiCovariance₀ k =
      ((1 / 3 : ℝ) • q0 (1 / 2) k + (1 / 2 : ℝ) • q1 (1 / 2) k + q2 (1 / 2) k) +
        (4 : ℝ) • (1 : Mat3) := by
    unfold frozenRiccatiCovariance₀ frozenRiccatiCovariance₁ physicalInner
    module
  rw [he, Matrix.add_mulVec, weighted_covariance_annihilates_ones (1 / 2) k (by norm_num),
    zero_add, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem frozenSchedule_precisionMatrix_ones (β a h k χ : ℝ) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    riccatiPrecisionMatrix (frozenSchedule β a (1 / 2) h k) χ *ᵥ ones =
      (1 - 4 * a * β ^ 2 * χ * h) • ones := by
  rw [riccatiPrecisionMatrix, frozenSchedule_weightedCovariance β a h k hh hk,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    frozenRiccatiCovariance₀_ones]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem frozenSchedule_hessianTotal (β a h k c u χ z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hχ : χ ≠ 0)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) :
    1 - 4 * a * β ^ 2 * χ * h ≠ 0 ∧
      (riccatiRecursion (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)).hessianTotal =
        3 * χ / (1 - 4 * a * β ^ 2 * χ * h) := by
  let R := riccatiRecursion (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)
  have hH := riccatiRecursion_precisionMatrix (frozenSchedule β a (1 / 2) h k) c u χ z hl
  have hHv := congrArg (fun A : Mat3 => A *ᵥ ones) hH
  rw [← Matrix.mulVec_mulVec, frozenSchedule_precisionMatrix_ones β a h k χ hh hk,
    Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at hHv
  have hone : ones = fun _ : Fin 3 => (1 : ℝ) := by
    ext i
    fin_cases i <;> rfl
  rw [hone] at hHv
  have he (i : Fin 3) : (1 - 4 * a * β ^ 2 * χ * h) * (∑ j, R.hessian i j) = χ := by
    have hi := congrFun hHv i
    simpa only [R, QuadraticTerminal.hessianMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, mul_one] using hi
  have hd : 1 - 4 * a * β ^ 2 * χ * h ≠ 0 := by
    intro hz
    have H := he 0
    rw [hz, zero_mul] at H
    exact hχ H.symm
  refine ⟨hd, (eq_div_iff hd).mpr ?_⟩
  change R.hessianTotal * (1 - 4 * a * β ^ 2 * χ * h) = 3 * χ
  rw [mul_comm]
  calc
    _ = ∑ i, (1 - 4 * a * β ^ 2 * χ * h) * (∑ j, R.hessian i j) := Finset.mul_sum _ _ _
    _ = ∑ _ : Fin 3, χ := Finset.sum_congr rfl (fun i _ => he i)
    _ = 3 * χ := by simp

theorem frozenSchedule_value_logdet_of_curvature_ne_zero (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hχ : χ ≠ 0)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) :
    (riccatiRecursion (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)).value (fun _ => z) =
      3 * c + frozenRiccatiLogDeterminant a (a * β ^ 2 * χ * h) k +
        6 * a * β ^ 2 * h * u ^ 2 / (1 - 4 * a * β ^ 2 * χ * h) := by
  have H := (riccatiRecursion_aligned_value (frozenSchedule β a (1 / 2) h k)
    (separableTaylorQuadratic c u χ z) (fun _ => z) (u / χ)
    (separableTaylorQuadratic_aligned c u χ z hχ)).2
  obtain ⟨hd, htotal⟩ := frozenSchedule_hessianTotal β a h k c u χ z hh hk hχ hl
  rw [frozenSchedule_logCorrection β a h k c u χ z ha hh hk hl, htotal] at H
  have hbase : (separableTaylorQuadratic c u χ z).value (fun _ => z) = 3 * c := by
    rw [separableTaylorQuadratic_value]
    simp
  have hbaseH : (separableTaylorQuadratic c u χ z).hessianTotal = 3 * χ := by
    simp [QuadraticTerminal.hessianTotal, separableTaylorQuadratic]
  rw [hbase, hbaseH] at H
  rw [H]
  generalize he : 1 - 4 * a * β ^ 2 * χ * h = d at hd ⊢
  field_simp [hχ, hd]
  rw [← he]
  ring

def matrixEntryTotal (A : Mat3) : ℝ := ∑ i, ∑ j, A i j

private theorem ones_apply_one (i : Fin 3) : ones i = 1 := by
  fin_cases i <;> rfl

private theorem matrixEntryTotal_eq_mulVec (A : Mat3) :
    matrixEntryTotal A = ∑ i, (A *ᵥ ones) i := by
  simp only [matrixEntryTotal, Matrix.mulVec, dotProduct, ones_apply_one, mul_one]

theorem frozenSchedule_weightedEntryTotal (β a h k : ℝ) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    matrixEntryTotal (riccatiWeightedCovariance (frozenSchedule β a (1 / 2) h k)) = 12 * a * β ^ 2 * h := by
  rw [frozenSchedule_weightedCovariance β a h k hh hk, matrixEntryTotal_eq_mulVec,
    Matrix.smul_mulVec, frozenRiccatiCovariance₀_ones]
  simp only [Pi.smul_apply, smul_eq_mul, ones_apply_one, mul_one, Fin.sum_univ_succ]
  ring

private theorem weightedEntryTotal_cons (v : ℝ × Vec3) (l : List (ℝ × Vec3)) :
    matrixEntryTotal (riccatiWeightedCovariance (v :: l)) =
      v.1 * (∑ i, v.2 i) ^ 2 + matrixEntryTotal (riccatiWeightedCovariance l) := by
  simp only [matrixEntryTotal, riccatiWeightedCovariance, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Fin.sum_univ_succ]
  ring

theorem riccatiRecursion_affine (l : List (ℝ × Vec3)) (c u z : ℝ) :
    (∀ i j, (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).hessian i j = 0) ∧
    (∀ i, (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).linear i = u) ∧
    (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).value (fun _ => z) =
      3 * c + u ^ 2 / 2 * matrixEntryTotal (riccatiWeightedCovariance l) := by
  induction l with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      simp [riccatiRecursion, separableTaylorQuadratic]
    · intro i
      simp [riccatiRecursion, separableTaylorQuadratic]
    · rw [riccatiRecursion, separableTaylorQuadratic_value]
      simp [riccatiWeightedCovariance, matrixEntryTotal]
  | cons v l ih =>
    rcases ih with ⟨hH, hL, hV⟩
    let R := riccatiRecursion l (separableTaylorQuadratic c u 0 z)
    have hD : R.hessianDirection v.2 = 0 := by
      ext i
      simp only [R, QuadraticTerminal.hessianDirection, hH, zero_mul,
        Finset.sum_const_zero, Pi.zero_apply]
    have hP : R.precision v.1 v.2 = 1 := by
      simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature, hD,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
    have hS : R.slope v.2 (fun _ => z) = u * ∑ i, v.2 i := by
      simp only [R, QuadraticTerminal.slope, QuadraticTerminal.linearDirection,
        hL, hD, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      rw [Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      change (R.update v.1 v.2).hessian i j = 0
      simp only [QuadraticTerminal.update, hD, Pi.zero_apply, mul_zero, add_zero]
      exact hH i j
    · intro i
      change (R.update v.1 v.2).linear i = u
      simp only [QuadraticTerminal.update, hD, Pi.zero_apply, mul_zero, add_zero]
      exact hL i
    · change (R.update v.1 v.2).value (fun _ => z) = _
      rw [QuadraticTerminal.update_value, hP, hS, hV, weightedEntryTotal_cons]
      simp only [Real.log_one, zero_div, sub_zero, mul_one]
      ring

theorem frozenSchedule_value_logdet (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) :
    (riccatiRecursion (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)).value (fun _ => z) =
      3 * c + frozenRiccatiLogDeterminant a (a * β ^ 2 * χ * h) k +
        6 * a * β ^ 2 * h * u ^ 2 / (1 - 4 * a * β ^ 2 * χ * h) := by
  by_cases hχ : χ = 0
  · subst χ
    rw [(riccatiRecursion_affine (frozenSchedule β a (1 / 2) h k) c u z).2.2,
      frozenSchedule_weightedEntryTotal β a h k hh hk]
    simp only [frozenRiccatiLogDeterminant, mul_zero, zero_mul, zero_smul,
      sub_zero, Matrix.det_one, Real.log_one, add_zero, zero_div, div_one]
    ring
  · exact frozenSchedule_value_logdet_of_curvature_ne_zero β a h k c u χ z ha hh hk hχ hl

theorem frozenRiccatiValue_eq_logdet (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)) :
    frozenRiccatiValue β α a s h k z =
      3 * Phi β α (s + 4 * h) z +
        frozenRiccatiLogDeterminant a (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) k +
        6 * a * β ^ 2 * h * jet β α 1 (s + 4 * h) z ^ 2 /
          (1 - 4 * a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) :=
  frozenSchedule_value_logdet β a h k _ _ _ z ha hh hk hl

theorem frozenTerminalTheta_zero_eq_logdet (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)) :
    frozenTerminalTheta β α a s h k z 0 =
      3 * Phi β α (s + 4 * h) z +
        frozenRiccatiLogDeterminant a (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) k +
        6 * a * β ^ 2 * h * jet β α 1 (s + 4 * h) z ^ 2 /
          (1 - 4 * a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) := by
  rw [frozenTerminalTheta_zero β α a s h k z hl]
  exact frozenRiccatiValue_eq_logdet β α a s h k z ha hh hk hl

theorem frozenRiccatiValue_difference_logdet (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hl₀ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)) :
    frozenRiccatiValue β α a s h k z - frozenRiccatiValue β α a s h 0 z =
      frozenRiccatiLogDeterminant a (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) k -
        frozenRiccatiLogDeterminant a (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) 0 := by
  rw [frozenRiccatiValue_eq_logdet β α a s h k z ha hh hk hl,
    frozenRiccatiValue_eq_logdet β α a s h 0 z ha hh (by norm_num) hl₀]
  ring

theorem EvenSecondControl.add {f g : ℝ → ℝ} {κ A B D E : ℝ}
    (hf : EvenSecondControl f κ A B) (hg : EvenSecondControl g κ D E) :
    EvenSecondControl (fun k => f k + g k) κ (A + D) (B + E) := by
  rcases hf with ⟨f₁, f₂, hfd, hfb, hfe⟩
  rcases hg with ⟨g₁, g₂, hgd, hgb, hge⟩
  refine ⟨fun k => f₁ k + g₁ k, fun k => f₂ k + g₂ k, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨(hfd k hk).1.add (hgd k hk).1, (hfd k hk).2.add (hgd k hk).2⟩
  · intro k hk
    exact (abs_add_le _ _).trans (by linarith [hfb k hk, hgb k hk])
  · intro k hk
    dsimp only
    rw [hfe k hk, hge k hk]

theorem EvenSecondControl.const_mul {f : ℝ → ℝ} {κ A B : ℝ}
    (hf : EvenSecondControl f κ A B) (c : ℝ) :
    EvenSecondControl (fun k => c * f k) κ (|c| * A) (|c| * B) := by
  rcases hf with ⟨f₁, f₂, hd, hb, he⟩
  refine ⟨fun k => c * f₁ k, fun k => c * f₂ k, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨(hd k hk).1.const_mul c, (hd k hk).2.const_mul c⟩
  · intro k hk
    dsimp only
    rw [abs_mul]
    have H := mul_le_mul_of_nonneg_left (hb k hk) (abs_nonneg c)
    nlinarith
  · intro k hk
    exact congrArg (fun x => c * x) (he k hk)

theorem EvenSecondControl.sub_const {f : ℝ → ℝ} {κ A B : ℝ}
    (hf : EvenSecondControl f κ A B) (c : ℝ) :
    EvenSecondControl (fun k => f k - c) κ A B := by
  rcases hf with ⟨f₁, f₂, hd, hb, he⟩
  refine ⟨f₁, f₂, ?_, hb, ?_⟩
  · intro k hk
    exact ⟨(hd k hk).1.sub_const c, (hd k hk).2⟩
  · intro k hk
    exact congrArg (fun x => x - c) (he k hk)

theorem EvenSecondControl.mono {f : ℝ → ℝ} {κ A B D E : ℝ}
    (hf : EvenSecondControl f κ A B) (hA : A ≤ D) (hB : B ≤ E) :
    EvenSecondControl f κ D E := by
  rcases hf with ⟨f₁, f₂, hd, hb, he⟩
  refine ⟨f₁, f₂, hd, ?_, he⟩
  intro k hk
  exact (hb k hk).trans (add_le_add hA (mul_le_mul_of_nonneg_right hB (abs_nonneg k)))

def verticalDerivative (F : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ F x (0, 1)

theorem contDiff_verticalDerivative {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (verticalDerivative F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem verticalDerivative_hasDerivAt {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t k : ℝ) :
    HasDerivAt (fun x => F (t, x)) (verticalDerivative F (t, k)) k := by
  have hline : HasDerivAt (fun x : ℝ => (t, x)) (0, 1) k :=
    (hasDerivAt_const k t).prodMk (hasDerivAt_id k)
  exact ((hF.differentiable (by simp) (t, k)).hasFDerivAt.comp_hasDerivAt k hline)

theorem smooth_uniform_vertical_bounds {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      |F (t, k)| ≤ B ∧ |verticalDerivative F (t, k)| ≤ B ∧
        |verticalDerivative (verticalDerivative F) (t, k)| ≤ B := by
  have hK : IsCompact ((Icc (-1 : ℝ) 1) ×ˢ (Icc (-(1 / 2) : ℝ) (1 / 2))) :=
    isCompact_Icc.prod isCompact_Icc
  have hF₁ := contDiff_verticalDerivative hF
  have hF₂ := contDiff_verticalDerivative hF₁
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn hF₁.continuous.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn hF₂.continuous.continuousOn
  refine ⟨1 + |B₀| + |B₁| + |B₂|, by positivity, ?_⟩
  intro t ht k hk
  have h₀ : |F (t, k)| ≤ B₀ := hB₀ (t, k) ⟨ht, hk⟩
  have h₁ : |verticalDerivative F (t, k)| ≤ B₁ := hB₁ (t, k) ⟨ht, hk⟩
  have h₂ : |verticalDerivative (verticalDerivative F) (t, k)| ≤ B₂ := hB₂ (t, k) ⟨ht, hk⟩
  refine ⟨?_, ?_, ?_⟩ <;> linarith [le_abs_self B₀, le_abs_self B₁, le_abs_self B₂,
    abs_nonneg B₀, abs_nonneg B₁, abs_nonneg B₂]

def frozenRiccatiCovariance (j : Fin 3) (k : ℝ) : Mat3 :=
  ![frozenRiccatiCovariance₀ k, frozenRiccatiCovariance₁ k, frozenRiccatiCovariance₂ k] j

def frozenDetArgument (j : Fin 3) (x : ℝ × ℝ) : ℝ :=
  logDetArgument (frozenRiccatiCovariance j x.2) x.1

def frozenDetTail (j : Fin 3) (x : ℝ × ℝ) : ℝ :=
  logDetPolynomialTail x.1 (matrixTrace (frozenRiccatiCovariance j x.2))
    (secondTraceInvariant (frozenRiccatiCovariance j x.2)) (frozenRiccatiCovariance j x.2).det

theorem frozenDetArgument_contDiff (j : Fin 3) : ContDiff ℝ ∞ (frozenDetArgument j) := by
  change ContDiff ℝ ∞ (fun x : ℝ × ℝ => logDetArgument (frozenRiccatiCovariance j x.2) x.1)
  fin_cases j <;>
    simp [frozenRiccatiCovariance, frozenRiccatiCovariance₀,
      frozenRiccatiCovariance₁, frozenRiccatiCovariance₂, physicalInner, logDetArgument,
      secondTraceInvariant, matrixTrace, Matrix.det_fin_three, Matrix.mul_apply,
      q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight,
      Fin.sum_univ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> fun_prop

theorem frozenDetTail_contDiff (j : Fin 3) : ContDiff ℝ ∞ (frozenDetTail j) := by
  change ContDiff ℝ ∞ (fun x : ℝ × ℝ => logDetPolynomialTail x.1
    (matrixTrace (frozenRiccatiCovariance j x.2))
    (secondTraceInvariant (frozenRiccatiCovariance j x.2)) (frozenRiccatiCovariance j x.2).det)
  fin_cases j <;>
    simp [frozenRiccatiCovariance, frozenRiccatiCovariance₀,
      frozenRiccatiCovariance₁, frozenRiccatiCovariance₂, physicalInner, logDetPolynomialTail,
      secondTraceInvariant, matrixTrace, Matrix.det_fin_three, Matrix.mul_apply,
      q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight,
      Fin.sum_univ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> fun_prop

private theorem frozenCovariance_invariants_even (j : Fin 3) (k : ℝ) :
    matrixTrace (frozenRiccatiCovariance j (-k)) = matrixTrace (frozenRiccatiCovariance j k) ∧
    secondTraceInvariant (frozenRiccatiCovariance j (-k)) = secondTraceInvariant (frozenRiccatiCovariance j k) ∧
    (frozenRiccatiCovariance j (-k)).det = (frozenRiccatiCovariance j k).det := by
  refine ⟨?_, ?_, ?_⟩ <;> fin_cases j <;>
    simp [frozenRiccatiCovariance, frozenRiccatiCovariance₀, frozenRiccatiCovariance₁,
      frozenRiccatiCovariance₂, physicalInner, matrixTrace, secondTraceInvariant,
      Matrix.det_fin_three, Matrix.mul_apply, q0, q1, q2, outer, commonVector,
      sharedVector, tentWeight, rampWeight, Fin.sum_univ_succ] <;> ring

theorem frozenDetArgument_even (j : Fin 3) (t k : ℝ) :
    frozenDetArgument j (t, -k) = frozenDetArgument j (t, k) := by
  obtain ⟨ht, he, hd⟩ := frozenCovariance_invariants_even j k
  simp only [frozenDetArgument, logDetArgument, ht, he, hd]

theorem frozenDetTail_even (j : Fin 3) (t k : ℝ) :
    frozenDetTail j (t, -k) = frozenDetTail j (t, k) := by
  obtain ⟨ht, he, hd⟩ := frozenCovariance_invariants_even j k
  simp only [frozenDetTail, ht, he, hd]

theorem logCubicRemainder_evenSecondControl_signed {p p₁ p₂ : ℝ → ℝ} {κ B t : ℝ}
    (hB : 0 ≤ B) (hsmall : |t| * B ≤ 1 / 2)
    (hd : ∀ k ∈ Icc (-κ) κ, HasDerivAt p (p₁ k) k ∧ HasDerivAt p₁ (p₂ k) k)
    (hb : ∀ k ∈ Icc (-κ) κ, |p k| ≤ B ∧ |p₁ k| ≤ B ∧ |p₂ k| ≤ B)
    (he : ∀ k ∈ Icc (-κ) κ, p (-k) = p k) :
    EvenSecondControl (fun k => logCubicRemainder (t * p k)) κ (10 * B ^ 4 * t ^ 4) 0 := by
  by_cases ht : 0 ≤ t
  · exact logCubicRemainder_evenSecondControl hB ht
      (by simpa only [abs_of_nonneg ht] using hsmall) hd hb he
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    have hdn : ∀ k ∈ Icc (-κ) κ,
        HasDerivAt (fun x => -p x) (-p₁ k) k ∧ HasDerivAt (fun x => -p₁ x) (-p₂ k) k :=
      fun k hk => ⟨(hd k hk).1.neg, (hd k hk).2.neg⟩
    have hbn : ∀ k ∈ Icc (-κ) κ, |-p k| ≤ B ∧ |-p₁ k| ≤ B ∧ |-p₂ k| ≤ B := by
      intro k hk
      simpa only [abs_neg] using hb k hk
    have hen : ∀ k ∈ Icc (-κ) κ, -p (-k) = -p k :=
      fun k hk => congrArg Neg.neg (he k hk)
    have H := logCubicRemainder_evenSecondControl hB (neg_nonneg.mpr ht')
      (by simpa only [abs_of_nonpos ht'] using hsmall) hdn hbn hen
    convert H using 1
    · funext k
      congr 1
      ring
    · ring

def logDetTracePolynomial (A : Mat3) (t : ℝ) : ℝ :=
  -t * matrixTrace A - t ^ 2 / 2 * matrixTrace (A * A) - t ^ 3 / 3 * matrixTrace (A * A * A)

def frozenDetError (j : Fin 3) (t k : ℝ) : ℝ :=
  Real.log (1 - t • frozenRiccatiCovariance j k).det - logDetTracePolynomial (frozenRiccatiCovariance j k) t

theorem frozenDetError_eq (j : Fin 3) (t k : ℝ) :
    frozenDetError j t k = logCubicRemainder (t * frozenDetArgument j (t, k)) +
      t ^ 4 * frozenDetTail j (t, k) := by
  rw [frozenDetError, log_det_one_sub_expansion]
  unfold logDetTracePolynomial frozenDetArgument frozenDetTail
  ring

theorem frozenDetError_uniform_control (j : Fin 3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, |t| ≤ δ →
      EvenSecondControl (frozenDetError j t) (1 / 2) (C * t ^ 4) 0 := by
  obtain ⟨B, hB, hb⟩ := smooth_uniform_vertical_bounds (frozenDetArgument_contDiff j)
  obtain ⟨D, hD, hd⟩ := smooth_uniform_vertical_bounds (frozenDetTail_contDiff j)
  refine ⟨10 * B ^ 4 + D, min 1 (1 / (2 * B)), by positivity, by positivity, min_le_left _ _, ?_⟩
  intro t ht
  have ht₁ : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (ht.trans (min_le_left _ _))
  have hsmall : |t| * B ≤ 1 / 2 := by
    have H := mul_le_mul_of_nonneg_right (ht.trans (min_le_right _ _)) hB.le
    have he : 1 / (2 * B) * B = (1 / 2 : ℝ) := by field_simp
    exact he ▸ H
  have harg := logCubicRemainder_evenSecondControl_signed hB.le hsmall
    (fun k _ => ⟨verticalDerivative_hasDerivAt (frozenDetArgument_contDiff j) t k,
      verticalDerivative_hasDerivAt (contDiff_verticalDerivative (frozenDetArgument_contDiff j)) t k⟩)
    (fun k hk => hb t ht₁ k hk) (fun k _ => frozenDetArgument_even j t k)
  have htail : EvenSecondControl (fun k => frozenDetTail j (t, k)) (1 / 2) D 0 := by
    refine ⟨fun k => verticalDerivative (frozenDetTail j) (t, k),
      fun k => verticalDerivative (verticalDerivative (frozenDetTail j)) (t, k), ?_, ?_, ?_⟩
    · intro k _
      exact ⟨verticalDerivative_hasDerivAt (frozenDetTail_contDiff j) t k,
        verticalDerivative_hasDerivAt (contDiff_verticalDerivative (frozenDetTail_contDiff j)) t k⟩
    · intro k hk
      simpa only [zero_mul, add_zero] using (hd t ht₁ k hk).2.2
    · intro k _
      exact frozenDetTail_even j t k
  have H := harg.add (htail.const_mul (t ^ 4))
  simp only [abs_of_nonneg (by positivity : 0 ≤ t ^ 4), mul_zero, add_zero] at H
  convert H using 1
  · funext k
    exact frozenDetError_eq j t k
  · ring

def frozenRiccatiLogError (a t k : ℝ) : ℝ :=
  (-3 * frozenDetError 0 t k + frozenDetError 1 t k + frozenDetError 2 t k) / (2 * a)

theorem frozenRiccatiLogError_eq (h a b χ k : ℝ) (ha : a ≠ 0) :
    frozenRiccatiLogDeterminant a (a * b * χ * h) k - frozenRiccatiTracePolynomial h a b χ k =
      frozenRiccatiLogError a (a * b * χ * h) k := by
  dsimp [frozenRiccatiLogError, frozenDetError, logDetTracePolynomial, frozenRiccatiCovariance,
    frozenRiccatiTracePolynomial, frozenRiccatiLogDeterminant]
  field_simp
  ring

theorem frozenRiccatiLogError_uniform_control :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ a t : ℝ, |t| ≤ δ →
      EvenSecondControl (frozenRiccatiLogError a t) (1 / 2) (|1 / (2 * a)| * C * t ^ 4) 0 := by
  obtain ⟨C₀, δ₀, hC₀, hδ₀, hδ₀₁, H₀⟩ := frozenDetError_uniform_control 0
  obtain ⟨C₁, δ₁, hC₁, hδ₁, _, H₁⟩ := frozenDetError_uniform_control 1
  obtain ⟨C₂, δ₂, hC₂, hδ₂, _, H₂⟩ := frozenDetError_uniform_control 2
  refine ⟨3 * C₀ + C₁ + C₂, min (min δ₀ δ₁) δ₂, by positivity,
    lt_min (lt_min hδ₀ hδ₁) hδ₂, ((min_le_left _ _).trans (min_le_left _ _)).trans hδ₀₁, ?_⟩
  intro a t ht
  have ht₀ : |t| ≤ δ₀ := (ht.trans (min_le_left _ _)).trans (min_le_left _ _)
  have ht₁ : |t| ≤ δ₁ := (ht.trans (min_le_left _ _)).trans (min_le_right _ _)
  have ht₂ : |t| ≤ δ₂ := ht.trans (min_le_right _ _)
  have H := ((((H₀ t ht₀).const_mul (-3)).add (H₁ t ht₁)).add (H₂ t ht₂)).const_mul (1 / (2 * a))
  norm_num at H
  convert H using 1
  · funext k
    unfold frozenRiccatiLogError
    ring
  · norm_num [abs_div, abs_mul]
    ring

theorem EvenSecondControl.transfer {f g : ℝ → ℝ} {κ ρ A B : ℝ}
    (H : EvenSecondControl g ρ A B) (hκρ : κ < ρ)
    (he : ∀ k ∈ Icc (-ρ) ρ, f k = g k) : EvenSecondControl f κ A B := by
  rcases H with ⟨f₁, f₂, hd, hb, hg⟩
  have hsub : Icc (-κ) κ ⊆ Icc (-ρ) ρ :=
    fun k hk => ⟨(neg_le_neg hκρ.le).trans hk.1, hk.2.trans hκρ.le⟩
  refine ⟨f₁, f₂, ?_, (fun k hk => hb k (hsub hk)), ?_⟩
  · intro k hk
    have hn : Icc (-ρ) ρ ∈ nhds k := Icc_mem_nhds (by linarith [hk.1]) (by linarith [hk.2])
    have hnear : f =ᶠ[nhds k] g := by
      filter_upwards [hn] with t ht
      exact he t ht
    exact ⟨(hd k (hsub hk)).1.congr_of_eventuallyEq hnear, (hd k (hsub hk)).2⟩
  · intro k hk
    have hneg : -k ∈ Icc (-ρ) ρ := ⟨by linarith [(hsub hk).2], by linarith [(hsub hk).1]⟩
    rw [he (-k) hneg, he k (hsub hk)]
    exact hg k (hsub hk)

theorem riccatiCoefficientError_eq_logError (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hl₀ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)) :
    riccatiCoefficientError β α a s h z k =
      frozenRiccatiLogError a (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) k -
        frozenRiccatiLogError a (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) 0 := by
  rw [riccatiCoefficientError, frozenRiccatiValue_difference_logdet β α a s h k z ha hh hk hl hl₀,
    ← frozenRiccatiTracePolynomial_difference h a (β ^ 2) (jet β α 2 (s + 4 * h) z) k]
  linear_combination frozenRiccatiLogError_eq h a (β ^ 2) (jet β α 2 (s + 4 * h) z) k ha -
    frozenRiccatiLogError_eq h a (β ^ 2) (jet β α 2 (s + 4 * h) z) 0 ha

theorem riccatiCoefficientError_uniform_control (β a₀ B : ℝ) (ha₀ : 0 < a₀) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Icc a₀ 1 → 0 < h → h ≤ h₀ → |jet β α 2 (s + 4 * h) z| ≤ B →
      EvenSecondControl (riccatiCoefficientError β α a s h z) (1 / 4)
        (C * Real.sqrt h * h ^ 3) (C * h ^ 3) := by
  obtain ⟨D, δ, hD, hδ, _, Herr⟩ := frozenRiccatiLogError_uniform_control
  obtain ⟨hstart, hstart₀, Hstart⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  let P : ℝ := β ^ 2 * B
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let C : ℝ := 1 / (2 * a₀) * D * P ^ 4 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, min 1 (min hstart (δ / (P + 1))), hC, by positivity, ?_⟩
  intro α a s h z ha hh hh₀ hχ
  have hap : 0 < a := ha₀.trans_le ha.1
  have ha1 : a ∈ Ioc (0 : ℝ) 1 := ⟨hap, ha.2⟩
  have hh1 : h ≤ 1 := hh₀.trans (min_le_left _ _)
  have hhs : h ≤ hstart := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhδ : h ≤ δ / (P + 1) := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  let t := a * β ^ 2 * jet β α 2 (s + 4 * h) z * h
  have htP : |t| ≤ P * h := by
    dsimp only [t, P]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hap, abs_of_nonneg (sq_nonneg β), abs_of_pos hh]
    calc
      _ ≤ 1 * β ^ 2 * B * h := by gcongr; exact ha.2
      _ = _ := by ring
  have htδ : |t| ≤ δ := by
    have H := (le_div_iff₀ (by positivity : 0 < P + 1)).mp hhδ
    exact htP.trans (by nlinarith)
  have hQ (k : ℝ) (hk : |k| ≤ 1 / 2) :
      RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) :=
    Hstart α a s h k z ha1 hh.le hhs hk hχ
  have H := (Herr a t htδ).sub_const (frozenRiccatiLogError a t 0)
  have Hactual : EvenSecondControl (riccatiCoefficientError β α a s h z) (1 / 4)
      (|1 / (2 * a)| * D * t ^ 4) 0 := by
    apply H.transfer (by norm_num)
    intro k hk
    exact riccatiCoefficientError_eq_logError β α a s h k z (ne_of_gt hap) hh.le
      (abs_le.mpr hk) (hQ k (abs_le.mpr hk)) (hQ 0 (by norm_num))
  have hInv : |1 / (2 * a)| ≤ 1 / (2 * a₀) := by
    rw [abs_of_pos (by positivity : 0 < 1 / (2 * a))]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [ha.1])
  have ht₄ : t ^ 4 ≤ P ^ 4 * h ^ 4 := by
    calc
      _ = |t| ^ 4 := (Even.pow_abs (by decide : Even 4) t).symm
      _ ≤ (P * h) ^ 4 := by gcongr
      _ = _ := mul_pow _ _ _
  have hbound : |1 / (2 * a)| * D * t ^ 4 ≤ C * h ^ 4 := by
    calc
      _ ≤ (1 / (2 * a₀)) * D * (P ^ 4 * h ^ 4) := by gcongr
      _ ≤ C * h ^ 4 := by dsimp only [C]; nlinarith [pow_nonneg hh.le 4]
  exact (Hactual.mono hbound le_rfl).fourth_order hC.le hh.le hh1

theorem scalarData_riccatiCoefficientError_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      EvenSecondControl
        (riccatiCoefficientError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
        (1 / 4) (C * Real.sqrt h * h ^ 3) (C * h ^ 3) := by
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  let a₀ := c * v
  have ha₀ : 0 < a₀ := mul_pos hc hv
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨C, h₁, hC, hh₁, H⟩ := riccatiCoefficientError_uniform_control β a₀ B ha₀ hB
  refine ⟨C, min h₁ (min (l / 2) ((D.q - u) / 3)), hC, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhh₁ : h ≤ h₁ := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 3 := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : v ≤ r - h := (min_le_left _ _).trans (by linarith [hr.1])
  have hamass : cdf (D.μ : Measure ℝ) (r - h) ∈ Icc a₀ 1 := by
    refine ⟨?_, cdf_le_one _ _⟩
    exact (hlin v ⟨hv.le, min_le_right _ _⟩).trans ((cdf (D.μ : Measure ℝ)).mono hs)
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  apply H _ _ (r - h) h z hamass hh hhh₁
  exact (scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by
    dsimp only [B]
    linarith)

end SKBarriers2.Corner
