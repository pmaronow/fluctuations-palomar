module

public import SKBarriers2.Corner.Penalty

@[expose] public section

noncomputable section
open scoped BigOperators Matrix
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def physicalInner (k : ℝ) : Mat3 := q2 (1 / 2) k + (4 : ℝ) • (1 : Mat3)

def normContraction (Q₀ Q₁ Q₂ : Mat3) : ℝ :=
  matrixSquare 3 Q₀ / 3 + (matrixSquare 3 (Q₀ + Q₁) - matrixSquare 3 Q₀) / 2 +
    matrixSquare 3 (Q₀ + Q₁ + Q₂) - matrixSquare 3 (Q₀ + Q₁)

def riccatiContraction (Q₀ Q₁ Q₂ : Mat3) : ℝ :=
  let H₁ := Q₂ + (1 / 2 : ℝ) • Q₁
  let H₂ := Q₂ * Q₂ + (1 / 2 : ℝ) • (Q₂ * Q₁ + Q₁ * Q₂) +
    (1 / 4 : ℝ) • (Q₁ * Q₁)
  matrixTrace (Q₂ * Q₂ * Q₂) / 6 + matrixTrace (Q₁ * (Q₂ * Q₂)) / 2 +
    matrixTrace (Q₁ * Q₂ * Q₁) / 4 + matrixTrace (Q₁ * Q₁ * Q₁) / 24 +
    matrixTrace (Q₀ * H₂) / 2 + matrixTrace (Q₀ * H₁ * Q₀) / 6 +
    matrixTrace (Q₀ * Q₀ * Q₀) / 54

def wickContraction (Q₀ Q₁ Q₂ : Mat3) : ℝ :=
  (entryCubeSum Q₀ / 3 + (entryCubeSum (Q₀ + Q₁) - entryCubeSum Q₀) / 2 +
    entryCubeSum (Q₀ + Q₁ + Q₂) - entryCubeSum (Q₀ + Q₁)) / 12

def physicalNorm (k : ℝ) : ℝ :=
  normContraction (q0 (1 / 2) k) (q1 (1 / 2) k) (physicalInner k)

def physicalRiccati (k : ℝ) : ℝ :=
  riccatiContraction (q0 (1 / 2) k) (q1 (1 / 2) k) (physicalInner k)

def physicalWick (k : ℝ) : ℝ :=
  wickContraction (q0 (1 / 2) k) (q1 (1 / 2) k) (physicalInner k)

theorem physical_norm_difference (k : ℝ) :
    physicalNorm k - physicalNorm 0 = penaltyPolynomial (1 / 2) k := by
  simp [physicalNorm, normContraction, physicalInner, matrixSquare,
    q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight,
    Matrix.one_apply, Fin.sum_univ_succ, penaltyPolynomial, gain]
  ring

set_option maxHeartbeats 800000 in
theorem physical_riccati_difference (k : ℝ) :
    physicalRiccati k - physicalRiccati 0 =
      riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0 +
        2 * penaltyPolynomial (1 / 2) k := by
  simp [physicalRiccati, riccatiContraction, physicalInner, riccatiJet,
    matrixTrace, q0, q1, q2, outer, commonVector, sharedVector,
    tentWeight, rampWeight, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.one_apply,
    Fin.sum_univ_succ, penaltyPolynomial, gain]
  ring

theorem physical_wick_difference (k : ℝ) :
    physicalWick k - physicalWick 0 = wickJet (1 / 2) k - wickJet (1 / 2) 0 := by
  simp [physicalWick, wickContraction, physicalInner, wickJet, entryCubeSum,
    q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight,
    Matrix.one_apply, Fin.sum_univ_succ]
  ring

def frozenCoefficient₁ (k a b u χ : ℝ) : ℝ :=
  b * χ / 2 * matrixTrace (q0 (1 / 2) k + q1 (1 / 2) k + physicalInner k) +
    a * b * u ^ 2 / 2 * quadraticForm
      ((1 / 3 : ℝ) • q0 (1 / 2) k + (1 / 2 : ℝ) • q1 (1 / 2) k + physicalInner k) ones

def frozenCoefficient₂ (k a b χ : ℝ) : ℝ := a * b ^ 2 * χ ^ 2 / 4 * physicalNorm k

def frozenCoefficient₃ (k a b u χ w g₄ : ℝ) : ℝ :=
  a ^ 2 * b ^ 3 * χ ^ 3 * physicalRiccati k +
    a * b ^ 3 * w ^ 2 * physicalWick k +
    a * b ^ 3 * χ * (g₄ + 2 * a * u * w) * physicalNorm k

theorem FJ_coefficient₁ (k a b u χ : ℝ) :
    frozenCoefficient₁ k a b u χ - frozenCoefficient₁ 0 a b u χ = 0 := by
  simp [frozenCoefficient₁, physicalInner, matrixTrace, quadraticForm,
    q0, q1, q2, outer, commonVector, sharedVector, ones,
    tentWeight, rampWeight, Matrix.one_apply, Fin.sum_univ_succ]
  ring

theorem FJ_coefficient₂ (k a b χ : ℝ) :
    frozenCoefficient₂ k a b χ - frozenCoefficient₂ 0 a b χ =
      a * b ^ 2 / 4 * χ ^ 2 * penaltyPolynomial (1 / 2) k := by
  unfold frozenCoefficient₂
  rw [← mul_sub, physical_norm_difference]
  ring

theorem FJ_coefficient₃ (k a b u χ w g₄ : ℝ) :
    frozenCoefficient₃ k a b u χ w g₄ - frozenCoefficient₃ 0 a b u χ w g₄ =
      a ^ 2 * b ^ 3 * χ ^ 3 * (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
        a * b ^ 3 * w ^ 2 * (wickJet (1 / 2) k - wickJet (1 / 2) 0) +
        a * b ^ 3 * χ * (g₄ + 2 * a * χ ^ 2 + 2 * a * u * w) *
          penaltyPolynomial (1 / 2) k := by
  have hR := physical_riccati_difference k
  have hW := physical_wick_difference k
  have hN := physical_norm_difference k
  unfold frozenCoefficient₃
  calc
    _ = a ^ 2 * b ^ 3 * χ ^ 3 * (physicalRiccati k - physicalRiccati 0) +
        a * b ^ 3 * w ^ 2 * (physicalWick k - physicalWick 0) +
        a * b ^ 3 * χ * (g₄ + 2 * a * u * w) * (physicalNorm k - physicalNorm 0) := by ring
    _ = _ := by rw [hR, hW, hN]; ring

theorem FJ_terminal_shift_cancellation (k a b u χ w g₄ : ℝ) :
    (a * b ^ 2 / 4) * (-4 * b * χ * (g₄ + 2 * a * χ ^ 2 + 2 * a * u * w)) *
        penaltyPolynomial (1 / 2) k +
      a * b ^ 3 * χ * (g₄ + 2 * a * χ ^ 2 + 2 * a * u * w) *
        penaltyPolynomial (1 / 2) k = 0 := by
  ring

end SKBarriers2.Corner
