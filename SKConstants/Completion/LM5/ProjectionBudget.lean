module

public import SKConstants.Completion.LC5.Energy
public import SKConstants.Completion.LC0.TerminalLink
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5

variable {Past : Type*}

theorem paperRemainingProjectionTrace_symm (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (j : Fin (K+1)) :
    (paperRemainingProjectionTrace r n target update K s z j).IsSymm := by
  induction K with
  | zero => simp [paperRemainingProjectionTrace, frameProjection, Matrix.IsSymm]
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [paperRemainingProjectionTrace, frameProjection, Matrix.IsSymm]
    · exact ih _ _ j

theorem paperRemainingProjectionTrace_idempotent (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0) (j : Fin (K+1)) :
    let P := paperRemainingProjectionTrace r n target update K s z j
    P*P = P := by
  have hf {m : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
      (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
      frameProjection E * frameProjection E = frameProjection E := by
    unfold frameProjection
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, frame_mul_transpose E hE,
      Matrix.one_mul]
  induction K with
  | zero => exact hf s.2 horth
  | succ K ih =>
    refine Fin.cases (hf s.2 horth) (fun j => ?_) j
    exact ih _ _ (tailRows_orthogonal _ (paperFrame_orthogonal _ _ horth)) j

def paperSpinCoefficients (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) (j : Fin K) : ℝ :=
  N⁻¹ * (x ⬝ᵥ paperQueryDirectionTrace r (r+K) N target update K (a,1) z j)

def paperResidualSpin (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) : Fin (r+K) → ℝ :=
  paperResidualProjection r (r+K) target update K (a,1) z *ᵥ x

theorem actualPaper_residual_norm_identity (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (hx : dot x x = N) :
    N⁻¹ * dot (paperResidualSpin r K target update a z x)
      (paperResidualSpin r K target update a z x) =
      1 - ∑ j, (paperSpinCoefficients r K N target update a z x j)^2 := by
  let P := paperResidualProjection r (r+K) target update K (a,1) z
  have hI : ∀ i j : Fin (r+K), dot ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) i)
      ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) j) = if i=j then 1 else 0 := by
    intro i j
    simp [dot, Matrix.one_apply]
  have hsym : P.IsSymm := paperRemainingProjectionTrace_symm r (r+K) target update K
    (a,1) z (Fin.last K)
  have hid : P*P=P := paperRemainingProjectionTrace_idempotent r (r+K) target update K
    (a,1) z hI (Fin.last K)
  have hnorm : dot (P *ᵥ x) (P *ᵥ x) = dot x (P *ᵥ x) := by
    change (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ x)
    rw [dotProduct_comm (P *ᵥ x) (P *ᵥ x), Matrix.dotProduct_mulVec]
    have hv : (P *ᵥ x) ᵥ* P = P *ᵥ (P *ᵥ x) := by
      calc
        _ = (P *ᵥ x) ᵥ* Pᵀ := by congr 1; exact hsym.symm
        _ = _ := Matrix.vecMul_transpose P (P *ᵥ x)
    rw [hv, Matrix.mulVec_mulVec, hid, dotProduct_comm]
  have hp : P = 1 - ∑ i : Fin K,
      N⁻¹ • Matrix.vecMulVec
        (paperQueryDirectionTrace r (r+K) N target update K (a,1) z i)
        (paperQueryDirectionTrace r (r+K) N target update K (a,1) z i) := by
    dsimp [P, paperResidualProjection]
    rw [actualPaper_remainingProjection_eq_past_queries r K N hN]
    simp only [Fin.val_last, Fin.is_lt, ite_true]
  change N⁻¹ * dot (P *ᵥ x) (P *ᵥ x) = _
  rw [hnorm]
  change N⁻¹ * (x ⬝ᵥ (P *ᵥ x)) = _
  rw [hp]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub,
    dotProduct_sum, dotProduct_smul, smul_eq_mul, op_smul_eq_smul]
  change N⁻¹ * (dot x x - ∑ j, N⁻¹ *
    ((paperQueryDirectionTrace r (r+K) N target update K (a,1) z j ⬝ᵥ x) *
      (x ⬝ᵥ paperQueryDirectionTrace r (r+K) N target update K (a,1) z j))) = _
  rw [hx, mul_sub, inv_mul_cancel₀ hN.ne', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [dotProduct_comm _ x]
  unfold paperSpinCoefficients
  ring

theorem actualPaper_coefficient_budget (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (hx : dot x x = N) :
    (∑ j, (paperSpinCoefficients r K N target update a z x j)^2) ≤ 1 := by
  have hy := actualPaper_residual_norm_identity r K N hN target update a z x hx
  have hn : 0 ≤ N⁻¹ * dot (paperResidualSpin r K target update a z x)
      (paperResidualSpin r K target update a z x) := by
    apply mul_nonneg (inv_nonneg.mpr hN.le)
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

def signSpin {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ := fun i => scalarHiddenSign (x i)

theorem signSpin_norm_sq {n : ℕ} (x : Fin n → Bool) : dot (signSpin x) (signSpin x) = n := by
  have he (i : Fin n) : signSpin x i * signSpin x i = 1 := by
    unfold signSpin scalarHiddenSign
    cases x i <;> norm_num
  simp [dot, he]

theorem actualPaper_sign_completionVariance_le (r K : ℕ) (hN : 0 < r+K)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → Bool) :
    completionVariance (r+K : ℕ)
      (paperSpinCoefficients r K (r+K : ℕ) target update a z (signSpin x))
      (paperResidualSpin r K target update a z (signSpin x)) ≤
        (1/2 : ℝ) * ((r+K : ℕ) : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  exact completionVariance_le _ hp _ _
    (actualPaper_coefficient_budget r K _ hp target update a z _ (signSpin_norm_sq x))
    (actualPaper_residual_norm_identity r K _ hp target update a z _ (signSpin_norm_sq x))

end SKConstants.Completion.LM5
