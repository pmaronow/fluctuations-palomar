module

public import SKConstants.Completion.LC5.ActualAssembly
public import SKConstants.Completion.LC5.Padding
public import SKConstants.Completion.LC5.CompletionLaws
public import SKConstants.Completion.LC5.SourceSplitting
import Mathlib.Tactic

@[expose] public section
noncomputable section
open NormedSpace InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LC5
open GaussianProposal

theorem projectedQueryEnergy_operator_error_padded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R k m : ℕ) (hdim : k+m = 2^R) (η : ℝ) (T g : Fin k → E) (x : E)
    (s b : EuclideanSpace ℝ (Fin k)) (H0 : Matrix (Fin k) (Fin k) ℝ)
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖familyGram T-1‖ ≤ η)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖familyCross T g-H0‖ ≤ η)
    (heq : ‖familyCoordinates T x-s‖ ≤ η)
    (hev : ‖familyCoordinates g x-b‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |projectedQueryEnergy (gramSchmidtNormed ℝ T) g x - inner (𝕜 := ℝ) s b| ≤
      queryError R η := by
  have hd : 1 ≤ ((R+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hηsmall : η ≤ 3/4 := by
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ ((R+1 : ℕ) : ℝ)^2 by nlinarith) hη
    nlinarith
  have hGram := hEA.trans hηsmall
  have hsym : (familyGram T-1).transpose = familyGram T-1 := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, familyGram, Matrix.one_apply]
    rw [real_inner_comm]
    split_ifs <;> simp_all
  have hg : (gramSchmidtCholesky T).transpose*gramSchmidtCholesky T =
      1+(familyGram T-1) := by rw [gramSchmidtCholesky_gram T hGram]; abel
  have h := upper_cholesky_energy_of_operator_errors_padded R k m hdim η (familyGram T-1)
    (gramSchmidtCholesky T) H0 (familyCross T g-H0) s (familyCoordinates T x-s)
    b (familyCoordinates g x-b) hη hsmall hEA hsym (gramSchmidtCholesky_upper T)
    (gramSchmidtCholesky_positive T hGram) hg (gramSchmidtCholesky_isUnit T hGram)
    hH0 hEH heq hev hs hb
  rw [projectedQueryEnergy_eq_cholesky T g hGram x]
  simpa only [add_sub_cancel] using h

theorem actualPaper_query_energy_normalForm {Past : Type*} (r K : ℕ)
    (N : ℝ) (hN : 0 < N)
    (target : (j : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (hGram : ‖familyGram (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))-1‖ ≤ (3/4 : ℝ)) :
    let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j)
    let U := fun j => WithLp.toLp 2
      (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
    let g := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (fun l => paperEndpointTrace (r+K) K z j (.inl l))
    let x0 := (Real.sqrt N)⁻¹ • WithLp.toLp 2 x
    paperQueryEnergy r (r+K) N target update K (a,1) z x =
      queryEnergyNormalForm (familyCross U T) (familyCross T g)
        (familyCoordinates T x0) (familyCoordinates g x0) := by
  rw [paperQueryEnergy_eq_projected r K N hN]
  exact (actualPaper_query_cholesky_coordinates r K target update a z (Real.sqrt N)⁻¹
    (inv_pos.mpr (Real.sqrt_pos.mpr hN)) hGram _ _).2.2.2.2.2

theorem actualPaper_query_energy_operator_error {Past : Type*}
    (r K R m : ℕ) (hdim : K+m = 2^R) (N η : ℝ) (hN : 0 < N)
    (target : (j : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (s b : EuclideanSpace ℝ (Fin K)) (H0 : Matrix (Fin K) (Fin K) ℝ)
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖familyGram (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))-1‖ ≤ η)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖familyCross (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))
      (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
        (fun l => paperEndpointTrace (r+K) K z j (.inl l)))-H0‖ ≤ η)
    (heq : ‖familyCoordinates (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j))
      ((Real.sqrt N)⁻¹ • WithLp.toLp 2 x)-s‖ ≤ η)
    (hev : ‖familyCoordinates (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (fun l => paperEndpointTrace (r+K) K z j (.inl l)))
      ((Real.sqrt N)⁻¹ • WithLp.toLp 2 x)-b‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |paperQueryEnergy r (r+K) N target update K (a,1) z x - inner (𝕜 := ℝ) s b| ≤
      queryError R η := by
  let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
    (paperTargetTrace r (r+K) target update K (a,1) z j)
  let U := fun j => WithLp.toLp 2
    (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
  have hd : 1 ≤ ((R+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hηsmall : η ≤ 3/4 := by
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ ((R+1 : ℕ) : ℝ)^2 by nlinarith) hη
    nlinarith
  have hGram := hEA.trans hηsmall
  have hU : U = gramSchmidtNormed ℝ T := funext fun j =>
    actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z (Real.sqrt N)⁻¹
      (inv_pos.mpr (Real.sqrt_pos.mpr hN)) hGram j
  rw [paperQueryEnergy_eq_projected r K N hN]
  change |projectedQueryEnergy U _ _ - inner (𝕜 := ℝ) s b| ≤ _
  rw [hU]
  exact projectedQueryEnergy_operator_error_padded R K m hdim η T _ _ s b H0
    hη hsmall hEA hH0 hEH heq hev hs hb

end SKConstants.Completion.LC5
