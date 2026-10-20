module

public import SKConstants.Completion.LFine.QueryIdentity
public import SKConstants.Completion.LFine.QueryError
public import SKConstants.Completion.LFine.ResidualNorm
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9
open GaussianProposal FineInformation SKConstantsOAI.ZeroTemperatureSK LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem remainingProjection_diagonal_bounds {m n : ℕ}
    (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i=j then 1 else 0) (i : Fin n) :
    0 ≤ remainingProjection F i i ∧ remainingProjection F i i ≤ 1 := by
  let P := remainingProjection F
  have hsym (j k : Fin n) : P j k = P k j := by
    dsimp [P, remainingProjection]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hsq : (∑ k, P i k^2) = P i i := by
    have h := congrArg (fun A => A i i) (remainingProjection_idempotent F hF)
    change (∑ k, P i k * P k i) = P i i at h
    simpa only [← hsym i, ← pow_two] using h
  have hnonneg : 0 ≤ P i i := by
    rw [← hsq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hle : (P i i)^2 ≤ P i i := by
    exact (Finset.single_le_sum (fun k _ => sq_nonneg (P i k))
      (Finset.mem_univ i)).trans_eq hsq
  exact ⟨hnonneg, by nlinarith⟩

theorem projection_diagonal_loss {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (ζ : Fin n → ℝ) (L s rank : ℝ)
    (hP : ∀ i, P i i ≤ 1) (hζ : ∀ i, ζ i ≤ L*s)
    (htrace : (∑ i, (1-P i i)) = rank) :
    (n : ℝ)⁻¹ * ∑ i, ζ i - L*s*rank/(n : ℝ) ≤
      (n : ℝ)⁻¹ * ∑ i, P i i * ζ i := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : (∑ i, ζ i) - (∑ i, P i i*ζ i) ≤ L*s*rank := by
    calc
      _ = ∑ i, (1-P i i)*ζ i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, (1-P i i)*(L*s) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hζ i) (sub_nonneg.mpr (hP i))
      _ = L*s*rank := by rw [← Finset.sum_mul, htrace]; ring
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnR.le)
  simp only [div_eq_mul_inv]
  nlinarith

theorem freshRows_oneQuery_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (n m : ℕ) (hn : 0 < n)
    (Bpast Dpast : Fin n → ScalarContinuousPath a)
    (s : ℝ) (hs : 0 < s) (L : ℝ) (hL : 0 ≤ L)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (hm₀ : E *ᵥ m₀ = 0)
    (hposterior : FreshPosteriorMeanStatement W β hβ a h f n Bpast Dpast)
    (hζ : ∀ i, |mixedMean (freshRowsLaw W h f n)
      (gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))) i| ≤ L*s) :
    let mean := fun i => fixedPastPosterior W β hβ a (Bpast i) (Dpast i)
    let t := fun i => (mean i-m₀ i)/s
    let C := queryResidualNorm n E t
    let P := remainingProjection (paperFrame E t)
    let row := gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))
    s*C*((n : ℝ)⁻¹ * ∑ i, mixedMean (freshRowsLaw W h f n) row i) -
      L*s^2*C*((n : ℝ)-(m : ℝ))/(n : ℝ) - 2*L*s/(n : ℝ) ≤
      ∫ z, oneQueryEnergy row n (normalizedQuery n (paperFrame E t 0)) P z
        ∂freshRowsLaw W h f n := by
  dsimp only
  let mean := fun i => fixedPastPosterior W β hβ a (Bpast i) (Dpast i)
  let t := fun i => (mean i-m₀ i)/s
  let F := paperFrame E t
  let P := remainingProjection F
  let row := gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))
  let ζ := mixedMean (freshRowsLaw W h f n) row
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hF := paperFrame_orthogonal E t hE
  have hp := remainingProjection_diagonal_bounds F hF
  have hc : 0 ≤ queryResidualNorm n E t := by unfold queryResidualNorm; positivity
  have hd := projection_diagonal_loss hn P ζ L s ((n : ℝ)-(m : ℝ))
    (fun i => (hp i).2) (fun i => (le_abs_self _).trans (hζ i))
    (remainingProjection_trace_deficit F hF)
  have hcorr := oneQuery_correction_abs_le hn (normalizedQuery n (F 0)) mean ζ P L s hs.le hL
    (paperFrame_query_abs_sum_le E t hE)
    (fun i => by rw [abs_of_nonneg (hp i).1]; exact (hp i).2)
    (fun i => by
      exact (actualParisiFullMagnetization_curvature_bounds β _ _).1)
    hζ
  have hi := freshRows_oneQuery_of_posterior W β hβ a h f n m Bpast Dpast n hnR s hs.ne'
    E m₀ hE hm₀ hposterior
  dsimp only at hi
  rw [hi]
  change s*queryResidualNorm n E t*((n : ℝ)⁻¹*∑ i, ζ i) -
    L*s^2*queryResidualNorm n E t*((n : ℝ)-(m : ℝ))/(n : ℝ) - 2*L*s/(n : ℝ) ≤
    s*queryResidualNorm n E t*((n : ℝ)⁻¹*∑ i, P i i*ζ i) -
      2*((n : ℝ)⁻¹)^2*∑ i, normalizedQuery n (F 0) i*P i i*mean i*ζ i
  have hmain := mul_le_mul_of_nonneg_left hd (mul_nonneg hs.le hc)
  have hupper := (abs_le.mp hcorr).2
  simp only [div_eq_mul_inv] at hmain hupper ⊢
  nlinarith

def queryTotalSquare {n : ℕ} (N : ℝ) (t : Fin n → ℝ) : ℝ := N⁻¹ * dot t t

def queryRemovedSquare {m n : ℕ} (N : ℝ)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ) : ℝ :=
  N⁻¹ * dot ((1-frameProjection E) *ᵥ t) ((1-frameProjection E) *ᵥ t)

theorem queryResidualNorm_square_difference {m n : ℕ} (N : ℝ) (hN : 0 < N)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    (queryResidualNorm N E t)^2 = queryTotalSquare N t-queryRemovedSquare N E t := by
  let P := frameProjection E
  have hd : dot t (P *ᵥ t) = dot (E *ᵥ t) (E *ᵥ t) := by
    change t ⬝ᵥ ((Eᵀ*E) *ᵥ t) = _
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rfl
  have hn : dot (P *ᵥ t) (P *ᵥ t) = dot (E *ᵥ t) (E *ᵥ t) :=
    frameProjection_target_norm_square E t hE
  have hrem : dot ((1-P) *ᵥ t) ((1-P) *ᵥ t) = dot t t-dot (E *ᵥ t) (E *ᵥ t) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change (t-P *ᵥ t) ⬝ᵥ (t-P *ᵥ t) = _
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
    change dot t t-dot t (P *ᵥ t) - (dot (P *ᵥ t) t-dot (P *ᵥ t) (P *ᵥ t)) = _
    rw [show dot (P *ᵥ t) t = dot t (P *ᵥ t) from dotProduct_comm _ _, hd, hn]
    ring
  unfold queryResidualNorm queryTotalSquare queryRemovedSquare
  rw [div_pow, Real.sq_sqrt (dot_self_nonneg _), Real.sq_sqrt hN.le]
  change _ = N⁻¹*dot t t - N⁻¹*dot ((1-P) *ᵥ t) ((1-P) *ᵥ t)
  rw [hrem]
  ring

theorem queryResidualNorm_eq_sqrt_difference {m n : ℕ} (N : ℝ) (hN : 0 < N)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    queryResidualNorm N E t = Real.sqrt (queryTotalSquare N t-queryRemovedSquare N E t) := by
  rw [← queryResidualNorm_square_difference N hN E t hE,
    Real.sqrt_sq_eq_abs, abs_of_nonneg]
  unfold queryResidualNorm
  positivity

theorem queryRemovedSquare_nonneg {m n : ℕ} (N : ℝ) (hN : 0 ≤ N)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ) :
    0 ≤ queryRemovedSquare N E t := by
  exact mul_nonneg (inv_nonneg.mpr hN) (dot_self_nonneg _)

theorem queryRemovedSquare_le_total {m n : ℕ} (N : ℝ) (hN : 0 < N)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    queryRemovedSquare N E t ≤ queryTotalSquare N t := by
  have h := queryResidualNorm_square_difference N hN E t hE
  nlinarith [sq_nonneg (queryResidualNorm N E t)]

end SKConstants.Completion.N9
