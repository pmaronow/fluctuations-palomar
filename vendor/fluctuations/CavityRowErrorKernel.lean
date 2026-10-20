module

public import CavityMomentAllocation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Cavity
open Hierarchy

def rowCovarianceKernel (n : ℕ) (d : FullCoordinate n → ℝ)
    (σ τ : Spin n × Bool) : ℝ :=
  ∑ i, d i*fullFeature n σ (Pi.single i 1)*fullFeature n τ (Pi.single i 1)

theorem rowInterpolationSlope_covariance (n : ℕ) (b h K : ℝ)
    (σ τ : Spin n × Bool) :
    rowCovarianceKernel n (rowInterpolationSlope n b h K) σ τ =
      spinValue σ.2*spinValue τ.2*
        (h+b*deletedOverlap n (joinSpin σ) (joinSpin τ)-K) := by
  unfold rowCovarianceKernel
  simp_rw [fullFeature_single]
  simp only [rowInterpolationSlope,fullCoefficient,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,zero_add,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_one,one_mul]
  have hr (i : Fin n) : dormantCoefficient n σ (.inl i) =
      rowInteractionCoefficient n (joinSpin σ) i := by
    simp [dormantCoefficient,rowInteractionCoefficient,joinSpin_last,joinSpin]
  have ht (i : Fin n) : dormantCoefficient n τ (.inl i) =
      rowInteractionCoefficient n (joinSpin τ) i := by
    simp [dormantCoefficient,rowInteractionCoefficient,joinSpin_last,joinSpin]
  simp_rw [hr,ht]
  rw [rowInteraction_covariance]
  simp only [dormantCoefficient,joinSpin_last,Fin.sum_univ_one]
  ring

theorem rowInterpolationSlope_centered (n : ℕ) (b h S : ℝ)
    (σ τ : Spin n × Bool) :
    rowCovarianceKernel n (rowInterpolationSlope n b h (h+b*S)) σ τ =
      spinValue σ.2*spinValue τ.2*b*
        (deletedOverlap n (joinSpin σ) (joinSpin τ)-S) := by
  rw [rowInterpolationSlope_covariance]
  ring

theorem abs_deletedOverlap_le_one (n : ℕ) (σ τ : Spin (n+1)) :
    |deletedOverlap n σ τ| ≤ 1 := by
  unfold deletedOverlap
  rw [abs_div]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n+1 : ℕ))]
  have hn : (0:ℝ) < (n+1 : ℕ) := by positivity
  apply (div_le_one hn).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_spinValue,one_mul,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  push_cast
  linarith

theorem rowInterpolationSlope_kernel_abs_le (n : ℕ) (b h K : ℝ)
    (σ τ : Spin n × Bool) :
    |rowCovarianceKernel n (rowInterpolationSlope n b h K) σ τ| ≤ |h|+|b|+|K| := by
  rw [rowInterpolationSlope_covariance,abs_mul,abs_mul,abs_spinValue,abs_spinValue,
    one_mul,one_mul]
  apply (abs_sub _ _).trans
  apply add_le_add _ le_rfl
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_deletedOverlap_le_one n _ _)

theorem rowInterpolationSlope_kernel_square (n : ℕ) (b h S : ℝ)
    (σ τ : Spin n × Bool) :
    (rowCovarianceKernel n (rowInterpolationSlope n b h (h+b*S)) σ τ)^2 =
      b^2*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S)^2 := by
  rw [rowInterpolationSlope_centered]
  have hs (s : Bool) : spinValue s ^ 2 = 1 := by
    simpa only [pow_two] using spinValue_sq s
  simp only [mul_pow, hs, one_mul]

end OAI.SKFluctuations.Cavity
