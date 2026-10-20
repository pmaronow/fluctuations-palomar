module

public import CavityActualStarTransfer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem low_row_covariance_centered (n : ℕ) (b h S t : ℝ) (σ τ : Spin n × Bool) :
    rowCovarianceKernel n (fullVariance n 0 t b h (h+b*S)) σ τ =
      spinValue σ.2*spinValue τ.2*
        (h+b*S+t*b*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S)) := by
  rw [fullVariance_row_covariance]
  ring

 theorem low_row_covariance_power_le (n m : ℕ) (b h S t : ℝ) (σ τ : Spin n × Bool) :
    |rowCovarianceKernel n (fullVariance n 0 t b h (h+b*S)) σ τ|^m ≤
      (2:ℝ)^(m-1)*(|h+b*S|^m+|t*b|^m*
        |deletedOverlap n (joinSpin σ) (joinSpin τ)-S|^m) := by
  rw [low_row_covariance_centered,abs_mul,abs_mul,abs_spinValue,abs_spinValue,one_mul,one_mul]
  have H : |h+b*S+t*b*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S)| ≤
      |h+b*S|+|t*b| * |deletedOverlap n (joinSpin σ) (joinSpin τ)-S| := by
    simpa only [abs_mul] using abs_add_le (h+b*S)
      (t*b*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S))
  have HA := add_pow_le (abs_nonneg (h+b*S))
    (mul_nonneg (abs_nonneg (t*b)) (abs_nonneg (deletedOverlap n (joinSpin σ) (joinSpin τ)-S))) m
  apply (pow_le_pow_left₀ (abs_nonneg _) H m).trans
  simpa only [mul_pow] using HA

 theorem actual_low_row_moment_le (n m : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n → ℝ) (q : ℕ → FullCoordinate n → ℝ)
    (x : FullCoordinate n → ℝ) (s r : T.Slot) (b h S t : ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ => |rowCovarianceKernel n (fullVariance n 0 t b h (h+b*S))
        (T.atSlot σ s) (T.atSlot σ r)|^m) x ≤
      (2:ℝ)^(m-1)*(|h+b*S|^m+|t*b|^m*
        T.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ => |deletedOverlap n (joinSpin (T.atSlot σ s))
            (joinSpin (T.atSlot σ r))-S|^m) x) := by
  let w := fun σ => T.disorderWeight (fullWeight n) (fullFeature n) v q σ x
  have hw := T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x
  have H := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (low_row_covariance_power_le n m b h S t (T.atSlot σ s) (T.atSlot σ r)) (hw.1 σ))
  change (∑ σ, w σ*_) ≤ _
  apply H.trans_eq
  change (∑ σ, w σ*((2:ℝ)^(m-1)*(|h+b*S|^m+|t*b|^m*
      |deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ r))-S|^m))) =
    (2:ℝ)^(m-1)*(|h+b*S|^m+|t*b|^m*(∑ σ, w σ*
      |deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ r))-S|^m))
  calc
    _ = (2:ℝ)^(m-1)*(|h+b*S|^m*(∑ σ, w σ)+|t*b|^m*(∑ σ, w σ*
      |deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ r))-S|^m)) := by
      simp only [mul_add,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by rw [show ∑ σ, w σ = 1 from hw.2,mul_one]

end OAI.SKFluctuations.Cavity
