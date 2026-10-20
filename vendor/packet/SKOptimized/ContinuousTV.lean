module

public import SKOptimized.TVBridge

/-!
# Poisson uniformization and weighted TV reductions

Poisson normalization and summability proofs are adapted from the pinned
OpenAI SKBarriers Uniformization module. New statements allow every
threshold below one half. They prove finite reductions from sign-passage
probabilities, not the new sign-passage estimates.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SKOptimized.Model

def clockWeight (a : ℝ) (k : ℕ) : ℝ := Real.exp (-a)*a^k/(k.factorial:ℝ)

theorem clockWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ clockWeight a k := by
  unfold clockWeight
  positivity

theorem clockWeight_hasSum (a : ℝ) : HasSum (clockWeight a) 1 := by
  have H := (NormedSpace.expSeries_div_hasSum_exp a).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ,← Real.exp_add,neg_add_cancel,Real.exp_zero] at H
  unfold clockWeight
  simpa only [mul_div_assoc] using H

theorem clockWeight_sum (a : ℝ) : ∑' k : ℕ, clockWeight a k = 1 := (clockWeight_hasSum a).tsum_eq

theorem uniformization_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x y : Config n) :
    Summable (fun k : ℕ => clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (clockWeight_nonneg (by positivity) k)
    (discreteKernel_nonneg β J k x y)) (fun k => ?_) (clockWeight_hasSum ((n:ℝ)*t)).summable
  exact mul_le_of_le_one_right (clockWeight_nonneg (by positivity) k) (discreteKernel_le_one hn β J k x y)

theorem continuousKernel_eq_clock {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : continuousKernel β J t x y =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y := by
  simp only [continuousKernel,clockWeight,neg_mul]

theorem continuousKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0 ≤ t)
    (x y : Config n) : 0 ≤ continuousKernel β J t x y := by
  rw [continuousKernel_eq_clock]
  apply tsum_nonneg
  intro k
  apply mul_nonneg
  · exact clockWeight_nonneg (by positivity) k
  · exact discreteKernel_nonneg β J k x y

theorem continuousKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x : Config n) : ∑ y : Config n, continuousKernel β J t x y = 1 := by
  classical
  simp_rw [continuousKernel_eq_clock]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) =>
    uniformization_summable hn β J ht x y)]
  simp_rw [← Finset.mul_sum,discreteKernel_sum hn,mul_one]
  exact clockWeight_sum _


theorem continuous_sign_mass_of_tv_threshold {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) (x v : Config n) {t : ℝ} (ht : 0 ≤ t)
    (τ : ℝ) (hTV : continuousDistance β J x t ≤ τ) :
    (1 / 2 : ℝ) - τ ≤
      ∑ y : Config n, if overlap v y ≤ 0 then continuousKernel β J t x y else 0 := by
  have H := finite_event_le_tv (continuousKernel β J t x) (gibbs β J)
    (continuousKernel_sum hn β J ht x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ continuousDistance β J x t at H
  linarith

theorem continuous_tv_of_sign_mass {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) (x v : Config n) {t : ℝ} (ht : 0 ≤ t)
    (τ : ℝ) (hpass : (∑ y : Config n, if overlap v y ≤ 0
      then continuousKernel β J t x y else 0) < (1 / 2 : ℝ) - τ) :
    τ < continuousDistance β J x t := by
  by_contra h
  have H := continuous_sign_mass_of_tv_threshold hn β J x v ht τ (le_of_not_gt h)
  linarith

/-- Gibbs mass of starts that have TV at most the specified threshold. -/
def finiteMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (τ : ℝ)
    (distance : Config n → ℝ) : ℝ :=
  ∑ x : Config n, if distance x ≤ τ then gibbs β J x else 0

/-- Gibbs mass of starts that have TV above the specified threshold. -/
def finiteAboveMass {n : ℕ} (β : ℝ) (J : Disorder n) (τ : ℝ)
    (distance : Config n → ℝ) : ℝ :=
  ∑ x : Config n, if τ < distance x then gibbs β J x else 0

theorem finite_above_add_mixed {n : ℕ} (β : ℝ) (J : Disorder n) (τ : ℝ)
    (distance : Config n → ℝ) :
    finiteAboveMass β J τ distance + finiteMixedMass β J τ distance = 1 := by
  classical
  rw [finiteAboveMass, finiteMixedMass, ← Finset.sum_add_distrib, ← gibbs_sum β J]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : distance x ≤ τ
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- Multiplying a mixed-start mass by the available sign-event gap avoids
any threshold-dependent division. This is valid for the actual discrete kernel. -/
theorem discrete_mixed_mass_times_gap {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) (k : ℕ) (τ : ℝ)
    (v : Config n → Config n) :
    ((1 / 2 : ℝ) - τ) * finiteMixedMass β J τ (fun x => discreteDistance β J x k) ≤
      ∑ x : Config n, gibbs β J x *
        ∑ y : Config n, if overlap (v x) y ≤ 0 then discreteKernel β J k x y else 0 := by
  classical
  rw [finiteMixedMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : discreteDistance β J x k ≤ τ
  · simp only [ite_eq_left h]
    have H := mul_le_mul_of_nonneg_left
      (discrete_sign_mass_of_tv_threshold hn β J x (v x) k τ h) (gibbs_pos β J x).le
    simpa only [mul_comm (gibbs β J x)] using H
  · simp only [ite_eq_right h, mul_zero]
    apply mul_nonneg (gibbs_pos β J x).le
    apply Finset.sum_nonneg
    intro y _
    split_ifs
    · exact discreteKernel_nonneg β J k x y
    · rfl

theorem continuous_mixed_mass_times_gap {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0 ≤ t) (τ : ℝ)
    (v : Config n → Config n) :
    ((1 / 2 : ℝ) - τ) * finiteMixedMass β J τ (fun x => continuousDistance β J x t) ≤
      ∑ x : Config n, gibbs β J x *
        ∑ y : Config n, if overlap (v x) y ≤ 0 then continuousKernel β J t x y else 0 := by
  classical
  rw [finiteMixedMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : continuousDistance β J x t ≤ τ
  · simp only [ite_eq_left h]
    have H := mul_le_mul_of_nonneg_left
      (continuous_sign_mass_of_tv_threshold hn β J x (v x) ht τ h) (gibbs_pos β J x).le
    simpa only [mul_comm (gibbs β J x)] using H
  · simp only [ite_eq_right h, mul_zero]
    apply mul_nonneg (gibbs_pos β J x).le
    apply Finset.sum_nonneg
    intro y _
    split_ifs
    · exact continuousKernel_nonneg β J ht x y
    · rfl

theorem discrete_above_mass_lower_bound {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) (k : ℕ) (τ E : ℝ) (hτ : τ < 1 / 2)
    (v : Config n → Config n)
    (hpass : (∑ x : Config n, gibbs β J x *
      ∑ y : Config n, if overlap (v x) y ≤ 0 then discreteKernel β J k x y else 0) ≤ E) :
    1 - E / ((1 / 2 : ℝ) - τ) ≤
      finiteAboveMass β J τ (fun x => discreteDistance β J x k) := by
  have hgap : 0 < (1 / 2 : ℝ) - τ := sub_pos.mpr hτ
  have H := (discrete_mixed_mass_times_gap hn β J k τ v).trans hpass
  have H' : finiteMixedMass β J τ (fun x => discreteDistance β J x k) ≤
      E / ((1 / 2 : ℝ) - τ) := by
    apply (le_div_iff₀ hgap).mpr
    simpa only [mul_comm ((1 / 2 : ℝ) - τ)] using H
  have he := finite_above_add_mixed β J τ (fun x => discreteDistance β J x k)
  linarith

theorem continuous_above_mass_lower_bound {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0 ≤ t) (τ E : ℝ) (hτ : τ < 1 / 2)
    (v : Config n → Config n)
    (hpass : (∑ x : Config n, gibbs β J x *
      ∑ y : Config n, if overlap (v x) y ≤ 0 then continuousKernel β J t x y else 0) ≤ E) :
    1 - E / ((1 / 2 : ℝ) - τ) ≤
      finiteAboveMass β J τ (fun x => continuousDistance β J x t) := by
  have hgap : 0 < (1 / 2 : ℝ) - τ := sub_pos.mpr hτ
  have H := (continuous_mixed_mass_times_gap hn β J ht τ v).trans hpass
  have H' : finiteMixedMass β J τ (fun x => continuousDistance β J x t) ≤
      E / ((1 / 2 : ℝ) - τ) := by
    apply (le_div_iff₀ hgap).mpr
    simpa only [mul_comm ((1 / 2 : ℝ) - τ)] using H
  have he := finite_above_add_mixed β J τ (fun x => continuousDistance β J x t)
  linarith

end SKOptimized.Model
