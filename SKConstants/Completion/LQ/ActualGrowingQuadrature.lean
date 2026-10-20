module

public import SKConstants.Completion.LQ.StoppingQuadrature
public import SKConstants.Completion.LQ.ActualProfileBounds

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace SKConstants.Completion.LQ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def actualParisiQueryIntervalSpinMean (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) : ℝ :=
  (∫ v in (s : ℝ)..(t : ℝ), actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v) /
    Real.sqrt ((t : ℝ) - (s : ℝ))

def actualParisiGrowingEnergySum (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q,
    (actualParisiPosteriorIntervalScale W β (growingQueryTime δ i) (growingQueryTime δ (i + 1)) : ℝ) *
      actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (i + 1)) (growingQueryTime δ (i + 2))

def actualParisiGrowingEntropyFrozen (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i ∈ Finset.range (q + 1),
    (actualParisiQueryRho W β (growingQueryTime δ i))^2 *
      ∫ v in (growingQueryTime δ i : ℝ)..(growingQueryTime δ (i + 1) : ℝ),
        actualParisiFullEntropyRateExpected W β v

def actualParisiGrowingEntropyQueries (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i ∈ Finset.range q,
    (actualParisiQueryRho W β (growingQueryTime δ (i + 1)))^2 *
      ∫ v in (growingQueryTime δ (i + 1) : ℝ)..(growingQueryTime δ (i + 2) : ℝ),
        actualParisiFullEntropyRateExpected W β v

lemma actual_energy_reference_eq (W : BrownianSystem Ω) (β V : ℝ) :
    energyReference (actualParisiFullSusceptibilitySquareExpected W β)
      (fun v => actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v) V =
        actualParisiEnergyReference W β V := by
  unfold energyReference actualParisiEnergyReference
  congr 1
  funext v
  ring

lemma actual_information_reference_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ) (hV : 0 ≤ V) :
    informationReference (actualParisiFullSusceptibilitySquareExpected W β)
      (actualParisiFullEntropyRateExpected W β) (β^2) V = actualParisiEntropyReference W β V := by
  have H : (∫ v in 0..V, (actualParisiQueryRho W β v)^2 * actualParisiFullEntropyRateExpected W β v) =
      β^2 * (∫ v in 0..V, actualParisiFullSusceptibilitySquareExpected W β v *
        actualParisiFullEntropyRateExpected W β v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le hV] at hv
    rw [actual_rho_sq_eq W β hβ v hv.1]
    ring
  unfold informationReference actualParisiEntropyReference
  rw [H]
  ring

lemma actual_growing_energy_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) :
    actualParisiGrowingEnergySum W β δ q =
      growingEnergySum (actualParisiFullSusceptibilitySquareExpected W β)
        (fun v => actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v) δ q := by
  unfold actualParisiGrowingEnergySum growingEnergySum
  apply Finset.sum_congr rfl
  intro i _hi
  rw [actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _
    (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self i))]
  rfl

lemma actual_growing_information_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (q : ℕ) :
    actualParisiGrowingEntropyFrozen W β δ q =
      growingInformationAll (actualParisiFullSusceptibilitySquareExpected W β)
        (actualParisiFullEntropyRateExpected W β) (β^2) δ q ∧
    actualParisiGrowingEntropyQueries W β δ q =
      growingInformationQueries (actualParisiFullSusceptibilitySquareExpected W β)
        (actualParisiFullEntropyRateExpected W β) (β^2) δ q := by
  constructor
  all_goals
    simp only [actualParisiGrowingEntropyFrozen, actualParisiGrowingEntropyQueries,
      growingInformationAll, growingInformationQueries]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [actual_rho_sq_eq W β hβ _ (growingQueryTime δ _).coe_nonneg]
    simp only [meshTime]
    ring

theorem actual_growing_energy_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ)
    (hsmall : ∀ i < q + 1, growingQueryDuration δ i ≤ 1) :
    |actualParisiGrowingEnergySum W β δ q -
      actualParisiEnergyReference W β (growingQueryTime δ (q + 1))| ≤
      (1 / β^2 + 33 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)) * (δ : ℝ) := by
  have H := growing_energy_error (actualParisiFullSusceptibilitySquareExpected W β)
    (fun v => actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v)
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) δ hδ q
    (fun t _ht => (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1)
    (actual_square_profile_antitone W β hβ) (actual_square_profile_drop W β hβ)
    (actual_square_profile_tail W β hβ) (fun t _ht => actual_query_integrand_bounds W β hβ t)
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)
    (((continuous_actualParisiFullSusceptibilityExpected W β).mul
      (continuous_actualParisiQueryRho W β)).intervalIntegrable _ _)
    (((continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt.mul
      ((continuous_actualParisiFullSusceptibilityExpected W β).mul
        (continuous_actualParisiQueryRho W β))).intervalIntegrable _ _)
    (fun i hi => by exact_mod_cast hsmall i hi)
  rw [actual_energy_reference_eq, actual_square_profile_zero W β hβ] at H
  rw [actual_growing_energy_eq W β hβ δ hδ q]
  have he : Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * Real.exp (1 / 2) =
      Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc (33 : ℝ), he] at H
  exact H

theorem actual_growing_information_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ)
    (hsmall : ∀ i < q + 1, growingQueryDuration δ i ≤ 1) :
    0 ≤ actualParisiGrowingEntropyFrozen W β δ q -
      actualParisiEntropyReference W β (growingQueryTime δ (q + 1)) ∧
      actualParisiGrowingEntropyFrozen W β δ q -
        actualParisiEntropyReference W β (growingQueryTime δ (q + 1)) ≤
          4 * β^2 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) := by
  have H := growing_information_error (actualParisiFullSusceptibilitySquareExpected W β)
    (actualParisiFullEntropyRateExpected W β) (β^2)
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) δ hδ q (sq_nonneg β)
    (actual_square_profile_antitone W β hβ) (actual_square_profile_drop W β hβ)
    (actual_square_profile_tail W β hβ)
    (fun t _ht => actualParisiFullEntropyRateExpected_bounds W β t)
    ((continuous_actualParisiFullEntropyRateExpected W β).intervalIntegrable _ _)
    (((continuous_actualParisiFullSusceptibilitySquareExpected W β).mul
      (continuous_actualParisiFullEntropyRateExpected W β)).intervalIntegrable _ _)
    (fun i hi => by exact_mod_cast hsmall i hi)
  rw [actual_information_reference_eq W β hβ _ (meshTime_nonneg δ (q + 1)),
    ← (actual_growing_information_eq W β hβ δ q).1] at H
  exact H

theorem actual_growing_information_auxiliary (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (q : ℕ) :
    actualParisiGrowingEntropyFrozen W β δ q - actualParisiGrowingEntropyQueries W β δ q =
      (1 / 2 : ℝ) * ∫ v in 0..(δ : ℝ), actualParisiFullEntropyRateExpected W β v := by
  rw [(actual_growing_information_eq W β hβ δ q).1, (actual_growing_information_eq W β hβ δ q).2,
    growing_information_auxiliary, actual_square_profile_zero W β hβ]
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  field_simp

theorem actual_growing_information_auxiliary_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (q : ℕ) :
    0 ≤ actualParisiGrowingEntropyFrozen W β δ q - actualParisiGrowingEntropyQueries W β δ q ∧
      actualParisiGrowingEntropyFrozen W β δ q - actualParisiGrowingEntropyQueries W β δ q ≤ (δ : ℝ) / 2 := by
  rw [actual_growing_information_auxiliary W β hβ δ q]
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg δ.coe_nonneg
      (fun v _hv => (actualParisiFullEntropyRateExpected_bounds W β v).1))
  · have H := intervalIntegral.integral_mono_on δ.coe_nonneg
      ((continuous_actualParisiFullEntropyRateExpected W β).intervalIntegrable 0 δ)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 δ)
      (fun v _hv => (actualParisiFullEntropyRateExpected_bounds W β v).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at H
    linarith

theorem actual_growing_information_queries_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ)
    (hsmall : ∀ i < q + 1, growingQueryDuration δ i ≤ 1) :
    |actualParisiGrowingEntropyQueries W β δ q -
      actualParisiEntropyReference W β (growingQueryTime δ (q + 1))| ≤
      (4 * β^2 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) + 1 / 2) * (δ : ℝ) := by
  have H := growing_information_queries_error (actualParisiFullSusceptibilitySquareExpected W β)
    (actualParisiFullEntropyRateExpected W β) (β^2)
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) δ hδ q (sq_nonneg β)
    (actualParisiFullSusceptibilitySquareExpected_bounds W β 0).1
    (actual_square_profile_antitone W β hβ) (actual_square_profile_drop W β hβ)
    (actual_square_profile_tail W β hβ)
    (fun t _ht => actualParisiFullEntropyRateExpected_bounds W β t)
    ((continuous_actualParisiFullEntropyRateExpected W β).intervalIntegrable _ _)
    (((continuous_actualParisiFullSusceptibilitySquareExpected W β).mul
      (continuous_actualParisiFullEntropyRateExpected W β)).intervalIntegrable _ _)
    (fun i hi => by exact_mod_cast hsmall i hi)
  rw [actual_information_reference_eq W β hβ _ (meshTime_nonneg δ (q + 1)),
    ← (actual_growing_information_eq W β hβ δ q).2, actual_square_profile_zero W β hβ] at H
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have hc : (β^2 / 2) * (1 / β^2) = (1 / 2 : ℝ) := by field_simp
  rw [hc] at H
  exact H

end SKConstants.Completion.LQ
