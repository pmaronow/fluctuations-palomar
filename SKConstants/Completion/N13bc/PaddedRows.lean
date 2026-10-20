module

public import SKConstants.Completion.N13bc.Padding
public import SKConstants.Completion.LW.ExplicitSevenConcentration

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace
namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK LW Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def paddedDuration {k m : ℕ} (t : ℕ → ℝ≥0) (h : k ≤ m) : Fin m → ℝ :=
  liftVector h (WithLp.toLp 2 (fun j : Fin k => previousDuration t j))

theorem paddedDuration_nonneg {k m : ℕ} (t : ℕ → ℝ≥0) (ht : Monotone t)
    (h : k ≤ m) (j : Fin m) : 0 ≤ paddedDuration t h j := by
  dsimp [paddedDuration, liftVector]
  split_ifs
  · exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ _)))
  · exact le_refl 0

theorem paddedDuration_sum {k m : ℕ} (t : ℕ → ℝ≥0) (h : k ≤ m)
    (J : Finset (Fin m)) :
    (∑ j ∈ J, paddedDuration t h j) = ∑ j ∈ restrictSet h J, previousDuration t j :=
  sum_liftVector h _ J

theorem paddedPosterior_secondMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) {k m : ℕ} (h : k ≤ m)
    (a : EuclideanSpace ℝ (Fin m)) :
    (∫ u, ⟪liftVector h (posteriorRow W β t k u),a⟫_ℝ^2
      ∂linkedScalarLaw W Z β V) ≤ ‖a‖^2 := by
  simp_rw [liftVector_inner]
  rw [posteriorRow_secondMoment W Z β hβ t ht k V]
  exact pow_le_pow_left₀ (norm_nonneg _) (restrictVector_norm_le h a) 2

theorem paddedQuery_secondMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) {k m : ℕ} (h : k ≤ m)
    (a : EuclideanSpace ℝ (Fin m)) :
    (∫ u, ⟪liftVector h (queryRow W Z β hβ t k u),a⟫_ℝ^2
      ∂linkedScalarLaw W Z β V) ≤ ‖a‖^2 := by
  simp_rw [liftVector_inner]
  rw [queryRow_secondMoment W Z β hβ t ht k V]
  exact pow_le_pow_left₀ (norm_nonneg _) (restrictVector_norm_le h a) 2

theorem paddedPosterior_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) {k m : ℕ} (h : k ≤ m)
    (hV : t k ≤ V) {R : ℝ} (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (a : EuclideanSpace ℝ (Fin m)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪liftVector h (posteriorRow W β t k u),a⟫_ℝ)
      (Real.toNNReal R) (linkedScalarLaw W Z β V) := by
  simp_rw [liftVector_inner]
  apply hasSubgaussianMGF_of_proxy_le
    (posteriorRow_unit_hasSubgaussianMGF W Z β hβ t ht k V hV
      (restrictVector h a) ((restrictVector_norm_le h a).trans ha))
  exact NNReal.coe_le_coe.mp (by
    simpa only [Real.coe_toNNReal _ (by linarith : 0 ≤ R)] using hProxy)

theorem paddedQuery_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) {k m : ℕ} (h : k ≤ m)
    (a : EuclideanSpace ℝ (Fin m)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪liftVector h (queryRow W Z β hβ t k u),a⟫_ℝ)
      1 (linkedScalarLaw W Z β V) := by
  simp_rw [liftVector_inner]
  exact queryRow_unit_hasSubgaussianMGF W Z β hβ t ht k V
    (restrictVector h a) ((restrictVector_norm_le h a).trans ha)

theorem paddedPosterior_weighted_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) {k m : ℕ} (h : k ≤ m)
    (w : EuclideanSpace ℝ (Fin k)) {B : ℝ}
    (hw : ∀ j, |w j / posteriorWeight W β t k j| ≤ B) (J : Finset (Fin m)) :
    HasSubgaussianMGF (fun u => ⟪liftVector h (posteriorRow W β t k u),
      coordinateProjection J (liftVector h w)⟫_ℝ)
      (Real.toNNReal (B^2 * ∑ j ∈ J, paddedDuration t h j))
      (linkedScalarLaw W Z β V) := by
  simp_rw [liftVector_inner, restrictVector_projection, restrictVector_liftVector,
    paddedDuration_sum]
  exact posteriorRow_weighted_block_hasSubgaussianMGF W Z β hβ t ht k V w hw _

theorem posteriorWeight_set_norm_sq_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (J : Finset (Fin k)) :
    ‖coordinateProjection J (posteriorWeight W β t k)‖^2 ≤
      ∑ j ∈ J, previousDuration t j := by
  rw [coordinateProjection_norm_sq]
  apply Finset.sum_le_sum
  intro j _
  rw [posteriorWeight_eq_integral W β hβ t ht, LQ.posteriorScale]
  have hn : 0 ≤ ∫ v in (t j : ℝ)..(t (j+1) : ℝ),
      actualParisiFullSusceptibilitySquareExpected W β v :=
    intervalIntegral.integral_nonneg (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _)))
      (fun v _ => (actualParisiFullSusceptibilitySquareExpected_bounds W β v).1)
  rw [Real.sq_sqrt hn]
  have H := intervalIntegral.integral_mono_on
    (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _)))
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (t j : ℝ) (t (j+1)))
    (fun v _ => (actualParisiFullSusceptibilitySquareExpected_bounds W β v).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one, previousDuration] using H

theorem paddedWeight_norm_sq_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) {k m : ℕ} (h : k ≤ m) (J : Finset (Fin m)) :
    ‖coordinateProjection J (liftVector h (posteriorWeight W β t k))‖^2 ≤
      ∑ j ∈ J, paddedDuration t h j := by
  rw [liftVector_projection, liftVector_norm, paddedDuration_sum]
  exact posteriorWeight_set_norm_sq_le W β hβ t ht k _

theorem liftMatrix_centeredCross {Ξ : Type*} [MeasurableSpace Ξ] {k m : ℕ}
    (h : k ≤ m) (X Y : Ξ → EuclideanSpace ℝ (Fin k)) (μ : Measure Ξ) (u : Ξ) :
    liftMatrix h (centeredCrossMatrix X Y μ u) =
      centeredCrossMatrix (fun z => liftVector h (X z)) (fun z => liftVector h (Y z)) μ u := by
  ext i j
  simp only [liftMatrix, centeredCrossMatrix, liftVector, WithLp.ofLp_toLp]
  split_ifs <;> simp

end SKConstants.Completion.N13bc
