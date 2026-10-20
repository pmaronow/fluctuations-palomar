module

public import SKConstants.Completion.LGram.RowBlocks
public import SKConstants.Completion.LC1.UpperBlock
public import SKConstants.Completion.LC1.QuerySpinMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK LC1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance population_primary_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance population_aux_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

def mixedPopulation (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) : Matrix (Fin (k+(k+1))) (Fin (k+(k+1))) ℝ :=
  populationGram (actualParisiFullQuerySpinLaw W Z β H)
    (actualParisiFullMixedRow W Z β hβ t g k)

def populationTargetSpin (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => mixedPopulation W Z β hβ t g k H (posteriorIndex k i) (spinIndex k))

def populationQuerySpin (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => mixedPopulation W Z β hβ t g k H (queryIndex k i) (spinIndex k))

def populationCross (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) : Matrix (Fin k) (Fin k) ℝ :=
  (mixedPopulation W Z β hβ t g k H).submatrix (posteriorIndex k) (queryIndex k)

@[simp] theorem mixedRow_posterior (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t g : ℕ → ℝ≥0) (k : ℕ)
    (u : (Bool × Ω) × A) (i : Fin k) :
    actualParisiFullMixedRow W Z β hβ t g k u (posteriorIndex k i) =
      actualParisiNormalizedPosteriorRow W β t k u.1.2 i := by
  simp [actualParisiFullMixedRow, posteriorIndex]

@[simp] theorem mixedRow_query (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t g : ℕ → ℝ≥0) (k : ℕ)
    (u : (Bool × Ω) × A) (i : Fin k) :
    actualParisiFullMixedRow W Z β hβ t g k u (queryIndex k i) =
      scalarNormalizedBrownianRow (d:=k) (actualParisiQueryBrownianSystem W Z β hβ).B g
        (u.1.2,u.2) i := by
  simp [actualParisiFullMixedRow, queryIndex]

@[simp] theorem mixedRow_spin (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t g : ℕ → ℝ≥0) (k : ℕ) (u : (Bool × Ω) × A) :
    actualParisiFullMixedRow W Z β hβ t g k u (spinIndex k) = scalarHiddenSign u.1.1 := by
  simp [actualParisiFullMixedRow, spinIndex]

theorem normalizedPosterior_coordinate_product (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (k : ℕ) (i j : Fin k) :
    (∫ w, actualParisiNormalizedPosteriorRow W β t k w i *
      actualParisiNormalizedPosteriorRow W β t k w j ∂W.law) = if i=j then 1 else 0 := by
  let s := fun i : Fin k => (actualParisiPosteriorIntervalScale W β (t i) (t (i+1)):ℝ)
  have he (w : Ω) : actualParisiNormalizedPosteriorRow W β t k w i *
      actualParisiNormalizedPosteriorRow W β t k w j =
      (actualParisiMagnetizationIncrement W β (t i) (t (i+1)) w *
        actualParisiMagnetizationIncrement W β (t j) (t (j+1)) w) / (s i*s j) := by
    dsimp [actualParisiNormalizedPosteriorRow, s]
    ring
  simp_rw [he]
  rw [integral_div]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    simp_rw [← pow_two]
    rw [actualParisiIncrement_secondMoment W β hβ _ _ (ht.monotone (Nat.le_succ _))]
    change (actualParisiFullOverlap W β (t (i+1))-actualParisiFullOverlap W β (t i)) /
      (s i)^2 = 1
    rw [← actualParisiPosteriorIntervalScale_sq W β hβ _ _ (ht (Nat.lt_succ_self _))]
    have hs : s i ≠ 0 := (NNReal.coe_pos.mpr
      (actualParisiPosteriorIntervalScale_pos W β hβ _ _ (ht (Nat.lt_succ_self _)))).ne'
    change (s i)^2 / (s i)^2 = 1
    field_simp
  · rw [ite_eq_right hij]
    have hz : (∫ w, actualParisiMagnetizationIncrement W β (t i) (t (i+1)) w *
        actualParisiMagnetizationIncrement W β (t j) (t (j+1)) w ∂W.law) = 0 := by
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact actualParisiIncrement_disjoint_crossMoment W β hβ _ _ _ _
          (ht.monotone (Nat.le_succ _)) (ht.monotone (by omega)) (ht.monotone (Nat.le_succ _))
      · simpa only [mul_comm] using actualParisiIncrement_disjoint_crossMoment W β hβ
          (t j) (t (j+1)) (t i) (t (i+1)) (ht.monotone (Nat.le_succ _))
          (ht.monotone (by omega)) (ht.monotone (Nat.le_succ _))
    rw [hz, zero_div]

theorem mixedPopulation_target_block (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) :
    (mixedPopulation W Z β hβ t g k H).submatrix (posteriorIndex k) (posteriorIndex k) = 1 := by
  ext i j
  simp only [mixedPopulation, populationGram, Matrix.submatrix_apply, mixedRow_posterior,
    Matrix.one_apply]
  have hm : Measurable (fun w => actualParisiNormalizedPosteriorRow W β t k w i *
      actualParisiNormalizedPosteriorRow W β t k w j) := by
    exact ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp
      (measurable_actualParisiNormalizedPosteriorRow W β t k))).mul
      ((measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp
        (measurable_actualParisiNormalizedPosteriorRow W β t k)))
  exact ((actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).integral_comp
    hm.aestronglyMeasurable).trans (normalizedPosterior_coordinate_product W β hβ t ht k i j)

theorem populationCross_shifted_upper (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) (H : ℝ≥0) :
    ∀ i j : Fin k, i ≤ j → populationCross W Z β hβ t (fun l => t (l+1)) k H i j = 0 := by
  intro i j hij
  simpa only [populationCross, mixedPopulation, populationGram, Matrix.submatrix_apply,
    mixedRow_posterior, mixedRow_query] using
    actualQuerySpinLaw_shifted_upper_block W Z β hβ t ht k H i j hij

theorem populationTargetSpin_eq_scale (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) (hH : t k ≤ H) (i : Fin k) :
    populationTargetSpin W Z β hβ t g k H i =
      (actualParisiPosteriorIntervalScale W β (t i) (t (i+1)):ℝ) := by
  simp only [populationTargetSpin, mixedPopulation, populationGram, mixedRow_posterior, mixedRow_spin]
  have hm : Measurable (fun u : Bool × Ω => actualParisiNormalizedPosteriorRow W β t k u.2 i *
      scalarHiddenSign u.1) := by
    exact (((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp
      (measurable_actualParisiNormalizedPosteriorRow W β t k))).comp measurable_snd).mul
      ((measurable_of_finite scalarHiddenSign).comp measurable_fst)
  exact ((actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integral_comp
    hm.aestronglyMeasurable).trans
    (actualParisiFullTerminalSpinLaw_normalized_increment_spin_moment W β hβ _ _ _
      (ht (Nat.lt_succ_self _)) ((ht.monotone (by omega)).trans hH))

theorem populationQuerySpin_eq_integral (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (g : ℕ → ℝ≥0)
    (hg : Monotone g) (k : ℕ) (H : ℝ≥0) (hH : g k ≤ H) (i : Fin k) :
    populationQuerySpin W Z β hβ t g k H i =
      (∫ r in (g i:ℝ)..(g (i+1):ℝ), actualParisiQueryRho W β r *
        actualParisiFullSusceptibilityExpected W β r) /
        Real.sqrt ((g (i+1):ℝ)-(g i:ℝ)) := by
  simpa only [populationQuerySpin, mixedPopulation, populationGram, mixedRow_query, mixedRow_spin] using
    actualQuerySpinLaw_normalized_query_spin_moment W Z β hβ g k i H
      (hg (Nat.le_succ _)) ((hg (by omega)).trans hH)

end SKConstants.Completion.LGram
