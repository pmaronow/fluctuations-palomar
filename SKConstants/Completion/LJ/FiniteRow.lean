module

public import SKConstants.Completion.LJ.TaylorRow
public import SKConstants.Completion.LC1.QuerySpinMoments
public import SKConstants.Completion.LC1.UpperBlock
public import SKConstants.Completion.LQ.ActualGrowingQuadrature
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualRowPotential (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (u : Bool × Ω) : ℝ :=
  rowPotential (scalarHiddenSign u.1) (actualParisiFullPosteriorMean W β S u.2)

theorem actualRowPotential_eq_error (W : BrownianSystem Ω) (β : ℝ)
    (S : ℝ≥0) (u : Bool × Ω) :
    actualRowPotential W β S u = (1 - actualParisiPinningError W β S u) / 2 := by
  cases hb : u.1 <;> simp only [actualRowPotential, rowPotential, actualParisiPinningError,
    scalarHiddenSign, hb, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem measurable_actualRowPotential (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) :
    Measurable (actualRowPotential W β S) := by
  have he : actualRowPotential W β S = fun u => (1 - actualParisiPinningError W β S u) / 2 :=
    funext (actualRowPotential_eq_error W β S)
  rw [he]
  exact (measurable_const.sub (measurable_actualParisiPinningError W β S)).div_const 2

theorem integrable_actualRowPotential (W : BrownianSystem Ω) (β : ℝ) (S H : ℝ≥0) :
    Integrable (actualRowPotential W β S) (actualParisiFullTerminalSpinLaw β W H) := by
  apply Integrable.of_bound (measurable_actualRowPotential W β S).aestronglyMeasurable 2
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs, actualRowPotential_eq_error]
  obtain ⟨he0, he4⟩ := actualParisiPinningError_mem_Icc W β S u
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem actualRowPotential_mean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S H : ℝ≥0) (hSH : S ≤ H) :
    (∫ u, actualRowPotential W β S u ∂actualParisiFullTerminalSpinLaw β W H) =
      actualParisiFullOverlap W β S / 2 := by
  have hi : Integrable (actualParisiPinningError W β S) (actualParisiFullTerminalSpinLaw β W H) :=
    Integrable.of_bound (measurable_actualParisiPinningError W β S).aestronglyMeasurable 4
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (actualParisiPinningError_mem_Icc W β S u).1]
        exact (actualParisiPinningError_mem_Icc W β S u).2))
  simp_rw [actualRowPotential_eq_error]
  rw [integral_div, integral_sub (integrable_const 1) hi,
    actualParisiPinningError_mean W β hβ S H hSH]
  simp only [integral_const, probReal_univ, one_smul]
  change (1 - (1 - actualParisiFullOverlap W β S)) / 2 = _
  ring

def gridPosteriorScale (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  actualParisiPosteriorIntervalScale W β (t j) (t (j + 1))

def gridQueryMean (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  LQ.actualParisiQueryIntervalSpinMean W β (t (j + 1)) (t (j + 2))

def gridEnergy (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (K : ℕ) : ℝ :=
  ∑ j : Fin K, gridPosteriorScale W β t j * gridQueryMean W β t j

def gridQuery (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (K : ℕ) (j : Fin K) (u : (Bool × Ω) × A) : ℝ :=
  scalarNormalizedBrownianRow (d := K) (actualParisiQueryBrownianSystem W Z β hβ).B
    (fun k => t (k + 1)) (u.1.2, u.2) j

theorem measurable_gridQuery (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (K : ℕ) (j : Fin K) :
    Measurable (gridQuery W Z β hβ t K j) := by
  exact (((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
    ((actualParisiQueryBrownianSystem W Z β hβ).measurable _)).div_const _ |>.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem integrable_gridQuery (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (K : ℕ) (j : Fin K) (H : ℝ≥0) :
    Integrable (gridQuery W Z β hβ t K j) (actualParisiFullQuerySpinLaw W Z β H) := by
  exact (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integrable_comp
    ((((actualParisiQueryBrownianSystem W Z β hβ).brownian.integrable_eval _).sub
      ((actualParisiQueryBrownianSystem W Z β hβ).brownian.integrable_eval _)).div_const _)

theorem integrable_gridQueryRow (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (K : ℕ) (j : Fin K) (H : ℝ≥0) :
    Integrable (fun u => (scalarHiddenSign u.1.1 -
      actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) * gridQuery W Z β hβ t K j u)
      (actualParisiFullQuerySpinLaw W Z β H) := by
  apply (integrable_gridQuery W Z β hβ t K j H).bdd_mul (c := 2)
  · exact (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_actualParisiFullPosteriorMean W β _).comp
        (measurable_snd.comp measurable_fst))).aestronglyMeasurable
  · exact ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs]
      have hs : |scalarHiddenSign u.1.1| = 1 := by cases hb : u.1.1 <;> norm_num [scalarHiddenSign, hb]
      exact (abs_sub _ _).trans (by
        rw [hs]
        linarith [abs_actualParisiFullPosteriorMean_le W β (t (j + 1)) u.1.2]))

theorem gridQueryRow_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (K : ℕ) (j : Fin K) (H : ℝ≥0) (hH : t (K + 1) ≤ H) :
    (∫ u, (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) *
      gridQuery W Z β hβ t K j u ∂actualParisiFullQuerySpinLaw W Z β H) =
      gridQueryMean W β t j := by
  let Q := actualParisiQueryBrownianSystem W Z β hβ
  let F := actualParisiFullPosteriorMean W β (t (j + 1))
  have hi := integrable_gridQuery W Z β hβ t K j H
  have hsi : Integrable (fun u => scalarHiddenSign u.1.1 * gridQuery W Z β hβ t K j u)
      (actualParisiFullQuerySpinLaw W Z β H) := by
    apply hi.bdd_mul (c := 1)
      ((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable
    exact ae_of_all _ (fun u => by cases hb : u.1.1 <;> norm_num [scalarHiddenSign, hb])
  have hmi : Integrable (fun u => F u.1.2 * gridQuery W Z β hβ t K j u)
      (actualParisiFullQuerySpinLaw W Z β H) := by
    apply hi.bdd_mul (c := 1)
      ((measurable_actualParisiFullPosteriorMean W β _).comp
        (measurable_snd.comp measurable_fst)).aestronglyMeasurable
    exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs]; exact abs_actualParisiFullPosteriorMean_le W β _ _)
  have hspin : (∫ u, scalarHiddenSign u.1.1 * gridQuery W Z β hβ t K j u
      ∂actualParisiFullQuerySpinLaw W Z β H) = gridQueryMean W β t j := by
    simp_rw [mul_comm (scalarHiddenSign _)]
    change (∫ u, scalarNormalizedBrownianRow (d := K) Q.B (fun k => t (k + 1))
      (u.1.2, u.2) j * scalarHiddenSign u.1.1 ∂actualParisiFullQuerySpinLaw W Z β H) = _
    rw [LC1.actualQuerySpinLaw_normalized_query_spin_moment W Z β hβ
      (fun k => t (k + 1)) K j H (ht (by omega)) ((ht (by omega)).trans hH)]
    unfold gridQueryMean LQ.actualParisiQueryIntervalSpinMean
    congr 1
    apply intervalIntegral.integral_congr
    intro r _
    ring
  have hpath : (∫ u, F u.1.2 * gridQuery W Z β hβ t K j u
      ∂actualParisiFullQuerySpinLaw W Z β H) = 0 := by
    have hm : Measurable (fun u : Ω × A => F u.1 *
        ((Q.B (t (j + 2)) u - Q.B (t (j + 1)) u) /
          Real.sqrt ((t (j + 2) : ℝ) - (t (j + 1) : ℝ)))) :=
      ((measurable_actualParisiFullPosteriorMean W β _).comp measurable_fst).mul
        (((Q.measurable _).sub (Q.measurable _)).div_const _)
    change (∫ u, F u.1.2 * ((Q.B (t (j + 2)) (u.1.2, u.2) -
      Q.B (t (j + 1)) (u.1.2, u.2)) / Real.sqrt ((t (j + 2) : ℝ) -
      (t (j + 1) : ℝ))) ∂actualParisiFullQuerySpinLaw W Z β H) = 0
    refine ((actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp
      hm.aestronglyMeasurable).trans ?_
    have hz := LC1.actualQuery_increment_integral_adapted W Z β hβ
      (t (j + 1)) (t (j + 2) - t (j + 1)) F
      (LC1.actualMagnetization_adapted_le W β _ _ le_rfl)
      (integrable_actualParisiMagnetizationObservable W β _)
    rw [add_tsub_cancel_of_le (ht (by omega))] at hz
    simp_rw [← mul_div_assoc]
    rw [integral_div]
    rw [hz, zero_div]
  simp_rw [sub_mul]
  rw [integral_sub hsi hmi, hspin, hpath, sub_zero]

def actualFiniteRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (K : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  (∑ j : Fin K, (gridQueryMean W β t j / gridPosteriorScale W β t j) *
    (actualRowPotential W β (t (j + 1)) u.1 - actualRowPotential W β (t j) u.1)) +
  (∑ j : Fin K, gridPosteriorScale W β t j *
    ((scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) *
      gridQuery W Z β hβ t K j u)) - gridEnergy W β t K / 2

theorem integrable_actualFiniteRow (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (K : ℕ) (H : ℝ≥0) :
    Integrable (actualFiniteRow W Z β hβ t K) (actualParisiFullQuerySpinLaw W Z β H) := by
  have hp (S : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A => actualRowPotential W β S u.1)
      (actualParisiFullQuerySpinLaw W Z β H) :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integrable_comp
      (integrable_actualRowPotential W β S H)
  exact ((integrable_finsetSum (Finset.univ : Finset (Fin K)) (fun j _ =>
    ((hp (t (j + 1))).sub (hp (t j))).const_mul (gridQueryMean W β t j / gridPosteriorScale W β t j))).add
    (integrable_finsetSum (Finset.univ : Finset (Fin K)) (fun j _ =>
      (integrable_gridQueryRow W Z β hβ t K j H).const_mul (gridPosteriorScale W β t j)))).sub
        (integrable_const _)

theorem actualFiniteRow_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (K : ℕ) (H : ℝ≥0) (hH : t (K + 1) ≤ H) :
    (∫ u, actualFiniteRow W Z β hβ t K u ∂actualParisiFullQuerySpinLaw W Z β H) =
      gridEnergy W β t K := by
  let ν := actualParisiFullQuerySpinLaw W Z β H
  have hp (S : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A => actualRowPotential W β S u.1) ν :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integrable_comp
      (integrable_actualRowPotential W β S H)
  have hpm (S : ℝ≥0) (hS : S ≤ H) :
      (∫ u : (Bool × Ω) × A, actualRowPotential W β S u.1 ∂ν) =
        actualParisiFullOverlap W β S / 2 :=
    ((actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integral_comp
      (measurable_actualRowPotential W β S).aestronglyMeasurable).trans
        (actualRowPotential_mean W β hβ S H hS)
  have hfirst (j : Fin K) :
      (∫ u : (Bool × Ω) × A, (gridQueryMean W β t j / gridPosteriorScale W β t j) *
        (actualRowPotential W β (t (j + 1)) u.1 - actualRowPotential W β (t j) u.1) ∂ν) =
        gridPosteriorScale W β t j * gridQueryMean W β t j / 2 := by
    rw [integral_const_mul, integral_sub (hp _) (hp _),
      hpm _ ((ht.monotone (by omega)).trans hH), hpm _ ((ht.monotone (by omega)).trans hH)]
    have hs := actualParisiPosteriorIntervalScale_sq W β hβ (t j) (t (j + 1)) (ht (by omega))
    have hsne : gridPosteriorScale W β t j ≠ 0 :=
      (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _ (ht (by omega)))).ne'
    change (gridQueryMean W β t j / gridPosteriorScale W β t j) *
      (actualParisiFullOverlap W β (t (j + 1)) / 2 - actualParisiFullOverlap W β (t j) / 2) = _
    have hh : actualParisiFullOverlap W β (t (j + 1)) / 2 - actualParisiFullOverlap W β (t j) / 2 =
        (gridPosteriorScale W β t j) ^ 2 / 2 := by
      dsimp only [gridPosteriorScale]
      linarith [hs]
    rw [hh]
    field_simp [hsne]

  have h1 (j : Fin K) : Integrable (fun u : (Bool × Ω) × A =>
      (gridQueryMean W β t j / gridPosteriorScale W β t j) *
        (actualRowPotential W β (t (j + 1)) u.1 - actualRowPotential W β (t j) u.1)) ν :=
    ((hp _).sub (hp _)).const_mul _
  have h2 (j : Fin K) : Integrable (fun u => gridPosteriorScale W β t j *
      ((scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) *
        gridQuery W Z β hβ t K j u)) ν :=
    (integrable_gridQueryRow W Z β hβ t K j H).const_mul _
  have hsecond (j : Fin K) : (∫ u,
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) *
        gridQuery W Z β hβ t K j u ∂ν) = gridQueryMean W β t j :=
    gridQueryRow_mean W Z β hβ t ht.monotone K j H hH
  have hi1 := integrable_finsetSum (Finset.univ : Finset (Fin K)) (fun j _ => h1 j)
  have hi2 := integrable_finsetSum (Finset.univ : Finset (Fin K)) (fun j _ => h2 j)
  have hadd := integral_add hi1 hi2
  have hsub := integral_sub (hi1.add hi2) (integrable_const (gridEnergy W β t K / 2) :
    Integrable (fun _ : (Bool × Ω) × A => gridEnergy W β t K / 2) ν)
  simp only [Pi.add_apply] at hadd hsub
  unfold actualFiniteRow
  change (∫ u, (∑ j : Fin K, _) + (∑ j : Fin K, _) - _ ∂ν) = _
  rw [hsub, hadd,
    integral_finsetSum (Finset.univ : Finset (Fin K)) (fun j _ => h1 j),
    integral_finsetSum (Finset.univ : Finset (Fin K)) (fun j _ => h2 j)]
  simp only [hfirst, integral_const_mul, hsecond]
  change (∑ j : Fin K, gridPosteriorScale W β t j * gridQueryMean W β t j / 2) +
    (∑ j : Fin K, gridPosteriorScale W β t j * gridQueryMean W β t j) - _ = _
  rw [← Finset.sum_div]
  change gridEnergy W β t K / 2 + gridEnergy W β t K -
    (∫ _ : (Bool × Ω) × A, gridEnergy W β t K / 2 ∂ν) = gridEnergy W β t K
  simp only [integral_const, probReal_univ, one_smul]
  ring

theorem gridEnergy_growing_eq (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    gridEnergy W β (growingQueryTime δ) K = LQ.actualParisiGrowingEnergySum W β δ K := by
  unfold gridEnergy gridPosteriorScale gridQueryMean LQ.actualParisiGrowingEnergySum
  exact Fin.sum_univ_eq_sum_range (fun j =>
    (actualParisiPosteriorIntervalScale W β (growingQueryTime δ j) (growingQueryTime δ (j + 1)) : ℝ) *
      LQ.actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (j + 1))
        (growingQueryTime δ (j + 2))) K

theorem actualGrowingFiniteRow_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) :
    (∫ u, actualFiniteRow W Z β hβ (growingQueryTime δ) K u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) =
      LQ.actualParisiGrowingEnergySum W β δ K := by
  rw [actualFiniteRow_mean W Z β hβ _ (growingQueryTime_strictMono δ hδ) K _ le_rfl,
    gridEnergy_growing_eq]

theorem actualFiniteRow_reference_mean_balance (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (K : ℕ) (H : ℝ≥0) (hH : t (K + 1) ≤ H)
    (hV : parisiEquilibriumPhysicalEndpoint β ≤ H) :
    actualParisiEntropyReference W β H -
      β * (∫ u, actualFiniteRow W Z β hβ t K u ∂actualParisiFullQuerySpinLaw W Z β H) =
      Real.log 2 - parisiContinuumFunctional β
        (ProbabilityTheory.cdf (parisiEquilibriumMeasure β : Measure ℝ)) +
      β ^ 2 * (actualParisiFullSusceptibilityExpected W β H) ^ 2 / 4 +
      β * (actualParisiEnergyReference W β H - gridEnergy W β t K) := by
  rw [actualFiniteRow_mean W Z β hβ t ht K H hH]
  have hh := actualParisi_scalar_entropy_energy_identity W β hβ H (by exact_mod_cast hV)
  linarith

theorem actualGrowingFiniteRow_mean_error (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ i < K + 1, growingQueryDuration δ i ≤ 1) :
    |(∫ u, actualFiniteRow W Z β hβ (growingQueryTime δ) K u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) -
        actualParisiEnergyReference W β (growingQueryTime δ (K + 1))| ≤
      (1 / β ^ 2 + 33 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)) *
        (δ : ℝ) := by
  rw [actualGrowingFiniteRow_mean W Z β hβ δ hδ K]
  exact LQ.actual_growing_energy_error W β hβ δ hδ K hsmall

end SKConstants.Completion.LJ
