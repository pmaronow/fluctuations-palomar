module

public import SKConstants.Completion.Blueprint5a.Statements
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S73
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Blueprint4 SKConstants.Blueprint5a

variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]

theorem quadraticIntegral_abs_le (c a : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hc : IntervalIntegrable (fun v => |c v|) volume s t)
    (ha : ∀ v, |a v| ≤ 1) :
    |∫ v in s..t, c v * a v ^ 2| ≤ ∫ v in s..t, |c v| := by
  apply (show ‖∫ v in s..t, c v * a v ^ 2‖ ≤ _ from
    intervalIntegral.norm_integral_le_of_norm_le hst (ae_of_all _ (fun v _ => ?_)) hc)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have hsq : |a v| ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (a v), ha v]
  simpa using mul_le_mul_of_nonneg_left hsq (abs_nonneg (c v))

theorem measurable_quadraticLimit (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (K : ℕ) : Measurable (quadraticLimit (A := A) W β δ K) := by
  have ha : Measurable (fun p : ((Bool × Ω) × A) × ℝ =>
      LJ.actualCurvature W β p.2.toNNReal p.1.1.2) := by
    have hf : Measurable (fun p : ((Bool × Ω) × A) × ℝ => (p.2, p.1.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst))
    simpa only [Function.comp_def, LJ.actualCurvature] using
      (LC1.measurable_actualFullCurvature_process_real W β).comp hf
  have hp : Measurable (fun p : ((Bool × Ω) × A) × ℝ =>
      actualParisiFullSusceptibilityExpected W β p.2) :=
    (continuous_actualParisiFullSusceptibilityExpected W β).measurable.comp measurable_snd
  have hj (j : ℕ) : Measurable (fun u : (Bool × Ω) × A =>
      ∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ),
        (β * actualParisiFullSusceptibilityExpected W β v - LJ.residualCoarseA W β (mesh δ) K j) *
          LJ.actualCurvature W β v.toNNReal u.1.2 ^ 2) := by
    have hm := (((hp.const_mul β).sub
      (measurable_const (a := LJ.residualCoarseA W β (mesh δ) K j))).mul
        (ha.pow_const 2)).stronglyMeasurable
    have hs := (hm.integral_prod_right'
      (ν := volume.restrict (Ioc (mesh δ j : ℝ) (mesh δ (j + 1) : ℝ)))).measurable
    have ht := (hm.integral_prod_right'
      (ν := volume.restrict (Ioc (mesh δ (j + 1) : ℝ) (mesh δ j : ℝ)))).measurable
    exact hs.sub ht
  exact (Finset.measurable_fun_sum _ (fun j _ => hj j)).const_mul _

omit [MeasurableSpace A] in
theorem quadraticLimit_abs_le_budget (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (hδ : 0 < δ) (K : ℕ) (u : (Bool × Ω) × A) :
    |quadraticLimit W β δ K u| ≤ (1 / 2 : ℝ) *
      ∑ j ∈ Finset.range (K + 1), ∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ),
        |β * actualParisiFullSusceptibilityExpected W β v - LJ.residualCoarseA W β (mesh δ) K j| := by
  unfold quadraticLimit
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact quadraticIntegral_abs_le _ _ _ _
    (NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j)))
    ((((continuous_actualParisiFullSusceptibilityExpected W β).const_mul β).sub
      continuous_const).abs.intervalIntegrable _ _)
    (fun v => LJ.actualCurvature_abs_le W β v.toNNReal u.1.2)

theorem quadraticLimit_measurable_bounded (h2 : CoarseCoefficientBudgetStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      Measurable (quadraticLimit (A := A) W β δ K) ∧
      ∀ u, |quadraticLimit (A := A) W β δ K u| ≤ C * δ := by
  obtain ⟨C, hC, hbudget⟩ := h2 W β hβ
  refine ⟨C / 2, half_pos hC, fun δ K hmesh => ⟨measurable_quadraticLimit W β δ K, ?_⟩⟩
  intro u
  exact (quadraticLimit_abs_le_budget W β δ hmesh.1 K u).trans
    (by nlinarith [(hbudget δ K hmesh).2])

theorem measurable_quadraticGroup (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (K l : ℕ) : Measurable (quadraticGroup (A := A) W β δ K l) := by
  unfold quadraticGroup LJ.refinedResidualQuadratic
  apply Finset.measurable_fun_sum
  intro j _
  apply Finset.measurable_fun_sum
  intro i _
  exact (((((measurable_actualParisiFullPosteriorMean W β _).sub
    (measurable_actualParisiFullPosteriorMean W β _)).comp
      (measurable_snd.comp measurable_fst)).pow_const 2).const_mul _).div_const 2

theorem quadraticGroup_memLp (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K l : ℕ)
    (μ : Measure ((Bool × Ω) × A)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (quadraticGroup W β δ K l) p μ := by
  unfold quadraticGroup LJ.refinedResidualQuadratic
  apply memLp_finsetSum
  intro j _
  apply memLp_finsetSum
  intro i _
  have hm : Measurable (fun u : (Bool × Ω) × A =>
      (actualParisiFullPosteriorMean W β (refinedGrid δ l j (i + 1)) u.1.2 -
        actualParisiFullPosteriorMean W β (refinedGrid δ l j i) u.1.2) ^ 2) :=
    (((measurable_actualParisiFullPosteriorMean W β _).sub
      (measurable_actualParisiFullPosteriorMean W β _)).comp
        (measurable_snd.comp measurable_fst)).pow_const 2
  have hb : MemLp (fun u : (Bool × Ω) × A =>
      (actualParisiFullPosteriorMean W β (refinedGrid δ l j (i + 1)) u.1.2 -
        actualParisiFullPosteriorMean W β (refinedGrid δ l j i) u.1.2) ^ 2) p μ := by
    apply (memLp_const (4 : ℝ)).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h : |actualParisiFullPosteriorMean W β (refinedGrid δ l j (i + 1)) u.1.2 -
      actualParisiFullPosteriorMean W β (refinedGrid δ l j i) u.1.2| ≤ 1 + 1 :=
      (abs_sub _ _).trans (add_le_add
      (abs_actualParisiFullPosteriorMean_le W β _ u.1.2)
      (abs_actualParisiFullPosteriorMean_le W β _ u.1.2))
    nlinarith [sq_abs (actualParisiFullPosteriorMean W β (refinedGrid δ l j (i + 1)) u.1.2 -
      actualParisiFullPosteriorMean W β (refinedGrid δ l j i) u.1.2),
      abs_nonneg (actualParisiFullPosteriorMean W β (refinedGrid δ l j (i + 1)) u.1.2 -
        actualParisiFullPosteriorMean W β (refinedGrid δ l j i) u.1.2)]
  simpa only [div_eq_mul_inv] using
    ((hb.const_mul (-(β * actualParisiFullSusceptibilityExpected W β (refinedGrid δ l j i) -
      LJ.residualCoarseA W β (mesh δ) K j))).mul_const (2 : ℝ)⁻¹)

theorem refinedGrid_left_integral_tendsto (f : ℝ → ℝ) (hf : Continuous f)
    (δ : ℝ≥0) (j : ℕ) :
    Tendsto (fun l => ∑ i ∈ Finset.range (2 ^ l), f (refinedGrid δ l j i) *
      ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)) atTop
      (𝓝 (∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ), f v)) := by
  have h := SJ7.frozen_integral_dyadic_tendsto
    (fun v => f ((growingQueryTime δ j : ℝ) + v)) (fun _ => (1 : ℝ))
    (hf.comp (continuous_const.add continuous_id)) continuous_const
    (growingQueryDuration δ j) (fun _ _ => by norm_num)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_comp_add_left, add_zero] at h
  simpa only [refinedGrid, LJ3.growingLagDyadicTime, scalarBrownianDyadicTime,
    brownianDyadicGrid, growingQueryTime_succ, NNReal.coe_add, add_sub_add_left_eq_sub] using h

def quadraticBracket (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K l : ℕ)
    (u : (Bool × Ω) × A) : ℝ :=
  -(1 / 2) * ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (2 ^ l),
    (β * actualParisiFullSusceptibilityExpected W β (refinedGrid δ l j i) -
      LJ.residualCoarseA W β (mesh δ) K j) *
        LJ.actualCurvature W β (refinedGrid δ l j i) u.1.2 ^ 2 *
          ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)

theorem measurable_quadraticBracket (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (K l : ℕ) : Measurable (quadraticBracket (A := A) W β δ K l) := by
  unfold quadraticBracket
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro j _
  apply Finset.measurable_fun_sum
  intro i _
  exact ((((LJ.measurable_actualCurvature W β _).comp
    (measurable_snd.comp measurable_fst)).pow_const 2).const_mul _).mul_const _

omit [MeasurableSpace A] in
theorem quadraticBracket_tendsto_of_continuous (W : BrownianSystem Ω) (β : ℝ)
    (δ : ℝ≥0) (K : ℕ) (u : (Bool × Ω) × A)
    (hu : Continuous (fun t => LJ.actualCurvature W β t u.1.2)) :
    Tendsto (fun l => quadraticBracket W β δ K l u) atTop
      (𝓝 (quadraticLimit W β δ K u)) := by
  have hj (j : ℕ) : Tendsto (fun l => ∑ i ∈ Finset.range (2 ^ l),
      (β * actualParisiFullSusceptibilityExpected W β (refinedGrid δ l j i) -
        LJ.residualCoarseA W β (mesh δ) K j) *
          LJ.actualCurvature W β (refinedGrid δ l j i) u.1.2 ^ 2 *
            ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)) atTop
        (𝓝 (∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ),
          (β * actualParisiFullSusceptibilityExpected W β v - LJ.residualCoarseA W β (mesh δ) K j) *
            LJ.actualCurvature W β v.toNNReal u.1.2 ^ 2)) := by
    simpa only [Real.toNNReal_coe] using
      refinedGrid_left_integral_tendsto
        (fun v => (β * actualParisiFullSusceptibilityExpected W β v -
          LJ.residualCoarseA W β (mesh δ) K j) * LJ.actualCurvature W β v.toNNReal u.1.2 ^ 2)
        ((((continuous_actualParisiFullSusceptibilityExpected W β).const_mul β).sub
          continuous_const).mul ((hu.comp continuous_real_toNNReal).pow 2)) δ j
  exact (tendsto_finsetSum _ (fun j _ => hj j)).const_mul _

theorem quadraticBracket_tendsto_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    ∀ᵐ u ∂meshLaw W Z β δ K, Tendsto (fun l => quadraticBracket W β δ K l u) atTop
      (𝓝 (quadraticLimit W β δ K u)) := by
  have hp : MeasurePreserving (fun u : (Bool × Ω) × A => u.1.2)
      (meshLaw W Z β δ K) W.law :=
    (actualParisiFullQuerySpinLaw_path_hasLaw W Z β (growingQueryTime δ (K + 1))).measurePreserving
      (measurable_snd.comp measurable_fst)
  filter_upwards [hp.quasiMeasurePreserving.ae (LJ.actualCurvature_continuous_ae W β)] with u hu
  exact quadraticBracket_tendsto_of_continuous W β δ K u hu

theorem quadraticCoefficient_abs_le (W : BrownianSystem Ω) (β b v : ℝ) :
    |β * actualParisiFullSusceptibilityExpected W β v - b| ≤ |β| + |b| := by
  apply (abs_sub _ _).trans
  apply add_le_add _ le_rfl
  rw [abs_mul, abs_of_nonneg (actualParisiFullSusceptibilityExpected_nonneg W β v)]
  exact mul_le_of_le_one_right (abs_nonneg β) (LBase.actual_susceptibility_le_one W β v)

def quadraticCap (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ) : ℝ :=
  (1 / 2) * ∑ j ∈ Finset.range (K + 1),
    (|β| + |LJ.residualCoarseA W β (mesh δ) K j|) * (growingQueryDuration δ j : ℝ)

theorem quadraticCap_nonneg (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    0 ≤ quadraticCap W β δ K := by
  unfold quadraticCap
  positivity

theorem quadraticCurvatureCoefficient_abs_le (W : BrownianSystem Ω) (β b v : ℝ) (w : Ω) :
    |(β * actualParisiFullSusceptibilityExpected W β v - b) *
      LJ.actualCurvature W β v.toNNReal w ^ 2| ≤ |β| + |b| := by
  rw [abs_mul, abs_pow]
  have ha : |LJ.actualCurvature W β v.toNNReal w| ^ 2 ≤ 1 := by
    nlinarith [LJ.actualCurvature_abs_le W β v.toNNReal w,
      abs_nonneg (LJ.actualCurvature W β v.toNNReal w)]
  exact (mul_le_of_le_one_right (abs_nonneg _) ha).trans
    (quadraticCoefficient_abs_le W β b v)

omit [MeasurableSpace A] in
theorem quadraticBracket_abs_le (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K l : ℕ)
    (u : (Bool × Ω) × A) : |quadraticBracket W β δ K l u| ≤ quadraticCap W β δ K := by
  unfold quadraticBracket quadraticCap
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ l),
        |(β * actualParisiFullSusceptibilityExpected W β (refinedGrid δ l j i) -
          LJ.residualCoarseA W β (mesh δ) K j) *
            LJ.actualCurvature W β (refinedGrid δ l j i) u.1.2 ^ 2 *
              ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ l),
        (|β| + |LJ.residualCoarseA W β (mesh δ) K j|) *
          ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (refinedGrid δ l j i : ℝ) ≤ refinedGrid δ l j (i + 1) :=
        NNReal.coe_le_coe.mpr (LJ3.growingLagDyadicTime_monotone δ l j (Nat.le_succ i))
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hi)]
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hi)
      simpa only [Real.toNNReal_coe] using quadraticCurvatureCoefficient_abs_le W β
        (LJ.residualCoarseA W β (mesh δ) K j) (refinedGrid δ l j i) u.1.2
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => (refinedGrid δ l j i : ℝ))]
      simp only [refinedGrid, LJ3.growingLagDyadicTime_end, LJ3.growingLagDyadicTime_zero,
        growingQueryTime_sub]

omit [MeasurableSpace A] in
theorem quadraticLimit_abs_le_cap (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ)
    (u : (Bool × Ω) × A) : |quadraticLimit W β δ K u| ≤ quadraticCap W β δ K := by
  unfold quadraticLimit quadraticCap
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (mesh δ j : ℝ)) (b := (mesh δ (j + 1) : ℝ))
    (f := fun v => (β * actualParisiFullSusceptibilityExpected W β v -
      LJ.residualCoarseA W β (mesh δ) K j) * LJ.actualCurvature W β v.toNNReal u.1.2 ^ 2)
    (C := |β| + |LJ.residualCoarseA W β (mesh δ) K j|)
    (fun v _ => by
      simpa only [Real.norm_eq_abs] using quadraticCurvatureCoefficient_abs_le W β
        (LJ.residualCoarseA W β (mesh δ) K j) v u.1.2)
  simpa only [Real.norm_eq_abs, growingQueryTime_sub,
    abs_of_nonneg (growingQueryDuration δ j).coe_nonneg] using hh

theorem quadraticLimit_memLp (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ)
    (μ : Measure ((Bool × Ω) × A)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (quadraticLimit W β δ K) p μ :=
  (memLp_const (quadraticCap W β δ K)).mono'
    (measurable_quadraticLimit W β δ K).aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using quadraticLimit_abs_le_cap W β δ K u))

theorem quadraticGroupLimit_integrable_sq_unconditional (W : BrownianSystem Ω) (β : ℝ)
    (δ : ℝ≥0) (K l : ℕ) (μ : Measure ((Bool × Ω) × A)) [IsFiniteMeasure μ] :
    Integrable (fun u => (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2) μ :=
  ((quadraticGroup_memLp W β δ K l μ 2).sub (quadraticLimit_memLp W β δ K μ 2)).integrable_sq

theorem quadraticBracket_tendsto_L2 (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    Tendsto (fun l => ∫ u, (quadraticBracket W β δ K l u - quadraticLimit W β δ K u) ^ 2
      ∂meshLaw W Z β δ K) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := meshLaw W Z β δ K)
    (f := fun _ => (0 : ℝ))
    (F := fun l u => (quadraticBracket W β δ K l u - quadraticLimit W β δ K u) ^ 2)
    (bound := fun _ => (2 * quadraticCap W β δ K) ^ 2)
    (fun l => (((measurable_quadraticBracket W β δ K l).sub
      (measurable_quadraticLimit W β δ K)).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun l => ae_of_all _ (fun u => ?_)) ?_
  · simpa only [integral_zero] using hh
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha := (abs_sub _ _).trans (add_le_add (quadraticBracket_abs_le W β δ K l u)
      (quadraticLimit_abs_le_cap W β δ K u))
    nlinarith [sq_abs (quadraticBracket W β δ K l u - quadraticLimit W β δ K u),
      abs_nonneg (quadraticBracket W β δ K l u - quadraticLimit W β δ K u)]
  · filter_upwards [quadraticBracket_tendsto_ae W Z β δ K] with u hu
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      (hu.sub_const (quadraticLimit W β δ K u)).pow 2

theorem posteriorIncrement_hasSubgaussianMGF (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) :
    HasSubgaussianMGF (actualParisiMagnetizationIncrement W β s t) (t - s) W.law := by
  let := W.isProbability
  refine ⟨fun θ => ?_, fun θ => ?_⟩
  · apply Integrable.of_bound
      (((measurable_actualParisiMagnetizationIncrement W β s t).const_mul θ).exp.aestronglyMeasurable)
      (Real.exp (2 * |θ|))
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      θ * actualParisiMagnetizationIncrement W β s t w ≤
          |θ * actualParisiMagnetizationIncrement W β s t w| := le_abs_self _
      _ ≤ |θ| * 2 := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (actualParisiMagnetizationIncrement_abs_le W β s t w) (abs_nonneg θ)
      _ = _ := by ring
  · have hh := actualParisiFullProcess_predictable_mgf_test W β hβ s (t - s)
      (fun _ => 1) (fun _ => 1) measurable_const measurable_const (fun _ => zero_le_one)
      1 1 zero_le_one zero_le_one (fun _ => le_rfl) (fun _ => by norm_num) θ
    rw [← NNReal.coe_add s (t - s), add_tsub_cancel_of_le hst] at hh
    simpa only [mgf, actualParisiMagnetizationIncrement, actualParisiMagnetizationObservable,
      add_tsub_cancel_of_le hst, one_mul, one_pow, mul_one, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one,
      smul_eq_mul, mul_comm (θ ^ 2)] using hh

theorem subgaussian_abs_moment_le {U : Type} [MeasurableSpace U] (μ : Measure U)
    [IsProbabilityMeasure μ] (X : U → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hX : HasSubgaussianMGF X c μ) (n : ℕ) :
    Integrable (fun w => |X w| ^ n) μ ∧
      (∫ w, |X w| ^ n ∂μ) ≤ 2 * (n.factorial : ℝ) * Real.exp (1 / 2) * (Real.sqrt c) ^ n := by
  let r : ℝ := Real.sqrt c
  have hr : 0 < r := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hc)
  have hr2 : r ^ 2 = c := Real.sq_sqrt c.coe_nonneg
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have he (x : ℝ) : Real.exp (|x| / r) ≤ Real.exp (r⁻¹ * x) + Real.exp (-r⁻¹ * x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, div_eq_mul_inv, mul_comm x]
      linarith [Real.exp_pos (-r⁻¹ * x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have hx' : -x / r = -r⁻¹ * x := by ring
      rw [hx']
      linarith [Real.exp_pos (r⁻¹ * x)]
  have hpoint (w : U) : |X w| ^ n ≤ (n.factorial : ℝ) * r ^ n *
      (Real.exp (r⁻¹ * X w) + Real.exp (-r⁻¹ * X w)) := by
    have hp := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp
      (x := |X w| / r) (div_nonneg (abs_nonneg (X w)) hr.le) n)
    calc
      _ = r ^ n * (|X w| / r) ^ n := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n hr.ne')]
      _ ≤ r ^ n * (Real.exp (|X w| / r) * (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg hr.le n)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (he (X w)) (mul_nonneg hn.le (pow_nonneg hr.le n))
        nlinarith only [hh]
  have hi := ((hX.1 r⁻¹).add (hX.1 (-r⁻¹))).const_mul ((n.factorial : ℝ) * r ^ n)
  have hiX : Integrable (fun w => |X w| ^ n) μ :=
    hi.mono' (hX.aemeasurable.abs.pow_const n).aestronglyMeasurable
      (ae_of_all _ (fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) n)]
        exact hpoint w))
  refine ⟨hiX, (integral_mono hiX hi hpoint).trans ?_⟩
  rw [integral_const_mul]
  simp only [Pi.add_apply]
  rw [integral_add (hX.1 r⁻¹) (hX.1 (-r⁻¹))]
  have hscale : (c : ℝ) * r⁻¹ ^ 2 / 2 = 1 / 2 := by
    rw [inv_pow, ← div_eq_mul_inv, hr2, div_self (NNReal.coe_pos.mpr hc).ne']
  have hp := hX.2 r⁻¹
  have hm := hX.2 (-r⁻¹)
  change (∫ w, Real.exp (r⁻¹ * X w) ∂μ) ≤ Real.exp _ at hp
  change (∫ w, Real.exp (-r⁻¹ * X w) ∂μ) ≤ Real.exp _ at hm
  rw [hscale] at hp
  rw [neg_sq, hscale] at hm
  have hh := mul_le_mul_of_nonneg_left (add_le_add hp hm)
    (mul_nonneg hn.le (pow_nonneg hr.le n))
  nlinarith only [hh]

theorem posteriorIncrement_fourth_moment_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, actualParisiMagnetizationIncrement W β s t w ^ 4 ∂W.law) ≤
      48 * Real.exp (1 / 2) * ((t : ℝ) - s) ^ 2 := by
  let := W.isProbability
  rcases eq_or_lt_of_le hst with rfl | hst'
  · simp [actualParisiMagnetizationIncrement]
  have hh := (subgaussian_abs_moment_le W.law (actualParisiMagnetizationIncrement W β s t)
    (t - s) (tsub_pos_iff_lt.mpr hst') (posteriorIncrement_hasSubgaussianMGF W β hβ s t hst) 4).2
  have hsqrt : Real.sqrt ((t - s : ℝ≥0) : ℝ) ^ 4 = ((t : ℝ) - s) ^ 2 := by
    calc
      _ = (Real.sqrt ((t - s : ℝ≥0) : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (t - s).coe_nonneg, NNReal.coe_sub hst]
  rw [hsqrt] at hh
  norm_num only [show (4 : ℕ).factorial = 24 from rfl, Nat.cast_ofNat] at hh
  simpa only [show (2 : ℝ) * 24 = 48 by norm_num,
    (show Even (4 : ℕ) from by decide).pow_abs] using hh

theorem originalIncrement_integral_past_test (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (s t : ℝ≥0) (hst : s ≤ t) (F : ScalarContinuousPath s → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun w => F (boundedDriftPastPath W b s w)) W.law) :
    (∫ w, F (boundedDriftPastPath W b s w) * (W.B t w - W.B s w) ∂W.law) = 0 := by
  have hi := (brownian_future_indep_boundedDriftPastPath W b s).comp
    (measurable_pi_apply (t - s)) hF
  have hi' : IndepFun (fun w => W.B t w - W.B s w)
      (fun w => F (boundedDriftPastPath W b s w)) W.law := by
    simpa only [Function.comp_def, add_tsub_cancel_of_le hst] using hi
  rw [hi'.symm.integral_fun_mul_eq_mul_integral hFi.aestronglyMeasurable
    ((W.measurable t).sub (W.measurable s)).aestronglyMeasurable,
    integral_sub (W.brownian.integrable_eval _) (W.brownian.integrable_eval _),
    W.brownian.integral_eval, W.brownian.integral_eval, sub_self, mul_zero]

theorem posteriorIncrement_frozen_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, (actualParisiMagnetizationIncrement W β s t w -
      LJ.actualCurvature W β s w * (W.B t w - W.B s w)) ^ 2 ∂W.law) =
      ∫ u in (s : ℝ)..(t : ℝ), ∫ w,
        (LJ.actualCurvature W β s w - LJ.actualCurvature W β u.toNNReal w) ^ 2 ∂W.law := by
  let := W.isProbability
  let g : ℕ → ℝ≥0 := fun k => if k = 0 then s else t
  have hg : Monotone g := by
    apply monotone_nat_of_le_succ
    intro k
    by_cases hk : k = 0
    · simpa only [g, hk, ↓reduceIte, zero_add, Nat.one_ne_zero] using hst
    · simp only [g, hk, ↓reduceIte, Nat.succ_ne_zero, le_refl]
  have hgeq (w : Ω) : LJ.posteriorBrownianSum W β g 1 w =
      LJ.actualCurvature W β s w * (W.B t w - W.B s w) := by
    simp only [LJ.posteriorBrownianSum, Finset.sum_range_one, g, ↓reduceIte, zero_add, Nat.one_ne_zero]
  have hs := LJ.posteriorBrownianSum_isometry W β g hg 1
  have hstcross := LJ.posteriorBrownianSum_terminal_cross W β hβ g hg 1
  simp only [Finset.sum_range_one, g, ↓reduceIte, zero_add, Nat.one_ne_zero, hgeq] at hstcross
  let F : ScalarContinuousPath s → ℝ := fun p =>
    actualParisiPastMagnetization β s p * LJ.curvatureFieldCoefficient β g 0 p
  have hF : Measurable F := (measurable_actualParisiPastMagnetization β s).mul
    (LJ.measurable_curvatureFieldCoefficient β g 0)
  have hFa : (fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w)) =ᵐ[W.law]
      (fun w => actualParisiMagnetizationObservable W β s w * LJ.actualCurvature W β s w) := by
    filter_upwards [actualParisiPastMagnetization_version W β s,
      LJ.curvatureFieldCoefficient_actual W β g 0] with w hm ha
    exact congrArg₂ (fun x y : ℝ => x * y) hm ha
  have hFi : Integrable (fun w => actualParisiMagnetizationObservable W β s w *
      LJ.actualCurvature W β s w) W.law := by
    apply Integrable.of_bound ((measurable_actualParisiMagnetizationObservable W β s).mul
      (LJ.measurable_actualCurvature W β s)).aestronglyMeasurable 1
    exact ae_of_all _ (fun w => by
      rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (actualParisiMagnetizationObservable_abs_le W β s w)
        (LJ.actualCurvature_abs_le W β s w) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hscross : (∫ w, actualParisiMagnetizationObservable W β s w *
      LJ.posteriorBrownianSum W β g 1 w ∂W.law) = 0 := by
    have hh := originalIncrement_integral_past_test W (actualParisiFullScalarDrift β) s t hst F hF
      (hFi.congr hFa.symm)
    refine (integral_congr_ae ?_).trans hh
    filter_upwards [hFa] with w hw
    rw [hgeq, hw]
    ring
  let X := actualParisiMagnetizationIncrement W β s t
  let Y := LJ.posteriorBrownianSum W β g 1
  have hX : MemLp X 2 W.law := (posteriorIncrement_hasSubgaussianMGF W β hβ s t hst).memLp 2
  have hY : MemLp Y 2 W.law := hs.1
  have hXs : MemLp (actualParisiMagnetizationObservable W β s) 2 W.law :=
    (memLp_const (1 : ℝ)).mono'
      (measurable_actualParisiMagnetizationObservable W β s).aestronglyMeasurable
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using
        actualParisiMagnetizationObservable_abs_le W β s w))
  have hXt : MemLp (actualParisiMagnetizationObservable W β t) 2 W.law :=
    (memLp_const (1 : ℝ)).mono'
      (measurable_actualParisiMagnetizationObservable W β t).aestronglyMeasurable
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using
        actualParisiMagnetizationObservable_abs_le W β t w))
  have hcross : (∫ w, X w * Y w ∂W.law) =
      ∫ u in (s : ℝ)..(t : ℝ), ∫ w, LJ.actualCurvature W β s w *
        LJ.actualCurvature W β u.toNNReal w ∂W.law := by
    change (∫ w, (actualParisiMagnetizationObservable W β t w -
      actualParisiMagnetizationObservable W β s w) * Y w ∂W.law) = _
    simp_rw [sub_mul]
    have hh := integral_sub (hXt.integrable_mul hY) (hXs.integrable_mul hY)
    simp only [Pi.mul_apply] at hh
    rw [hh, hscross, sub_zero]
    simpa only [Y, hgeq] using hstcross
  have he (w : Ω) : (X w - Y w) ^ 2 = X w ^ 2 + Y w ^ 2 - 2 * (X w * Y w) := by ring
  simp_rw [← hgeq]
  change (∫ w, (X w - Y w) ^ 2 ∂W.law) = _
  simp_rw [he]
  have hsub := integral_sub (hX.integrable_sq.add hY.integrable_sq) ((hX.integrable_mul hY).const_mul 2)
  have hadd := integral_add hX.integrable_sq hY.integrable_sq
  simp only [Pi.add_apply, Pi.mul_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, hcross]
  have hX2 : (∫ w, X w ^ 2 ∂W.law) =
      ∫ u in (s : ℝ)..(t : ℝ), actualParisiFullSusceptibilitySquareExpected W β u := by
    exact (actualParisiIncrement_secondMoment W β hβ s t hst).trans
      (actualParisiFullSusceptibilitySquareExpected_interval W β hβ s t hst).symm
  rw [hX2, hs.2]
  simp only [Finset.sum_range_one, g, ↓reduceIte, zero_add, Nat.one_ne_zero]
  have hr : IntervalIntegrable (actualParisiFullSusceptibilitySquareExpected W β) volume s t :=
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable (s : ℝ) t
  have hc : IntervalIntegrable (fun u : ℝ => ∫ w, LJ.actualCurvature W β s w *
      LJ.actualCurvature W β u.toNNReal w ∂W.law) volume s t :=
    (LJ.continuous_actualCurvature_pair W β s).intervalIntegrable (s : ℝ) t
  rw [show ((t : ℝ) - s) * actualParisiFullSusceptibilitySquareExpected W β s =
      ∫ _ in (s : ℝ)..(t : ℝ), actualParisiFullSusceptibilitySquareExpected W β s by
        rw [intervalIntegral.integral_const, smul_eq_mul]]
  rw [← intervalIntegral.integral_add hr intervalIntegrable_const,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hr.add intervalIntegrable_const) (hc.const_mul 2)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr hst)] at hu
  dsimp only
  rw [LJ.actualCurvature_difference_sq, Real.coe_toNNReal u (s.coe_nonneg.trans hu.1)]
  ring

attribute [local irreducible] LJ.actualCurvature

theorem posteriorIncrement_frozen_error_small (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (s t : ℝ≥0), s ≤ t → t ≤ T → (t : ℝ) - s < η →
      (∫ w, (actualParisiMagnetizationIncrement W β s t w -
        LJ.actualCurvature W β s w * (W.B t w - W.B s w)) ^ 2 ∂W.law) ≤ ε * ((t : ℝ) - s) := by
  let := W.isProbability
  obtain ⟨η, hη, hsmall⟩ := expected_sq_difference_uniform_small_of_bounded W.law
    (LJ.actualCurvature W β) (fun s => (LJ.measurable_actualCurvature W β s).aestronglyMeasurable)
    (LJ.actualCurvature_continuous_ae W β) 1
    (fun s w => by rw [Real.norm_eq_abs]; exact LJ.actualCurvature_abs_le W β s w) T ε hε
  refine ⟨η, hη, fun s t hst htT hwidth => ?_⟩
  rw [posteriorIncrement_frozen_error W β hβ s t hst]
  have hc : Continuous (fun u : ℝ => ∫ w,
      (LJ.actualCurvature W β s w - LJ.actualCurvature W β u.toNNReal w) ^ 2 ∂W.law) :=
    (LJ.continuous_actualCurvature_difference_sq W β).comp (continuous_const.prodMk continuous_real_toNNReal)
  have hh := intervalIntegral.integral_mono_on (NNReal.coe_le_coe.mpr hst)
    (hc.intervalIntegrable s t) (intervalIntegrable_const (c := ε) (μ := volume))
    (fun u hu => ?_)
  · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh
  · have hu0 : 0 ≤ u := s.coe_nonneg.trans hu.1
    have huT : u.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal u hu0]
      exact hu.2.trans (NNReal.coe_le_coe.mpr htT)
    apply (hsmall s (hst.trans htT) u.toNNReal huT ?_).le
    rw [Real.coe_toNNReal u hu0, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hu.1)]
    exact (sub_le_sub_right hu.2 _).trans_lt hwidth

theorem quadraticBracket_memLp (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K l : ℕ)
    (μ : Measure ((Bool × Ω) × A)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (quadraticBracket W β δ K l) p μ :=
  (memLp_const (quadraticCap W β δ K)).mono'
    (measurable_quadraticBracket W β δ K l).aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using quadraticBracket_abs_le W β δ K l u))

theorem quadraticGroupLimit_partial (h2 : CoarseCoefficientBudgetStatement)
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      Measurable (quadraticLimit (A := A) W β δ K) ∧
      (∀ u, |quadraticLimit (A := A) W β δ K u| ≤ C * δ) ∧
      ∀ l, Integrable (fun u => (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2)
        (meshLaw W Z β δ K) := by
  obtain ⟨C, hC, hb⟩ := quadraticLimit_measurable_bounded (A := A) h2 W β hβ
  exact ⟨C, hC, fun δ K hmesh => ⟨(hb δ K hmesh).1, (hb δ K hmesh).2,
    fun l => quadraticGroupLimit_integrable_sq_unconditional W β δ K l (meshLaw W Z β δ K)⟩⟩

theorem squared_error_integral_le {U : Type} [MeasurableSpace U] (μ : Measure U)
    (X Y Z : U → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    (∫ w, (X w - Z w) ^ 2 ∂μ) ≤
      2 * ((∫ w, (X w - Y w) ^ 2 ∂μ) + ∫ w, (Y w - Z w) ^ 2 ∂μ) := by
  have hi := integral_mono ((hX.sub hZ).integrable_sq)
    ((((hX.sub hY).integrable_sq).add ((hY.sub hZ).integrable_sq)).const_mul 2)
    (fun w => show (X w - Z w) ^ 2 ≤ 2 * ((X w - Y w) ^ 2 + (Y w - Z w) ^ 2) by
      nlinarith [sq_nonneg ((X w - Y w) - (Y w - Z w))])
  have hadd := integral_add (hX.sub hY).integrable_sq (hY.sub hZ).integrable_sq
  simp only [Pi.sub_apply] at hadd
  simpa only [integral_const_mul, Pi.add_apply, Pi.sub_apply, hadd] using hi

theorem quadraticGroup_tendsto_L2_iff_replacement (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    Tendsto (fun l => ∫ u, (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2
      ∂meshLaw W Z β δ K) atTop (𝓝 0) ↔
    Tendsto (fun l => ∫ u, (quadraticGroup W β δ K l u - quadraticBracket W β δ K l u) ^ 2
      ∂meshLaw W Z β δ K) atTop (𝓝 0) := by
  have hB := quadraticBracket_tendsto_L2 W Z β δ K
  have hQ := quadraticLimit_memLp W β δ K (meshLaw W Z β δ K) 2
  have hG (l : ℕ) := quadraticGroup_memLp W β δ K l (meshLaw W Z β δ K) 2
  have hBl (l : ℕ) := quadraticBracket_memLp W β δ K l (meshLaw W Z β δ K) 2
  constructor
  · intro hlim
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun l => squared_error_integral_le (meshLaw W Z β δ K) _ _ _ (hG l) hQ (hBl l))
    simpa only [sub_sq_comm (quadraticLimit W β δ K _) _, zero_add, mul_zero] using
      (hlim.add hB).const_mul 2
  · intro hlim
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun l => squared_error_integral_le (meshLaw W Z β δ K) _ _ _ (hG l) (hBl l) hQ)
    simpa only [zero_add, mul_zero] using (hlim.add hB).const_mul 2

end SKConstants.Completion.S73
