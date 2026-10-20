module

public import SKConstants.Completion.X73A.QuadraticVariation
public import SKConstants.Completion.S72.Node
public import SKConstants.Completion.S71.Node
public import SKConstants.Completion.S74a.Node
public import SKConstants.Completion.S745.Node
public import SKConstants.Completion.S76.Node
public import SKConstants.Completion.Blueprint5a.AssemblySJ7

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X73A
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Blueprint5a
variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]

def weightedPosteriorCell (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (j : ℕ)
    (c : ℝ → ℝ) (l : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ l), c (refinedGrid δ l j i) *
    actualParisiMagnetizationIncrement W β (refinedGrid δ l j i) (refinedGrid δ l j (i + 1)) w ^ 2

def weightedCompensatorCell (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (j : ℕ)
    (c : ℝ → ℝ) (l : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ l), c (refinedGrid δ l j i) *
    posteriorSquareCompensator W β (refinedGrid δ l j i) (refinedGrid δ l j (i + 1)) w

def weightedCurvatureCell (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (j : ℕ)
    (c : ℝ → ℝ) (w : Ω) : ℝ :=
  ∫ r in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ), c r * LJ.actualCurvature W β r.toNNReal w ^ 2

theorem measurable_weightedPosteriorCell (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (l : ℕ) : Measurable (weightedPosteriorCell W β δ j c l) :=
  Finset.measurable_sum _ (fun _i _ =>
    ((measurable_actualParisiMagnetizationIncrement W β _ _).pow_const 2).const_mul _)

theorem measurable_weightedCompensatorCell (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (l : ℕ) : Measurable (weightedCompensatorCell W β δ j c l) :=
  Finset.measurable_sum _ (fun _i _ => (measurable_posteriorSquareCompensator W β _ _).const_mul _)

theorem measurable_weightedCurvatureCell (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (hc : Measurable c) : Measurable (weightedCurvatureCell W β δ j c) :=
  SKConstantsOAI.ZeroTemperatureSK.WeakIto.measurable_time_integral
    ((hc.comp measurable_fst).mul
      ((LC1.measurable_actualFullCurvature_process_real W β).pow_const 2)) _ _

theorem weightedPosteriorCell_memLp (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (l : ℕ) (p : ℝ≥0∞) : MemLp (weightedPosteriorCell W β δ j c l) p W.law := by
  let := W.isProbability
  unfold weightedPosteriorCell
  apply memLp_finsetSum
  intro i _
  apply MemLp.const_mul
  apply memLp_of_abs_le W.law _
    ((measurable_actualParisiMagnetizationIncrement W β _ _).pow_const 2) 4 _ p
  intro w
  rw [abs_pow]
  have hh := actualParisiMagnetizationIncrement_abs_le W β
    (refinedGrid δ l j i) (refinedGrid δ l j (i + 1)) w
  nlinarith [abs_nonneg (actualParisiMagnetizationIncrement W β
    (refinedGrid δ l j i) (refinedGrid δ l j (i + 1)) w)]

theorem weightedCompensatorCell_abs_le (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ r, |c r| ≤ C)
    (l : ℕ) (w : Ω) :
    |weightedCompensatorCell W β δ j c l w| ≤ C * (growingQueryDuration δ j : ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ l), C *
        ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hc _) (posteriorSquareCompensator_abs_le W β _ _
        (LJ3.growingLagDyadicTime_monotone δ l j (Nat.le_succ i)) w) (abs_nonneg _) hC
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => (refinedGrid δ l j i : ℝ)), refinedGrid,
        LJ3.growingLagDyadicTime_end, LJ3.growingLagDyadicTime_zero, growingQueryTime_sub]

theorem weightedCurvatureCell_abs_le (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (C : ℝ) (hC : ∀ r, |c r| ≤ C) (w : Ω) :
    |weightedCurvatureCell W β δ j c w| ≤ C * (growingQueryDuration δ j : ℝ) := by
  have hst : (mesh δ j : ℝ) ≤ mesh δ (j + 1) := by
    change (growingQueryTime δ j : ℝ) ≤ growingQueryTime δ (j + 1)
    rw [growingQueryTime_succ, NNReal.coe_add]
    exact le_add_of_nonneg_right (growingQueryDuration δ j).coe_nonneg
  have hi := S73.quadraticIntegral_abs_le c (fun r => LJ.actualCurvature W β r.toNNReal w)
    _ _ hst (hc.abs.intervalIntegrable _ _) (fun r => LJ.actualCurvature_abs_le W β _ w)
  have hh := intervalIntegral.integral_mono_on hst (hc.abs.intervalIntegrable _ _)
    (intervalIntegrable_const (c := C) (μ := volume)) (fun r _ => hC r)
  apply hi.trans
  simpa only [intervalIntegral.integral_const, smul_eq_mul, growingQueryTime_sub, mul_comm] using hh

theorem weightedCompensatorCell_memLp (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ r, |c r| ≤ C)
    (l : ℕ) (p : ℝ≥0∞) : MemLp (weightedCompensatorCell W β δ j c l) p W.law := by
  let := W.isProbability
  exact memLp_of_abs_le W.law _ (measurable_weightedCompensatorCell W β δ j c l) _
    (weightedCompensatorCell_abs_le W β δ j c C hC hc l) p

theorem weightedCurvatureCell_memLp (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (C : ℝ) (hC : ∀ r, |c r| ≤ C)
    (p : ℝ≥0∞) : MemLp (weightedCurvatureCell W β δ j c) p W.law := by
  let := W.isProbability
  exact memLp_of_abs_le W.law _ (measurable_weightedCurvatureCell W β δ j c hc.measurable) _
    (weightedCurvatureCell_abs_le W β δ j c hc C hC) p

theorem weightedPosteriorCell_compensator_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (δ : ℝ≥0) (j : ℕ) (c : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ r, |c r| ≤ C) :
    Tendsto (fun l => ∫ w, (weightedPosteriorCell W β δ j c l w -
      weightedCompensatorCell W β δ j c l w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  have he (l : ℕ) (w : Ω) : weightedPosteriorCell W β δ j c l w -
      weightedCompensatorCell W β δ j c l w =
      ∑ i ∈ Finset.range (2 ^ l), c (refinedGrid δ l j i) *
        compensatedPosteriorSquare W β (refinedGrid δ l j i) (refinedGrid δ l j (i + 1)) w := by
    simp only [weightedPosteriorCell, weightedCompensatorCell, compensatedPosteriorSquare,
      mul_sub, Finset.sum_sub_distrib]
  simp_rw [he]
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => ?_) (by
      have h := (brownianDyadicWidth_tendsto (growingQueryDuration δ j)).const_mul
        ((96 * Real.exp (1 / 2) + 2) * C ^ 2)
      have hh := h.mul_const (growingQueryDuration δ j : ℝ)
      simpa only [mul_zero, zero_mul] using hh)
  have hh := compensatedPosteriorSquare_sum_secondMoment_le W β hβ
    (refinedGrid δ l j) (LJ3.growingLagDyadicTime_monotone δ l j)
    (fun i => c (refinedGrid δ l j i)) (2 ^ l) C
    (brownianDyadicWidth (growingQueryDuration δ j) l) hC (fun i _ => hc _) (fun i _ => ?_)
  · simpa only [LJ3.growingLagDyadicTime_end, LJ3.growingLagDyadicTime_zero,
      growingQueryTime_sub] using hh
  · simpa only [refinedGrid, LJ3.growingLagDyadicTime, scalarBrownianDyadicTime,
      brownianDyadicGrid, NNReal.coe_add, add_sub_add_left_eq_sub] using
      brownianDyadicGrid_width_le (growingQueryDuration δ j) l i

theorem weightedCompensatorCell_tendsto_of_continuous (W : BrownianSystem Ω) (β : ℝ)
    (δ : ℝ≥0) (j : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (w : Ω)
    (hw : Continuous (fun t => LJ.actualCurvature W β t w)) :
    Tendsto (fun l => weightedCompensatorCell W β δ j c l w) atTop
      (𝓝 (weightedCurvatureCell W β δ j c w)) := by
  have hg : Continuous (fun r : ℝ => LJ.actualCurvature W β
      ((mesh δ j : ℝ) + r).toNNReal w ^ 2) :=
    ((hw.comp continuous_real_toNNReal).comp (continuous_const.add continuous_id)).pow 2
  have h := SJ7.frozen_integral_dyadic_tendsto
    (fun r => c ((mesh δ j : ℝ) + r))
    (fun r => LJ.actualCurvature W β ((mesh δ j : ℝ) + r).toNNReal w ^ 2)
    (hc.comp (continuous_const.add continuous_id)) hg (growingQueryDuration δ j)
    (fun r _ => by
      rw [abs_pow]
      have hh := LJ.actualCurvature_abs_le W β ((mesh δ j : ℝ) + r).toNNReal w
      nlinarith [abs_nonneg (LJ.actualCurvature W β ((mesh δ j : ℝ) + r).toNNReal w)])
  have hshift (a b : ℝ) :
      (∫ r in a..b, LJ.actualCurvature W β ((mesh δ j : ℝ) + r).toNNReal w ^ 2) =
        ∫ r in (mesh δ j : ℝ) + a..(mesh δ j : ℝ) + b,
          LJ.actualCurvature W β r.toNNReal w ^ 2 :=
    intervalIntegral.integral_comp_add_left (fun r => LJ.actualCurvature W β r.toNNReal w ^ 2) _
  have htarget : (∫ r in (0 : ℝ)..(growingQueryDuration δ j : ℝ),
      c ((mesh δ j : ℝ) + r) * LJ.actualCurvature W β ((mesh δ j : ℝ) + r).toNNReal w ^ 2) =
      ∫ r in (mesh δ j : ℝ)..(mesh δ j : ℝ) + (growingQueryDuration δ j : ℝ),
        c r * LJ.actualCurvature W β r.toNNReal w ^ 2 := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left
      (fun r => c r * LJ.actualCurvature W β r.toNNReal w ^ 2) (mesh δ j : ℝ)
        (a := 0) (b := (growingQueryDuration δ j : ℝ))
  simp_rw [hshift, htarget] at h
  simpa only [weightedCompensatorCell, weightedCurvatureCell, posteriorSquareCompensator,
    refinedGrid, LJ3.growingLagDyadicTime, scalarBrownianDyadicTime,
    mesh, intervalIntegral.integral_comp_add_left, add_zero, growingQueryTime_succ, NNReal.coe_add,
    brownianDyadicGrid] using h

theorem weightedCompensatorCell_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (j : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (C : ℝ) (hC : 0 ≤ C)
    (hcC : ∀ r, |c r| ≤ C) :
    Tendsto (fun l => ∫ w, (weightedCompensatorCell W β δ j c l w -
      weightedCurvatureCell W β δ j c w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  let := W.isProbability
  have h := tendsto_integral_of_dominated_convergence (μ := W.law)
    (f := fun _ => (0 : ℝ))
    (F := fun l w => (weightedCompensatorCell W β δ j c l w - weightedCurvatureCell W β δ j c w) ^ 2)
    (bound := fun _ => (2 * (C * (growingQueryDuration δ j : ℝ))) ^ 2)
    (fun l => (((measurable_weightedCompensatorCell W β δ j c l).sub
      (measurable_weightedCurvatureCell W β δ j c hc.measurable)).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun l => ae_of_all _ (fun w => ?_)) ?_
  · simpa only [integral_zero] using h
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (abs_sub _ _).trans (add_le_add
      (weightedCompensatorCell_abs_le W β δ j c C hC hcC l w)
      (weightedCurvatureCell_abs_le W β δ j c hc C hcC w))
    nlinarith [sq_abs (weightedCompensatorCell W β δ j c l w - weightedCurvatureCell W β δ j c w),
      abs_nonneg (weightedCompensatorCell W β δ j c l w - weightedCurvatureCell W β δ j c w)]
  · filter_upwards [LJ.actualCurvature_continuous_ae W β] with w hw
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((weightedCompensatorCell_tendsto_of_continuous W β δ j c hc w hw).sub_const
        (weightedCurvatureCell W β δ j c w)).pow 2

theorem weightedPosteriorCell_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (j : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (C : ℝ) (hC : 0 ≤ C)
    (hcC : ∀ r, |c r| ≤ C) :
    Tendsto (fun l => ∫ w, (weightedPosteriorCell W β δ j c l w -
      weightedCurvatureCell W β δ j c w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  have h1 := weightedPosteriorCell_compensator_tendsto_L2 W β hβ δ j c C hC hcC
  have h2 := weightedCompensatorCell_tendsto_L2 W β δ j c hc C hC hcC
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => S73.squared_error_integral_le W.law _ _ _
      (weightedPosteriorCell_memLp W β δ j c l 2)
      (weightedCompensatorCell_memLp W β δ j c C hC hcC l 2)
      (weightedCurvatureCell_memLp W β δ j c hc C hcC 2))
  simpa only [zero_add, mul_zero] using (h1.add h2).const_mul 2

theorem meanSquare_finset_sum {μ : Measure Ω} (X : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hX : ∀ j l, MemLp (X j l) 2 μ) (hY : ∀ j, MemLp (Y j) 2 μ)
    (hlim : ∀ j, Tendsto (fun l => ∫ w, (X j l w - Y j w) ^ 2 ∂μ) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun l => ∫ w, ((∑ j ∈ Finset.range n, X j l w) -
      ∑ j ∈ Finset.range n, Y j w) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) (fun l => ?_) (by
    have hs := tendsto_finsetSum (Finset.range n) (fun j _ => hlim j)
    simpa only [Finset.sum_const_zero, mul_zero] using hs.const_mul (n : ℝ))
  have hsX := memLp_finsetSum (Finset.range n) (fun j _ => hX j l)
  have hsY := memLp_finsetSum (Finset.range n) (fun j _ => hY j)
  have hh := integral_mono (hsX.sub hsY).integrable_sq
    ((integrable_finsetSum (Finset.range n) (fun j _ => ((hX j l).sub (hY j)).integrable_sq)).const_mul
      (n : ℝ)) (fun w => ?_)
  · rw [integral_const_mul, integral_finsetSum _ (fun j _ => ((hX j l).sub (hY j)).integrable_sq)] at hh
    exact hh
  · change ((∑ j ∈ Finset.range n, X j l w) - ∑ j ∈ Finset.range n, Y j w) ^ 2 ≤
      (n : ℝ) * ∑ j ∈ Finset.range n, (X j l w - Y j w) ^ 2
    rw [← Finset.sum_sub_distrib]
    simpa only [Finset.card_range, Nat.cast_ofNat] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := fun j => X j l w - Y j w))

omit [MeasurableSpace A] in
theorem quadraticGroup_eq_weightedCells (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (K l : ℕ) (u : (Bool × Ω) × A) :
    quadraticGroup W β δ K l u = -(1 / 2 : ℝ) * ∑ j ∈ Finset.range (K + 1),
      weightedPosteriorCell W β δ j
        (fun r => β * actualParisiFullSusceptibilityExpected W β r -
          LJ.residualCoarseA W β (mesh δ) K j) l u.1.2 := by
  unfold quadraticGroup LJ.refinedResidualQuadratic weightedPosteriorCell
    actualParisiMagnetizationIncrement actualParisiMagnetizationObservable actualParisiFullPosteriorMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticGroup_tendsto_L2 (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) :
    Tendsto (fun l => ∫ u, (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2
      ∂meshLaw W Z β δ K) atTop (𝓝 0) := by
  let c := fun j r => β * actualParisiFullSusceptibilityExpected W β r -
    LJ.residualCoarseA W β (mesh δ) K j
  let C := fun j => |β| + |LJ.residualCoarseA W β (mesh δ) K j|
  have hC (j : ℕ) : 0 ≤ C j := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hc (j : ℕ) : Continuous (c j) :=
    ((continuous_actualParisiFullSusceptibilityExpected W β).const_mul β).sub continuous_const
  have hb (j : ℕ) (r : ℝ) : |c j r| ≤ C j := S73.quadraticCoefficient_abs_le W β _ r
  let X := fun j l => weightedPosteriorCell W β δ j (c j) l
  let Y := fun j => weightedCurvatureCell W β δ j (c j)
  have hx (j l : ℕ) : MemLp (X j l) 2 W.law := weightedPosteriorCell_memLp W β δ j (c j) l 2
  have hy (j : ℕ) : MemLp (Y j) 2 W.law := weightedCurvatureCell_memLp W β δ j (c j) (hc j) _ (hb j) 2
  have hlim := meanSquare_finset_sum X Y hx hy (fun j =>
    weightedPosteriorCell_tendsto_L2 W β hβ δ j (c j) (hc j) _ (hC j) (hb j)) (K + 1)
  have heq (l : ℕ) :
      (∫ u, (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2 ∂meshLaw W Z β δ K) =
        (1 / 4 : ℝ) * ∫ w, ((∑ j ∈ Finset.range (K + 1), X j l w) -
          ∑ j ∈ Finset.range (K + 1), Y j w) ^ 2 ∂W.law := by
    have hm := ((memLp_finsetSum (Finset.range (K + 1)) (fun j _ => hx j l)).sub
      (memLp_finsetSum (Finset.range (K + 1)) (fun j _ => hy j))).integrable_sq.aestronglyMeasurable
    have hmap := (actualParisiFullQuerySpinLaw_path_hasLaw W Z β
      (growingQueryTime δ (K + 1))).integral_comp hm
    calc
      _ = ∫ u, (1 / 4 : ℝ) * ((∑ j ∈ Finset.range (K + 1), X j l u.1.2) -
          ∑ j ∈ Finset.range (K + 1), Y j u.1.2) ^ 2 ∂meshLaw W Z β δ K := by
        apply integral_congr_ae
        apply ae_of_all
        intro u
        dsimp only
        rw [quadraticGroup_eq_weightedCells]
        change (-(1 / 2 : ℝ) * (∑ j ∈ Finset.range (K + 1), X j l u.1.2) -
          -(1 / 2 : ℝ) * (∑ j ∈ Finset.range (K + 1), Y j u.1.2)) ^ 2 = _
        ring
      _ = _ := by
        rw [integral_const_mul]
        exact congrArg (fun r : ℝ => (1 / 4 : ℝ) * r) hmap
  simp_rw [heq]
  simpa only [mul_zero] using hlim.const_mul (1 / 4 : ℝ)

theorem quadraticGroupLimit_holds : QuadraticGroupLimitStatement := by
  intro Ω A _ _ W Z β hβ
  obtain ⟨C, hC, hb⟩ := S73.quadraticGroupLimit_partial S72.coarseCoefficientBudget_holds W Z β hβ
  refine ⟨C, hC, fun δ K hmesh => ?_⟩
  obtain ⟨hm, hbound, hi⟩ := hb δ K hmesh
  exact ⟨hm, hbound, hi, quadraticGroup_tendsto_L2 W Z β hβ δ K⟩

theorem growingResidualMGF_holds : SKConstants.Blueprint4.GrowingResidualMGFStatement :=
  growingResidualMGF_of_subnodes S71.refinedResidualLimit_holds quadraticGroupLimit_holds
    signSymmetrization_holds
    (S745.linearGroupSubgaussian_holds S72.coarseCoefficientBudget_holds)
    (S745.predictableGroupMGF_holds S72.coarseCoefficientBudget_holds) S76.lagGroupMGF_holds

end SKConstants.Completion.X73A
