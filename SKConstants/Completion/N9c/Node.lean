module

public import SKConstants.Completion.N9c.FreshMixedMean
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9c
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LFine N9
variable {Ω : Type*} [MeasurableSpace Ω]

theorem fineCell_past_le_horizon (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) :
    growingQueryTime δ (e.val+1) ≤ Horizon δ K :=
  (growingQueryTime_strictMono δ hδ).monotone (by omega)

theorem fineCell_horizon_eq (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) :
    growingQueryTime δ (e.val+1) +
      (growingQueryDuration δ (e.val+1) + (Horizon δ K-growingQueryTime δ (e.val+2))) =
        Horizon δ K := by
  rw [← add_assoc]
  have ht : growingQueryTime δ (e.val+1) + growingQueryDuration δ (e.val+1) =
      growingQueryTime δ (e.val+2) := by
    simpa only [show e.val+1+1 = e.val+2 by omega] using (growingQueryTime_succ δ (e.val+1)).symm
  rw [ht]
  exact add_tsub_cancel_of_le ((growingQueryTime_strictMono δ hδ).monotone (by omega))

theorem fineEnergy_sourceHistoryFactorization_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    (SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) =
    (Measure.pi (fun _ : Fin (r+K) => freshRowInputLaw W
      (growingQueryTime δ (e.val+1)) (growingQueryDuration δ (e.val+1))
      (Horizon δ K-growingQueryTime δ (e.val+2)))).map
      (fun u i => castDriverHistory (fineCell_horizon_eq δ hδ K e)
        (freshRowHistory W β hβ (growingQueryTime δ (e.val+1))
          (growingQueryDuration δ (e.val+1)) (Horizon δ K-growingQueryTime δ (e.val+2)) (u i))) :=
  sourceHistories_eq_freshRows W β hβ δ hδ r K _ _ _
    (growingQueryDuration_pos δ hδ _) (fineCell_horizon_eq δ hδ K e)

theorem fineEnergy_sourceMixedTargetIndependence_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    iIndepFun (fun i (u : (Fin (r+K) → Bool) × SourceInput δ r K) =>
      (sourceFreshMixedMean W β hβ δ r K (growingQueryTime δ (e.val+1))
        (growingQueryDuration δ (e.val+1)) (Horizon δ K-growingQueryTime δ (e.val+2))
        (fineCell_past_le_horizon δ hδ K e) u i,
          SourceTargets W β hβ δ r K u.2 e i)) (SourceLinkedLaw W β hβ δ r K) :=
  sourceFreshMixedMean_target_independent W β hβ δ hδ r K _ _ _
    (fineCell_past_le_horizon δ hδ K e) e

theorem fineEnergy_sourceMixedMean_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K) (e : Fin K) :
    (∫ u, (((r+K : ℕ) : ℝ)⁻¹ * ∑ i,
      sourceFreshMixedMean W β hβ δ r K (growingQueryTime δ (e.val+1))
        (growingQueryDuration δ (e.val+1)) (Horizon δ K-growingQueryTime δ (e.val+2))
        (fineCell_past_le_horizon δ hδ K e) u i) ∂SourceLinkedLaw W β hβ δ r K) =
      LQ.actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (e.val+1))
        (growingQueryTime δ (e.val+2)) := by
  have hm := sourceFreshMixedMean_average_integral W β hβ δ hδ r K hn
    (growingQueryTime δ (e.val+1)) (growingQueryDuration δ (e.val+1))
    (Horizon δ K-growingQueryTime δ (e.val+2)) (growingQueryDuration_pos δ hδ _)
    (fineCell_horizon_eq δ hδ K e) (fineCell_past_le_horizon δ hδ K e)
  convert hm using 2
  simpa only [show e.val+1+1 = e.val+2 by omega] using growingQueryTime_succ δ (e.val+1)

theorem sourceFreshMixedMean_eq_frozen (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (a h f : ℝ≥0) (ha : a ≤ Horizon δ K)
    (u : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)) :
    sourceFreshMixedMean W β hβ δ r K a h f ha u i =
      frozenQueryMixedMean W β hβ a h f
        (fun j => (historyDriverPast a _ ha (SourceHistories W β hβ δ r K u j)).1)
        (fun j => (historyDriverPast a _ ha (SourceHistories W β hβ δ r K u j)).2) i := by
  rw [frozenQueryMixedMean_eq_row]
  rfl

theorem fineEnergy_sourceCovariance_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (a h f : ℝ≥0) (ha : a ≤ Horizon δ K) (e : Fin K) (L : ℝ) (hL : 0 ≤ L)
    (hζ : ∀ᵐ u ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
      0 ≤ sourceFreshMixedMean W β hβ δ r K a h f ha u i ∧
        sourceFreshMixedMean W β hβ δ r K a h f ha u i ≤ L) :
    -L/(r+K : ℕ) ≤ ∫ u,
      (((r+K : ℕ) : ℝ)⁻¹ * ∑ i, sourceFreshMixedMean W β hβ δ r K a h f ha u i) *
        (((r+K : ℕ) : ℝ)⁻¹ * ∑ i, (SourceTargets W β hβ δ r K u.2 e i)^2 - 1)
          ∂SourceLinkedLaw W β hβ δ r K := by
  let ζ := sourceFreshMixedMean W β hβ δ r K a h f ha
  let T := fun (u : (Fin (r+K) → Bool) × SourceInput δ r K) i =>
    SourceTargets W β hβ δ r K u.2 e i
  let R := fun i u => (max 0 (min L (ζ u i)),(T u i)^2)
  have hm (i : Fin (r+K)) : Measurable (R i) :=
    (measurable_const.max (measurable_const.min
      (measurable_sourceFreshMixedMean W β hβ δ r K a h f ha i))).prodMk
      ((((measurable_pi_apply i).comp ((measurable_pi_apply e).comp
        (measurable_SourceTargets W β hβ δ r K))).comp measurable_snd).pow_const 2)
  have hi : iIndepFun R (SourceLinkedLaw W β hβ δ r K) :=
    (sourceFreshMixedMean_target_independent W β hβ δ hδ r K a h f ha e).comp
      (fun _ p => (max 0 (min L p.1),p.2^2)) (fun _ => by fun_prop)
  have hc := empirical_covariance_lower (SourceLinkedLaw W β hβ δ r K) (r+K) hn R hm hi L
    (fun _ _ => ⟨le_max_left _ _,max_le hL (min_le_left _ _)⟩)
    (fun _ _ => sq_nonneg _)
    (fun i => (N9b.sourceTarget_memLp W β hβ δ hδ r K hn e i 2).integrable_sq)
    (fun i => N9b.sourceTarget_second W β hβ δ hδ r K hn e i)
  apply hc.trans_eq
  apply integral_congr_ae
  filter_upwards [hζ] with u hu
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact (congrArg (max 0) (min_eq_right (hu i).2)).trans (max_eq_right (hu i).1)

theorem fineEnergy_sourceRemovedSquare_regular_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (e : Fin K) (m : ℕ)
    (E : ((Fin (r+K) → Bool) × SourceInput δ r K) → Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
    (hEm : Measurable E) (hE : ∀ u i j, dot (E u i) (E u j) = if i=j then 1 else 0) :
    let Y := fun u => queryRemovedSquare (r+K : ℕ) (E u) (SourceTargets W β hβ δ r K u.2 e)
    MemLp Y 2 (SourceLinkedLaw W β hβ δ r K) ∧
      Integrable (fun u => Y u^2) (SourceLinkedLaw W β hβ δ r K) ∧
        (∫ u, Y u ∂SourceLinkedLaw W β hβ δ r K) ≤ 1 := by
  dsimp only
  let μ := SourceLinkedLaw W β hβ δ r K
  let T := fun (u : (Fin (r+K) → Bool) × SourceInput δ r K) => SourceTargets W β hβ δ r K u.2 e
  let Q := fun u => queryTotalSquare (r+K : ℕ) (T u)
  let Y := fun u => queryRemovedSquare (r+K : ℕ) (E u) (T u)
  have hTm : Measurable T := ((measurable_pi_apply e).comp
    (measurable_SourceTargets W β hβ δ r K)).comp measurable_snd
  have hYm : Measurable Y := by
    dsimp [Y,queryRemovedSquare,dot,Matrix.mulVec,dotProduct,frameProjection,
      Matrix.mul_apply,Matrix.transpose_apply]
    fun_prop
  have hnR : 0 < ((r+K : ℕ) : ℝ) := Nat.cast_pos.mpr hn
  have hQ : MemLp Q 2 μ := by
    convert (memLp_finsetSum Finset.univ (fun i _ =>
      memLp_square_of_four μ (fun u => T u i)
        (N9b.sourceTarget_memLp W β hβ δ hδ r K hn e i 4))).const_mul (((r+K : ℕ) : ℝ)⁻¹) using 1
    ext u
    simp only [Q,queryTotalSquare,dot,pow_two]
  have hY : MemLp Y 2 μ := by
    apply hQ.mono hYm.aestronglyMeasurable
    apply ae_of_all
    intro u
    have hy := queryRemovedSquare_nonneg (r+K : ℕ) hnR.le (E u) (T u)
    have hle := queryRemovedSquare_le_total (r+K : ℕ) hnR (E u) (T u) (hE u)
    simpa only [Y,Q,Real.norm_eq_abs,abs_of_nonneg hy,abs_of_nonneg (hy.trans hle)] using hle
  refine ⟨hY,hY.integrable_sq,?_⟩
  have he : (∫ u, Q u ∂μ) = 1 := by
    change (∫ u, ((r+K : ℕ) : ℝ)⁻¹*dot (T u) (T u) ∂μ) = 1
    simpa only [dot,pow_two] using N9b.sourceTargets_norm_mean W β hβ δ hδ r K hn e
  rw [← he]
  exact integral_mono_ae (hY.integrable (by norm_num)) (hQ.integrable (by norm_num))
    (ae_of_all _ fun u => queryRemovedSquare_le_total (r+K : ℕ) hnR (E u) (T u) (hE u))

end SKConstants.Completion.N9c
