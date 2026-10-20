module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.N20.Scalar

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators unitInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SKConstants.N20
open SKConstantsOAI.ZeroTemperatureSK Blueprint GaussianProposal

variable {Ω : Type} [MeasurableSpace Ω]
local instance replayScalarLaw_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem measurable_rowMap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (n : ℕ) (f : A → B) (hf : Measurable f) :
    Measurable (fun z : Fin n → A => fun i => f (z i)) :=
  Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i))

theorem measurable_thresholdErrors (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → I) =>
      fun i => thresholdError (z.1 i) (z.2 i)) := by
  apply Measurable.of_eval
  intro i
  have hp : Measurable (fun z : (Fin n → ℝ) × (Fin n → I) => (z.1 i, z.2 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  exact measurable_thresholdError.comp hp

def replayMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (S : ℝ≥0) (v : M1.ReplayInput δ r₀ q) : Fin (r₀ + q) → ℝ :=
  fun i => actualParisiFullMagnetization β S
    (actualParisiGrowingReplayField W β hβ δ r₀ q S v i)

theorem measurable_replayMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (S : ℝ≥0) :
    Measurable (replayMean W β hβ δ r₀ q S) := by
  have hm : Measurable (actualParisiFullMagnetization β (S : ℝ)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact Measurable.of_eval (fun i => hm.comp
    ((measurable_pi_apply i).comp (M1.measurable_ReplayField W β hβ δ r₀ q S)))

theorem linked_spin_mean_law (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r₀ q : ℕ) (hr : 0 < r₀) (S : ℝ≥0) (hS : S ≤ M1.Horizon δ q) :
    (M1.ReplayLinkedLaw W β hβ δ r₀ q).map
      (fun u => fun i => (u.1 i, replayMean W β hβ δ r₀ q S u.2 i)) =
    Measure.pi (fun _ : Fin (r₀ + q) =>
      (actualParisiFullTerminalSpinLaw β W (M1.Horizon δ q)).map
        (fun b => (b.1, actualParisiFullPosteriorMean W β S b.2))) := by
  let F : Bool × (Iic (M1.Horizon δ q) → ℝ) → Bool × ℝ :=
    fun z => (z.1, actualParisiFullMagnetization β S (z.2 ⟨S, hS⟩))
  have hm : Measurable (actualParisiFullMagnetization β (S : ℝ)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hF : Measurable F := measurable_fst.prodMk
    (hm.comp ((measurable_pi_apply (⟨S, hS⟩ : Iic (M1.Horizon δ q))).comp measurable_snd))
  have hRows : Measurable (fun u : (Fin (r₀ + q) → Bool) × M1.ReplayInput δ r₀ q =>
      fun i => (u.1 i, fun t : Iic (M1.Horizon δ q) =>
        actualParisiGrowingReplayField W β hβ δ r₀ q t.1 u.2 i)) := by
    refine Measurable.of_eval (fun i => ?_)
    refine ((measurable_pi_apply i).comp measurable_fst).prodMk ?_
    exact Measurable.of_eval (fun t => ((measurable_pi_apply i).comp
      (M1.measurable_ReplayField W β hβ δ r₀ q t.1)).comp measurable_snd)
  have hModel : Measurable (fun b : Bool × Ω =>
      (b.1, fun t : Iic (M1.Horizon δ q) => actualParisiFullScalarProcess W β t.1 b.2)) := by
    exact measurable_fst.prodMk (Measurable.of_eval (fun t =>
      ((actualParisiFullScalarDrift β).solution_measurable W t.1).comp measurable_snd))
  have he := congrArg (fun μ => μ.map (fun z => fun i : Fin (r₀ + q) => F (z i)))
    (hRow W β hβ δ hδ r₀ q hr)
  rw [Measure.map_map (measurable_rowMap (r₀ + q) F hF) hRows,
    Measure.pi_map_pi (fun _ => hF.aemeasurable)] at he
  simpa only [Measure.map_map hF hModel, Function.comp_def, F, replayMean,
    actualParisiFullPosteriorMean] using he

theorem replay_mean_law (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r₀ q : ℕ) (hr : 0 < r₀) (S : ℝ≥0) (hS : S ≤ M1.Horizon δ q) :
    (M1.ReplayLaw W δ r₀ q).map (replayMean W β hβ δ r₀ q S) =
      Measure.pi (fun _ : Fin (r₀ + q) => W.law.map (actualParisiFullPosteriorMean W β S)) := by
  have hM := measurable_replayMean W β hβ δ r₀ q S
  have hB : Measurable (fun b : Bool × Ω => (b.1, actualParisiFullPosteriorMean W β S b.2)) :=
    measurable_fst.prodMk ((measurable_actualParisiFullPosteriorMean W β S).comp measurable_snd)
  have hSM : Measurable (fun u : (Fin (r₀ + q) → Bool) × M1.ReplayInput δ r₀ q =>
      fun i => (u.1 i, replayMean W β hβ δ r₀ q S u.2 i)) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp hM).comp measurable_snd))
  have he := congrArg (fun μ => μ.map (fun z => fun i : Fin (r₀ + q) => (z i).2))
    (linked_spin_mean_law hRow W β hβ δ hδ r₀ q hr S hS)
  rw [Measure.map_map (measurable_rowMap (r₀ + q) (Prod.snd : Bool × ℝ → ℝ) measurable_snd) hSM,
    Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)] at he
  have hleft : (M1.ReplayLinkedLaw W β hβ δ r₀ q).map
      (fun u => replayMean W β hβ δ r₀ q S u.2) =
      (M1.ReplayLaw W δ r₀ q).map (replayMean W β hβ δ r₀ q S) := by
    rw [← M1.replayLinkedLaw_base_marginal W β hβ δ r₀ q, Measure.map_map hM measurable_snd]
    rfl
  have hright : ((actualParisiFullTerminalSpinLaw β W (M1.Horizon δ q)).map
      (fun b => (b.1, actualParisiFullPosteriorMean W β S b.2))).map Prod.snd =
      W.law.map (actualParisiFullPosteriorMean W β S) := by
    rw [Measure.map_map measurable_snd hB,
      ← actualParisiFullTerminalSpinLaw_path_marginal β W (M1.Horizon δ q),
      Measure.map_map (measurable_actualParisiFullPosteriorMean W β S) measurable_snd]
    rfl
  simpa only [Function.comp_def, hleft, hright] using he

theorem replay_fine_errors_law (hLink : ThresholdLinkStatement) (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r₀ q : ℕ) (hr : 0 < r₀) (S : ℝ≥0) (hS : S ≤ M1.Horizon δ q) :
    ((M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q))).map
      (fun z => fun i => (scalarHiddenSign
        (thresholdSpin (replayMean W β hβ δ r₀ q (M1.Horizon δ q) z.1) z.2 i) -
        replayMean W β hβ δ r₀ q S z.1 i) ^ 2) =
    (actualParisiTerminalSpinRowsLaw W β (M1.Horizon δ q) (r₀ + q)).map
      (fun z => fun i => actualParisiPinningError W β S (z i)) := by
  let E : Bool × ℝ → ℝ := fun z => (scalarHiddenSign z.1 - z.2) ^ 2
  have hE : Measurable E :=
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub measurable_snd).pow_const 2
  have hM := measurable_replayMean W β hβ δ r₀ q S
  have hSM : Measurable (fun u : (Fin (r₀ + q) → Bool) × M1.ReplayInput δ r₀ q =>
      fun i => (u.1 i, replayMean W β hβ δ r₀ q S u.2 i)) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp hM).comp measurable_snd))
  have hLinkMap : Measurable (fun z : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) =>
      (thresholdSpin (replayMean W β hβ δ r₀ q (M1.Horizon δ q) z.1) z.2, z.1)) :=
    ((measurable_thresholdSpin _).comp
      (((measurable_replayMean W β hβ δ r₀ q _).comp measurable_fst).prodMk
        measurable_snd)).prodMk measurable_fst
  have hB : Measurable (fun b : Bool × Ω => (b.1, actualParisiFullPosteriorMean W β S b.2)) :=
    measurable_fst.prodMk ((measurable_actualParisiFullPosteriorMean W β S).comp measurable_snd)
  have he := congrArg (fun μ => μ.map (fun z => fun i : Fin (r₀ + q) => E (z i)))
    (linked_spin_mean_law hRow W β hβ δ hδ r₀ q hr S hS)
  rw [Measure.map_map (measurable_rowMap (r₀ + q) E hE) hSM,
    Measure.pi_map_pi (fun _ => hE.aemeasurable)] at he
  rw [Measure.map_map hE hB] at he
  have hErr : Measurable (fun u : (Fin (r₀ + q) → Bool) × M1.ReplayInput δ r₀ q =>
      fun i => (scalarHiddenSign (u.1 i) - replayMean W β hβ δ r₀ q S u.2 i) ^ 2) :=
    Measurable.of_eval (fun i =>
      (((measurable_of_finite scalarHiddenSign).comp
        ((measurable_pi_apply i).comp measurable_fst)).sub
        (((measurable_pi_apply i).comp hM).comp measurable_snd)).pow_const 2)
  have hL := hLink W β hβ δ r₀ q
  change ((M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q))).map
    (fun z => (thresholdSpin (replayMean W β hβ δ r₀ q (M1.Horizon δ q) z.1) z.2, z.1)) =
      M1.ReplayLinkedLaw W β hβ δ r₀ q at hL
  simp only [Function.comp_def, E] at he
  rw [← hL, Measure.map_map hErr hLinkMap] at he
  unfold actualParisiTerminalSpinRowsLaw
  rw [Measure.pi_map_pi
    (μ := fun _ : Fin (r₀ + q) => actualParisiFullTerminalSpinLaw β W (M1.Horizon δ q))
    (f := fun _ => actualParisiPinningError W β S)
    (fun _ => (measurable_actualParisiPinningError W β S).aemeasurable)]
  unfold actualParisiPinningError
  simpa only [Function.comp_def, E] using he

theorem iid_threshold_errors_map {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (m : A → ℝ) (hm : Measurable m) (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => μ.map m)).prod (thresholdLaw n)).map
      (fun z => fun i => thresholdError (z.1 i) (z.2 i)) =
    (Measure.pi (fun _ : Fin n => μ.prod (volume : Measure I))).map
      (fun z => fun i => thresholdError (m (z i).1) (z i).2) := by
  have hmV : Measurable (fun z : Fin n → A => fun i => m (z i)) :=
    Measurable.of_eval (fun i => hm.comp (measurable_pi_apply i))
  have hE := measurable_thresholdErrors n
  have hp : (Measure.pi (fun _ : Fin n => μ.map m)).prod (thresholdLaw n) =
      ((Measure.pi (fun _ : Fin n => μ)).prod (thresholdLaw n)).map
        (Prod.map (fun z : Fin n → A => fun i => m (z i)) id) := by
    rw [← Measure.pi_map_pi (fun _ => hm.aemeasurable)]
    simpa only [Measure.map_id] using Measure.map_prod_map
      (Measure.pi (fun _ : Fin n => μ)) (thresholdLaw n) hmV measurable_id
  rw [hp, Measure.map_map hE (hmV.prodMap measurable_id)]
  have ha := (measurePreserving_arrowProdEquivProdArrow A I (Fin n)
    (fun _ => μ) (fun _ => (volume : Measure I))).map_eq
  rw [← ha, Measure.map_map (hE.comp (hmV.prodMap measurable_id))
    (MeasurableEquiv.arrowProdEquivProdArrow A I (Fin n)).measurable]
  rfl

theorem replay_coarse_errors_law (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r₀ q : ℕ) (hr : 0 < r₀) (S : ℝ≥0) (hS : S ≤ M1.Horizon δ q) :
    ((M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q))).map
      (fun z => fun i => thresholdError (replayMean W β hβ δ r₀ q S z.1 i) (z.2 i)) =
    (Measure.pi (fun _ : Fin (r₀ + q) => W.law.prod (volume : Measure I))).map
      (fun z => fun i => scalarThresholdError W β S (z i)) := by
  have hM := measurable_replayMean W β hβ δ r₀ q S
  have hE := measurable_thresholdErrors (r₀ + q)
  calc
    _ = (((M1.ReplayLaw W δ r₀ q).map (replayMean W β hβ δ r₀ q S)).prod
        (thresholdLaw (r₀ + q))).map (fun z => fun i => thresholdError (z.1 i) (z.2 i)) := by
      have hp : ((M1.ReplayLaw W δ r₀ q).map (replayMean W β hβ δ r₀ q S)).prod
          (thresholdLaw (r₀ + q)) = ((M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q))).map
            (Prod.map (replayMean W β hβ δ r₀ q S) id) := by
        simpa only [Measure.map_id] using Measure.map_prod_map
          (M1.ReplayLaw W δ r₀ q) (thresholdLaw (r₀ + q)) hM measurable_id
      rw [hp, Measure.map_map hE (hM.prodMap measurable_id)]
      rfl
    _ = _ := by
      rw [replay_mean_law hRow W β hβ δ hδ r₀ q hr S hS]
      exact iid_threshold_errors_map W.law (actualParisiFullPosteriorMean W β S)
        (measurable_actualParisiFullPosteriorMean W β S) (r₀ + q)

end SKConstants.N20
