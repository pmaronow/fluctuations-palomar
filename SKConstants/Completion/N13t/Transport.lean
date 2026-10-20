module

public import SKConstants.Completion.N13t.Integrals

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 Blueprint4

variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualRowLinked_absolutelyContinuous (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) : actualParisiFullQuerySpinLaw W Z β V ≪ LM4.actualRowBaseLaw W Z := by
  rw [← LM4.actual_linkedRowLaw_eq β W Z V]
  exact withDensity_absolutelyContinuous _ _

theorem measurable_fullHistoryInformation (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (J : M1.ScalarDriverHistory V → ℝ) (hJm : Measurable J) :
    Measurable (fullHistoryInformation W β V J) :=
  (((measurable_historyLinkDensity β V).comp
    (measurable_observationDProjection V)).log.sub hJm).add
      (((measurable_historyDBracket W β V).comp
        (measurable_observationDProjection V)).div_const 2)

theorem fullHistoryInformation_model_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (J : M1.ScalarDriverHistory V → ℝ) :
    (fun u => fullHistoryInformation W β V J (modelFullHistory W Z β hβ V u)) =ᵐ[
      actualParisiFullQuerySpinLaw W Z β V]
      rowInformationV W β V (J ∘ modelFullHistory W Z β hβ V) := by
  have hac := actualRowLinked_absolutelyContinuous W Z β V
  filter_upwards [hac.ae_le (modelFullHistory_version W Z β hβ V),
    hac.ae_le (fullHistoryDBracket_model_ae W Z β hβ V)] with u hu hb
  change Real.log (actualParisiSpinLinkDensity β u.1.1 V
      ((modelFullHistory W Z β hβ V u).2.1 ⟨V, V.coe_nonneg, le_rfl⟩)) -
      J (modelFullHistory W Z β hβ V u) +
      fullHistoryDBracket W β V (modelFullHistory W Z β hβ V u) / 2 = _
  rw [(hu ⟨V, V.coe_nonneg, le_rfl⟩).1, hb]
  rfl

theorem modelFullHistories_linked_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (n : ℕ) :
    HasLaw (fun ω : Fin n → (Bool × Ω) × A => fun i => modelFullHistory W Z β hβ V (ω i))
      (Measure.pi fun _ : Fin n => fullHistoryLinkedLaw W Z β hβ V)
      (Measure.pi fun _ : Fin n => actualParisiFullQuerySpinLaw W Z β V) := by
  refine ⟨(Measurable.of_eval fun i =>
    (measurable_modelFullHistory W Z β hβ V).comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  exact Measure.pi_map_pi (fun _ => (measurable_modelFullHistory W Z β hβ V).aemeasurable)

theorem replay_average_identDistrib
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (Fh : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ) (hFm : Measurable Fh)
    (F : (Bool × Ω) × Ω → ℝ)
    (hF : (fun u => Fh (modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q) u))
      =ᵐ[actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)] F) :
    IdentDistrib
      (fun u => (∑ i, Fh (replayFullHistories W β hβ δ r q u i)) / (r + q : ℕ))
      (fun ω : Fin (r + q) → (Bool × Ω) × Ω => (∑ i, F (ω i)) / (r + q : ℕ))
      (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q))
      (Measure.pi fun _ : Fin (r + q) =>
        actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)) := by
  let H := scalarGrowingSourceHorizon δ q
  let T : (Fin (r + q) → (Bool × Ω) × Ω) → Fin (r + q) → M1.ScalarDriverHistory H :=
    fun ω i => modelFullHistory W W β hβ H (ω i)
  let S : (Fin (r + q) → M1.ScalarDriverHistory H) → ℝ :=
    fun ω => (∑ i, Fh (ω i)) / (r + q : ℕ)
  have hTm : Measurable T := Measurable.of_eval fun i =>
    (measurable_modelFullHistory W W β hβ H).comp (measurable_pi_apply i)
  have hSm : Measurable S := (Finset.measurable_fun_sum _ fun i _ =>
    hFm.comp (measurable_pi_apply i)).div_const _
  have hR : HasLaw (replayFullHistories W β hβ δ r q)
      (Measure.pi fun _ : Fin (r + q) => fullHistoryLinkedLaw W W β hβ H)
      (growingReplayLinkedLaw W β hβ δ r q H) :=
    ⟨(measurable_replayFullHistories W β hβ δ r q).aemeasurable, h.2⟩
  have hT := modelFullHistories_linked_hasLaw W W β hβ H (r + q)
  have hpi : ∀ᵐ ω ∂(Measure.pi fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β H),
      ∀ i, Fh (T ω i) = F (ω i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β H) i).ae hF
  have hae : (S ∘ T) =ᵐ[Measure.pi fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β H]
      fun ω => (∑ i, F (ω i)) / (r + q : ℕ) := by
    filter_upwards [hpi] with ω hω
    apply congrArg (fun s : ℝ => s / (r + q : ℕ))
    exact Finset.sum_congr rfl (fun i _ => hω i)
  exact ((hR.identDistrib hT).comp hSm).trans
    (IdentDistrib.of_ae_eq (hSm.comp hTm).aemeasurable hae)

theorem replayInformation_sub_finiteRow_identDistrib
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (J : ObservationDHistory (scalarGrowingSourceHorizon δ q) → ℝ) (hJm : Measurable J)
    (hJ : IsHistoryDIntegral W β hβ (scalarGrowingSourceHorizon δ q) J)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I) :
    IdentDistrib
      (fun u => (growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I u -
        β * ∑ i, finiteHistoryRow W β (scalarGrowingSourceHorizon δ q) (growingQueryTime δ) q
          (replayFullHistories W β hβ δ r q u i)) / (r + q : ℕ))
      (fun ω : Fin (r + q) → (Bool × Ω) × Ω =>
        (∑ i, (rowInformationV W β (scalarGrowingSourceHorizon δ q)
            (J ∘ modelObservationDHistory W β hβ (scalarGrowingSourceHorizon δ q)) (ω i) -
          β * LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q (ω i))) / (r + q : ℕ))
      (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q))
      (Measure.pi fun _ : Fin (r + q) =>
        actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)) := by
  let H := scalarGrowingSourceHorizon δ q
  let Jf := J ∘ observationDProjection H
  let μ := growingReplayLinkedLaw W β hβ δ r q H
  let ν := Measure.pi fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β H
  let R := replayFullHistories W β hβ δ r q
  let T : (Fin (r + q) → (Bool × Ω) × Ω) → Fin (r + q) → M1.ScalarDriverHistory H :=
    fun ω i => modelFullHistory W W β hβ H (ω i)
  let S : (Fin (r + q) → M1.ScalarDriverHistory H) → ℝ := fun ω =>
    (∑ i, (fullHistoryInformation W β H Jf (ω i) -
      β * finiteHistoryRow W β H (growingQueryTime δ) q (ω i))) / (r + q : ℕ)
  have hRm : Measurable R := measurable_replayFullHistories W β hβ δ r q
  have hTm : Measurable T := Measurable.of_eval fun i =>
    (measurable_modelFullHistory W W β hβ H).comp (measurable_pi_apply i)
  have hSm : Measurable S :=
    (Finset.measurable_fun_sum _ fun i _ =>
      ((measurable_fullHistoryInformation W β H Jf
        (hJm.comp (measurable_observationDProjection H))).sub
        ((measurable_finiteHistoryRow W β H (growingQueryTime δ) q).const_mul β)).comp
          (measurable_pi_apply i)).div_const _
  have hR : HasLaw R (Measure.pi fun _ : Fin (r + q) => fullHistoryLinkedLaw W W β hβ H) μ :=
    ⟨hRm.aemeasurable, h.2⟩
  have hT := modelFullHistories_linked_hasLaw W W β hβ H (r + q)
  have hrep : (S ∘ R) =ᵐ[μ]
      fun u => (growingReplayInformation W β hβ δ hδ r q H I u -
        β * ∑ i, finiteHistoryRow W β H (growingQueryTime δ) q (R u i)) / (r + q : ℕ) := by
    filter_upwards [growingReplayInformation_eq_fullHistory_sum_ae W β hβ δ hδ r q h J hJ I hI]
      with u hu
    dsimp only [S, Function.comp_apply]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hu]
  have hrow : ∀ᵐ ω ∂ν, ∀ i,
      fullHistoryInformation W β H Jf (T ω i) =
        rowInformationV W β H (J ∘ modelObservationDHistory W β hβ H) (ω i) ∧
      finiteHistoryRow W β H (growingQueryTime δ) q (T ω i) =
        LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q (ω i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β H) i).ae
      ((fullHistoryInformation_model_ae W W β hβ H Jf).and
      ((actualRowLinked_absolutelyContinuous W W β H).ae_le
        (finiteHistoryRow_model_ae W W β hβ H (growingQueryTime δ)
          (growingQueryTime_strictMono δ hδ).monotone q le_rfl)))
  have hmodel : (S ∘ T) =ᵐ[ν]
      fun ω => (∑ i, (rowInformationV W β H
          (J ∘ modelObservationDHistory W β hβ H) (ω i) -
        β * LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q (ω i))) / (r + q : ℕ) := by
    filter_upwards [hrow] with ω hω
    apply congrArg (fun s : ℝ => s / (r + q : ℕ))
    apply Finset.sum_congr rfl
    intro i _
    rw [(hω i).1, (hω i).2]
  exact (IdentDistrib.of_ae_eq (hSm.comp hRm).aemeasurable hrep).symm.trans
    (((hR.identDistrib hT).comp hSm).trans
      (IdentDistrib.of_ae_eq (hSm.comp hTm).aemeasurable hmodel))

end SKConstants.Completion.N13t
