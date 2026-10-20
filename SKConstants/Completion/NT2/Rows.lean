module

public import SKConstants.Completion.T0.All
public import SKConstants.Completion.N13g.RowAttachment

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.NT2
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 N13A LGram LC4a LM3

variable {Ω : Type} [MeasurableSpace Ω]

theorem hasLaw_reindex {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {m n : ℕ} (h : m = n)
    {f : X → Fin m → Y} (hf : HasLaw f (Measure.pi fun _ : Fin m => ν) μ) :
    HasLaw (fun x i => f x (Fin.cast h.symm i)) (Measure.pi fun _ : Fin n => ν) μ := by
  subst n
  simpa only [Fin.cast_refl, id_eq] using hf

def sharpHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    Fin n → M1.ScalarDriverHistory (coarseTime p n) :=
  fun i => M1.ReplayHistories W β hβ (coarseMesh p n) (coarseRank p n)
    (coarseCount p n) (T0.sharpToReplay p n y)
      (Fin.cast (rankCount_add p.a p.b n).symm i)

theorem measurable_sharpHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sharpHistories W β hβ p n) :=
  Measurable.of_eval fun i =>
    (measurable_pi_apply (Fin.cast (rankCount_add p.a p.b n).symm i)).comp
    ((M1.measurable_ReplayHistories W β hβ _ _ _).comp (T0.measurable_sharpToReplay p n))

theorem sharpHistories_linked_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    HasLaw (sharpHistories W β hβ p n)
      (Measure.pi fun _ : Fin n => N13t.fullHistoryLinkedLaw W W β hβ (coarseTime p n))
      (sharpLinkedLaw W β hβ p n) :=
  hasLaw_reindex (rankCount_add p.a p.b n)
    (T0.sharpFullHistories_linked_hasLaw W β hβ p n hn)

theorem sharpHistories_unlinked_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    HasLaw (sharpHistories W β hβ p n)
      (Measure.pi fun _ : Fin n => N13t.fullHistoryBaseLaw W W β hβ (coarseTime p n))
      (sharpUnlinkedLaw W p n) :=
  hasLaw_reindex (rankCount_add p.a p.b n)
    (T0.sharpFullHistories_unlinked_hasLaw W β hβ p n hn)

theorem replayRows_eq_historyRows_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hN : 0 < r + q) :
    ∀ᵐ u ∂M1.ReplayLinkedLaw W β hβ δ r q,
      N13g.statisticsRows (N13g.replayStatistics W β hβ δ r q u) =
        fun i => NDH.historyMixedRow W β δ q (M1.ReplayHistories W β hβ δ r q u i) := by
  let G := fun u : Spin (r + q) × M1.SourceInput δ r q =>
    (u.1, M1.ToReplay W β hβ δ r q u.2)
  have hG : Measurable G :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r q).comp measurable_snd)
  have hmap : (M1.SourceLinkedLaw W β hβ δ r q).map G =
      M1.ReplayLinkedLaw W β hβ δ r q :=
    M1.growingSource_toReplay_linked_law W β hβ δ r q hN
  have hm : Measurable (fun u : Spin (r + q) × M1.ReplayInput δ r q =>
      fun i => NDH.historyMixedRow W β δ q (M1.ReplayHistories W β hβ δ r q u i)) :=
    Measurable.of_eval fun i => (NDH.measurable_historyMixedRow W β δ q).comp
      ((measurable_pi_apply i).comp (M1.measurable_ReplayHistories W β hβ δ r q))
  rw [← hmap]
  apply (ae_map_iff hG.aemeasurable (measurableSet_eq_fun
    ((N13g.measurable_statisticsRows δ r q).comp
      (N13g.measurable_replayStatistics W β hβ δ r q)) hm)).mpr
  apply Eventually.of_forall
  intro u
  change (N13g.statisticsRows ∘ N13g.replayStatistics W β hβ δ r q ∘ G) u = _
  rw [N13g.replayStatistics_toReplay W β hβ δ r q hN]
  dsimp only [Function.comp_apply]
  rw [N13g.sourceStatistics_rows, NDH.literalSourceRows_eq_historyMixedRows W β hβ δ hδ r q]
  have hh := congrFun (M1.replayHistories_toReplay W β hβ δ r q hN) u
  change _ = fun i => NDH.historyMixedRow W β δ q ((M1.ReplayHistories W β hβ δ r q ∘ G) u i)
  rw [hh]
  rfl

theorem sharpRows_eq_historyRows_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ y ∂sharpLinkedLaw W β hβ p n,
      sharpRows W β hβ p n y =
        fun i => NDH.historyMixedRow W β (coarseMesh p n) (coarseCount p n)
          (sharpHistories W β hβ p n y i) := by
  have h := replayRows_eq_historyRows_ae W β hβ (coarseMesh p n)
    (paperGrowingQueryMeshSize_pos p.a n hn) (coarseRank p n) (coarseCount p n)
    (by simpa only [coarseRank, coarseCount, rankCount_add] using hn)
  have hh := ae_of_ae_map (T0.measurable_sharpToReplay p n).aemeasurable
    ((T0.sharpToReplay_linked_law W β hβ p n).symm ▸ h)
  filter_upwards [hh] with y hy
  funext i
  have hi := congrFun hy (Fin.cast (rankCount_add p.a p.b n).symm i)
  simpa only [sharpRows, N13g.statisticsRows, N13g.replayStatistics,
    T0.sharpToReplay, Fin.cast_cast, Fin.cast_refl, id_eq, sharpHistories] using hi

theorem historyRows_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q N : ℕ) :
    HasLaw (fun a : Fin N → M1.ScalarDriverHistory (M1.Horizon δ q) =>
      fun i => NDH.historyMixedRow W β δ q (a i))
      (mixedVectorRowsLaw W W β hβ (growingQueryTime δ)
        (fun j => growingQueryTime δ (j + 1)) q (M1.Horizon δ q) N)
      (Measure.pi fun _ : Fin N => N13t.fullHistoryLinkedLaw W W β hβ (M1.Horizon δ q)) := by
  refine ⟨(Measurable.of_eval fun i =>
    (NDH.measurable_historyMixedRow W β δ q).comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  rw [Measure.pi_map_pi (fun _ => (NDH.measurable_historyMixedRow W β δ q).aemeasurable)]
  have hrow : (N13t.fullHistoryLinkedLaw W W β hβ (M1.Horizon δ q)).map
      (NDH.historyMixedRow W β δ q) =
      (actualParisiFullQuerySpinLaw W W β (M1.Horizon δ q)).map
        (actualParisiFullMixedRow W W β hβ (growingQueryTime δ)
          (fun j => growingQueryTime δ (j + 1)) q) := by
    rw [N13t.fullHistoryLinkedLaw, Measure.map_map (NDH.measurable_historyMixedRow W β δ q)
      (N13t.measurable_modelFullHistory W W β hβ _)]
    exact Measure.map_congr (NDH.historyMixedRow_model_ae W β hβ δ hδ q)
  rw [hrow]
  exact (Measure.pi_map_pi (fun _ =>
    (measurable_actualParisiFullMixedRow W W β hβ (growingQueryTime δ)
      (fun j => growingQueryTime δ (j + 1)) q).aemeasurable)).symm

theorem sharpRows_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    HasLaw (sharpRows W β hβ p n) (canonicalArrayLaw W β hβ p n)
      (sharpLinkedLaw W β hβ p n) := by
  have h := (historyRows_hasLaw W β hβ (coarseMesh p n)
    (paperGrowingQueryMeshSize_pos p.a n hn) (coarseCount p n) n).comp
      (sharpHistories_linked_hasLaw W β hβ p n hn)
  exact h.congr (sharpRows_eq_historyRows_ae W β hβ p n hn)

end SKConstants.Completion.NT2
