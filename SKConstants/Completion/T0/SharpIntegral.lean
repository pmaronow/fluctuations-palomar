module

public import SKConstants.Completion.T0.Node
public import SKConstants.Completion.N13A.Regularity
public import SKConstants.Completion.N19.Transport
public import SKConstants.Completion.NReplay.InputLaw

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.T0
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC4a LM3 Blueprint Blueprint4 N13A

variable {Ω : Type} [MeasurableSpace Ω]

def sharpToReplay (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    Spin (coarseRank p n + coarseCount p n) ×
      M1.ReplayInput (coarseMesh p n) (coarseRank p n) (coarseCount p n) :=
  (fun i => y.1 (Fin.cast (rankCount_add p.a p.b n) i), sharpReplayInput p n y)

theorem measurable_sharpToReplay (p : Parameters) (n : ℕ) :
    Measurable (sharpToReplay p n) :=
  (Measurable.of_eval fun i =>
    (measurable_pi_apply (Fin.cast (rankCount_add p.a p.b n) i)).comp measurable_fst).prodMk
    (measurable_sharpReplayInput p n)

theorem sharpToReplay_unlinked_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    (sharpUnlinkedLaw W p n).map (sharpToReplay p n) =
      (M1.spinPrior (coarseRank p n + coarseCount p n)).prod
        (M1.ReplayLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)) := by
  let f : Prim n × N13a.CoarseAux p n →
      M1.ReplayInput (coarseMesh p n) (coarseRank p n) (coarseCount p n) :=
    fun y => replayInput (castMatrix (rankCount_add p.a p.b n) (physical n y.1)) y.2
  have hf : Measurable f := (measurable_sharpReplayInput p n).comp
    ((measurable_const (a := (fun _ : Fin n => false))).prodMk measurable_id)
  have hfl := N19.cast_replayInput_law
    (fun _ _ _ _ => NReplay.replayInput_law _ _ _ _)
    W (coarseMesh p n) (coarseRank p n) (coarseCount p n) n (rankCount_add p.a p.b n)
  have hs : ∀ (N n : ℕ) (h : N = n),
      (uniformSpinLaw n).map (fun x i => x (Fin.cast h i)) = M1.spinPrior N := by
    intro N n h
    subst n
    change (uniformSpinLaw N).map id = _
    rw [Measure.map_id]
    exact (spinPrior_eq_uniformSpinLaw N).symm
  have hsm : Measurable (fun x : Spin n => fun i => x (Fin.cast (rankCount_add p.a p.b n) i)) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  change ((uniformSpinLaw n).prod ((primLaw n).prod
    (replayAuxLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)))).map
      (Prod.map (fun x i => x (Fin.cast (rankCount_add p.a p.b n) i)) f) = _
  rw [← Measure.map_prod_map _ _ hsm hf, hs, hfl]

theorem sharpLink_eq_path (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    sharpLink W β hβ p n y =
      M1.TerminalDensity β (coarseTime p n)
        (actualParisiGrowingReplayField W β hβ (coarseMesh p n)
          (coarseRank p n) (coarseCount p n) (coarseTime p n)) (sharpToReplay p n y) := by
  unfold sharpLink M1.TerminalDensity
  rw [← (finCongr (rankCount_add p.a p.b n)).prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rfl

theorem sharpToReplay_linked_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :
    (sharpLinkedLaw W β hβ p n).map (sharpToReplay p n) =
      M1.ReplayLinkedLaw W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) := by
  let g := fun u => ENNReal.ofReal (M1.TerminalDensity β (coarseTime p n)
    (actualParisiGrowingReplayField W β hβ (coarseMesh p n)
      (coarseRank p n) (coarseCount p n) (coarseTime p n)) u)
  have hg : Measurable g := (M1.measurable_terminalDensity _ _ _
    (M1.measurable_ReplayField W β hβ _ _ _ _)).ennreal_ofReal
  have he : (fun y => ENNReal.ofReal (sharpLink W β hβ p n y)) = g ∘ sharpToReplay p n := by
    funext y
    exact congrArg ENNReal.ofReal (sharpLink_eq_path W β hβ p n y)
  change ((sharpUnlinkedLaw W p n).withDensity _).map (sharpToReplay p n) = _
  rw [he, map_withDensity_comp _ _ (measurable_sharpToReplay p n) _ hg,
    sharpToReplay_unlinked_law W p n]
  rfl

theorem sharpFullHistories_unlinked_hasLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (hn : 0 < n) :
    HasLaw (M1.ReplayHistories W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) ∘
      sharpToReplay p n)
      (Measure.pi fun _ : Fin (coarseRank p n + coarseCount p n) =>
        N13t.fullHistoryBaseLaw W W β hβ (coarseTime p n))
      (sharpUnlinkedLaw W p n) := by
  have hm := M1.measurable_ReplayHistories W β hβ (coarseMesh p n)
    (coarseRank p n) (coarseCount p n)
  refine ⟨(hm.comp (measurable_sharpToReplay p n)).aemeasurable, ?_⟩
  rw [← Measure.map_map hm (measurable_sharpToReplay p n), sharpToReplay_unlinked_law W p n]
  exact NDH.literal_unlinked_replay_full_histories_law W β hβ (coarseMesh p n)
    (paperGrowingQueryMeshSize_pos p.a n hn) (coarseRank p n) (coarseCount p n)
    (by simpa only [coarseRank, coarseCount, rankCount_add] using hn)

theorem sharpFullHistories_linked_hasLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (hn : 0 < n) :
    HasLaw (M1.ReplayHistories W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) ∘
      sharpToReplay p n)
      (Measure.pi fun _ : Fin (coarseRank p n + coarseCount p n) =>
        N13t.fullHistoryLinkedLaw W W β hβ (coarseTime p n))
      (sharpLinkedLaw W β hβ p n) := by
  have hm := M1.measurable_ReplayHistories W β hβ (coarseMesh p n)
    (coarseRank p n) (coarseCount p n)
  refine ⟨(hm.comp (measurable_sharpToReplay p n)).aemeasurable, ?_⟩
  rw [← Measure.map_map hm (measurable_sharpToReplay p n), sharpToReplay_linked_law W β hβ p n]
  exact NDH.literal_linked_replay_full_histories_law W β hβ (coarseMesh p n)
    (paperGrowingQueryMeshSize_pos p.a n hn) (coarseRank p n) (coarseCount p n)
    (by simpa only [coarseRank, coarseCount, rankCount_add] using hn)

def replayPathDLeftSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q l : ℕ)
    (u : Spin (r + q) × M1.ReplayInput δ r q) : ℝ :=
  ∑ i, N13t.fullHistoryDLeftSum W β (scalarGrowingSourceHorizon δ q) l
    (M1.ReplayHistories W β hβ δ r q u i)

theorem measurable_replayPathDLeftSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q l : ℕ) : Measurable (replayPathDLeftSum W β hβ δ r q l) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact (N13t.measurable_fullHistoryDLeftSum W β _ l).comp
    ((measurable_pi_apply i).comp (M1.measurable_ReplayHistories W β hβ δ r q))

theorem growingReplayDLeftSum_eq_path_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q l : ℕ) :
    growingReplayDLeftSum W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) l =ᵐ[
      growingReplayUnlinkedLaw W δ r q]
        fun u => replayPathDLeftSum W β hβ δ r q l (M1.RawToReplay W δ r q u) := by
  filter_upwards [growingReplayDLeftSum_eq_history_sum_ae W β hβ δ hδ r q
    (scalarGrowingSourceHorizon δ q) le_rfl l] with u hu
  rw [hu]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (historyDLeftSum W β (scalarGrowingSourceHorizon δ q) l)
    (N13t.replayFullHistories_observationD W β hβ δ r q u i).symm

theorem replayPathDIntegral_exists (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) :
    ∃ J, N13t.IsL2Limit ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q))
      (replayPathDLeftSum W β hβ δ r q) J := by
  obtain ⟨I₀, hI₀, _, _, _, _, _⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q)
  obtain ⟨I, hm, hI, -⟩ := N13t.growingReplayDIntegral_measurable_version
    W β hβ δ hδ r q _ I₀ hI₀
  have hlim : N13t.IsL2Limit (growingReplayUnlinkedLaw W δ r q)
      (growingReplayDLeftSum W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q)) I :=
    ⟨hm, hI⟩
  have hlaw : HasLaw (M1.RawToReplay W δ r q)
      ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q))
      (growingReplayUnlinkedLaw W δ r q) :=
    ⟨(M1.measurable_RawToReplay W δ r q).aemeasurable,
      M1.rawToReplay_unlinked_law W δ r q⟩
  exact N13t.exists_isL2Limit_of_hasLaw hlaw (replayPathDLeftSum W β hβ δ r q)
    (measurable_replayPathDLeftSum W β hβ δ r q) I
    (hlim.congr_sums (growingReplayDLeftSum_eq_path_ae W β hβ δ hδ r q))

theorem sharpDLeftSum_eq_path (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n l : ℕ) (y : SharpInput p n) :
    sharpDLeftSum W β hβ p n l y =
      replayPathDLeftSum W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) l
        (sharpToReplay p n y) := by
  unfold sharpDLeftSum replayPathDLeftSum
  rw [← (finCongr (rankCount_add p.a p.b n)).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [N13t.fullHistoryDLeftSum, Function.comp_apply, historyDLeftSum,
    predictableGaussianSum_eq_fin_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem isSharpDIntegral_of_path (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ)
    (J : Spin (coarseRank p n + coarseCount p n) ×
      M1.ReplayInput (coarseMesh p n) (coarseRank p n) (coarseCount p n) → ℝ)
    (hJ : N13t.IsL2Limit
      ((M1.spinPrior (coarseRank p n + coarseCount p n)).prod
        (M1.ReplayLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)))
      (replayPathDLeftSum W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)) J) :
    IsSharpDIntegral W β hβ p n (J ∘ sharpToReplay p n) := by
  have hlaw : HasLaw (sharpToReplay p n)
      ((M1.spinPrior (coarseRank p n + coarseCount p n)).prod
        (M1.ReplayLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)))
      (sharpUnlinkedLaw W p n) :=
    ⟨(measurable_sharpToReplay p n).aemeasurable, sharpToReplay_unlinked_law W p n⟩
  exact (hJ.comp_hasLaw hlaw (measurable_sharpToReplay p n)).congr_sums
    (fun l => Eventually.of_forall fun y => (sharpDLeftSum_eq_path W β hβ p n l y).symm)

theorem sharpDIntegral_exists_of_mesh_pos
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (hδ : 0 < coarseMesh p n) :
    ∃ J : SharpInput p n → ℝ, IsSharpDIntegral W β hβ p n J := by
  obtain ⟨J, hJ⟩ := replayPathDIntegral_exists W β hβ (coarseMesh p n) hδ
    (coarseRank p n) (coarseCount p n)
  exact ⟨J ∘ sharpToReplay p n, isSharpDIntegral_of_path W β hβ p n J hJ⟩

theorem sharpDIntegral_holds
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (hn : 0 < n) :
    ∃ J : SharpInput p n → ℝ, IsSharpDIntegral W β hβ p n J :=
  sharpDIntegral_exists_of_mesh_pos W β hβ p n
    (paperGrowingQueryMeshSize_pos p.a n hn)

theorem isSharpDIntegral_unique
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (I J : SharpInput p n → ℝ)
    (hI : IsSharpDIntegral W β hβ p n I) (hJ : IsSharpDIntegral W β hβ p n J) :
    I =ᵐ[sharpUnlinkedLaw W p n] J := by
  have : IsProbabilityMeasure (sharpUnlinkedLaw W p n) := by
    unfold sharpUnlinkedLaw
    infer_instance
  exact N13t.IsL2Limit.unique hI hJ

end SKConstants.Completion.T0
