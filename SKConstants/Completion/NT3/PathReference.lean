module

public import SKConstants.Completion.NT3.ProductLift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.NT3
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC4a LM3 Blueprint Blueprint4 N13A

variable {Ω : Type} [MeasurableSpace Ω]

abbrev PathInput (δ : ℝ≥0) (r q : ℕ) := Spin (r + q) × M1.ReplayInput δ r q

def pathDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (u : PathInput δ r q) : ℝ :=
  ∑ i, N13t.fullHistoryDBracket W β (scalarGrowingSourceHorizon δ q)
    (M1.ReplayHistories W β hβ δ r q u i)

theorem measurable_pathDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : Measurable (pathDBracket W β hβ δ r q) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact ((measurable_historyDBracket W β _).comp
    (N13t.measurable_observationDProjection _)).comp
      ((measurable_pi_apply i).comp (M1.measurable_ReplayHistories W β hβ δ r q))

theorem rawDBracket_eq_path_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) :
    growingReplayDBracket W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) =ᵐ[
      growingReplayUnlinkedLaw W δ r q]
      pathDBracket W β hβ δ r q ∘ M1.RawToReplay W δ r q := by
  filter_upwards [growingReplayDBracket_eq_history_sum_ae W β hβ δ hδ r q
    (scalarGrowingSourceHorizon δ q) le_rfl] with u hu
  rw [hu]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (historyDBracket W β (scalarGrowingSourceHorizon δ q))
    (N13t.replayFullHistories_observationD W β hβ δ r q u i).symm

def pathReferenceDensity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (J : PathInput δ r q → ℝ) (u : PathInput δ r q) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (J u - pathDBracket W β hβ δ r q u / 2))

theorem measurable_pathReferenceDensity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (J : PathInput δ r q → ℝ) (hm : Measurable J) :
    Measurable (pathReferenceDensity W β hβ δ r q J) :=
  (hm.sub ((measurable_pathDBracket W β hβ δ r q).div_const 2)).exp.ennreal_ofReal

theorem pathDIntegral_comp_raw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (J : PathInput δ r q → ℝ)
    (hJ : N13t.IsL2Limit ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q))
      (T0.replayPathDLeftSum W β hβ δ r q) J) :
    IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q)
      (J ∘ M1.RawToReplay W δ r q) := by
  have hlaw : HasLaw (M1.RawToReplay W δ r q)
      ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q))
      (growingReplayUnlinkedLaw W δ r q) :=
    ⟨(M1.measurable_RawToReplay W δ r q).aemeasurable, M1.rawToReplay_unlinked_law W δ r q⟩
  exact ((hJ.comp_hasLaw hlaw (M1.measurable_RawToReplay W δ r q)).congr_sums
    (fun l => (T0.growingReplayDLeftSum_eq_path_ae W β hβ δ hδ r q l).symm)).2

theorem pathReference_static_marginal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (J : PathInput δ r q → ℝ)
    (hJ : N13t.IsL2Limit ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q))
      (T0.replayPathDLeftSum W β hβ δ r q) J) :
    (((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q)).withDensity
      (pathReferenceDensity W β hβ δ r q J)).map (fun u => (u.2.1, u.1)) =
      parisiGrowingReplaySpinStaticLaw W δ (r + q) q := by
  let I := J ∘ M1.RawToReplay W δ r q
  have hI := pathDIntegral_comp_raw W β hβ δ hδ r q J hJ
  have hm := measurable_pathReferenceDensity W β hβ δ r q J hJ.1
  have he : (fun u => ENNReal.ofReal
      (growingReplayDExponential W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I u)) =ᵐ[
      growingReplayUnlinkedLaw W δ r q]
      pathReferenceDensity W β hβ δ r q J ∘ M1.RawToReplay W δ r q := by
    filter_upwards [rawDBracket_eq_path_ae W β hβ δ hδ r q] with u hu
    change ENNReal.ofReal (Real.exp (I u - growingReplayDBracket W β hβ δ hδ r q
      (scalarGrowingSourceHorizon δ q) u / 2)) = _
    rw [hu]
    rfl
  have hmap : (growingReplayDReference W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I).map
      (M1.RawToReplay W δ r q) =
      ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q)).withDensity
        (pathReferenceDensity W β hβ δ r q J) := by
    have hrawmap : (growingReplayUnlinkedLaw W δ r q).map (M1.RawToReplay W δ r q) =
        (M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q) :=
      M1.rawToReplay_unlinked_law W δ r q
    unfold growingReplayDReference
    rw [withDensity_congr_ae he,
      map_withDensity_comp _ _ (M1.measurable_RawToReplay W δ r q) _ hm,
      hrawmap]
  rw [← hmap, Measure.map_map (measurable_snd.fst.prodMk measurable_fst)
    (M1.measurable_RawToReplay W δ r q)]
  obtain ⟨I₀, hI₀, _, _, _, hstatic, _⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q)
  change (growingReplayDReference W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I).map
    Prod.fst = _
  rw [growingReplayDReference_unique W β hβ δ hδ r q _ I I₀ hI hI₀]
  exact hstatic

end SKConstants.Completion.NT3
