module

public import SKConstants.Completion.N7.HistoryIntegral
public import SKConstants.Completion.LM3.Results

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3
variable {Ω : Type*} [MeasurableSpace Ω]

theorem growingReplay_information_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hn : 0 < r₀ + q)
    (V : ℝ≥0) (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ r₀ q V hVH)
    (I : GrowingReplaySpace Ω δ r₀ q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r₀ q V I) :
    (∫ u, growingReplayInformation W β hβ δ hδ r₀ q V I u
      ∂growingReplayLinkedLaw W β hβ δ r₀ q V) =
      (r₀ + q : ℕ) * actualParisiEntropyReference W β V := by
  obtain ⟨J, _, hJ⟩ := historyDIntegral_exists_of_historyLaw W β hβ δ hδ r₀ q V hVH hHist ⟨0, hn⟩
  rw [growingReplay_information_mean_eq_row_mean W β hβ δ hδ r₀ q V hVH hHist J hJ I hI,
    history_information_mean W β hβ V J hJ]

theorem actualReplay_forward_KL_of_historyLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hn : 0 < r₀ + q)
    (V : ℝ≥0) (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ r₀ q V hVH) :
    klDiv ((growingReplayLinkedLaw W β hβ δ r₀ q V).map (replayOutput δ r₀ q))
      (skJointLaw (r₀ + q) β) ≤
      ENNReal.ofReal ((r₀ + q : ℕ) * actualParisiEntropyReference W β V -
        (r₀ + q : ℕ) * Real.log 2 +
        (∫ G, Real.log (gibbsPartition β G) ∂skDisorderLaw (r₀ + q)) -
        β * (∫ u, quadraticHamiltonian (replayOutput δ r₀ q u).1
          (replayOutput δ r₀ q u).2 ∂growingReplayLinkedLaw W β hβ δ r₀ q V)) := by
  obtain ⟨I, hI, _⟩ := actualReplayGaussianReference_integral_exists W β hβ δ hδ r₀ q V
  have h := actualReplay_forward_KL W β hβ δ hδ r₀ q V I hI
  rw [growingReplay_information_mean W β hβ δ hδ r₀ q hn V hVH hHist I hI] at h
  exact h

def pathReplayOutput (δ : ℝ≥0) (r₀ q : ℕ)
    (u : Spin (r₀ + q) × M1.ReplayInput δ r₀ q) :
    Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ × Spin (r₀ + q) := (u.2.1.2.1, u.1)

theorem measurable_pathReplayOutput (δ : ℝ≥0) (r₀ q : ℕ) :
    Measurable (pathReplayOutput δ r₀ q) := measurable_snd.fst.snd.fst.prodMk measurable_fst

theorem actualReplay_output_eq_pathReplay
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (growingReplayLinkedLaw W β hβ δ r₀ q (scalarGrowingSourceHorizon δ q)).map
        (replayOutput δ r₀ q) =
      (M1.ReplayLinkedLaw W β hβ δ r₀ q).map (pathReplayOutput δ r₀ q) := by
  rw [← growingReplayLinkedLaw_toReplay_at_horizon W β hβ δ r₀ q,
    Measure.map_map (measurable_pathReplayOutput δ r₀ q) (M1.measurable_RawToReplay W δ r₀ q)]
  rfl

end SKConstants.Completion.N7
