module

public import SKConstants.Completion.N13t.Transport
public import SKConstants.Completion.N13t.Reference

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 Blueprint Blueprint4

def RawSharpTransportStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ), 0 < r + q →
    ReplayFullHistoryLawStatement W β hβ δ r q →
    ∃ (I : GrowingReplaySpace Ω δ r q → ℝ) (Jrow : (Bool × Ω) × Ω → ℝ),
      Measurable I ∧ IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I ∧
      Measurable Jrow ∧ LM4b.IsActualRowDIntegral W W β hβ (scalarGrowingSourceHorizon δ q) Jrow ∧
      IdentDistrib
        (fun u => (growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I u -
          β * ∑ i, finiteHistoryRow W β (scalarGrowingSourceHorizon δ q) (growingQueryTime δ) q
            (replayFullHistories W β hβ δ r q u i)) / (r + q : ℕ))
        (fun ω : Fin (r + q) → (Bool × Ω) × Ω =>
          (∑ i, (rowInformationV W β (scalarGrowingSourceHorizon δ q) Jrow (ω i) -
            β * LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q (ω i))) / (r + q : ℕ))
        (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q))
        (Measure.pi fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)) ∧
      ((growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).withDensity
        (fun u => ENNReal.ofReal (Real.exp (-growingReplayInformation W β hβ δ hδ r q
          (scalarGrowingSourceHorizon δ q) I u)))).map (fun u => (u.1.1.2.1, u.1.2)) =
        (skDisorderLaw (r + q)).prod (Measure.pi fun _ : Fin (r + q) => scalarHiddenPriorBool 0)

theorem rawSharpTransport_holds : RawSharpTransportStatement := by
  intro Ω _ W β hβ δ hδ r q hn hFull
  obtain ⟨I₀, hI₀, _, _, _, _, _⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q)
  obtain ⟨I, hIm, hI, -⟩ := growingReplayDIntegral_measurable_version W β hβ δ hδ r q _ I₀ hI₀
  obtain ⟨J, hJm, hJ⟩ := historyDIntegral_exists_of_fullHistoryLaw W β hβ δ hδ r q hn hFull
  refine ⟨I, J ∘ modelObservationDHistory W β hβ (scalarGrowingSourceHorizon δ q), hIm, hI,
    hJm.comp (measurable_modelObservationDHistory W β hβ _),
    N7.historyDIntegral_model W β hβ _ J hJ,
    replayInformation_sub_finiteRow_identDistrib W β hβ δ hδ r q hFull J hJm hJ I hI, ?_⟩
  exact growingReplay_inverse_information_matrix_spin_marginal W β hβ δ hδ r q _ I hI

def ReplaySharpRowConcentrationStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ),
      0 < r + q → LagMesh β δ q → ReplayFullHistoryLawStatement W β hβ δ r q →
      ∀ I, IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
          {u | Real.log 2 - parisiPressure β +
              2 * β ^ 2 * actualParisiFullSusceptibilityExpected W β (scalarGrowingSourceHorizon δ q) +
              C * δ + η <
            (growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I u -
              β * ∑ i, finiteHistoryRow W β (scalarGrowingSourceHorizon δ q)
                (growingQueryTime δ) q (replayFullHistories W β hβ δ r q u i)) / (r + q : ℕ)} ≤
          2 * Real.exp (-(c * (r + q : ℕ) * η ^ 2 / δ))

theorem replaySharpRowConcentration_holds (h3 : JointEndpointIdentityStatement)
    (h7 : GrowingResidualMGFStatement) : ReplaySharpRowConcentrationStatement := by
  intro Ω _ W β hβ
  obtain ⟨C, c, hC, hc, hmain⟩ := sharpRowConcentration_of_engine h3 h7 W W β hβ
  refine ⟨C, c, hC, hc, ?_⟩
  intro δ hδ r q hn hmesh hFull I hI η hη hη1
  obtain ⟨J, hJm, hJ⟩ := historyDIntegral_exists_of_fullHistoryLaw W β hβ δ hδ r q hn hFull
  have hmodel := N7.historyDIntegral_model W β hβ (scalarGrowingSourceHorizon δ q) J hJ
  have hbound := hmain δ q hmesh
    (J ∘ modelObservationDHistory W β hβ (scalarGrowingSourceHorizon δ q)) hmodel
    (r + q) hn η hη hη1
  have hid := replayInformation_sub_finiteRow_identDistrib W β hβ δ hδ r q hFull J hJm hJ I hI
  have he := congrArg ENNReal.toReal (hid.measure_mem_eq (measurableSet_Ioi (a :=
    Real.log 2 - parisiPressure β +
      2 * β ^ 2 * actualParisiFullSusceptibilityExpected W β (scalarGrowingSourceHorizon δ q) +
      C * δ + η)))
  exact he.trans_le hbound

end SKConstants.Completion.N13t
