module

public import SKConstants.Completion.NT2.Information

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.NT2
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4 N13A LM3

variable {Ω : Type} [MeasurableSpace Ω]

def SharpTransportT2Statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∀ᶠ n : ℕ in atTop,
      ∃ (J : SharpInput p n → ℝ) (Jrow : (Bool × Ω) × Ω → ℝ),
        IsSharpDIntegral W β hβ p n J ∧ Measurable Jrow ∧
        LM4b.IsActualRowDIntegral W W β hβ (coarseTime p n) Jrow ∧
        HasLaw (sharpRows W β hβ p n) (canonicalArrayLaw W β hβ p n)
          (sharpLinkedLaw W β hβ p n) ∧
        IdentDistrib
          (fun y => sharpInformation W β hβ p n J y / n -
            β * linearEnergy W β hβ (sharpRows W β hβ p n y))
          (fun ω : Fin n → (Bool × Ω) × Ω =>
            (∑ i, (rowInformationV W β (coarseTime p n) Jrow (ω i) -
              β * LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n))
                (coarseCount p n) (ω i))) / n)
          (sharpLinkedLaw W β hβ p n)
          (Measure.pi fun _ : Fin n => actualParisiFullQuerySpinLaw W W β (coarseTime p n))

theorem sharpTransportT2_at_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    ∃ (J : SharpInput p n → ℝ) (Jrow : (Bool × Ω) × Ω → ℝ),
      IsSharpDIntegral W β hβ p n J ∧ Measurable Jrow ∧
      LM4b.IsActualRowDIntegral W W β hβ (coarseTime p n) Jrow ∧
      HasLaw (sharpRows W β hβ p n) (canonicalArrayLaw W β hβ p n)
        (sharpLinkedLaw W β hβ p n) ∧
      IdentDistrib
        (fun y => sharpInformation W β hβ p n J y / n -
          β * linearEnergy W β hβ (sharpRows W β hβ p n y))
        (fun ω : Fin n → (Bool × Ω) × Ω =>
          (∑ i, (rowInformationV W β (coarseTime p n) Jrow (ω i) -
            β * LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n))
              (coarseCount p n) (ω i))) / n)
        (sharpLinkedLaw W β hβ p n)
        (Measure.pi fun _ : Fin n => actualParisiFullQuerySpinLaw W W β (coarseTime p n)) := by
  have hδ := paperGrowingQueryMeshSize_pos p.a n hn
  have hN : 0 < coarseRank p n + coarseCount p n := by
    simpa only [coarseRank, coarseCount, rankCount_add] using hn
  obtain ⟨J, hJm, hJ⟩ := N13t.historyDIntegral_exists_of_fullHistoryLaw W β hβ
    (coarseMesh p n) hδ (coarseRank p n) (coarseCount p n) hN
    (T0.replayFullHistoryLaw_holds W β hβ (coarseMesh p n) hδ
      (coarseRank p n) (coarseCount p n) hN)
  have hI := isSharpDIntegral_historySum W β hβ p n hn J hJm hJ
  refine ⟨sharpHistoryIntegral W β hβ p n J,
    J ∘ modelObservationDHistory W β hβ (coarseTime p n), hI,
    hJm.comp (measurable_modelObservationDHistory W β hβ (coarseTime p n)),
    N7.historyDIntegral_model W β hβ (coarseTime p n) J hJ,
    sharpRows_hasLaw W β hβ p n hn, ?_⟩
  exact sharpInformation_sub_linearEnergy_identDistrib W β hβ p n hn _ hI J hJm hJ

theorem sharpTransportT2_holds : SharpTransportT2Statement := by
  intro Ω _ W β hβ p _ _
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact sharpTransportT2_at_holds W β hβ p n hn

end SKConstants.Completion.NT2
