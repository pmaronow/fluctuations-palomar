module

public import SKConstants.Completion.N13t.Transport

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK Blueprint4 LC4a

variable {Ω : Type} [MeasurableSpace Ω]

def residualHistory (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (q : ℕ)
    (Zv : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ)
    (u : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q)) : ℝ :=
  Zv u - (finiteHistoryRow W β (scalarGrowingSourceHorizon δ q) (growingQueryTime δ) q u +
    LJ.gridEnergy W β (growingQueryTime δ) q / 2)

theorem measurable_residualHistory (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (q : ℕ)
    (Zv : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ) (hm : Measurable Zv) :
    Measurable (residualHistory W β δ q Zv) :=
  hm.sub ((measurable_finiteHistoryRow W β _ _ q).add measurable_const)

theorem residualHistory_model_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ)
    (Zv : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ) :
    (fun u => residualHistory W β δ q Zv
      (modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q) u)) =ᵐ[
      actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)]
      growingResidual W W β hβ δ q
        (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) := by
  filter_upwards [(actualRowLinked_absolutelyContinuous W W β _).ae_le
    (finiteHistoryRow_model_ae W W β hβ _ (growingQueryTime δ)
      (growingQueryTime_strictMono δ hδ).monotone q le_rfl)] with u hu
  change Zv _ - (finiteHistoryRow W β _ _ q _ + _) = Zv _ - (LJ.actualFiniteRow W W β hβ _ q u + _)
  exact congrArg (fun x => Zv (modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q) u) -
    (x + LJ.gridEnergy W β (growingQueryTime δ) q / 2)) hu

theorem replay_centeredResidual_identDistrib
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (Zv : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ) (hm : Measurable Zv) :
    let ER := ∫ u, growingResidual W W β hβ δ q
      (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) u
        ∂actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)
    IdentDistrib
      (fun u => (∑ i, (residualHistory W β δ q Zv
        (replayFullHistories W β hβ δ r q u i) - ER)) / (r + q : ℕ))
      (fun ω : Fin (r + q) → (Bool × Ω) × Ω => (∑ i,
        (growingResidual W W β hβ δ q
          (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) (ω i) - ER)) /
          (r + q : ℕ))
      (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q))
      (Measure.pi fun _ : Fin (r + q) => actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)) := by
  let ER := ∫ u, growingResidual W W β hβ δ q
    (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) u
      ∂actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)
  exact replay_average_identDistrib W β hβ δ r q h
    (fun u => residualHistory W β δ q Zv u - ER)
    ((measurable_residualHistory W β δ q Zv hm).sub measurable_const)
    (fun u => growingResidual W W β hβ δ q
      (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) u - ER)
    ((residualHistory_model_ae W β hβ δ hδ q Zv).mono
      (fun u hu => congrArg (fun x : ℝ => x - ER) hu))

theorem replay_growingResidual_concentration (h7 : GrowingResidualMGFStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ (δ : ℝ≥0) (r q : ℕ),
      0 < r + q → LagMesh β δ q → ReplayFullHistoryLawStatement W β hβ δ r q →
      ∀ Zv, IsL2Limit (fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q))
        (jointHistoryLeftSum W β (scalarGrowingSourceHorizon δ q)) Zv →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
      let ER := ∫ u, growingResidual W W β hβ δ q
        (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) u
          ∂actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)
      (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
        {u | η ≤ |(∑ i, (residualHistory W β δ q Zv
            (replayFullHistories W β hβ δ r q u i) - ER)) / (r + q : ℕ)|} ≤
        2 * Real.exp (-(c * (r + q : ℕ) * η ^ 2 / δ)) := by
  obtain ⟨c, hc, hmain⟩ := growingResidualConcentration_of_mgf h7 W W β hβ
  refine ⟨c, hc, ?_⟩
  intro δ r q hn hmesh hFull Zv hZv η hη hη1
  have hδ := hmesh.1
  dsimp only
  have hid := (replay_centeredResidual_identDistrib W β hβ δ hδ r q hFull Zv hZv.1).comp measurable_abs
  have he := congrArg ENNReal.toReal (hid.measure_mem_eq (measurableSet_Ici (a := η)))
  exact he.trans_le (hmain δ q hmesh
    (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q))
    (jointHistoryIntegral_model W W β hβ _ Zv hZv) (r + q) hn η hη hη1)

theorem residualHistory_original_mean (h7 : GrowingResidualMGFStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (q : ℕ)
    (hmesh : LagMesh β δ q)
    (Zv : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ)
    (hZv : IsL2Limit (fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q))
      (jointHistoryLeftSum W β (scalarGrowingSourceHorizon δ q)) Zv) :
    (∫ u, growingResidual W W β hβ δ q
      (Zv ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) u
        ∂actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)) =
      3 / 2 * (actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ q) -
        LJ.gridEnergy W β (growingQueryTime δ) q) := by
  obtain ⟨_, _, _, _, hmain⟩ := h7 W W β hβ
  exact (hmain δ q hmesh _ (jointHistoryIntegral_model W W β hβ _ Zv hZv)).2.1

end SKConstants.Completion.N13t
