module

public import SKConstants.Completion.Blueprint.NodesLower

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace SKConstants.NReplay
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint

theorem replayInput_shuffle {M A C D : Type*}
    [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure M) (a : Measure A) (c : Measure C) (d : Measure D)
    [SFinite μ] [SFinite a] [SFinite c] [SFinite d] :
    (μ.prod (a.prod (c.prod d))).map
      (fun x => ((x.2.1, (x.1, x.2.2.1)), x.2.2.2)) =
      (a.prod (μ.prod c)).prod d := by
  have h0 := (measurePreserving_prodAssoc μ a (c.prod d)).symm
  have h1 := (Measure.measurePreserving_swap (μ := μ) (ν := a)).prod
    (MeasurePreserving.id (c.prod d))
  have h2 := measurePreserving_prodAssoc a μ (c.prod d)
  have h3 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc μ c d).symm
  have h4 := (measurePreserving_prodAssoc a (μ.prod c) d).symm
  exact (h4.comp (h3.comp (h2.comp (h1.comp h0)))).map_eq

theorem replayInput_law {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    ((primLaw (r₀ + q)).prod (replayAuxLaw W δ r₀ q)).map
      (fun x => replayInput (physical (r₀ + q) x.1) x.2) = M1.ReplayLaw W δ r₀ q := by
  have hM : Measurable (physical (r₀ + q)) := (continuous_goeMatrix _).measurable
  have hm : (primLaw (r₀ + q)).map (physical (r₀ + q)) = skDisorderLaw (r₀ + q) := rfl
  have hi := (Measure.map_prod_map (primLaw (r₀ + q)) (replayAuxLaw W δ r₀ q)
    hM measurable_id).symm
  rw [Measure.map_id, hm] at hi
  have hr := congrArg (fun ν => ν.map (fun p => replayInput p.1 p.2)) hi
  rw [Measure.map_map (measurable_replayInput δ r₀ q) (hM.prodMap measurable_id)] at hr
  exact hr.trans (replayInput_shuffle _ _ _ _)

end SKConstants.NReplay
