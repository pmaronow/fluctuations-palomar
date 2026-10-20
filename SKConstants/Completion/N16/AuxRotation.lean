module

public import SKConstants.Completion.N16.PathRotation
public import SKConstants.Completion.N16.ProductLaws
public import SKConstants.Completion.Blueprint.ExperimentMeasurable
public import SKConstants.Completion.LM6.Regression

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.N16
open Blueprint GaussianProposal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem completion_rotation (N K : ℕ) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((paperCompletionNoiseLaw N K).prod (paperCompletionNoiseLaw N K)).map
      (fun p => completionComb c s K p.1 p.2) = paperCompletionNoiseLaw N K := by
  induction K with
  | zero => simp [paperCompletionNoiseLaw, completionComb, Measure.dirac_prod_dirac]
  | succ K ih =>
    change (((primitiveGaussian (Fin N)).prod (paperCompletionNoiseLaw N K)).prod
      ((primitiveGaussian (Fin N)).prod (paperCompletionNoiseLaw N K))).map
      (fun p => (c • p.1.1 + s • p.2.1, completionComb c s K p.1.2 p.2.2)) =
      (primitiveGaussian (Fin N)).prod (paperCompletionNoiseLaw N K)
    have h := prod_pair_map (primitiveGaussian (Fin N)) (paperCompletionNoiseLaw N K)
      (fun p => c • p.1 + s • p.2) (fun p => completionComb c s K p.1 p.2)
      (by fun_prop) (measurable_completionComb c s K)
    rw [M6.primitiveGaussian_normalized_sum_law c s hcs, ih] at h
    exact h

theorem replayAux_rotation (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((replayAuxLaw W δ r₀ q).prod (replayAuxLaw W δ r₀ q)).map
      (fun p => combineAux c s p.1 p.2) = replayAuxLaw W δ r₀ q := by
  have hB (T : ℝ≥0) :
      ((Measure.pi (fun _ : Fin (r₀ + q) => scalarPrimitiveBrownianPathLaw W T)).prod
        (Measure.pi (fun _ : Fin (r₀ + q) => scalarPrimitiveBrownianPathLaw W T))).map
        (fun p => c • p.1 + s • p.2) =
      Measure.pi (fun _ : Fin (r₀ + q) => scalarPrimitiveBrownianPathLaw W T) := pi_pair_map
    (fun _ : Fin (r₀ + q) => scalarPrimitiveBrownianPathLaw W T)
    (fun _ p => c • p.1 + s • p.2) (fun _ => by fun_prop)
    (fun _ => brownianPath_rotation W T c s hcs)
  have hbr (j : ℕ) :
      ((Measure.pi (fun _ : Fin (r₀ + q) =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))).prod
        (Measure.pi (fun _ : Fin (r₀ + q) =>
          scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))).map
        (fun p => c • p.1 + s • p.2) =
      Measure.pi (fun _ : Fin (r₀ + q) =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)) := pi_pair_map
    (fun _ : Fin (r₀ + q) => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))
    (fun _ p => c • p.1 + s • p.2) (fun _ => by fun_prop)
    (fun _ => bridgePath_rotation W _ c s hcs)
  have hstream :
      ((Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (r₀ + q) =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))).prod
        (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (r₀ + q) =>
          scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))).map
        (fun p => c • p.1 + s • p.2) =
      Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (r₀ + q) =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))) := infinitePi_pair_map
    (fun j : ℕ => Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))
    (fun _ p => c • p.1 + s • p.2) (fun _ => by fun_prop) hbr
  have hinitial := prod_pair_map
    (Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0)))
    (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))
    (fun p => c • p.1 + s • p.2) (fun p => c • p.1 + s • p.2)
    (by fun_prop) (by fun_prop)
  rw [hB, hstream] at hinitial
  have htail := prod_pair_map (paperCompletionNoiseLaw (r₀ + q) q)
    (Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q)))
    (fun p => completionComb c s q p.1 p.2) (fun p => c • p.1 + s • p.2)
    (measurable_completionComb c s q) (by fun_prop)
  rw [completion_rotation _ _ c s hcs, hB] at htail
  have h := prod_pair_map
    ((Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
      (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (r₀ + q) =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))))
    ((paperCompletionNoiseLaw (r₀ + q) q).prod
      (Measure.pi (fun _ : Fin (r₀ + q) =>
        scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))))
    (fun p => (c • p.1.1 + s • p.2.1, c • p.1.2 + s • p.2.2))
    (fun p => (completionComb c s q p.1.1 p.2.1, c • p.1.2 + s • p.2.2))
    (by fun_prop)
    ((measurable_completionComb c s q).comp
      (measurable_fst.fst.prodMk measurable_snd.fst) |>.prodMk (by fun_prop))
  rw [hinitial, htail] at h
  exact h

end SKConstants.N16
