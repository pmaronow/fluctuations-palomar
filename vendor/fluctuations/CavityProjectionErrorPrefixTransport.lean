module

public import CavityExteriorResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

theorem physical_projection_error_moment_cons (n l : ℕ)
    (st : GaussianStep (FeatureIndex n)) (tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (hs : OrderedSteps a (st::tail))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (j t : ℕ) :
    let μ' := μ ⊗ₘ (plantedStepKernel (uniformWeight n) (finiteFeature n) st.1 st.2 tail).comap x hx
    let x' : P × (FeatureIndex n → ℝ) → FeatureIndex n → ℝ := fun p => x p.1+p.2
    physicalOverlapProjectionErrorMoment n l (st::tail) μ x hx (j+1) (t+1) =
      physicalOverlapProjectionErrorMoment n l tail μ' x'
        ((hx.comp measurable_fst).add measurable_snd) j t := by
  dsimp only
  obtain ⟨m,q⟩ := st
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) ((m,q)::tail) hs
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) tail hs.2.2.2
  have := plantedStepKernel_markov (uniformWeight_pos n) (finiteFeature n) m q tail hs
  let ν := physicalPathLaw μ n ((m,q)::tail) x hx
  let μ' := μ ⊗ₘ (plantedStepKernel (uniformWeight n) (finiteFeature n) m q tail).comap x hx
  let x' : P × (FeatureIndex n → ℝ) → FeatureIndex n → ℝ := fun p => x p.1+p.2
  have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
  let e : PhysicalPathState P n ((m,q)::tail) ≃ᵐ
      PhysicalPathState (P × (FeatureIndex n → ℝ)) n tail := MeasurableEquiv.prodAssoc.symm
  have hmap : ν.map e = physicalPathLaw μ' n tail x' hx' :=
    hierarchyPathLaw_cons (uniformWeight_pos n) (finiteFeature n) m q tail hs μ x hx
  have htest := conditionalForkTest_measurable (uniformWeight_pos n) (finiteFeature n)
    tail hs.2.2.2 x' hx' j
    ((physicalOverlapProjectionError_measurable n tail hs.2.2.2 x' hx' t).abs.pow_const (2*l))
  change (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) ((m,q)::tail) x (j+1)
    (fun z => |physicalOverlapProjectionError n ((m,q)::tail) x (t+1) z|^(2*l)) p ∂ν) =
    ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) tail x' j
      (fun z => |physicalOverlapProjectionError n tail x' t z|^(2*l)) p ∂physicalPathLaw μ' n tail x' hx'
  rw [←hmap,integral_map e.measurable.aemeasurable htest.aestronglyMeasurable]
  rfl

end OAI.SKFluctuations
