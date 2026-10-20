module

public import SKConstants.Completion.LC4a.ReplayKL
public import SKConstants.Completion.LF0.ExceptionalExpectation
public import SKConstants.Completion.LQ.ActualGrowingQuadrature
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators NNReal ENNReal

namespace SKConstants.Completion.LFine
open SKConstantsOAI.ZeroTemperatureSK LC4a LQ
variable {Ω : Type*} [MeasurableSpace Ω]

def fineReplayOutput (δ : ℝ≥0) (ranks q : ℕ)
    (u : GrowingReplaySpace Ω δ ranks q) :
    Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ × Spin (ranks+q) :=
  (u.1.1.2.1,u.1.2)

theorem measurable_fineReplayOutput (δ : ℝ≥0) (ranks q : ℕ) :
    Measurable (fineReplayOutput (Ω := Ω) δ ranks q) :=
  (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp measurable_fst)

def fineJointLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) :=
  (growingReplayLinkedLaw W β hβ δ ranks q (scalarGrowingSourceHorizon δ q)).map
    (fineReplayOutput δ ranks q)

instance fineJointLaw_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) [hδ : Fact (0 < δ)] (ranks q : ℕ) :
    IsProbabilityMeasure (fineJointLaw W β hβ δ ranks q) := by
  let := growingReplayLinkedLaw_probability W β hβ δ hδ.out ranks q
    (scalarGrowingSourceHorizon δ q)
  unfold fineJointLaw
  infer_instance

theorem fineJointLaw_matrix_marginal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    (fineJointLaw W β hβ δ ranks q).map Prod.fst = skDisorderLaw (ranks+q) := by
  let := W.isProbability
  let D := Measure.pi (fun _ : Fin (ranks+q) => W.law)
  let P := scalarGrowingReplayStaticLaw W δ (ranks+q) q
  let θ : GrowingReplaySpace Ω δ ranks q →
      ScalarGrowingReplayStaticData δ (ranks+q) q × (Fin (ranks+q) → Ω) :=
    fun u => (u.1.1,u.2)
  let ψ : ScalarGrowingReplayStaticData δ (ranks+q) q × (Fin (ranks+q) → Ω) →
      Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ := fun u => u.1.2.1
  have hθ : Measurable θ := measurable_fst.fst.prodMk measurable_snd
  have hψ : Measurable ψ := measurable_fst.snd.fst
  have hstatic : P.map (fun a => a.2.1) = skDisorderLaw (ranks+q) := by
    let A := (Measure.pi (fun _ : Fin (ranks+q) =>
      scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
        (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (ranks+q) =>
          scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))
    exact ((measurePreserving_fst (μ := skDisorderLaw (ranks+q))
      (ν := GaussianProposal.paperCompletionNoiseLaw (ranks+q) q)).comp
        (measurePreserving_snd (μ := A)
          (ν := (skDisorderLaw (ranks+q)).prod
            (GaussianProposal.paperCompletionNoiseLaw (ranks+q) q)))).map_eq
  have hp : (P.prod D).map ψ = skDisorderLaw (ranks+q) := by
    change (P.prod D).map ((fun a => a.2.1) ∘ Prod.fst) = _
    rw [← Measure.map_map (by fun_prop) measurable_fst]
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hstatic
  unfold fineJointLaw
  rw [Measure.map_map measurable_fst (measurable_fineReplayOutput δ ranks q)]
  change (growingReplayLinkedLaw W β hβ δ ranks q _).map (ψ ∘ θ) = _
  rw [← Measure.map_map hψ hθ,
    growingReplayLinkedLaw_path_marginal W β hβ δ hδ ranks q]
  exact hp

theorem fineJointLaw_energy_integrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    Integrable (fun z => quadraticHamiltonian z.1 z.2) (fineJointLaw W β hβ δ ranks q) := by
  exact LF0.gaussian_marginal_energy_integrable _ _ _ measurable_fst
    measurable_snd (fineJointLaw_matrix_marginal W β hβ δ hδ ranks q)

def ActualForwardKLComparisonStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) : Prop :=
  klDiv (fineJointLaw W β hβ δ ranks q) (skJointLaw (ranks+q) β) ≤
    ENNReal.ofReal ((ranks+q : ℕ)*actualParisiEntropyReference W β (scalarGrowingSourceHorizon δ q) -
      (ranks+q : ℕ)*Real.log 2 +
      (∫ A, Real.log (gibbsPartition β A) ∂skDisorderLaw (ranks+q)) -
      β*(∫ z, quadraticHamiltonian z.1 z.2 ∂fineJointLaw W β hβ δ ranks q))

end SKConstants.Completion.LFine
