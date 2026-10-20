module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic

public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace SKConstants.GaussianProposal

variable {Past Fresh Output : Type*}
  [MeasurableSpace Past] [MeasurableSpace Fresh] [MeasurableSpace Output]
  {μ : Measure Past} {ν : Measure Fresh} {ρ : Measure Output}
  {F : Past → Fresh → Output}

theorem adaptiveStep_measurePreserving_ae [SFinite μ] [SFinite ν]
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ᵐ p ∂μ, ν.map (F p) = ρ) :
    MeasurePreserving (fun x : Past × Fresh => (x.1, F x.1 x.2))
      (μ.prod ν) (μ.prod ρ) := by
  exact (MeasurePreserving.id μ).skew_product hF hlaw

theorem adaptiveStep_joint_law_ae [SFinite μ] [SFinite ν]
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ᵐ p ∂μ, ν.map (F p) = ρ) :
    (μ.prod ν).map (fun x : Past × Fresh => (x.1, F x.1 x.2)) = μ.prod ρ := by
  exact (adaptiveStep_measurePreserving_ae hF hlaw).map_eq

theorem adaptiveStep_joint_law [SFinite μ] [SFinite ν]
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ p, ν.map (F p) = ρ) :
    (μ.prod ν).map (fun x : Past × Fresh => (x.1, F x.1 x.2)) = μ.prod ρ := by
  exact adaptiveStep_joint_law_ae hF (Filter.Eventually.of_forall hlaw)

theorem adaptiveStep_output_law_ae [IsProbabilityMeasure μ] [SFinite ν]
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ᵐ p ∂μ, ν.map (F p) = ρ) :
    (μ.prod ν).map (Function.uncurry F) = ρ := by
  have : SFinite ρ := by
    obtain ⟨p, hp⟩ := hlaw.exists
    rw [← hp]
    infer_instance
  have hjoint := adaptiveStep_joint_law_ae hF hlaw
  have hpair : Measurable (fun x : Past × Fresh => (x.1, F x.1 x.2)) :=
    measurable_fst.prodMk hF
  have hsnd := congrArg (fun m : Measure (Past × Output) => m.map Prod.snd) hjoint
  simpa only [Measure.map_map measurable_snd hpair, Function.comp_def, Function.uncurry_def,
    Measure.map_snd_prod, measure_univ, one_smul] using hsnd

theorem adaptiveStep_independent_ae [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ᵐ p ∂μ, ν.map (F p) = ρ) :
    IndepFun Prod.fst (Function.uncurry F) (μ.prod ν) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    measurable_fst.aemeasurable hF.aemeasurable).2
  rw [Measure.map_fst_prod, measure_univ, one_smul,
    adaptiveStep_output_law_ae hF hlaw]
  exact adaptiveStep_joint_law_ae hF hlaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {past : Ω → Past} {fresh : Ω → Fresh}

theorem adaptiveStep_joint_law_of_input_law [SFinite μ] [SFinite ν]
    (hpast : Measurable past) (hfresh : Measurable fresh)
    (hinput : P.map (fun ω => (past ω, fresh ω)) = μ.prod ν)
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ᵐ p ∂μ, ν.map (F p) = ρ) :
    P.map (fun ω => (past ω, F (past ω) (fresh ω))) = μ.prod ρ := by
  have hpair : Measurable (fun x : Past × Fresh => (x.1, F x.1 x.2)) :=
    measurable_fst.prodMk hF
  calc
    P.map (fun ω => (past ω, F (past ω) (fresh ω))) =
        (P.map (fun ω => (past ω, fresh ω))).map
          (fun x : Past × Fresh => (x.1, F x.1 x.2)) := by
      rw [Measure.map_map hpair (hpast.prodMk hfresh)]
      rfl
    _ = (μ.prod ν).map (fun x : Past × Fresh => (x.1, F x.1 x.2)) := by rw [hinput]
    _ = μ.prod ρ := adaptiveStep_joint_law_ae hF hlaw

theorem adaptiveStep_joint_law_of_independent [IsProbabilityMeasure P]
    (hpast : Measurable past) (hfresh : Measurable fresh)
    (hindep : IndepFun past fresh P)
    (hF : Measurable (Function.uncurry F))
    (hlaw : ∀ᵐ p ∂P.map past, (P.map fresh).map (F p) = ρ) :
    P.map (fun ω => (past ω, F (past ω) (fresh ω))) = (P.map past).prod ρ := by
  exact adaptiveStep_joint_law_of_input_law hpast hfresh
    (hindep.map_prod_eq_prod_map_map hpast.aemeasurable hfresh.aemeasurable) hF hlaw

end SKConstants.GaussianProposal
