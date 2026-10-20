module

public import SKConstants.Completion.N4c.TerminalProduct
public import SKConstants.Completion.LC0.PrimitivePathVersions

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal ENNReal

namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem twoDriverWeightedPath_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (H : ℝ), (f v)^2 + (g v)^2 = 1) :
    ((scalarPrimitiveBrownianPathLaw W H).prod
      (scalarPrimitiveBrownianPathLaw Z H)).map (scalarTwoDriverWeightedPath f g hf hg H) =
      scalarPrimitiveBrownianPathLaw W H := by
  have h := congrArg (fun ν : Measure (ScalarContinuousPath H × ScalarContinuousPath H) =>
    ν.map Prod.fst) (weightedPair_preserves_brownian_law W Z f g hf hg H hunit)
  rw [Measure.map_map measurable_fst (measurable_WeightedPair f g hf hg H),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem twoDriverPicardPath_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (b : BoundedLipschitzDrift) (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (H : ℝ), (f v)^2 + (g v)^2 = 1) :
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)).map
      (fun p => scalarTwoDriverPicardPath b f g hf hg H (0,p)) =
      W.law.map (fun w => scalarForwardPicardPath b H
        (0,scalarPrimitiveBrownianPathVersion W H w)) := by
  let F : ScalarContinuousPath H → ScalarContinuousPath H :=
    fun p => scalarForwardPicardPath b H (0,p)
  have hF : Measurable F := (measurable_scalarForwardPicardPath b H).comp
    (measurable_const.prodMk measurable_id)
  change ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)).map
    (F ∘ scalarTwoDriverWeightedPath f g hf hg H) = _
  rw [← Measure.map_map hF (measurable_scalarTwoDriverWeightedPath f g hf hg H),
    twoDriverWeightedPath_law W Z f g hf hg H hunit]
  exact Measure.map_map hF (measurable_scalarPrimitiveBrownianPathVersion W H)

def PathPrefix (H : ℝ≥0) (p : ScalarContinuousPath H) : Iic H → ℝ :=
  fun t => p ⟨(t.1 : ℝ), t.1.coe_nonneg, t.property⟩

theorem measurable_PathPrefix (H : ℝ≥0) : Measurable (PathPrefix H) :=
  Measurable.of_eval (fun _t => ContinuousMap.measurable_eval _)

def ActualFieldPrefix (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0) : Ω → Iic H → ℝ :=
  fun w t => actualParisiFullScalarProcess W β t.1 w

theorem measurable_ActualFieldPrefix (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0) :
    Measurable (ActualFieldPrefix W β H) :=
  Measurable.of_eval (fun t => (actualParisiFullScalarDrift β).solution_measurable W t.1)

def PairObservation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    (ScalarContinuousPath H × ScalarContinuousPath H) → ScalarContinuousPath H :=
  fun p => scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) H (0,p)

theorem measurable_PairObservation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    Measurable (PairObservation W β hβ H) :=
  (measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
    (measurable_const.prodMk measurable_id)

theorem pairObservation_prefix_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)).map
      (PathPrefix H ∘ PairObservation W β hβ H) =
      W.law.map (ActualFieldPrefix W β H) := by
  rw [← Measure.map_map (measurable_PathPrefix H) (measurable_PairObservation W β hβ H)]
  rw [show ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)).map
      (PairObservation W β hβ H) = W.law.map (fun w =>
        scalarForwardPicardPath (actualParisiFullScalarDrift β) H
          (0,scalarPrimitiveBrownianPathVersion W H w)) from
    twoDriverPicardPath_law W W _ _ _ _ _ H
      (fun v _ => actualParisiStieltjesCoefficients_unit W β hβ v)]
  have hF : Measurable (fun w : Ω => scalarForwardPicardPath (actualParisiFullScalarDrift β) H
      (0,scalarPrimitiveBrownianPathVersion W H w)) :=
    (measurable_scalarForwardPicardPath _ H).comp
      (measurable_const.prodMk (measurable_scalarPrimitiveBrownianPathVersion W H))
  rw [Measure.map_map (measurable_PathPrefix H) hF]
  apply Measure.map_congr
  filter_upwards [scalarForwardPicardPath_primitive_version W (actualParisiFullScalarDrift β) H]
    with w hw
  funext t
  exact hw ⟨(t.1 : ℝ), t.1.coe_nonneg, t.property⟩

theorem pairObservation_linked_prefix_law
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    (ScalarTerminalLinkedLaw β H
      ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H))
      (fun p => PairObservation W β hβ H p ⟨H,H.coe_nonneg,le_rfl⟩)).map
        (fun u => (u.1, PathPrefix H (PairObservation W β hβ H u.2))) =
      (actualParisiFullTerminalSpinLaw β W H).map
        (fun u => (u.1, ActualFieldPrefix W β H u.2)) := by
  let := W.isProbability
  let E : (Iic H → ℝ) → ℝ := fun p => p ⟨H,le_rfl⟩
  have hE : Measurable E := measurable_pi_apply _
  change (ScalarTerminalLinkedLaw β H _ (E ∘ (PathPrefix H ∘ PairObservation W β hβ H))).map
      (Prod.map id (PathPrefix H ∘ PairObservation W β hβ H)) =
    (ScalarTerminalLinkedLaw β H W.law (E ∘ ActualFieldPrefix W β H)).map
      (Prod.map id (ActualFieldPrefix W β H))
  rw [scalarTerminalLinkedLaw_map β H _ _
      ((measurable_PathPrefix H).comp (measurable_PairObservation W β hβ H)) E hE,
    scalarTerminalLinkedLaw_map β H W.law _ (measurable_ActualFieldPrefix W β H) E hE,
    pairObservation_prefix_law W β hβ H]

end SKConstants.M1
