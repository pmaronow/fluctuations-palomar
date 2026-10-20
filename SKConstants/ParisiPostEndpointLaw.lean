module
public import SKConstants.ParisiFullScalarProcess
public import SKConstants.ParisiBrownianMarkov
public import SKConstants.ScalarProcessSeedPathLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiPostEndpointLaw_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def actualParisiEndpointPastPath (W : BrownianSystem Ω) (β : ℝ) :
    Ω → ScalarContinuousPath (parisiEquilibriumPhysicalEndpoint β) :=
  boundedDriftPastPath W (actualParisiFullScalarDrift β) (parisiEquilibriumPhysicalEndpoint β)

def actualParisiPostEndpointPath (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) :
    Ω → ScalarContinuousPath T :=
  boundedDriftRestartPath W (actualParisiFullScalarDrift β) (parisiEquilibriumPhysicalEndpoint β) T

theorem actualParisiPostEndpointPath_version (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) :
    ∀ᵐ w ∂W.law, ∀ t : Set.Icc (0:ℝ) (T:ℝ),
      actualParisiPostEndpointPath W β T w t =
        actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+⟨t,t.property.1⟩) w :=
  boundedDriftRestartPath_version W _ _ T

theorem actualParisiEndpointRestartCallback_eq_tanh (β : ℝ) (hβ : 1 < β) (T : ℝ≥0)
    (p : ScalarContinuousPath (parisiEquilibriumPhysicalEndpoint β) × ScalarContinuousPath T) :
    boundedDriftRestartCallback (actualParisiFullScalarDrift β)
      (parisiEquilibriumPhysicalEndpoint β) T p =
        scalarForwardPicardPath scalarTanhDrift T
          (p.1 ⟨parisiEquilibriumPhysicalEndpoint β,
            (parisiEquilibriumPhysicalEndpoint β).coe_nonneg,le_rfl⟩,p.2) := by
  ext t
  apply SKConstants.BoundedLipschitzDrift.solution_congr_nonneg_drift
  intro r hr x
  change (actualParisiFullScalarDrift β).f ((parisiEquilibriumPhysicalEndpoint β:ℝ)+r) (0+x) =
    Real.tanh x
  rw [zero_add]
  apply congrFun (actualParisiFullScalarDrift_eq_tanh_after_support β hβ _ _) x
  rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
  linarith

theorem actualParisiEndpointPast_post_jointLaw (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    W.law.map (fun w => (actualParisiEndpointPastPath W β w,
      actualParisiPostEndpointPath W β T w)) =
      ((W.law.map (actualParisiEndpointPastPath W β)).prod
        (W.law.map (brownianFinitePath W T))).map (fun p =>
          (p.1,scalarForwardPicardPath scalarTanhDrift T
            (p.1 ⟨parisiEquilibriumPhysicalEndpoint β,
              (parisiEquilibriumPhysicalEndpoint β).coe_nonneg,le_rfl⟩,p.2))) := by
  rw [show W.law.map (fun w => (actualParisiEndpointPastPath W β w,
    actualParisiPostEndpointPath W β T w)) = _ from
      boundedDriftPast_restart_jointLaw W (actualParisiFullScalarDrift β) _ T]
  congr 1
  funext p
  congr 1
  exact actualParisiEndpointRestartCallback_eq_tanh β hβ T p

theorem actualParisiEndpointSeed_post_picard_jointLaw (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    W.law.map (fun w =>
      (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β) w,
        actualParisiPostEndpointPath W β T w)) =
      ((actualParisiEndpointSeedLaw W β).prod (W.law.map (brownianFinitePath W T))).map
        (fun p => (p.1,scalarForwardPicardPath scalarTanhDrift T p)) := by
  let := W.isProbability
  let V := parisiEquilibriumPhysicalEndpoint β
  let seed := actualParisiPreContinuationField W β V
  let past := boundedDriftPastPath W (actualParisiFullScalarDrift β) V
  let future := brownianFinitePath (shiftedBrownianSystem W V) T
  let endpoint : ScalarContinuousPath V → ℝ := fun p => p ⟨V,V.coe_nonneg,le_rfl⟩
  have hm : Measurable endpoint := ContinuousMap.measurable_eval _
  have hp : endpoint ∘ past =ᵐ[W.law] seed := by
    filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) V] with w hw
    exact hw ⟨V,V.coe_nonneg,le_rfl⟩
  have hi : IndepFun seed future W.law := by
    have H := (brownian_futurePath_indep_boundedDriftPastPath W (actualParisiFullScalarDrift β) V T).symm
    exact (H.comp hm measurable_id).congr hp (Eventually.of_forall (fun _ => rfl))
  have hpair : W.law.map (fun w => (seed w,future w)) =
      (actualParisiEndpointSeedLaw W β).prod (W.law.map (brownianFinitePath W T)) := by
    rw [hi.map_prod_eq_prod_map_map
      (measurable_actualParisiPreContinuationField W β V).aemeasurable
      (measurable_brownianFinitePath _ _).aemeasurable,brownian_futurePath_law]
    rfl
  have he : (fun w => (seed w,actualParisiPostEndpointPath W β T w)) =ᵐ[W.law]
      (fun w => (seed w,scalarForwardPicardPath scalarTanhDrift T (seed w,future w))) := by
    filter_upwards [hp] with w hw
    congr 1
    rw [actualParisiPostEndpointPath,boundedDriftRestartPath,
      actualParisiEndpointRestartCallback_eq_tanh β hβ T]
    exact congrArg (scalarForwardPicardPath scalarTanhDrift T) (Prod.ext hw rfl)
  rw [Measure.map_congr he,←hpair,
    Measure.map_map (measurable_fst.prodMk (measurable_scalarForwardPicardPath scalarTanhDrift T))
      ((measurable_actualParisiPreContinuationField W β V).prodMk (measurable_brownianFinitePath _ _))]
  rfl

theorem actualParisiEndpointSeed_post_hidden_jointLaw (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    W.law.map (fun w =>
      (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β) w,
        actualParisiPostEndpointPath W β T w)) =
      (actualParisiSeedContinuationLaw W β W.law).map
        (fun u => (u.1,scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) := by
  let := W.isProbability
  rw [actualParisiEndpointSeed_post_picard_jointLaw W β hβ T]
  exact scalarForwardPicardPath_seedMixture_hidden_field_law
    (actualParisiEndpointSeedLaw W β) W.law W.B W.brownian T
    (brownianFinitePath W T) (measurable_brownianFinitePath W T) (brownianFinitePath_version W T)

end SKConstants
