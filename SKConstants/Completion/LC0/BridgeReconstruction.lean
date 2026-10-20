module
public import SKConstants.GaussianProposalScalarInitialState

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace SKConstants.M1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem scalarPrimitiveBrownianPathLaw_zero_ae (W : BrownianSystem Ω) (h : ℝ≥0) :
    ∀ᵐ c ∂scalarPrimitiveBrownianPathLaw W h, c ⟨0,le_rfl,h.coe_nonneg⟩ = 0 := by
  apply (ae_map_iff (measurable_scalarPrimitiveBrownianPathVersion W h).aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval _) measurable_const)).2
  filter_upwards [scalarPrimitiveBrownianPathVersion_ae W h,
    W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h0
  exact (hω _).trans h0

theorem scalarPinnedBridge_eq_of_endpoints (h : ℝ≥0) (c : ScalarContinuousPath h)
    (h0 : c ⟨0,le_rfl,h.coe_nonneg⟩ = 0)
    (hh : c ⟨h,h.coe_nonneg,le_rfl⟩ = 0) : scalarPinnedBridge h c = c := by
  ext t
  simp [scalarPinnedBridge, h0, hh]

theorem scalarPrimitiveBridgePathLaw_endpoints_ae (W : BrownianSystem Ω)
    (h : ℝ≥0) (hh : 0 < h) :
    ∀ᵐ c ∂scalarPrimitiveBridgePathLaw W h,
      c ⟨0,le_rfl,h.coe_nonneg⟩ = 0 ∧ c ⟨h,h.coe_nonneg,le_rfl⟩ = 0 := by
  apply (ae_map_iff (measurable_scalarBrownianBridgePath h).aemeasurable
    ((measurableSet_eq_fun (ContinuousMap.measurable_eval _) measurable_const).inter
      (measurableSet_eq_fun (ContinuousMap.measurable_eval _) measurable_const))).2
  filter_upwards [scalarPrimitiveBrownianPathLaw_zero_ae W h] with c hc
  change scalarBrownianBridgePath h c ⟨0,le_rfl,h.coe_nonneg⟩ = 0 ∧
    scalarBrownianBridgePath h c ⟨h,h.coe_nonneg,le_rfl⟩ = 0
  simp [scalarBrownianBridgePath, hc, (NNReal.coe_pos.mpr hh).ne']

theorem scalarPinnedBridge_ae_eq (W : BrownianSystem Ω) (h : ℝ≥0) (hh : 0 < h) :
    ∀ᵐ c ∂scalarPrimitiveBridgePathLaw W h, scalarPinnedBridge h c = c := by
  filter_upwards [scalarPrimitiveBridgePathLaw_endpoints_ae W h hh] with c hc
  exact scalarPinnedBridge_eq_of_endpoints h c hc.1 hc.2

theorem standardGaussian_sqrt_duration_map (h : ℝ≥0) :
    (gaussianReal 0 1).map (fun e : ℝ => Real.sqrt h * e) = gaussianReal 0 h := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp [Real.sq_sqrt h.coe_nonneg]

theorem scalarQueryBridgeComplete_law (W : BrownianSystem Ω)
    (h : ℝ≥0) (hh : 0 < h) :
    ((gaussianReal 0 1).prod (scalarPrimitiveBridgePathLaw W h)).map
      (scalarQueryBridgeComplete h) = scalarPrimitiveBrownianPathLaw W h := by
  let := W.isProbability
  have hbridge : scalarPrimitiveBridgePathLaw W h = W.law.map
      (fun ω => scalarBrownianBridgePath h (scalarPrimitiveBrownianPathVersion W h ω)) := by
    exact Measure.map_map (measurable_scalarBrownianBridgePath h)
      (measurable_scalarPrimitiveBrownianPathVersion W h)
  have hpin : (fun p : ℝ × ScalarContinuousPath h => scalarQueryBridgeComplete h p) =ᵐ[
      (gaussianReal 0 1).prod (scalarPrimitiveBridgePathLaw W h)]
      (fun p => scalarBrownianBridgeComplete h (Real.sqrt h * p.1,p.2)) := by
    filter_upwards [(measurePreserving_snd (μ := gaussianReal 0 1)
      (ν := scalarPrimitiveBridgePathLaw W h)).quasiMeasurePreserving.ae
        (scalarPinnedBridge_ae_eq W h hh)] with p hp
    simp only [scalarQueryBridgeComplete, hp]
  rw [Measure.map_congr hpin]
  have hprod := Measure.map_prod_map (gaussianReal 0 1) (scalarPrimitiveBridgePathLaw W h)
    (f := fun e : ℝ => Real.sqrt h * e) (g := id) (by fun_prop) measurable_id
  rw [standardGaussian_sqrt_duration_map, Measure.map_id] at hprod
  rw [show (fun p : ℝ × ScalarContinuousPath h =>
      scalarBrownianBridgeComplete h (Real.sqrt h * p.1,p.2)) =
      scalarBrownianBridgeComplete h ∘ Prod.map (fun e : ℝ => Real.sqrt h * e) id from rfl,
    ← Measure.map_map (measurable_scalarBrownianBridgeComplete h) (by fun_prop), ← hprod,
    hbridge]
  exact scalarBrownianBridgeComplete_law W.law W.B W.brownian.toIsPreBrownianReal h hh
    (scalarPrimitiveBrownianPathVersion W h) (measurable_scalarPrimitiveBrownianPathVersion W h)
    (scalarPrimitiveBrownianPathVersion_ae W h)

def scalarQueryBridgeCoordinates (h : ℝ≥0) (c : ScalarContinuousPath h) :
    ℝ × ScalarContinuousPath h :=
  (c ⟨h,h.coe_nonneg,le_rfl⟩ / Real.sqrt h, scalarBrownianBridgePath h c)

theorem measurable_scalarQueryBridgeCoordinates (h : ℝ≥0) :
    Measurable (scalarQueryBridgeCoordinates h) :=
  ((ContinuousMap.measurable_eval _).div_const _).prodMk (measurable_scalarBrownianBridgePath h)

theorem scalarQueryBridgeComplete_coordinates (h : ℝ≥0) (hh : 0 < h)
    (c : ScalarContinuousPath h) (hc : c ⟨0,le_rfl,h.coe_nonneg⟩ = 0) :
    scalarQueryBridgeComplete h (scalarQueryBridgeCoordinates h c) = c := by
  have hs : Real.sqrt (h : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hh)).ne'
  have hp : scalarPinnedBridge h (scalarBrownianBridgePath h c) = scalarBrownianBridgePath h c := by
    apply scalarPinnedBridge_eq_of_endpoints
    · simp [scalarBrownianBridgePath, hc]
    · simp [scalarBrownianBridgePath, (NNReal.coe_pos.mpr hh).ne']
  unfold scalarQueryBridgeComplete scalarQueryBridgeCoordinates
  rw [hp, mul_div_cancel₀ _ hs]
  exact scalarBrownianBridgeComplete_path h c

theorem scalarQueryBridgeCoordinates_complete (h : ℝ≥0) (hh : 0 < h)
    (p : ℝ × ScalarContinuousPath h)
    (h0 : p.2 ⟨0,le_rfl,h.coe_nonneg⟩ = 0)
    (he : p.2 ⟨h,h.coe_nonneg,le_rfl⟩ = 0) :
    scalarQueryBridgeCoordinates h (scalarQueryBridgeComplete h p) = p := by
  have hs : Real.sqrt (h : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hh)).ne'
  have hp := scalarPinnedBridge_eq_of_endpoints h p.2 h0 he
  apply Prod.ext
  · change scalarQueryBridgeComplete h p ⟨h,h.coe_nonneg,le_rfl⟩ / Real.sqrt h = p.1
    rw [scalarQueryBridgeComplete_endpoint h hh, mul_div_cancel_left₀ _ hs]
  · change scalarBrownianBridgePath h (scalarQueryBridgeComplete h p) = p.2
    ext t
    simp only [scalarBrownianBridgePath, ContinuousMap.coe_mk]
    rw [scalarQueryBridgeComplete_endpoint h hh]
    simp only [scalarQueryBridgeComplete, hp, scalarBrownianBridgeComplete,
      ContinuousMap.coe_mk]
    ring

theorem scalarQueryBridgeCoordinates_law (W : BrownianSystem Ω)
    (h : ℝ≥0) (hh : 0 < h) :
    (scalarPrimitiveBrownianPathLaw W h).map (scalarQueryBridgeCoordinates h) =
      (gaussianReal 0 1).prod (scalarPrimitiveBridgePathLaw W h) := by
  rw [← scalarQueryBridgeComplete_law W h hh,
    Measure.map_map (measurable_scalarQueryBridgeCoordinates h)
      (measurable_scalarQueryBridgeComplete h)]
  calc
    _ = ((gaussianReal 0 1).prod (scalarPrimitiveBridgePathLaw W h)).map id := by
      apply Measure.map_congr
      filter_upwards [(measurePreserving_snd (μ := gaussianReal 0 1)
        (ν := scalarPrimitiveBridgePathLaw W h)).quasiMeasurePreserving.ae
          (scalarPrimitiveBridgePathLaw_endpoints_ae W h hh)] with p hp
      exact scalarQueryBridgeCoordinates_complete h hh p hp.1 hp.2
    _ = _ := Measure.map_id

end SKConstants.M1
