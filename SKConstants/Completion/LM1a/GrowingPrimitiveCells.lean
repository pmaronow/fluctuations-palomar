module
public import SKConstants.Completion.LM1a.GrowingCells
public import SKConstants.Completion.LM1a.ResidualNoise
public import SKConstants.Completion.LM1a.LiteralPathRecovery

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

def GrowingPrimitiveCoordinates (δ : ℝ≥0) (q : ℕ)
    (b : ScalarContinuousPath (Horizon δ q)) :
    ScalarContinuousPath (growingQueryDuration δ 0) ×
      ((e : Fin q) → ℝ × ScalarContinuousPath (growingQueryDuration δ (e.val+1))) :=
  (scalarInitialAuxiliaryRestriction (Horizon δ q) (growingQueryDuration δ 0)
    (growingFirstDuration_le_horizon δ q) b, fun e => scalarQueryBridgeCoordinates
    (growingQueryDuration δ (e.val+1)) (GrowingCell δ q e.succ b))

theorem measurable_GrowingPrimitiveCoordinates (δ : ℝ≥0) (q : ℕ) :
    Measurable (GrowingPrimitiveCoordinates δ q) :=
  (measurable_scalarInitialAuxiliaryRestriction _ _ _).prodMk
    (Measurable.of_eval (fun e => (measurable_scalarQueryBridgeCoordinates _).comp
      (measurable_GrowingCell δ q e.succ)))

theorem growingPrimitiveCoordinates_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) :
    (scalarPrimitiveBrownianPathLaw W (Horizon δ q)).map
      (GrowingPrimitiveCoordinates δ q) =
      (scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0)).prod
        (Measure.pi (fun e : Fin q => (gaussianReal 0 1).prod
          (scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1))))) := by
  let F : (ScalarContinuousPath (growingQueryDuration δ 0) ×
      ((e : Fin q) → ScalarContinuousPath (growingQueryDuration δ (e.val+1)))) →
      ScalarContinuousPath (growingQueryDuration δ 0) ×
        ((e : Fin q) → ℝ × ScalarContinuousPath (growingQueryDuration δ (e.val+1))) :=
    fun p => (p.1,fun e => scalarQueryBridgeCoordinates
      (growingQueryDuration δ (e.val+1)) (p.2 e))
  have hm : Measurable F := measurable_fst.prodMk
    (Measurable.of_eval (fun e => (measurable_scalarQueryBridgeCoordinates _).comp
      ((measurable_pi_apply e).comp measurable_snd)))
  have he : GrowingPrimitiveCoordinates δ q =ᵐ[scalarPrimitiveBrownianPathLaw W (Horizon δ q)]
      F ∘ piHead (fun j : Fin (q+1) => ScalarContinuousPath (growingQueryDuration δ j.val)) ∘
        (fun b j => GrowingCell δ q j b) := by
    filter_upwards [scalarPrimitiveBrownianPathLaw_zero_ae W (Horizon δ q)] with b hb
    apply Prod.ext
    · ext t
      simp [GrowingPrimitiveCoordinates, F, piHead, GrowingCell,
        scalarInitialAuxiliaryRestriction, growingQueryTime_zero, hb]
    · rfl
  have hC := Measurable.of_eval (fun j => measurable_GrowingCell δ q j)
  rw [Measure.map_congr he, ← Measure.map_map hm ((piHead _).measurable.comp hC),
    ← Measure.map_map (piHead _).measurable
      (Measurable.of_eval (fun j => measurable_GrowingCell δ q j)),
    growingBrownianCells_law, piHead_law]
  have hpi : (Measure.pi (fun e : Fin q => scalarPrimitiveBrownianPathLaw W
      (growingQueryDuration δ (e.val+1)))).map
        (fun b (e : Fin q) => scalarQueryBridgeCoordinates
          (growingQueryDuration δ (e.val+1)) (b e)) =
      Measure.pi (fun e : Fin q => (gaussianReal 0 1).prod
        (scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1)))) := by
    have (e : Fin q) : IsProbabilityMeasure
        ((scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ (e.val+1))).map
          (scalarQueryBridgeCoordinates (growingQueryDuration δ (e.val+1)))) := by
      rw [scalarQueryBridgeCoordinates_law W _ (growingQueryDuration_pos δ hδ _)]
      infer_instance
    rw [Measure.pi_map_pi
      (μ := fun e : Fin q => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ (e.val+1)))
      (f := fun e : Fin q => scalarQueryBridgeCoordinates (growingQueryDuration δ (e.val+1)))
      (fun e => (measurable_scalarQueryBridgeCoordinates
        (growingQueryDuration δ (e.val+1))).aemeasurable)]
    exact congrArg Measure.pi (funext (fun e : Fin q => scalarQueryBridgeCoordinates_law W _
      (growingQueryDuration_pos δ hδ (e.val+1))))
  have hp := Measure.map_prod_map
    (scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))
    (Measure.pi (fun e : Fin q => scalarPrimitiveBrownianPathLaw W
      (growingQueryDuration δ (e.val+1))))
    (f := id)
    (g := fun b (e : Fin q) => scalarQueryBridgeCoordinates
      (growingQueryDuration δ (e.val+1)) (b e)) measurable_id
    (Measurable.of_eval (fun e : Fin q => (measurable_scalarQueryBridgeCoordinates
      (growingQueryDuration δ (e.val+1))).comp (measurable_pi_apply e)))
  rw [Measure.map_id, hpi] at hp
  exact hp.symm

theorem growingBrownianRowsCells_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (q n : ℕ) :
    (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (Horizon δ q))).map
      (fun b i j => GrowingCell δ q j (b i)) =
      Measure.pi (fun _ : Fin n => Measure.pi (fun j : Fin (q+1) =>
        scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ j.val))) := by
  rw [Measure.pi_map_pi (fun _ =>
    (Measurable.of_eval (fun j => measurable_GrowingCell δ q j)).aemeasurable)]
  simp_rw [growingBrownianCells_law]

theorem growingPrimitiveRowsCoordinates_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (q n : ℕ) :
    (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (Horizon δ q))).map
      (fun b i => GrowingPrimitiveCoordinates δ q (b i)) =
      Measure.pi (fun _ : Fin n =>
        (scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0)).prod
          (Measure.pi (fun e : Fin q => (gaussianReal 0 1).prod
            (scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1)))))) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_GrowingPrimitiveCoordinates δ q).aemeasurable)]
  simp_rw [growingPrimitiveCoordinates_law W δ hδ q]

end SKConstants.M1
