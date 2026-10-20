module
public import SKConstants.Completion.LM1a.PrimitiveRecovery
public import SKConstants.Completion.LM1a.PathDetermination

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem sourceDrivers_recover (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ)
    (p : DriverRows δ (Size r₀ q) q × Ancillary δ (Size r₀ q) q) :
    SourceDrivers δ r₀ q (Recover δ r₀ q p) = p.1 := by
  funext i
  apply Prod.ext
  · apply growingPath_eq_of_restriction_cells δ q
    · exact sourcePast_initial_restriction δ r₀ q (Recover δ r₀ q p) i
    · intro e
      have h := sourcePast_cell δ r₀ q (Recover δ r₀ q p) e i
      have hE : NoiseEndpoints (Size r₀ q) q (Recover δ r₀ q p).2 e i =
          (DriverCellCoordinates δ (Size r₀ q) q p.1 e i).1 :=
        congrArg (fun E => E e i) (NoiseEndpoints_pack (Size r₀ q) q
          (fun a => WithLp.toLp 2 (fun k =>
            (DriverCellCoordinates δ (Size r₀ q) q p.1 a k).1),p.2.1))
      have hu : ¬(e.val+1=0 ∨ q<e.val+1) := by omega
      have hB : (Recover δ r₀ q p).1.2.2 (e.val+1) i =
          (DriverCellCoordinates δ (Size r₀ q) q p.1 e i).2 := by
        simp only [Recover, RecoveredBridges, dite_eq_right hu,
          DriverCellCoordinates, Fin.succ]
      rw [hE,hB] at h
      exact h.trans (scalarQueryBridgeComplete_coordinates _
        (growingQueryDuration_pos δ hδ _) _ (GrowingCell_zero δ q e.succ (p.1 i).1))
  · rfl

theorem sourceAncillary_recover (δ : ℝ≥0) (r₀ q : ℕ)
    (p : DriverRows δ (Size r₀ q) q × Ancillary δ (Size r₀ q) q) :
    SourceAncillary δ r₀ q (Recover δ r₀ q p) = p.2 := by
  apply Prod.ext
  · exact NoiseResidual_pack (Size r₀ q) q _
  · funext j i
    simp only [SourceAncillary, Recover, RecoveredBridges, dite_eq_left j.property]

theorem recover_extracted_source_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    ((SourceLaw W δ r₀ q).map (fun s =>
      (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s))).map (Recover δ r₀ q) =
      SourceLaw W δ r₀ q := by
  rw [Measure.map_map (measurable_Recover δ r₀ q)
    ((measurable_SourceDrivers δ r₀ q).prodMk (measurable_SourceAncillary δ r₀ q))]
  exact (Measure.map_congr (Recover_source_ae W δ hδ r₀ q)).trans Measure.map_id

theorem primitive_product_law_iff (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    ((driverRowsLaw W δ (Size r₀ q) q).prod (AncillaryLaw W δ (Size r₀ q) q)).map
        (Recover δ r₀ q) = SourceLaw W δ r₀ q ↔
      (SourceLaw W δ r₀ q).map (fun s =>
        (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s)) =
      (driverRowsLaw W δ (Size r₀ q) q).prod (AncillaryLaw W δ (Size r₀ q) q) := by
  constructor
  · intro h
    rw [← h, Measure.map_map
      ((measurable_SourceDrivers δ r₀ q).prodMk (measurable_SourceAncillary δ r₀ q))
      (measurable_Recover δ r₀ q)]
    have he : (fun s => (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s)) ∘
        Recover δ r₀ q = id := by
      funext p
      exact Prod.ext (sourceDrivers_recover δ hδ r₀ q p) (sourceAncillary_recover δ r₀ q p)
    rw [he, Measure.map_id]
  · intro h
    rw [← h]
    exact recover_extracted_source_law W δ hδ r₀ q

end SKConstants.M1
