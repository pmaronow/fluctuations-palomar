module
public import SKConstants.Completion.LM1a.DriverCoordinatesLaw
public import SKConstants.Completion.LM1a.BridgeProductRecovery
public import SKConstants.Completion.LM1a.RecoveryBijection

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

section Shuffle
variable {A B C D E F : Type*}
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]
  (a : Measure A) (b : Measure B) (c : Measure C)
  (d : Measure D) (e : Measure E) (f : Measure F)
  [SFinite a] [SFinite b] [SFinite c] [SFinite d] [SFinite e] [SFinite f]

theorem prod_six_shuffle :
    ((a.prod (b.prod (c.prod d))).prod (e.prod f)).map
      (fun x => ((x.1.1,(x.1.2.1,(x.1.2.2.2,x.2.2))),(x.1.2.2.1,x.2.1))) =
      (a.prod (b.prod (d.prod f))).prod (c.prod e) := by
  have h0 := measurePreserving_prodAssoc a (b.prod (c.prod d)) (e.prod f)
  have h1 := (MeasurePreserving.id a).prod
    (measurePreserving_prodAssoc b (c.prod d) (e.prod f))
  have hq : MeasurePreserving (fun x : (C × D) × (E × F) =>
      ((x.1.1,x.2.1),(x.1.2,x.2.2)))
      ((c.prod d).prod (e.prod f)) ((c.prod e).prod (d.prod f)) :=
    ⟨by fun_prop, prod_quad_shuffle c d e f⟩
  have h2 := (MeasurePreserving.id a).prod ((MeasurePreserving.id b).prod hq)
  have h3 := (MeasurePreserving.id a).prod ((MeasurePreserving.id b).prod
    (Measure.measurePreserving_swap (μ := c.prod e) (ν := d.prod f)))
  have h4 := (MeasurePreserving.id a).prod
    (measurePreserving_prodAssoc b (d.prod f) (c.prod e)).symm
  have h5 := (measurePreserving_prodAssoc a (b.prod (d.prod f)) (c.prod e)).symm
  exact (h5.comp (h4.comp (h3.comp (h2.comp (h1.comp h0))))).map_eq
end Shuffle

def PackSourceCoordinates (δ : ℝ≥0) (r₀ q : ℕ)
    (p : DriverCoordinateInput δ (Size r₀ q) q × Ancillary δ (Size r₀ q) q) :
    SourceInput δ r₀ q :=
  ((p.1.1,(p.1.2.1,BridgeMerge δ (Size r₀ q) q (p.1.2.2.2,p.2.2))),
    PackNoise (Size r₀ q) q (p.1.2.2.1,p.2.1))

theorem measurable_PackSourceCoordinates (δ : ℝ≥0) (r₀ q : ℕ) :
    Measurable (PackSourceCoordinates δ r₀ q) :=
  (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
    ((measurable_BridgeMerge δ (Size r₀ q) q).comp
      (measurable_fst.snd.snd.snd.prodMk measurable_snd.snd)))).prodMk
    ((measurable_PackNoise (Size r₀ q) q).comp
      (measurable_fst.snd.snd.fst.prodMk measurable_snd.fst))

theorem packSourceCoordinates_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    ((driverCoordinateLaw W δ (Size r₀ q) q).prod (AncillaryLaw W δ (Size r₀ q) q)).map
      (PackSourceCoordinates δ r₀ q) = SourceLaw W δ r₀ q := by
  let D := Measure.pi (fun _ : Fin (Size r₀ q) => scalarPrimitiveBrownianPathLaw W (Horizon δ q))
  let A := Measure.pi (fun _ : Fin (Size r₀ q) =>
    scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))
  let E := Measure.pi (fun _ : Fin q => primitiveGaussian (Fin (Size r₀ q)))
  let U := Measure.pi (fun e : Fin q => Measure.pi (fun _ : Fin (Size r₀ q) =>
    scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1))))
  let R := residualNoiseLaw (Size r₀ q) q
  let V := Measure.infinitePi (fun j : UnusedBridge q => Measure.pi
    (fun _ : Fin (Size r₀ q) => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j.val)))
  have hs : MeasurePreserving
      (fun x : DriverCoordinateInput δ (Size r₀ q) q × Ancillary δ (Size r₀ q) q =>
        ((x.1.1,(x.1.2.1,(x.1.2.2.2,x.2.2))),(x.1.2.2.1,x.2.1)))
      ((D.prod (A.prod (E.prod U))).prod (R.prod V))
      ((D.prod (A.prod (U.prod V))).prod (E.prod R)) :=
    ⟨by fun_prop, prod_six_shuffle D A E U R V⟩
  have hb : MeasurePreserving (BridgeMerge δ (Size r₀ q) q) (U.prod V)
      (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (Size r₀ q) =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))) :=
    ⟨measurable_BridgeMerge _ _ _, bridgeMerge_law W δ (Size r₀ q) q⟩
  have hi := (MeasurePreserving.id D).prod ((MeasurePreserving.id A).prod hb)
  have hn : MeasurePreserving (PackNoise (Size r₀ q) q) (E.prod R)
      (paperAugmentedNoiseLaw (Size r₀ q) q) :=
    ⟨measurable_PackNoise _ _, PackNoise_law _ _⟩
  exact ((hi.prod hn).comp hs).map_eq

theorem Recover_eq_packDriverCoordinates (δ : ℝ≥0) (r₀ q : ℕ)
    (p : DriverRows δ (Size r₀ q) q × Ancillary δ (Size r₀ q) q) :
    Recover δ r₀ q p = PackSourceCoordinates δ r₀ q (DriverCoordinates δ (Size r₀ q) q p.1,p.2) := by
  have hb : BridgeMerge δ (Size r₀ q) q
      ((DriverCoordinates δ (Size r₀ q) q p.1).2.2.2,p.2.2) =
      RecoveredBridges δ (Size r₀ q) q p := by
    funext j i
    by_cases hu : j=0 ∨ q<j
    · have h := congrFun (BridgeMerge_unused δ (Size r₀ q) q
        ((DriverCoordinates δ (Size r₀ q) q p.1).2.2.2,p.2.2) ⟨j,hu⟩) i
      simpa only [RecoveredBridges, dite_eq_left hu] using h
    · cases j with
      | zero => exact (hu (Or.inl rfl)).elim
      | succ k =>
        let e : Fin q := ⟨k,by omega⟩
        have h := congrFun (BridgeMerge_used δ (Size r₀ q) q
          ((DriverCoordinates δ (Size r₀ q) q p.1).2.2.2,p.2.2) e) i
        simpa only [DriverCoordinates, GrowingPrimitiveCoordinates, RecoveredBridges,
          dite_eq_right hu, e, Fin.succ] using h
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact hb.symm
  · rfl

theorem growingSource_recovery_joint_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    ((driverRowsLaw W δ (Size r₀ q) q).prod (AncillaryLaw W δ (Size r₀ q) q)).map
      (Recover δ r₀ q) = SourceLaw W δ r₀ q := by
  have he : Recover δ r₀ q = PackSourceCoordinates δ r₀ q ∘
      Prod.map (DriverCoordinates δ (Size r₀ q) q) id :=
    funext (Recover_eq_packDriverCoordinates δ r₀ q)
  rw [he, ← Measure.map_map (measurable_PackSourceCoordinates δ r₀ q)
    ((measurable_DriverCoordinates δ (Size r₀ q) q).prodMap measurable_id),
    ← Measure.map_prod_map _ _ (measurable_DriverCoordinates δ (Size r₀ q) q) measurable_id,
    driverCoordinates_law W δ hδ, Measure.map_id, packSourceCoordinates_law W δ r₀ q]

theorem growingSource_drivers_ancillary_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    (SourceLaw W δ r₀ q).map (fun s =>
      (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s)) =
      (driverRowsLaw W δ (Size r₀ q) q).prod (AncillaryLaw W δ (Size r₀ q) q) :=
  (primitive_product_law_iff W δ hδ r₀ q).mp (growingSource_recovery_joint_law W δ hδ r₀ q)

theorem growingSource_drivers_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    (SourceLaw W δ r₀ q).map (SourceDrivers δ r₀ q) = driverRowsLaw W δ (Size r₀ q) q := by
  have h := congrArg (fun μ => μ.map Prod.fst) (growingSource_drivers_ancillary_law W δ hδ r₀ q)
  rw [Measure.map_map measurable_fst
    ((measurable_SourceDrivers δ r₀ q).prodMk (measurable_SourceAncillary δ r₀ q)),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

end SKConstants.M1
