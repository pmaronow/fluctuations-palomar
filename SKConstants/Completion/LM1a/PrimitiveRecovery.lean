module
public import SKConstants.Completion.LM1a.LiteralPathRecovery
public import SKConstants.Completion.LM1a.ProductTools

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev UnusedBridge (q : ℕ) := {j : ℕ // j=0 ∨ q<j}

abbrev DriverRows (δ : ℝ≥0) (n q : ℕ) :=
  Fin n → ScalarContinuousPath (Horizon δ q) × ScalarContinuousPath (Horizon δ q)

abbrev Ancillary (δ : ℝ≥0) (n q : ℕ) :=
  ResidualNoise n q × ((j : UnusedBridge q) →
    Fin n → ScalarContinuousPath (growingQueryDuration δ j.val))

def driverRowsLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    Measure (DriverRows δ n q) :=
  Measure.pi (fun _ : Fin n =>
    (scalarPrimitiveBrownianPathLaw W (Horizon δ q)).prod
      (scalarPrimitiveBrownianPathLaw W (Horizon δ q)))

def AncillaryLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    Measure (Ancillary δ n q) :=
  (residualNoiseLaw n q).prod
    (Measure.infinitePi (fun j : UnusedBridge q => Measure.pi (fun _ : Fin n =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j.val))))

instance driverRowsLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    IsProbabilityMeasure (driverRowsLaw W δ n q) := by unfold driverRowsLaw; infer_instance

instance AncillaryLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    IsProbabilityMeasure (AncillaryLaw W δ n q) := by unfold AncillaryLaw; infer_instance

def DriverCellCoordinates (δ : ℝ≥0) (n q : ℕ) (b : DriverRows δ n q)
    (e : Fin q) (i : Fin n) :=
  scalarQueryBridgeCoordinates (growingQueryDuration δ (e.val+1))
    (GrowingCell δ q e.succ (b i).1)

def RecoveredBridges (δ : ℝ≥0) (n q : ℕ)
    (p : DriverRows δ n q × Ancillary δ n q) (j : ℕ) (i : Fin n) :
    ScalarContinuousPath (growingQueryDuration δ j) :=
  if h : j=0 ∨ q<j then p.2.2 ⟨j,h⟩ i else
    (scalarQueryBridgeCoordinates (growingQueryDuration δ j)
      (GrowingCell δ q ⟨j,by omega⟩ (p.1 i).1)).2

def Recover (δ : ℝ≥0) (r₀ q : ℕ)
    (p : DriverRows δ (Size r₀ q) q × Ancillary δ (Size r₀ q) q) : SourceInput δ r₀ q :=
  ((fun i => (p.1 i).2,
    (fun i => scalarInitialAuxiliaryRestriction (Horizon δ q) (growingQueryDuration δ 0)
      (growingFirstDuration_le_horizon δ q)
      (p.1 i).1, RecoveredBridges δ (Size r₀ q) q p)),
    PackNoise (Size r₀ q) q
      (fun e => WithLp.toLp 2 (fun i => (DriverCellCoordinates δ (Size r₀ q) q p.1 e i).1),p.2.1))

def SourceAncillary (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :
    Ancillary δ (Size r₀ q) q :=
  (NoiseResidual (Size r₀ q) q s.2,fun j => s.1.2.2 j.val)

theorem measurable_DriverCellCoordinates (δ : ℝ≥0) (n q : ℕ) (e : Fin q) (i : Fin n) :
    Measurable (fun b => DriverCellCoordinates δ n q b e i) :=
  (measurable_scalarQueryBridgeCoordinates _).comp
    ((measurable_GrowingCell δ q e.succ).comp ((measurable_pi_apply i).fst))

theorem measurable_RecoveredBridges (δ : ℝ≥0) (n q : ℕ) :
    Measurable (RecoveredBridges δ n q) := by
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro i
  by_cases h : j=0 ∨ q<j
  · have hm : Measurable (fun p : DriverRows δ n q × Ancillary δ n q => p.2.2 ⟨j,h⟩ i) :=
      (measurable_pi_apply i).comp
        ((measurable_pi_apply (⟨j,h⟩ : UnusedBridge q)).comp
          (measurable_snd.snd : Measurable
            (fun p : DriverRows δ n q × Ancillary δ n q => p.2.2)))
    simpa only [RecoveredBridges, dite_eq_left h] using hm
  · have hm : Measurable (fun p : DriverRows δ n q × Ancillary δ n q =>
        (scalarQueryBridgeCoordinates (growingQueryDuration δ j)
          (GrowingCell δ q ⟨j,by omega⟩ (p.1 i).1)).2) :=
      (((measurable_scalarQueryBridgeCoordinates _).comp
        ((measurable_GrowingCell δ q ⟨j,by omega⟩).comp
          ((measurable_pi_apply i).comp measurable_fst).fst)).snd)
    simpa only [RecoveredBridges, dite_eq_right h] using hm

theorem measurable_Recover (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (Recover δ r₀ q) := by
  refine ((Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).snd)).prodMk
    ((Measurable.of_eval (fun i => (measurable_scalarInitialAuxiliaryRestriction _ _ _).comp
      (((measurable_pi_apply i).comp measurable_fst).fst))).prodMk
        (measurable_RecoveredBridges δ (Size r₀ q) q))).prodMk ?_
  apply (measurable_PackNoise (Size r₀ q) q).comp
  refine (Measurable.of_eval (fun e => (WithLp.measurable_toLp 2 _).comp
    (Measurable.of_eval (fun i => ?_)))).prodMk measurable_snd.fst
  exact ((measurable_DriverCellCoordinates δ (Size r₀ q) q e i).comp measurable_fst).fst

theorem measurable_SourceAncillary (δ : ℝ≥0) (r₀ q : ℕ) :
    Measurable (SourceAncillary δ r₀ q) :=
  ((measurable_NoiseResidual _ _).comp measurable_snd).prodMk
    (Measurable.of_eval (fun j => (measurable_pi_apply j.val).comp measurable_fst.snd.snd))

theorem DriverCellCoordinates_source (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ)
    (s : SourceInput δ r₀ q) (e : Fin q) (i : Fin (Size r₀ q))
    (hb : (s.1.2.2 (e.val+1) i) ⟨0,le_rfl,(growingQueryDuration δ (e.val+1)).coe_nonneg⟩ = 0 ∧
      (s.1.2.2 (e.val+1) i)
        ⟨growingQueryDuration δ (e.val+1),(growingQueryDuration δ (e.val+1)).coe_nonneg,le_rfl⟩ = 0) :
    DriverCellCoordinates δ (Size r₀ q) q (SourceDrivers δ r₀ q s) e i =
      (NoiseEndpoints (Size r₀ q) q s.2 e i,s.1.2.2 (e.val+1) i) := by
  unfold DriverCellCoordinates SourceDrivers
  rw [sourcePast_cell]
  exact scalarQueryBridgeCoordinates_complete _ (growingQueryDuration_pos δ hδ _)
    _ hb.1 hb.2

theorem Recover_source_of_bridge_endpoints (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ)
    (s : SourceInput δ r₀ q)
    (hb : ∀ (e : Fin q) (i : Fin (Size r₀ q)),
      (s.1.2.2 (e.val+1) i) ⟨0,le_rfl,(growingQueryDuration δ (e.val+1)).coe_nonneg⟩ = 0 ∧
      (s.1.2.2 (e.val+1) i)
        ⟨growingQueryDuration δ (e.val+1),(growingQueryDuration δ (e.val+1)).coe_nonneg,le_rfl⟩ = 0) :
    Recover δ r₀ q (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s) = s := by
  have hE : (fun e : Fin q => WithLp.toLp 2 (fun i =>
      (DriverCellCoordinates δ (Size r₀ q) q (SourceDrivers δ r₀ q s) e i).1)) =
        NoiseEndpoints (Size r₀ q) q s.2 := by
    funext e
    ext i
    exact congrArg Prod.fst (DriverCellCoordinates_source δ hδ r₀ q s e i (hb e i))
  have hB : RecoveredBridges δ (Size r₀ q) q
      (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s) = s.1.2.2 := by
    funext j i
    by_cases hu : j=0 ∨ q<j
    · simp only [RecoveredBridges, dite_eq_left hu, SourceAncillary]
    · cases j with
      | zero => exact (hu (Or.inl rfl)).elim
      | succ k =>
        let e : Fin q := ⟨k,by omega⟩
        have hc := congrArg Prod.snd (DriverCellCoordinates_source δ hδ r₀ q s e i (hb e i))
        simp only [DriverCellCoordinates, SourceDrivers] at hc
        simpa only [RecoveredBridges, dite_eq_right hu, e, SourceDrivers, Fin.succ] using hc
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        exact sourcePast_initial_restriction δ r₀ q s i
      · exact hB
  · change PackNoise (Size r₀ q) q (_,NoiseResidual (Size r₀ q) q s.2) = s.2
    rw [hE]
    exact PackNoise_extract _ _ s.2

theorem source_bridges_endpoints_ae (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    ∀ᵐ s ∂SourceLaw W δ r₀ q, ∀ (j : ℕ) (i : Fin (Size r₀ q)),
      (s.1.2.2 j i) ⟨0,le_rfl,(growingQueryDuration δ j).coe_nonneg⟩ = 0 ∧
      (s.1.2.2 j i)
        ⟨growingQueryDuration δ j,(growingQueryDuration δ j).coe_nonneg,le_rfl⟩ = 0 := by
  let μD := Measure.pi (fun _ : Fin (Size r₀ q) => scalarPrimitiveBrownianPathLaw W (Horizon δ q))
  let μA := Measure.pi (fun _ : Fin (Size r₀ q) =>
    scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))
  let μB := Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (Size r₀ q) =>
    scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))
  have hp : MeasurePreserving (fun s : SourceInput δ r₀ q => s.1.2.2)
      (SourceLaw W δ r₀ q) μB :=
    (measurePreserving_snd (μ := μA) (ν := μB)).comp
      ((measurePreserving_snd (μ := μD) (ν := μA.prod μB)).comp
        (measurePreserving_fst (μ := μD.prod (μA.prod μB))
          (ν := paperAugmentedNoiseLaw (Size r₀ q) q)))
  refine ae_all_iff.2 (fun j => ae_all_iff.2 (fun i => ?_))
  have hrow := measurePreserving_eval_infinitePi
    (fun j : ℕ => Measure.pi (fun _ : Fin (Size r₀ q) =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))) j
  have hcoord := measurePreserving_eval
    (fun _ : Fin (Size r₀ q) => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)) i
  exact ((hcoord.comp hrow).comp hp).quasiMeasurePreserving.ae
    (scalarPrimitiveBridgePathLaw_endpoints_ae W _ (growingQueryDuration_pos δ hδ j))

theorem Recover_source_ae (W : BrownianSystem Ω) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    ∀ᵐ s ∂SourceLaw W δ r₀ q,
      Recover δ r₀ q (SourceDrivers δ r₀ q s,SourceAncillary δ r₀ q s) = s := by
  filter_upwards [source_bridges_endpoints_ae W δ hδ r₀ q] with s hs
  exact Recover_source_of_bridge_endpoints δ hδ r₀ q s (fun e i => hs (e.val+1) i)

end SKConstants.M1
