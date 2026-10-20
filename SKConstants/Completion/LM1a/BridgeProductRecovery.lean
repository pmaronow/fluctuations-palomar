module
public import SKConstants.Completion.LM1a.PrimitiveRecovery

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

abbrev UsedBridge (q : ℕ) := {j : ℕ // ¬(j=0 ∨ q<j)}

def usedBridgeEquiv (q : ℕ) : Fin q ≃ UsedBridge q where
  toFun e := ⟨e.val+1,by omega⟩
  invFun j := ⟨j.val-1,by have h := j.property; omega⟩
  left_inv e := by apply Fin.ext; simp
  right_inv j := by apply Subtype.ext; have h := j.property; dsimp; omega

abbrev BridgeCells (δ : ℝ≥0) (n q : ℕ) :=
  (e : Fin q) → Fin n → ScalarContinuousPath (growingQueryDuration δ (e.val+1))

abbrev UnusedBridges (δ : ℝ≥0) (n q : ℕ) :=
  (j : UnusedBridge q) → Fin n → ScalarContinuousPath (growingQueryDuration δ j.val)

def BridgeMerge (δ : ℝ≥0) (n q : ℕ) (p : BridgeCells δ n q × UnusedBridges δ n q) :
    (j : ℕ) → Fin n → ScalarContinuousPath (growingQueryDuration δ j) :=
  (MeasurableEquiv.piEquivPiSubtypeProd
    (fun j : ℕ => Fin n → ScalarContinuousPath (growingQueryDuration δ j))
    (fun j => j=0 ∨ q<j)).symm
      (p.2, MeasurableEquiv.piCongrLeft
        (fun j : UsedBridge q => Fin n → ScalarContinuousPath (growingQueryDuration δ j.val))
        (usedBridgeEquiv q) p.1)

theorem measurable_BridgeMerge (δ : ℝ≥0) (n q : ℕ) : Measurable (BridgeMerge δ n q) :=
  (MeasurableEquiv.piEquivPiSubtypeProd _ _).symm.measurable.comp
    (measurable_snd.prodMk ((MeasurableEquiv.piCongrLeft _ _).measurable.comp measurable_fst))

theorem bridgeMerge_law (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    ((Measure.pi (fun e : Fin q => Measure.pi (fun _ : Fin n =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1))))).prod
      (Measure.infinitePi (fun j : UnusedBridge q => Measure.pi (fun _ : Fin n =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j.val))))).map
      (BridgeMerge δ n q) =
    Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin n =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))) := by
  let μ (j : ℕ) := Measure.pi (fun _ : Fin n =>
    scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))
  let U := Measure.infinitePi (fun j : UnusedBridge q => μ j.val)
  let V := Measure.infinitePi (fun j : UsedBridge q => μ j.val)
  let E := MeasurableEquiv.piCongrLeft
    (fun j : UsedBridge q => Fin n → ScalarContinuousPath (growingQueryDuration δ j.val))
    (usedBridgeEquiv q)
  have hE : MeasurePreserving E (Measure.pi (fun e : Fin q => μ (e.val+1))) V := by
    refine ⟨E.measurable, ?_⟩
    have h := Measure.infinitePi_map_piCongrLeft
      (fun j : UsedBridge q => μ j.val) (usedBridgeEquiv q)
    simpa only [Measure.infinitePi_eq_pi, E, V, usedBridgeEquiv, Equiv.coe_fn_mk] using h
  let F := MeasurableEquiv.piEquivPiSubtypeProd
    (fun j : ℕ => Fin n → ScalarContinuousPath (growingQueryDuration δ j))
    (fun j => j=0 ∨ q<j)
  have hF : MeasurePreserving F (Measure.infinitePi μ) (U.prod V) :=
    ⟨F.measurable, infinitePi_partition_law μ (fun j => j=0 ∨ q<j)⟩
  have h := hF.symm.comp
    ((Measure.measurePreserving_swap (μ := V) (ν := U)).comp
      (hE.prod (MeasurePreserving.id U)))
  exact h.map_eq

theorem BridgeMerge_unused (δ : ℝ≥0) (n q : ℕ)
    (p : BridgeCells δ n q × UnusedBridges δ n q) (j : UnusedBridge q) :
    BridgeMerge δ n q p j.val = p.2 j := by
  simp [BridgeMerge, j.property]

theorem BridgeMerge_used (δ : ℝ≥0) (n q : ℕ)
    (p : BridgeCells δ n q × UnusedBridges δ n q) (e : Fin q) :
    BridgeMerge δ n q p (e.val+1) = p.1 e := by
  simp [BridgeMerge, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', usedBridgeEquiv]

end SKConstants.M1
