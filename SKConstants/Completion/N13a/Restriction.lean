module

public import SKConstants.Completion.N13a.Statement

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem coarsePrefix_completion_measurable (n qf qb : ℕ) (hq : qb ≤ qf) :
    Measurable (coarsePrefix_completion n qf qb hq) := by
  induction qb generalizing qf with
  | zero => cases qf <;> exact measurable_const
  | succ qb ih =>
    cases qf with
    | zero => omega
    | succ qf =>
      exact measurable_fst.prodMk ((ih qf (by omega)).comp measurable_snd)

theorem coarsePrefix_completion_law (n qf qb : ℕ) (hq : qb ≤ qf) :
    (paperCompletionNoiseLaw n qf).map (coarsePrefix_completion n qf qb hq) =
      paperCompletionNoiseLaw n qb := by
  induction qb generalizing qf with
  | zero =>
    change (paperCompletionNoiseLaw n qf).map (fun _ => ()) = Measure.dirac ()
    simp
  | succ qb ih =>
    cases qf with
    | zero => omega
    | succ qf =>
      change ((primitiveGaussian (Fin n)).prod (paperCompletionNoiseLaw n qf)).map
        (Prod.map id (coarsePrefix_completion n qf qb (by omega))) = _
      rw [← Measure.map_prod_map _ _ measurable_id
        (coarsePrefix_completion_measurable n qf qb (by omega)), Measure.map_id,
        ih qf (by omega)]
      rfl

theorem coarsePrefix_input_measurable (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf) :
    Measurable (coarsePrefix_input δ n qb qf hq) := by
  unfold coarsePrefix_input
  exact (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
    ((coarsePrefix_completion_measurable n qf qb hq).comp measurable_fst.snd.snd))).prodMk
    (Measurable.of_eval (fun i =>
      (measurable_scalarInitialAuxiliaryRestriction _ _ _).comp
        ((measurable_pi_apply i).comp measurable_snd)))

theorem coarsePrefix_input_law (W : BrownianSystem Ω) (δ : ℝ≥0)
    (n qb qf : ℕ) (hq : qb ≤ qf) :
    (coarsePrefix_law W δ n qf).map (coarsePrefix_input δ n qb qf hq) =
      coarsePrefix_law W δ n qb := by
  let R := scalarInitialAuxiliaryRestriction (scalarGrowingSourceHorizon δ qf)
    (scalarGrowingSourceHorizon δ qb)
    (M1.growingQueryTime_monotone δ (Nat.add_le_add_right hq 1))
  have hR : Measurable R := measurable_scalarInitialAuxiliaryRestriction _ _ _
  have hRD : Measurable (fun d : Fin n → ScalarContinuousPath
      (scalarGrowingSourceHorizon δ qf) => fun i => R (d i)) :=
    Measurable.of_eval (fun i => hR.comp (measurable_pi_apply i))
  have hD : (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
      (scalarGrowingSourceHorizon δ qf))).map (fun d i => R (d i)) =
      Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
        (scalarGrowingSourceHorizon δ qb)) := by
    rw [Measure.pi_map_pi (fun _ => hR.aemeasurable)]
    congr 1
    funext i
    exact M1.scalarPrimitiveBrownianRestriction_law W _ _ _
  have hC := coarsePrefix_completion_measurable n qf qb hq
  let A : Measure (ScalarGrowingReplayAuxData δ n) :=
    (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
      (growingQueryDuration δ 0))).prod
      (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin n =>
        scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))
  unfold coarsePrefix_law scalarGrowingReplayStaticLaw
  change ((A.prod ((skDisorderLaw n).prod (paperCompletionNoiseLaw n qf))).prod
    (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
      (scalarGrowingSourceHorizon δ qf)))).map
    (Prod.map (Prod.map id (Prod.map id (coarsePrefix_completion n qf qb hq)))
      (fun d i => R (d i))) = _
  rw [← Measure.map_prod_map _ _ (measurable_id.prodMap (measurable_id.prodMap hC))
    hRD,
    ← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap hC),
    ← Measure.map_prod_map _ _ measurable_id hC,
    Measure.map_id, Measure.map_id, coarsePrefix_completion_law n qf qb hq, hD]

theorem coarsePrefix_castInput_measurable (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m) :
    Measurable (coarsePrefix_castInput δ q h) := by
  subst m
  exact measurable_id

theorem coarsePrefix_castInput_law (W : BrownianSystem Ω) (δ : ℝ≥0)
    (q : ℕ) {n m : ℕ} (h : n = m) :
    (coarsePrefix_law W δ n q).map (coarsePrefix_castInput δ q h) =
      coarsePrefix_law W δ m q := by
  subst m
  exact Measure.map_id

theorem coarsePrefix_replayInput_measurable (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) :
    Measurable (coarsePrefix_replayInput δ rf qf rb qb hdim hq) :=
  (coarsePrefix_castInput_measurable δ qb hdim).comp
    (coarsePrefix_input_measurable δ (rf + qf) qb qf hq)

theorem coarsePrefix_replayInput_law (W : BrownianSystem Ω) (δ : ℝ≥0)
    (rf qf rb qb : ℕ) (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) :
    (M1.ReplayLaw W δ rf qf).map (coarsePrefix_replayInput δ rf qf rb qb hdim hq) =
      M1.ReplayLaw W δ rb qb := by
  change (coarsePrefix_law W δ (rf + qf) qf).map
    (coarsePrefix_castInput δ qb hdim ∘ coarsePrefix_input δ (rf + qf) qb qf hq) = _
  rw [← Measure.map_map (coarsePrefix_castInput_measurable δ qb hdim)
    (coarsePrefix_input_measurable δ (rf + qf) qb qf hq),
    coarsePrefix_input_law W δ (rf + qf) qb qf hq,
    coarsePrefix_castInput_law W δ qb hdim]
  rfl

end SKConstants.N13a
