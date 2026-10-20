module

public import SKConstants.Completion.N13a.Restriction

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal Blueprint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev PrefixAux (δ : ℝ≥0) (n q : ℕ) :=
  ScalarGrowingReplayAuxData δ n × PaperCompletionNoise n q ×
    (Fin n → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))

def coarsePrefix_auxLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    Measure (PrefixAux δ n q) :=
  ((Measure.pi (fun _ : Fin n =>
      scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
    (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin n =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))).prod
  ((paperCompletionNoiseLaw n q).prod (Measure.pi (fun _ : Fin n =>
    scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))))

def coarsePrefix_aux (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf) :
    PrefixAux δ n qf → PrefixAux δ n qb :=
  fun a => (a.1,coarsePrefix_completion n qf qb hq a.2.1,
    fun i => scalarInitialAuxiliaryRestriction (scalarGrowingSourceHorizon δ qf)
      (scalarGrowingSourceHorizon δ qb)
      (M1.growingQueryTime_monotone δ (by omega)) (a.2.2 i))

theorem coarsePrefix_aux_measurable (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf) :
    Measurable (coarsePrefix_aux δ n qb qf hq) := by
  exact measurable_fst.prodMk
    (((coarsePrefix_completion_measurable n qf qb hq).comp measurable_snd.fst).prodMk
      (Measurable.of_eval (fun i => (measurable_scalarInitialAuxiliaryRestriction _ _ _).comp
        ((measurable_pi_apply i).comp measurable_snd.snd))))

theorem coarsePrefix_aux_law (W : BrownianSystem Ω) (δ : ℝ≥0)
    (n qb qf : ℕ) (hq : qb ≤ qf) :
    (coarsePrefix_auxLaw W δ n qf).map (coarsePrefix_aux δ n qb qf hq) =
      coarsePrefix_auxLaw W δ n qb := by
  let R := scalarInitialAuxiliaryRestriction (scalarGrowingSourceHorizon δ qf)
    (scalarGrowingSourceHorizon δ qb) (M1.growingQueryTime_monotone δ (by omega))
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
  unfold coarsePrefix_auxLaw
  change (Measure.prod _ ((paperCompletionNoiseLaw n qf).prod
    (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
      (scalarGrowingSourceHorizon δ qf))))).map
    (Prod.map id (Prod.map (coarsePrefix_completion n qf qb hq) (fun d i => R (d i)))) = _
  have hC := coarsePrefix_completion_measurable n qf qb hq
  rw [← Measure.map_prod_map _ _ measurable_id (hC.prodMap hRD),
    ← Measure.map_prod_map _ _ hC hRD, Measure.map_id,
    coarsePrefix_completion_law n qf qb hq, hD]

def coarsePrefix_castAux (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m) :
    PrefixAux δ n q → PrefixAux δ m q := by
  subst m
  exact id

theorem coarsePrefix_castAux_measurable (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m) :
    Measurable (coarsePrefix_castAux δ q h) := by
  subst m
  exact measurable_id

theorem coarsePrefix_castAux_law (W : BrownianSystem Ω) (δ : ℝ≥0)
    (q : ℕ) {n m : ℕ} (h : n = m) :
    (coarsePrefix_auxLaw W δ n q).map (coarsePrefix_castAux δ q h) =
      coarsePrefix_auxLaw W δ m q := by
  subst m
  exact Measure.map_id

def coarsePrefix_replayAux (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf+qf=rb+qb) (hq : qb ≤ qf) : ReplayAux δ rf qf → ReplayAux δ rb qb :=
  coarsePrefix_castAux δ qb hdim ∘ coarsePrefix_aux δ (rf+qf) qb qf hq

theorem coarsePrefix_replayAux_measurable (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf+qf=rb+qb) (hq : qb ≤ qf) :
    Measurable (coarsePrefix_replayAux δ rf qf rb qb hdim hq) :=
  (coarsePrefix_castAux_measurable δ qb hdim).comp
    (coarsePrefix_aux_measurable δ (rf+qf) qb qf hq)

theorem coarsePrefix_replayAux_law (W : BrownianSystem Ω) (δ : ℝ≥0)
    (rf qf rb qb : ℕ) (hdim : rf+qf=rb+qb) (hq : qb ≤ qf) :
    (replayAuxLaw W δ rf qf).map (coarsePrefix_replayAux δ rf qf rb qb hdim hq) =
      replayAuxLaw W δ rb qb := by
  change (coarsePrefix_auxLaw W δ (rf+qf) qf).map
    (coarsePrefix_castAux δ qb hdim ∘ coarsePrefix_aux δ (rf+qf) qb qf hq) = _
  rw [← Measure.map_map (coarsePrefix_castAux_measurable δ qb hdim)
    (coarsePrefix_aux_measurable δ (rf+qf) qb qf hq),
    coarsePrefix_aux_law W δ (rf+qf) qb qf hq, coarsePrefix_castAux_law W δ qb hdim]
  rfl

theorem coarsePrefix_input_replayInput (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf+qf=rb+qb) (hq : qb ≤ qf)
    (M : Matrix (Fin (rf+qf)) (Fin (rf+qf)) ℝ) (a : ReplayAux δ rf qf) :
    coarsePrefix_replayInput δ rf qf rb qb hdim hq (replayInput M a) =
      replayInput (castMatrix hdim.symm M) (coarsePrefix_replayAux δ rf qf rb qb hdim hq a) := by
  have he {n m : ℕ} (h : n=m) (y : PrefixAux δ n qb) (A : Matrix (Fin n) (Fin n) ℝ) :
      coarsePrefix_castInput δ qb h ((y.1,(A,y.2.1)),y.2.2) =
        (((coarsePrefix_castAux δ qb h y).1,
          (castMatrix h.symm A,(coarsePrefix_castAux δ qb h y).2.1)),
          (coarsePrefix_castAux δ qb h y).2.2) := by
    subst m
    rfl
  exact he hdim (coarsePrefix_aux δ (rf+qf) qb qf hq a) M

end SKConstants.N13a
