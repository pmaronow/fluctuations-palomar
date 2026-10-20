module

public import SKConstants.Completion.N19.Gram
public import SKConstants.Completion.Blueprint.AssemblySequence
public import SKConstants.Completion.LM1a.GrowingCells
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology Matrix.Norms.L2Operator

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal SKConstantsOAI.ZeroTemperatureSK LGram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

theorem stopIndex_mono (a B F : ℝ) (hBF : B ≤ F) (n : ℕ) :
    stopIndex a B n ≤ stopIndex a F n := by
  by_cases hn : 0 < n
  · have hT : paperGrowingQueryHorizon B n ≤ paperGrowingQueryHorizon F n :=
      Real.toNNReal_mono (mul_le_mul_of_nonneg_right hBF
        (Real.log_nonneg (by exact_mod_cast hn)))
    simp only [stopIndex, hn, ↓reduceDIte, paperGrowingQueryStop]
    exact Nat.find_min' (growingQueryTime_reaches (meshSize a n)
      (paperGrowingQueryMeshSize_pos a n hn) (paperGrowingQueryHorizon B n))
      (hT.trans (growingQueryStop_reaches _ _ (paperGrowingQueryHorizon F n)))
  · simp [stopIndex, hn]

theorem queryCount_mono (a B F : ℝ) (hBF : B ≤ F) (n : ℕ) :
    queryCount a B n ≤ queryCount a F n := by
  unfold queryCount
  exact min_le_min (Nat.sub_le_sub_right (stopIndex_mono a B F hBF n) 1) le_rfl

theorem cast_replayInput_law (hInput : ReplayInputLawStatement)
    (W : BrownianSystem Ω) (δ : ℝ≥0) (r q n : ℕ) (h : r + q = n) :
    ((primLaw n).prod (replayAuxLaw W δ r q)).map
      (fun y => replayInput (castMatrix h (physical n y.1)) y.2) = M1.ReplayLaw W δ r q := by
  subst n
  exact hInput W δ r q

def fineReplayInput (p : Parameters) (n : ℕ) (y : RunInput p n) :
    M1.ReplayInput (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) :=
  replayInput (castMatrix (rankCount_add p.a p.f n) (physical n y.1)) y.2.1

theorem measurable_fineReplayInput (p : Parameters) (n : ℕ) :
    Measurable (fineReplayInput p n) := by
  have hM : Measurable (fun y : RunInput p n =>
      castMatrix (rankCount_add p.a p.f n) (physical n y.1)) :=
    ((continuous_castMatrix (rankCount_add p.a p.f n)).measurable.comp
      (continuous_goeMatrix _).measurable).comp measurable_fst
  exact (measurable_replayInput _ _ _).comp (hM.prodMk measurable_snd.fst)

theorem fineReplayInput_law (hInput : ReplayInputLawStatement)
    (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    (runLaw W p n).map (fineReplayInput p n) =
      M1.ReplayLaw W (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) := by
  let f : Prim n × FineAux p n →
      M1.ReplayInput (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) :=
    fun y => replayInput (castMatrix (rankCount_add p.a p.f n) (physical n y.1)) y.2
  have hf : Measurable f := by
    have hM : Measurable (fun y : Prim n × FineAux p n =>
        castMatrix (rankCount_add p.a p.f n) (physical n y.1)) :=
      ((continuous_castMatrix (rankCount_add p.a p.f n)).measurable.comp
        (continuous_goeMatrix _).measurable).comp measurable_fst
    exact (measurable_replayInput _ _ _).comp (hM.prodMk measurable_snd)
  have hp : (runLaw W p n).map (fun y => (y.1, y.2.1)) =
      (primLaw n).prod (fineAuxLaw W p n) := by
    have hh := Measure.map_prod_map (primLaw n)
      ((fineAuxLaw W p n).prod (thresholdLaw n)) measurable_id measurable_fst
    change (((primLaw n).prod ((fineAuxLaw W p n).prod (thresholdLaw n))).map
      (Prod.map id Prod.fst)) = _
    simpa only [Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul,
      Prod.map_apply, id_eq] using hh.symm
  have hh := congrArg (fun μ => μ.map f) hp
  rw [Measure.map_map hf (measurable_fst.prodMk measurable_snd.fst)] at hh
  exact hh.trans (cast_replayInput_law hInput W _ _ _ _ (rankCount_add p.a p.f n))

def runPosteriorColumns (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n k : ℕ) (hk : k ≤ queryCount p.a p.f n) (y : RunInput p n) :
    Fin k → EuclideanSpace ℝ (Fin (rankCount p.a p.f n + queryCount p.a p.f n)) :=
  fieldPosteriorColumns W β (M1.Horizon (meshSize p.a n) (queryCount p.a p.f n))
    (growingQueryTime (meshSize p.a n)) k _
    (fun j hj => (M1.growingQueryTime_monotone _)
      (by omega : j ≤ queryCount p.a p.f n + 1))
    (replayFieldRows W β hβ _ _ _ (fineReplayInput p n y))

theorem measurable_runPosteriorColumns (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n k : ℕ) (hk : k ≤ queryCount p.a p.f n) :
    Measurable (runPosteriorColumns W β hβ p n k hk) :=
  (measurable_fieldPosteriorColumns _ _ _ _ _ _ _).comp
    ((measurable_replayFieldRows _ _ _ _ _ _).comp (measurable_fineReplayInput p n))

theorem measurableSet_runPosteriorGram_bad (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n k : ℕ) (hk : k ≤ queryCount p.a p.f n) (η : ℝ) :
    MeasurableSet {y | η < ‖familyGram (runPosteriorColumns W β hβ p n k hk y) - 1‖} := by
  apply measurableSet_lt measurable_const
  have hm := measurable_runPosteriorColumns W β hβ p n k hk
  unfold familyGram
  fun_prop

theorem run_posteriorGram_failure_le (hInput : ReplayInputLawStatement)
    (hRow : ReplayRowLawStatement) (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (hr : 0 < rankCount p.a p.f n)
    (k : ℕ) (hk : k ≤ queryCount p.a p.f n) (η : ℝ) (hη : 0 < η) :
    (runLaw W p n).real
      {y | η < ‖familyGram (runPosteriorColumns W β hβ p n k hk y) - 1‖} ≤
      gramTailBudget n (k + (k + 1))
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) k)) η := by
  have hmesh := paperGrowingQueryMeshSize_pos p.a n hn
  have htime : ∀ j ≤ k, growingQueryTime (meshSize p.a n) j ≤
      M1.Horizon (meshSize p.a n) (queryCount p.a p.f n) := fun j hj =>
    (growingQueryTime_strictMono _ hmesh).monotone (by omega)
  let E : Set (M1.ReplayInput (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n)) :=
    {u | η < ‖familyGram (fieldPosteriorColumns W β _ (growingQueryTime (meshSize p.a n)) k _ htime
      (replayFieldRows W β hβ _ _ _ u)) - 1‖}
  have hE : MeasurableSet E := by
    apply measurableSet_lt measurable_const
    have hm := (measurable_fieldPosteriorColumns W β _ _ k
      (rankCount p.a p.f n + queryCount p.a p.f n) htime).comp
      (measurable_replayFieldRows W β hβ (meshSize p.a n)
        (rankCount p.a p.f n) (queryCount p.a p.f n))
    unfold familyGram
    fun_prop
  have h := replay_posteriorGram_failure_le hRow W β hβ _ hmesh _ _ hr _
    (growingQueryTime_strictMono _ hmesh) k htime η hη
  have he : (runLaw W p n).real (fineReplayInput p n ⁻¹' E) =
      (M1.ReplayLaw W (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n)).real E := by
    rw [← map_measureReal_apply (measurable_fineReplayInput p n) hE, fineReplayInput_law hInput]
  change (runLaw W p n).real (fineReplayInput p n ⁻¹' E) ≤ _
  rw [he]
  simpa only [rankCount_add] using h

theorem perAngle_posteriorGram_failure_le (hInput : ReplayInputLawStatement)
    (hRow : ReplayRowLawStatement) (hAngle : PerAngleLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) :
    ∀ᶠ n : ℕ in atTop, ∀ (_hn : 0 < n) (_hr : 0 < rankCount p.a p.f n)
      (k : ℕ) (hk : k ≤ queryCount p.a p.f n) (θ : ℝ) (l : ℕ) (η : ℝ), 0 < η →
      (experimentLaw W p n).real {z | η <
        ‖familyGram (runPosteriorColumns W β hβ p n k hk (angleInput p n θ l z)) - 1‖} ≤
          gramTailBudget n (k + (k + 1))
            (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) k)) η := by
  filter_upwards [hAngle p W] with n hA hn hr k hk θ l η hη
  exact (experiment_real_of_run W p n θ l (hA θ l).2 _
    (measurableSet_runPosteriorGram_bad W β hβ p n k hk η)).trans_le
      (run_posteriorGram_failure_le hInput hRow W β hβ p n hn hr k hk η hη)

theorem twoAngle_posteriorGram_failure_le (hInput : ReplayInputLawStatement)
    (hRow : ReplayRowLawStatement) (hAngle : PerAngleLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) :
    ∀ᶠ n : ℕ in atTop, ∀ (_hn : 0 < n) (_hr : 0 < rankCount p.a p.f n)
      (k : ℕ) (hk : k ≤ queryCount p.a p.f n) (θ φ : ℝ) (l : ℕ) (η : ℝ), 0 < η →
      (experimentLaw W p n).real {z |
        η < ‖familyGram (runPosteriorColumns W β hβ p n k hk (angleInput p n θ l z)) - 1‖ ∨
        η < ‖familyGram (runPosteriorColumns W β hβ p n k hk (angleInput p n φ l z)) - 1‖} ≤
          2 * gramTailBudget n (k + (k + 1))
            (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) k)) η := by
  filter_upwards [perAngle_posteriorGram_failure_le hInput hRow hAngle W β hβ p]
    with n hA hn hr k hk θ φ l η hη
  have h := (measureReal_union_le
    {z | η < ‖familyGram (runPosteriorColumns W β hβ p n k hk (angleInput p n θ l z)) - 1‖}
    {z | η < ‖familyGram (runPosteriorColumns W β hβ p n k hk (angleInput p n φ l z)) - 1‖}
    (μ := experimentLaw W p n)).trans
      (add_le_add (hA hn hr k hk θ l η hη) (hA hn hr k hk φ l η hη))
  exact h.trans_eq (by ring)

end SKConstants.Completion.N19
