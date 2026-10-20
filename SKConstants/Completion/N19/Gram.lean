module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.LGram.IIDEvent
public import SKConstants.Completion.N19.Caps
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal SKConstantsOAI.ZeroTemperatureSK LGram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

def posteriorColumns (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (k N : ℕ)
    (w : Fin N → Ω) : Fin k → EuclideanSpace ℝ (Fin N) :=
  fun j => (Real.sqrt (N : ℝ))⁻¹ • WithLp.toLp 2
    (fun i => actualParisiNormalizedPosteriorRow W β t k (w i) j)

theorem measurable_posteriorColumns (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (k N : ℕ) : Measurable (posteriorColumns W β t k N) := by
  apply Measurable.of_eval
  intro j
  unfold posteriorColumns
  apply Measurable.const_smul (c := (Real.sqrt (N : ℝ))⁻¹)
  apply (WithLp.measurable_toLp 2 _).comp
  exact Measurable.of_eval (fun i => ((measurable_pi_apply j).comp
    ((WithLp.measurable_ofLp 2 _).comp (measurable_actualParisiNormalizedPosteriorRow W β t k))).comp
      (measurable_pi_apply i))

theorem measurableSet_posteriorGram_bad (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (k N : ℕ) (η : ℝ) :
    MeasurableSet {w | η < ‖familyGram (posteriorColumns W β t k N w) - 1‖} := by
  apply measurableSet_lt measurable_const
  have hm := measurable_posteriorColumns W β t k N
  unfold familyGram
  fun_prop

theorem iid_posteriorGram_failure_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k N : ℕ) (hN : 0 < N)
    (H : ℝ≥0) (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : Fin N => W.law)).real
      {w | η < ‖familyGram (posteriorColumns W β t k N w) - 1‖} ≤
      gramTailBudget N (k + (k + 1)) (actualParisiFullMixedRowMGFProxy W β (t k)) η := by
  let := W.isProbability
  let μ := actualParisiFullMixedRowsLaw W W β H N
  let P : (Fin N → (Bool × Ω) × Ω) → (Fin N → Ω) := fun w i => (w i).1.2
  have hP : Measurable P := by unfold P; fun_prop
  have hp : μ.map P = Measure.pi (fun _ : Fin N => W.law) := by
    have hlaw := actualParisiFullQuerySpinLaw_path_hasLaw W W β H
    have : IsProbabilityMeasure ((actualParisiFullQuerySpinLaw W W β H).map
        (fun u => u.1.2)) := by rw [hlaw.map_eq]; exact W.isProbability
    change (Measure.pi (fun _ : Fin N => actualParisiFullQuerySpinLaw W W β H)).map
      (fun w i => (w i).1.2) = _
    rw [Measure.pi_map_pi (fun _ =>
      (show Measurable (fun u : (Bool × Ω) × Ω => u.1.2) from measurable_snd.comp measurable_fst).aemeasurable)]
    simp only [hlaw.map_eq]
  have he (w : Fin N → (Bool × Ω) × Ω) :
      (fun j : Fin k => sampleColumn (mixedRowsArray W W β hβ t t k w) (posteriorIndex k j)) =
        posteriorColumns W β t k N (P w) := by
    funext j
    simp only [sampleColumn, mixedRowsArray, actualParisiFullMixedRows, mixedRow_posterior,
      posteriorColumns, P]
  have hsubset : P ⁻¹' {w | η < ‖familyGram (posteriorColumns W β t k N w) - 1‖} ⊆
      {w | mixedRowsArray W W β hβ t t k w ∉
        rowGramEvent (mixedPopulation W W β hβ t t k H) N η} := by
    intro w hw hg
    have hg' := (mixedRows_good_blocks W W β hβ t ht t k H w η hg).1
    rw [he w] at hg'
    exact (not_lt_of_ge hg') hw
  calc
    _ = μ.real (P ⁻¹' {w | η < ‖familyGram (posteriorColumns W β t k N w) - 1‖}) := by
      rw [← hp, map_measureReal_apply hP (measurableSet_posteriorGram_bad W β t k N η)]
    _ ≤ μ.real {w | mixedRowsArray W W β hβ t t k w ∉
        rowGramEvent (mixedPopulation W W β hβ t t k H) N η} :=
      measureReal_mono (h₂ := measure_ne_top μ _) hsubset
    _ ≤ _ := mixedRows_rowGramEvent_compl_le W W β hβ t ht k t ht H hN η hη

def replayFieldRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (u : M1.ReplayInput δ r q) :
    Fin (r + q) → Iic (M1.Horizon δ q) → ℝ :=
  fun i t => actualParisiGrowingReplayField W β hβ δ r q t.1 u i

theorem measurable_replayFieldRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : Measurable (replayFieldRows W β hβ δ r q) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro t
  exact (measurable_pi_apply i).comp (M1.measurable_ReplayField W β hβ δ r q t.1)

theorem replayFieldRows_law (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hr : 0 < r) :
    (M1.ReplayLaw W δ r q).map (replayFieldRows W β hβ δ r q) =
      (Measure.pi (fun _ : Fin (r + q) => W.law)).map
        (fun w i t => actualParisiFullScalarProcess W β t.1 (w i)) := by
  let := W.isProbability
  let H := M1.Horizon δ q
  let F : Ω → (Iic H → ℝ) := fun w t => actualParisiFullScalarProcess W β t.1 w
  have hF : Measurable F := Measurable.of_eval (fun t =>
    measurable_actualParisiPreContinuationField W β t.1)
  let Q : Bool × Ω → Bool × (Iic H → ℝ) := fun u => (u.1, F u.2)
  have hQ : Measurable Q := measurable_fst.prodMk (hF.comp measurable_snd)
  let ν := (actualParisiFullTerminalSpinLaw β W H).map Q
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hm : ν.map Prod.snd = W.law.map F := by
    rw [show ν = (actualParisiFullTerminalSpinLaw β W H).map Q from rfl,
      Measure.map_map measurable_snd hQ]
    change (actualParisiFullTerminalSpinLaw β W H).map (F ∘ Prod.snd) = _
    rw [← Measure.map_map hF measurable_snd, actualParisiFullTerminalSpinLaw_path_marginal]
  let forget : (Fin (r + q) → Bool × (Iic H → ℝ)) → (Fin (r + q) → Iic H → ℝ) :=
    fun w i => (w i).2
  have hf : Measurable forget := by unfold forget; fun_prop
  have hL : Measurable (fun u : (Fin (r + q) → Bool) × M1.ReplayInput δ r q =>
      fun i => (u.1 i, replayFieldRows W β hβ δ r q u.2 i)) := by
    exact Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp ((measurable_replayFieldRows W β hβ δ r q).comp measurable_snd)))
  have h := congrArg (fun μ => μ.map forget) (hRow W β hβ δ hδ r q hr)
  change ((M1.ReplayLinkedLaw W β hβ δ r q).map (fun u =>
    fun i => (u.1 i, replayFieldRows W β hβ δ r q u.2 i))).map forget =
      (Measure.pi (fun _ : Fin (r + q) => ν)).map forget at h
  rw [Measure.map_map hf hL] at h
  calc
    _ = (M1.ReplayLinkedLaw W β hβ δ r q).map
        (fun u => replayFieldRows W β hβ δ r q u.2) := by
      rw [← M1.replayLinkedLaw_base_marginal W β hβ δ r q,
        Measure.map_map (measurable_replayFieldRows W β hβ δ r q) measurable_snd]
      rfl
    _ = (Measure.pi (fun _ : Fin (r + q) => ν)).map forget := h
    _ = Measure.pi (fun _ : Fin (r + q) => W.law.map F) := by
      rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
      simp only [hm]
    _ = _ := (Measure.pi_map_pi (fun _ => hF.aemeasurable)).symm

def fieldPosteriorColumns (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0)
    (t : ℕ → ℝ≥0) (k N : ℕ) (ht : ∀ j ≤ k, t j ≤ H)
    (Y : Fin N → Iic H → ℝ) : Fin k → EuclideanSpace ℝ (Fin N) :=
  fun j => (Real.sqrt (N : ℝ))⁻¹ • WithLp.toLp 2 (fun i =>
    (actualParisiFullMagnetization β (t (j + 1))
        (Y i ⟨t (j + 1), ht (j + 1) (by omega)⟩) -
      actualParisiFullMagnetization β (t j) (Y i ⟨t j, ht j (by omega)⟩)) /
        (actualParisiPosteriorIntervalScale W β (t j) (t (j + 1)) : ℝ))

theorem measurable_fieldPosteriorColumns (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0)
    (t : ℕ → ℝ≥0) (k N : ℕ) (ht : ∀ j ≤ k, t j ≤ H) :
    Measurable (fieldPosteriorColumns W β H t k N ht) := by
  have hm (v : ℝ≥0) : Measurable (actualParisiFullMagnetization β v) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  unfold fieldPosteriorColumns
  fun_prop

theorem fieldPosteriorColumns_scalar_eq (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0)
    (t : ℕ → ℝ≥0) (k N : ℕ) (ht : ∀ j ≤ k, t j ≤ H) (w : Fin N → Ω) :
    fieldPosteriorColumns W β H t k N ht
      (fun i u => actualParisiFullScalarProcess W β u.1 (w i)) =
        posteriorColumns W β t k N w := by
  rfl

theorem replay_posteriorGram_failure_le (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hr : 0 < r) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (k : ℕ) (hH : ∀ j ≤ k, t j ≤ M1.Horizon δ q) (η : ℝ) (hη : 0 < η) :
    (M1.ReplayLaw W δ r q).real
      {u | η < ‖familyGram (fieldPosteriorColumns W β (M1.Horizon δ q) t k (r + q) hH
        (replayFieldRows W β hβ δ r q u)) - 1‖} ≤
      gramTailBudget (r + q) (k + (k + 1)) (actualParisiFullMixedRowMGFProxy W β (t k)) η := by
  let E : Set (Fin (r + q) → Iic (M1.Horizon δ q) → ℝ) :=
    {Y | η < ‖familyGram (fieldPosteriorColumns W β (M1.Horizon δ q) t k (r + q) hH Y) - 1‖}
  have hE : MeasurableSet E := by
    apply measurableSet_lt measurable_const
    have hm := measurable_fieldPosteriorColumns W β (M1.Horizon δ q) t k (r + q) hH
    unfold familyGram
    fun_prop
  have hF : Measurable (fun w : Fin (r + q) → Ω =>
      fun i (u : Iic (M1.Horizon δ q)) => actualParisiFullScalarProcess W β u.1 (w i)) := by
    exact Measurable.of_eval (fun i => Measurable.of_eval (fun u =>
      (measurable_actualParisiPreContinuationField W β u.1).comp (measurable_pi_apply i)))
  calc
    _ = ((M1.ReplayLaw W δ r q).map (replayFieldRows W β hβ δ r q)).real E :=
      (map_measureReal_apply (measurable_replayFieldRows W β hβ δ r q) hE).symm
    _ = ((Measure.pi (fun _ : Fin (r + q) => W.law)).map
        (fun w i u => actualParisiFullScalarProcess W β u.1 (w i))).real E := by
      rw [replayFieldRows_law hRow W β hβ δ hδ r q hr]
    _ = (Measure.pi (fun _ : Fin (r + q) => W.law)).real
        {w | η < ‖familyGram (posteriorColumns W β t k (r + q) w) - 1‖} := by
      rw [map_measureReal_apply hF hE]
      rfl
    _ ≤ _ := iid_posteriorGram_failure_le W β hβ t ht k (r + q) (by omega)
      (M1.Horizon δ q) η hη

end SKConstants.Completion.N19
