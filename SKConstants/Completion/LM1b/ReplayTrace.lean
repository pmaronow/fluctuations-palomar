module
public import SKConstants.Completion.LM1b.Statements

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators Matrix
namespace SKConstants.GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Past : Type*}

theorem paperMatrixQueryTargetTrace_eq (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    paperMatrixQueryTargetTrace r n N target update K s z W =
      paperTargetTrace r n target update K s (paperMatrixQueryNoiseRun r n N target update K s z W) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [paperMatrixQueryTargetTrace, paperMatrixQueryNoiseRun, paperTargetTrace, ih]

theorem paperMatrixQueryNoiseRun_terminal (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    proposalTerminalPast update K s.1 (paperMatrixQueryNoiseRun r n N target update K s z W) =
      paperMatrixQueryRun r n N target update K s z W := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [paperMatrixQueryNoiseRun, proposalTerminalPast, paperMatrixQueryRun]
    exact ih (update K s.1 (paperQueriedNoise N (paperFrame s.2 (target K s.1)) W z.1),
      tailRows (paperFrame s.2 (target K s.1))) z.2

theorem paperTraces_congr_endpoints (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hunit : ∀ k a z w, (∀ i : Fin n, z (.inl i) = w (.inl i)) → update k a z = update k a w)
    (K : ℕ) (s : PaperState r n K Past) (z w : StoppedNoise (Fin n) K)
    (hz : ∀ e i, paperNoiseTrace n K z e (.inl i) = paperNoiseTrace n K w e (.inl i)) :
    paperTargetTrace r n target update K s z = paperTargetTrace r n target update K s w ∧
    paperScalarPastTrace r n target update K s z = paperScalarPastTrace r n target update K s w ∧
    paperFrameTrace r n target update K s z = paperFrameTrace r n target update K s w ∧
    paperQueryDirectionTrace r n N target update K s z = paperQueryDirectionTrace r n N target update K s w ∧
    paperRemainingProjectionTrace r n target update K s z = paperRemainingProjectionTrace r n target update K s w := by
  induction K with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ K ih =>
    have hu : update K s.1 z.1 = update K s.1 w.1 := hunit K s.1 _ _ (hz 0)
    have hi := ih (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2 w.2
      (fun e i => hz e.succ i)
    simp only [paperTargetTrace, paperScalarPastTrace, paperFrameTrace,
      paperQueryDirectionTrace, paperRemainingProjectionTrace, ← hu]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · funext j
      exact Fin.cases rfl (fun j => congrFun hi.1 j) j
    · funext j
      exact Fin.cases rfl (fun j => congrFun hi.2.1 j) j
    · funext j
      exact Fin.cases rfl (fun j => congrFun hi.2.2.1 j) j
    · funext j
      exact Fin.cases rfl (fun j => congrFun hi.2.2.2.1 j) j
    · funext j
      exact Fin.cases rfl (fun j => congrFun hi.2.2.2.2 j) j

variable [MeasurableSpace Past]

theorem paperIndependentCompletions_noiseTrace_coupling (r n : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hunit : ∀ k a z w, (∀ i : Fin n, z (.inl i) = w (.inl i)) → update k a z = update k a w)
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : PaperAugmentedNoise n K) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcomp : frameProjection s.2 * W * frameProjection s.2 =
      paperTensorProposal r n (skSigma N) target update K s (paperAugmentedOriginal n K z)) :
    ∀ e i, paperNoiseTrace n K
      (paperMatrixQueryNoiseRun r n N target update K s
        (paperCompletionReplayNoise n K (paperIndependentCompletions r n target update K s z)) W)
      e (.inl i) = paperNoiseTrace n K (paperAugmentedOriginal n K z) e (.inl i) := by
  induction K generalizing W with
  | zero => exact fun e => Fin.elim0 e
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    have hF := paperFrame_orthogonal s.2 (target K s.1) horth
    have he := matrix_query_completed_endpoint_of_compression r n K N hN target update
      s horth (paperAugmentedOriginal n (K+1) z) W hcomp
    have hz : ∀ i : Fin n,
        paperQueriedNoise N F W
          (WithLp.toLp 2 (Sum.elim (paperIndependentCompletion F z.1).ofLp (fun _ => 0))) (.inl i) =
            z.1.1 (.inl i) := by
      intro i
      change (remainingProjection F *ᵥ (W *ᵥ normalizedQuery N (F 0)) +
        paperUsedProjection F *ᵥ (paperIndependentCompletion F z.1).ofLp) i = _
      rw [paperIndependentCompletion_used F hF]
      exact congrFun he i
    have hu := hunit K s.1 _ z.1.1 hz
    intro e i
    refine Fin.cases ?_ (fun e => ?_) e
    · exact hz i
    · change paperNoiseTrace n K
        (paperMatrixQueryNoiseRun r n N target update K
          (update K s.1 (paperQueriedNoise N F W
            (WithLp.toLp 2 (Sum.elim (paperIndependentCompletion F z.1).ofLp (fun _ => 0)))), tailRows F)
          (paperCompletionReplayNoise n K
            (paperIndependentCompletions r n target update K (update K s.1 z.1.1, tailRows F) z.2)) W)
        e (.inl i) = paperNoiseTrace n K (paperAugmentedOriginal n K z.2) e (.inl i)
      rw [hu]
      apply ih (update K s.1 z.1.1, tailRows F) (tailRows_orthogonal F hF) z.2 W
      exact matrix_remaining_compression_of_compression r n K (skSigma N) target update
        s horth (paperAugmentedOriginal n (K+1) z) W hcomp

end SKConstants.GaussianProposal

namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem growingSource_replay_endpoint_trace (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) (s : SourceInput δ r₀ q) :
    ReplayEndpoints W β hβ δ r₀ q (ToReplay W β hβ δ r₀ q s) = SourceEndpoints δ r₀ q s := by
  have hI : ∀ i j : Fin (r₀+q), dot ((1 : Matrix (Fin (r₀+q)) (Fin (r₀+q)) ℝ) i)
      ((1 : Matrix (Fin (r₀+q)) (Fin (r₀+q)) ℝ) j) = if i = j then 1 else 0 := by
    intro i j
    have he : (1 : Matrix (Fin (r₀+q)) (Fin (r₀+q)) ℝ) = canonicalBasis := by
      ext i j
      exact Matrix.one_apply
    rw [he]
    exact canonicalBasis_orthogonal i j
  funext e i
  apply paperIndependentCompletions_noiseTrace_coupling r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (by exact_mod_cast hN) (Target W β hβ δ r₀ q) (Update δ r₀ q)
    (fun k a z w hz => scalarGrowingPaperUpdate_eq_of_endpoint_eq _ _ _ _ k a z w hz)
    q (Initial δ r₀ q s, 1) hI s.2
    (actualParisiGrowingSourceAugmentedOutput W β hβ δ r₀ q s.1 s.2).1
  simp only [frameProjection, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem completeReplayTraceCoupling_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    CompleteReplayTraceCouplingStatement W β hβ δ r₀ q := by
  intro s
  have he := growingSource_replay_endpoint_trace W β hβ δ r₀ q hN s
  have ht := paperTraces_congr_endpoints r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (Target W β hβ δ r₀ q) (Update δ r₀ q)
    (fun k a z w hz => scalarGrowingPaperUpdate_eq_of_endpoint_eq _ _ _ _ k a z w hz)
    q (Initial δ r₀ q s, 1)
    (ReplayQueriedNoise W β hβ δ r₀ q (ToReplay W β hβ δ r₀ q s)) (Original δ r₀ q s)
    (fun e i => congrFun (congrFun he e) i)
  refine ⟨?_, he, ht.2⟩
  exact (paperMatrixQueryTargetTrace_eq r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (Target W β hβ δ r₀ q) (Update δ r₀ q) q
    (Initial δ r₀ q s, 1) (ReplayNoise δ r₀ q (ToReplay W β hβ δ r₀ q s))
    (ToReplay W β hβ δ r₀ q s).1.2.1).trans ht.1

end SKConstants.M1
