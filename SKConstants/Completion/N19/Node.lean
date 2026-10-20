module

public import SKConstants.Completion.N19.ExperimentCaps
public import SKConstants.Completion.N19.Rotation
public import SKConstants.Completion.N19.Transport
public import SKConstants.Completion.N19.GramRate
public import SKConstants.Completion.N19.Stability
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

abbrev coarsePosteriorColumns (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f) :=
  runPosteriorColumns W β hβ p n (queryCount p.a p.b n)
    (queryCount_mono p.a p.b p.f hbf n)

def coarseGramGood (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hbf : p.b ≤ p.f) (θ φ : ℝ) : Set (Outer n × Internal p n) :=
  {z | ‖familyGram (coarsePosteriorColumns W β hβ p n hbf (angleInput p n θ 0 z)) - 1‖ ≤ (3 / 4 : ℝ) ∧
    ‖familyGram (coarsePosteriorColumns W β hβ p n hbf (angleInput p n φ 0 z)) - 1‖ ≤ (3 / 4 : ℝ)}

theorem measurableSet_coarseGramGood (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f) (θ φ : ℝ) :
    MeasurableSet (coarseGramGood W β hβ p n hbf θ φ) := by
  have hθ := ((measurableSet_runPosteriorGram_bad W β hβ p n (queryCount p.a p.b n)
    (queryCount_mono p.a p.b p.f hbf n) (3 / 4)).preimage (measurable_angleInput p n θ 0)).compl
  have hφ := ((measurableSet_runPosteriorGram_bad W β hβ p n (queryCount p.a p.b n)
    (queryCount_mono p.a p.b p.f hbf n) (3 / 4)).preimage (measurable_angleInput p n φ 0)).compl
  convert hθ.inter hφ using 1
  ext z
  simp only [coarseGramGood, coarsePosteriorColumns, mem_inter_iff, mem_compl_iff,
    mem_preimage, mem_ofPred_eq, not_lt]

theorem coarseContinuity_gram_holds (hInput : ReplayInputLawStatement)
    (hRow : ReplayRowLawStatement) (hAngle : PerAngleLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop, ∀ θ φ : ℝ,
      (experimentLaw W p n).real (coarseGramGood W β hβ p n hb.2.1.le θ φ)ᶜ ≤
        2 * Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
  have hf0 : 0 < p.f := lt_trans hb.1 hb.2.1
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  filter_upwards [twoAngle_posteriorGram_failure_le hInput hRow hAngle W β hβ p,
    coarseGram_budget_eventually W β hβ p hf hb,
    schedule_eventually p.a p.f hf0 hf.1.le ha1] with n hA hbudget hsched θ φ
  have he : (coarseGramGood W β hβ p n hb.2.1.le θ φ)ᶜ = {z |
      (3 / 4 : ℝ) < ‖familyGram (coarsePosteriorColumns W β hβ p n hb.2.1.le
        (angleInput p n θ 0 z)) - 1‖ ∨
      (3 / 4 : ℝ) < ‖familyGram (coarsePosteriorColumns W β hβ p n hb.2.1.le
        (angleInput p n φ 0 z)) - 1‖} := by
    ext z
    simp only [coarseGramGood, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le]
  rw [he]
  exact (hA (by omega) hsched.2.2 (queryCount p.a p.b n)
    (queryCount_mono p.a p.b p.f hb.2.1.le n) θ φ 0 (3 / 4) (by norm_num)).trans
      (mul_le_mul_of_nonneg_left hbudget (by norm_num))

def coarseStabilityGood (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hbf : p.b ≤ p.f) (CB CD θ φ : ℝ) : Set (Outer n × Internal p n) :=
  experimentCap p n CB CD n ∩ coarseGramGood W β hβ p n hbf θ φ

theorem measurableSet_coarseStabilityGood (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f) (CB CD θ φ : ℝ) :
    MeasurableSet (coarseStabilityGood W β hβ p n hbf CB CD θ φ) :=
  (measurableSet_experimentCap p n CB CD n).inter
    (measurableSet_coarseGramGood W β hβ p n hbf θ φ)

theorem coarseContinuity_goodInputs_holds (hInput : ReplayInputLawStatement)
    (hRow : ReplayRowLawStatement) (hAngle : PerAngleLawStatement)
    (W : BrownianSystem Ω) :
    ∃ CB CD : ℝ, 0 < CB ∧ 0 < CD ∧ ∀ (p : Parameters),
      FineExponents p → ∀ hb : CoarseExponents p, ∀ (β : ℝ) (hβ : 1 < β),
      ∀ᶠ n : ℕ in atTop, ∀ θ φ : ℝ,
        (experimentLaw W p n).real (coarseStabilityGood W β hβ p n hb.2.1.le CB CD θ φ)ᶜ ≤
          Real.exp (-(n : ℝ) / 2) + 2 * Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
  obtain ⟨CB, CD, hCB, hCD, hcap⟩ := experimentCap_eventually_exp W
  refine ⟨CB, CD, hCB, hCD, fun p hf hb β hβ => ?_⟩
  filter_upwards [hcap p, coarseContinuity_gram_holds hInput hRow hAngle W β hβ p hf hb]
    with n hn hG θ φ
  exact (failure_inter_le (experimentLaw W p n) _ _).trans (add_le_add hn (hG θ φ))

end SKConstants.Completion.N19
