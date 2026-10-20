module

public import SKConstants.Completion.N19.Node
public import SKConstants.Completion.Blueprint4.NodesAt
public import SKConstants.Completion.N16.Node
public import SKConstants.Completion.NReplay.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology Matrix.Norms.L2Operator

namespace SKConstants.Completion.N19n
open Blueprint Blueprint4 GaussianProposal SKConstantsOAI.ZeroTemperatureSK LGram N19
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem coarseGram_budget_eventually_common {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseCommon p) :
    ∀ᶠ n : ℕ in atTop,
      gramTailBudget n (queryCount p.a p.b n + (queryCount p.a p.b n + 1))
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) (queryCount p.a p.b n)))
        (3 / 4) ≤ Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
  rcases hb with ⟨hb0, hbf, hz, hγ, hkb, hkbz, hkbγ, hkba, hkbb, h2γ, hbs, has⟩
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hba : p.b / 4 ≤ p.a := by linarith [hf.1]
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  let ε := (p.sb - p.b / 2) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  let u := p.b / 2 + ε
  have hu : 0 ≤ u := by dsimp [u]; linarith
  obtain ⟨C, hC, hproxy⟩ := mixedRowMGFProxy_global_bound W β hβ
  let C₀ := C * Real.exp (1 / 2) * (2 + p.b / ε)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let C₁ := C₀ * (3 + 2 * Real.exp 1 + 4 * |Real.log (2 * Real.exp 1 * C₀)| + 4 * u / ε)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hvar : ∀ᶠ n : ℕ in atTop,
      Concentration.squareVarianceScale
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) (queryCount p.a p.b n))) 3 ≤
          C₁ * (n : ℝ) ^ (u + ε) := by
    filter_upwards [schedule_eventually p.a p.b hb0 hba ha1] with n hsched
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    let V := growingQueryTime (meshSize p.a n) (queryCount p.a p.b n)
    have hV : (V : ℝ) ≤ p.b * Real.log n + 1 := by
      have h := (horizon_bounds p.a p.b hb0 hba n hsched.1 hsched.2.1).2
      have ht := (M1.growingQueryTime_monotone (meshSize p.a n))
        (Nat.le_succ (queryCount p.a p.b n))
      exact (NNReal.coe_le_coe.mpr ht).trans h
    have he : Real.exp ((V : ℝ) / 2) ≤ Real.exp (1 / 2) * (n : ℝ) ^ (p.b / 2) := by
      rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hroot : Real.sqrt (1 + (V : ℝ)) ≤ 1 + (V : ℝ) := by
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + (V : ℝ)), Real.sqrt_nonneg (1 + (V : ℝ)), V.coe_nonneg]
    have hlog := log_term_le (n : ℝ) V p.b ε hnR hb0.le hε hV
    have hK : (actualParisiFullMixedRowMGFProxy W β V : ℝ) ≤ C₀ * (n : ℝ) ^ u := by
      calc
        _ ≤ C * Real.exp ((V : ℝ) / 2) * Real.sqrt (1 + (V : ℝ)) := hproxy V
        _ ≤ (C * (Real.exp (1 / 2) * (n : ℝ) ^ (p.b / 2))) *
            ((2 + p.b / ε) * (n : ℝ) ^ ε) :=
          mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) (hroot.trans hlog) (by positivity) (by positivity)
        _ = C₀ * (n : ℝ) ^ u := by dsimp [C₀, u]; rw [Real.rpow_add hn0]; ring
    have hK1 : 1 ≤ (actualParisiFullMixedRowMGFProxy W β V : ℝ) := by
      simp only [actualParisiFullMixedRowMGFProxy, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [(actualParisiPosteriorRowMGFProxy W β V).coe_nonneg]
    exact varianceScale_le_rpow (n : ℝ) _ C₀ u ε hnR hK1 hC₀ hu hε hK
  have hdim : ∀ᶠ n : ℕ in atTop,
      (queryCount p.a p.b n + (queryCount p.a p.b n + 1) : ℕ) ≤ (17 : ℝ) * (n : ℝ) ^ p.a := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hq : (queryCount p.a p.b n : ℝ) ≤ 8 * (n : ℝ) ^ p.a := by
      have h := stopIndex_le p.a p.b hb0 hba n (by omega)
      have hl : queryCount p.a p.b n ≤ stopIndex p.a p.b n := by unfold queryCount; omega
      exact (Nat.cast_le.mpr hl).trans h
    have h1 := Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) ha.le
    push_cast
    linarith
  exact gramTailBudget_eventually_le _ _ p.a (u + ε) p.sb C₁ 17 (3 / 4)
    has (by dsimp [u, ε]; linarith) (by linarith) hC₁ (by norm_num) (by norm_num) (by norm_num) hdim hvar

variable {Ω : Type} [MeasurableSpace Ω]

theorem coarseContinuity_gram_common_holds (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseCommon p) (hD : 0 ≤ p.D) :
    ∀ᶠ n : ℕ in atTop, ∀ θ φ : ℝ,
      (experimentLaw W p n).real (coarseGramGood W β hβ p n hb.2.1.le θ φ)ᶜ ≤
        2 * Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
  have hf0 : 0 < p.f := lt_trans hb.1 hb.2.1
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  filter_upwards [N16.PerAngleLawNonnegativeExponentStatement_holds p hD W,
    coarseGram_budget_eventually_common W β hβ p hf hb,
    schedule_eventually p.a p.f hf0 hf.1.le ha1] with n hA hbudget hsched θ φ
  have hsingle (ψ : ℝ) : (experimentLaw W p n).real {z |
      (3 / 4 : ℝ) < ‖familyGram (coarsePosteriorColumns W β hβ p n hb.2.1.le
        (angleInput p n ψ 0 z)) - 1‖} ≤
        Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
    exact ((experiment_real_of_run W p n ψ 0 (hA ψ 0).2 _
      (measurableSet_runPosteriorGram_bad W β hβ p n (queryCount p.a p.b n)
        (queryCount_mono p.a p.b p.f hb.2.1.le n) (3 / 4))).trans_le
      (run_posteriorGram_failure_le replayInputLaw_holds hRow W β hβ p n
        (by omega) hsched.2.2 (queryCount p.a p.b n)
        (queryCount_mono p.a p.b p.f hb.2.1.le n) (3 / 4) (by norm_num))).trans hbudget
  have he : (coarseGramGood W β hβ p n hb.2.1.le θ φ)ᶜ = {z |
      (3 / 4 : ℝ) < ‖familyGram (coarsePosteriorColumns W β hβ p n hb.2.1.le
        (angleInput p n θ 0 z)) - 1‖} ∪ {z |
      (3 / 4 : ℝ) < ‖familyGram (coarsePosteriorColumns W β hβ p n hb.2.1.le
        (angleInput p n φ 0 z)) - 1‖} := by
    ext z
    simp only [coarseGramGood, mem_compl_iff, mem_ofPred_eq, mem_union,
      not_and_or, not_le]
  rw [he]
  exact (measureReal_union_le _ _).trans ((add_le_add (hsingle θ) (hsingle φ)).trans_eq (by ring))

theorem coarseContinuity_goodInputs_common_holds (hRow : ReplayRowLawStatement)
    (W : BrownianSystem Ω) :
    ∃ CB CD : ℝ, 0 < CB ∧ 0 < CD ∧ ∀ p : Parameters,
      FineExponents p → ∀ hb : CoarseCommon p, 0 ≤ p.D → ∀ (β : ℝ) (hβ : 1 < β),
      ∀ᶠ n : ℕ in atTop, ∀ θ φ : ℝ,
        (experimentLaw W p n).real (coarseStabilityGood W β hβ p n hb.2.1.le CB CD θ φ)ᶜ ≤
          Real.exp (-(n : ℝ) / 2) + 2 * Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
  obtain ⟨CB, CD, hCB, hCD, hcap⟩ := experimentCap_eventually_exp W
  refine ⟨CB, CD, hCB, hCD, fun p hf hb hD β hβ => ?_⟩
  filter_upwards [hcap p, coarseContinuity_gram_common_holds hRow W β hβ p hf hb hD]
    with n hn hG θ φ
  exact (failure_inter_le (experimentLaw W p n) _ _).trans (add_le_add hn (hG θ φ))

end SKConstants.Completion.N19n
