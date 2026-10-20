module

public import SKConstants.Completion.LGram.Budget
public import SKConstants.Completion.Blueprint.AssemblyFine
public import SKConstants.Completion.N19.Grid
public import SKConstants.Completion.LM1a.GrowingCells
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal SKConstantsOAI.ZeroTemperatureSK LGram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem varianceScale_le_rpow (N K C u ε : ℝ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hC : 0 < C) (hu : 0 ≤ u) (hε : 0 < ε) (hKC : K ≤ C * N ^ u) :
    Concentration.squareVarianceScale K 3 ≤
      C * (3 + 2 * Real.exp 1 + 4 * |Real.log (2 * Real.exp 1 * C)| + 4 * u / ε) *
        N ^ (u + ε) := by
  have hn0 : 0 < N := by linarith
  have hpow : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hlog := Real.log_le_rpow_div hn0.le hε
  have harg : 0 < 2 * Real.exp 1 * K := by positivity
  have hl : Real.log (2 * Real.exp 1 * K) ≤
      Real.log (2 * Real.exp 1 * C) + u * Real.log N := by
    have hm := Real.log_le_log harg
      (mul_le_mul_of_nonneg_left hKC (by positivity : 0 ≤ 2 * Real.exp 1))
    have he : 2 * Real.exp 1 * (C * N ^ u) = (2 * Real.exp 1 * C) * N ^ u := by ring
    rw [he, Real.rpow_def_of_pos hn0,
      Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hm
    nlinarith
  let L := 3 + 2 * Real.exp 1 + 4 * |Real.log (2 * Real.exp 1 * C)| + 4 * u / ε
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbase : 0 ≤ 3 + 2 * Real.exp 1 + 4 * |Real.log (2 * Real.exp 1 * C)| := by positivity
  have hb := mul_le_mul_of_nonneg_left hpow hbase
  have hu' := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * u)
  have hb' : 3 + 2 * Real.exp 1 + 4 * Real.log (2 * Real.exp 1 * K) ≤ L * N ^ ε := by
    dsimp [L]
    have he : 4 * u * (N ^ ε / ε) = (4 * u / ε) * N ^ ε := by ring
    rw [he] at hu'
    nlinarith [le_abs_self (Real.log (2 * Real.exp 1 * C))]
  calc
    _ ≤ K * (3 + 2 * Real.exp 1 + 4 * Real.log (2 * Real.exp 1 * K)) :=
      squareVarianceScale_three_le hK
    _ ≤ K * (L * N ^ ε) := mul_le_mul_of_nonneg_left hb' (by linarith)
    _ ≤ (C * N ^ u) * (L * N ^ ε) :=
      mul_le_mul_of_nonneg_right hKC (mul_nonneg hL (Real.rpow_nonneg hn0.le _))
    _ = C * L * N ^ (u + ε) := by rw [Real.rpow_add hn0]; ring

theorem gramTailBudget_eventually_le (d : ℕ → ℕ) (K : ℕ → ℝ)
    (a u s C D η : ℝ) (has : a < 1 - s) (hus : u < s) (hs : s < 1)
    (hC : 0 < C) (hD : 0 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1)
    (hd : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ D * (n : ℝ) ^ a)
    (hv : ∀ᶠ n : ℕ in atTop, Concentration.squareVarianceScale (K n) 3 ≤ C * (n : ℝ) ^ u) :
    ∀ᶠ n : ℕ in atTop,
      gramTailBudget n (d n) (K n) η ≤ Real.exp (-((n : ℝ) ^ (1 - s))) := by
  filter_upwards [hd, hv,
    constant_rpow_le_small_rpow a (1 - s) (D * Real.log 9) 1 has
      (mul_nonneg hD (Real.log_nonneg (by norm_num))) (by norm_num),
    constant_rpow_le_small_rpow (1 - s) (1 - u) 3 (η ^ 2 / (768 * C))
      (by linarith) (by norm_num) (by positivity),
    constant_rpow_le_small_rpow 0 (1 - s) (Real.log 2) 1 (by linarith)
      (Real.log_nonneg (by norm_num)) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hd hv hdim hneg htwo hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < Concentration.squareVarianceScale (K n) 3 :=
    Concentration.squareVarianceScale_pos (by norm_num)
  have hcost : (η ^ 2 / (768 * C)) * (n : ℝ) ^ (1 - u) ≤
      (n : ℝ) * η ^ 2 / (768 * Concentration.squareVarianceScale (K n) 3) := by
    calc
      _ = (n : ℝ) * η ^ 2 / (768 * (C * (n : ℝ) ^ u)) := by
        rw [Real.rpow_sub hn0, Real.rpow_one]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hv (by norm_num))
  have hd' := mul_le_mul_of_nonneg_right hd (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9))
  have hdim' : (d n : ℝ) * Real.log 9 ≤ (n : ℝ) ^ (1 - s) := by
    nlinarith
  simp only [Real.rpow_zero, mul_one, one_mul] at htwo
  rw [gramTailBudget_eq_exponential n (d n) (K n) η hη.le hη1]
  calc
    _ = Real.exp (Real.log 2 + ((d n : ℝ) * Real.log 9 -
        (n : ℝ) * η ^ 2 / (768 * Concentration.squareVarianceScale (K n) 3))) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem coarseGram_budget_eventually {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop,
      gramTailBudget n (queryCount p.a p.b n + (queryCount p.a p.b n + 1))
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) (queryCount p.a p.b n)))
        (3 / 4) ≤ Real.exp (-((n : ℝ) ^ (1 - p.sb))) := by
  rcases hb with ⟨hb0, hbf, hz, hγ, hkb, hkbz, hkbγ, hkba, hkbb, h2z, h2γ, has⟩
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hba : p.b / 4 ≤ p.a := by linarith [hf.1]
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  have hbs : p.b / 2 < p.sb := by
    linarith
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

end SKConstants.Completion.N19
