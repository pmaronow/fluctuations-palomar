module

public import SKConstants.Completion.N13bc.Gram
public import SKConstants.Completion.N19.GramRate
public import SKConstants.Completion.Blueprint4.Exponents4
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace SKConstants.Completion.N13bc
open Blueprint Blueprint4 SKConstantsOAI.ZeroTemperatureSK LGram

theorem clog_depth_le_log (K n : ℕ) (hKn : K ≤ n) (hn : 1 ≤ n) :
    (Nat.clog 2 K + 1 : ℕ) ≤ Real.log (n : ℝ) / Real.log 2 + 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hnR
  have hc := (Nat.ceil_lt_add_one hlog).le
  have heq : ⌈Real.logb 2 (n : ℝ)⌉₊ = Nat.clog 2 n := by
    simpa using Real.natCeil_logb_natCast 2 n
  rw [heq] at hc
  have hmono : (Nat.clog 2 K : ℝ) ≤ Nat.clog 2 n :=
    Nat.cast_le.mpr (Nat.clog_mono_right 2 hKn)
  simp only [Nat.cast_add, Nat.cast_one, Real.logb] at *
  linarith

theorem clog_depth_le_rpow (K n : ℕ) (hKn : K ≤ n) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) :
    (Nat.clog 2 K + 1 : ℕ) ≤ (2 + 1 / (ε * Real.log 2)) * (n : ℝ)^ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow hnR hε.le
  have H := div_le_div_of_nonneg_right
    (Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ n) hε) hlog2.le
  calc
    _ ≤ Real.log (n : ℝ) / Real.log 2 + 2 := clog_depth_le_log K n hKn hn
    _ ≤ ((n : ℝ)^ε / ε) / Real.log 2 + 2 * (n : ℝ)^ε := by linarith
    _ = _ := by ring

theorem fixedGramBudget_eventually_le
    (d r : ℕ → ℕ) (R : ℕ → ℝ) (a u s C D M : ℝ)
    (has : a < 1-s) (hus : u < s) (hs : s < 1)
    (hC : 0 < C) (hD : 0 ≤ D) (hM : 0 < M)
    (hd : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ D * (n : ℝ)^a)
    (hv : ∀ᶠ n : ℕ in atTop,
      196608 * (r n + 1 : ℝ)^4 * Concentration.squareVarianceScale (R n) 3 ≤
        C * (n : ℝ)^u) :
    ∀ᶠ n : ℕ in atTop,
      gramTailBudget n (d n) (R n) (fixedGramTolerance (r n)) ≤
        Real.exp (-(M * (n : ℝ)^(1-s))) := by
  filter_upwards [hd, hv,
    constant_rpow_le_small_rpow a (1-s) (D * Real.log 9) 1 has
      (mul_nonneg hD (Real.log_nonneg (by norm_num))) (by norm_num),
    constant_rpow_le_small_rpow (1-s) (1-u) (M+2) (1/C)
      (by linarith) (by linarith) (by positivity),
    constant_rpow_le_small_rpow 0 (1-s) (Real.log 2) 1 (by linarith)
      (Real.log_nonneg (by norm_num)) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hd hv hdim hneg htwo hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < Concentration.squareVarianceScale (R n) 3 :=
    Concentration.squareVarianceScale_pos (by norm_num)
  have hden : 0 < 196608 * (r n + 1 : ℝ)^4 *
      Concentration.squareVarianceScale (R n) 3 := by positivity
  have hcost : (1/C) * (n : ℝ)^(1-u) ≤
      (n : ℝ) / (196608 * (r n + 1 : ℝ)^4 *
        Concentration.squareVarianceScale (R n) 3) := by
    calc
      _ = (n : ℝ) / (C * (n : ℝ)^u) := by
        rw [Real.rpow_sub hn0, Real.rpow_one]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left hn0.le hden hv
  have hdim' := mul_le_mul_of_nonneg_right hd (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9))
  simp only [Real.rpow_zero, mul_one, one_mul] at htwo
  rw [gramTailBudget_fixed]
  calc
    _ = Real.exp (Real.log 2 + ((d n : ℝ)*Real.log 9 - (n : ℝ) /
        (196608 * (r n + 1 : ℝ)^4 * Concentration.squareVarianceScale (R n) 3))) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem coarseMixedVariance_eventually
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a b ε : ℝ) (hb : 0 < b) (hba : b/4 ≤ a) (ha1 : a < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Concentration.squareVarianceScale
        (actualParisiFullMixedRowMGFProxy W β
          (growingQueryTime (meshSize a n) (queryCount a b n))) 3 ≤
        C * (n : ℝ)^(b/2 + 2*ε) := by
  let u := b/2 + ε
  have hu : 0 ≤ u := by dsimp [u]; linarith
  obtain ⟨C,hC,hproxy⟩ := mixedRowMGFProxy_global_bound W β hβ
  let C₀ := C * Real.exp (1/2) * (2+b/ε)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let C₁ := C₀ * (3 + 2*Real.exp 1 + 4*|Real.log (2*Real.exp 1*C₀)| + 4*u/ε)
  refine ⟨C₁, by dsimp [C₁]; positivity, ?_⟩
  filter_upwards [schedule_eventually a b hb hba ha1] with n hsched
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  let V := growingQueryTime (meshSize a n) (queryCount a b n)
  have hV : (V : ℝ) ≤ b * Real.log n + 1 := by
    have h := (horizon_bounds a b hb hba n hsched.1 hsched.2.1).2
    exact (NNReal.coe_le_coe.mpr
      ((M1.growingQueryTime_monotone (meshSize a n)) (Nat.le_succ _))).trans h
  have he : Real.exp ((V : ℝ)/2) ≤ Real.exp (1/2) * (n : ℝ)^(b/2) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hroot : Real.sqrt (1+(V : ℝ)) ≤ 1+(V : ℝ) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1+(V : ℝ)),
      Real.sqrt_nonneg (1+(V : ℝ)), V.coe_nonneg]
  have hlog := log_term_le (n : ℝ) V b ε hnR hb.le hε hV
  have hK : (actualParisiFullMixedRowMGFProxy W β V : ℝ) ≤ C₀ * (n : ℝ)^u := by
    calc
      _ ≤ C * Real.exp ((V : ℝ)/2) * Real.sqrt (1+(V : ℝ)) := hproxy V
      _ ≤ (C * (Real.exp (1/2) * (n : ℝ)^(b/2))) *
          ((2+b/ε) * (n : ℝ)^ε) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) (hroot.trans hlog)
          (by positivity) (by positivity)
      _ = _ := by dsimp [C₀,u]; rw [Real.rpow_add hn0]; ring
  have hK1 : 1 ≤ (actualParisiFullMixedRowMGFProxy W β V : ℝ) := by
    simp only [actualParisiFullMixedRowMGFProxy, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [(actualParisiPosteriorRowMGFProxy W β V).coe_nonneg]
  convert N19.varianceScale_le_rpow (n : ℝ) _ C₀ u ε hnR hK1 hC₀ hu hε hK using 1 <;>
    dsimp [u] <;> congr 1 <;> ring

theorem coarseFixedGram_budget_eventually
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseExponents4 p)
    (M : ℝ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      gramTailBudget n (queryCount p.a p.b n + (queryCount p.a p.b n+1))
        (actualParisiFullMixedRowMGFProxy W β
          (growingQueryTime (meshSize p.a n) (queryCount p.a p.b n)))
        (fixedGramTolerance (Nat.clog 2 (queryCount p.a p.b n))) ≤
      Real.exp (-(M * (n : ℝ)^(1-p.sb))) := by
  rcases hb with ⟨hb0,hbf,hba',hkb,hkbz,hza,hzb,hzg,hγs,hγbs,hbs,hzs,hzγ,hzb',has⟩
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hba : p.b/4 ≤ p.a := hba'.le
  have ha1 : p.a < 1 := by linarith [hf.2.1]
  let ε := (p.sb-p.b/2)/16
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C,hC,hvar⟩ := coarseMixedVariance_eventually W β hβ p.a p.b ε hb0 hba ha1 hε
  let A := 2 + 1/(ε*Real.log 2)
  have hA : 0 < A := by dsimp [A]; positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hden : ∀ᶠ n : ℕ in atTop,
      196608 * (Nat.clog 2 (queryCount p.a p.b n)+1 : ℝ)^4 *
        Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β
            (growingQueryTime (meshSize p.a n) (queryCount p.a p.b n))) 3 ≤
          (196608*A^4*C) * (n : ℝ)^(p.b/2+6*ε) := by
    filter_upwards [hvar,eventually_ge_atTop (1 : ℕ)] with n hv hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hq : queryCount p.a p.b n ≤ n := Nat.min_le_right _ _
    have hr := clog_depth_le_rpow _ n hq hn ε hε
    have hr' : (Nat.clog 2 (queryCount p.a p.b n)+1 : ℝ)^4 ≤
        (A*(n : ℝ)^ε)^4 := by
      exact pow_le_pow_left₀ (by positivity) (by simpa only [Nat.cast_add,Nat.cast_one] using hr) 4
    calc
      _ ≤ 196608*(A*(n : ℝ)^ε)^4 * (C*(n : ℝ)^(p.b/2+2*ε)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr' (by norm_num)) hv
          (Concentration.squareVarianceScale_pos (by norm_num)).le (by positivity)
      _ = _ := by
        have hp : ((n : ℝ)^ε)^4 = (n : ℝ)^(ε*4) := by
          exact (Real.rpow_mul_natCast hn0.le ε 4).symm
        have hp2 : (n : ℝ)^(ε*4) * (n : ℝ)^(p.b/2+2*ε) =
            (n : ℝ)^(p.b/2+6*ε) := by
          rw [← Real.rpow_add hn0]
          congr 1
          ring
        rw [mul_pow, hp]
        calc
          _ = 196608*A^4*C * ((n : ℝ)^(ε*4) * (n : ℝ)^(p.b/2+2*ε)) := by ring
          _ = _ := by rw [hp2]
  have hdim : ∀ᶠ n : ℕ in atTop,
      (queryCount p.a p.b n + (queryCount p.a p.b n+1) : ℕ) ≤
        (17 : ℝ)*(n : ℝ)^p.a := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hq : (queryCount p.a p.b n : ℝ) ≤ 8*(n : ℝ)^p.a :=
      (Nat.cast_le.mpr (show queryCount p.a p.b n ≤ stopIndex p.a p.b n by
        unfold queryCount; omega)).trans (stopIndex_le p.a p.b hb0 hba n (by omega))
    have h1 := Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) ha.le
    push_cast
    linarith
  exact fixedGramBudget_eventually_le _ _ _ p.a (p.b/2+6*ε) p.sb
    (196608*A^4*C) 17 M has (by dsimp [ε]; linarith) (by linarith)
    (by positivity) (by norm_num) hM hdim hden

end SKConstants.Completion.N13bc
