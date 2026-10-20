module

public import SKConstants.Completion.Blueprint.AssemblyFine
public import SKConstants.Completion.LGram.Budget
public import SKConstants.Completion.LM4b.PsiConcentration

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint LGram

theorem exp_power_budget_absorb (a e s A c C : ℝ)
    (ha : a < e) (hs : s < e) (he : 0 < e) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.exp (A*(n : ℝ)^a - c*(n : ℝ)^e) ≤
        Real.exp (-((n : ℝ)^s))/4 := by
  filter_upwards [constant_rpow_le_small_rpow a e |A| (c/3) ha (abs_nonneg _) (by positivity),
    constant_rpow_le_small_rpow s e 1 (c/3) hs (by norm_num) (by positivity),
    constant_rpow_le_small_rpow 0 e |Real.log (4*(C+1))| (c/3) he (abs_nonneg _)
      (by positivity), eventually_ge_atTop 1] with n h1 h2 h3 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 ≤ (n : ℝ)^a := Real.rpow_nonneg hn0.le _
  have hA := mul_le_mul_of_nonneg_right (le_abs_self A) hp
  simp only [one_mul, Real.rpow_zero, mul_one] at h2 h3
  have hlog := le_abs_self (Real.log (4*(C+1)))
  have hb : A*(n : ℝ)^a-c*(n : ℝ)^e ≤
      -((n : ℝ)^s)-Real.log (4*(C+1)) := by linarith
  have hexp := Real.exp_le_exp.mpr hb
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by positivity : 0 < 4*(C+1))] at hexp
  calc
    _ ≤ (C+1)*Real.exp (A*(n : ℝ)^a-c*(n : ℝ)^e) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (C+1)*(Real.exp (-((n : ℝ)^s))/(4*(C+1))) := by
      rw [Real.exp_sub]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by field_simp

theorem squareVarianceScale_le_power
    (N K C k ε : ℝ) (hN : 1 ≤ N) (hK : 1 ≤ K) (hC : 0 < C)
    (hk : 0 ≤ k) (hε : 0 < ε) (hbound : K ≤ C*N^k) :
    Concentration.squareVarianceScale K 3 ≤
      C*(3+2*Real.exp 1+4*(|Real.log (2*Real.exp 1*C)|+k/ε))*N^(k+ε) := by
  have hN0 : 0 < N := by linarith
  have hpow : 1 ≤ N^ε := Real.one_le_rpow hN hε.le
  have hlog : Real.log (2*Real.exp 1*K) ≤
      Real.log (2*Real.exp 1*C) + k*Real.log N := by
    calc
      _ ≤ Real.log (2*Real.exp 1*(C*N^k)) :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hbound (by positivity))
      _ = _ := by rw [← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0]
  have hlogN := Real.log_le_rpow_div hN0.le hε
  have hconst : Real.log (2*Real.exp 1*C) ≤ |Real.log (2*Real.exp 1*C)| * N^ε :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hpow)
  have hlog' : Real.log (2*Real.exp 1*K) ≤
      (|Real.log (2*Real.exp 1*C)|+k/ε)*N^ε := by
    have hm := mul_le_mul_of_nonneg_left hlogN hk
    have hm' : k*Real.log N ≤ (k/ε)*N^ε := by
      calc
        _ ≤ k*(N^ε/ε) := hm
        _ = _ := by ring
    calc
      _ ≤ Real.log (2*Real.exp 1*C)+k*Real.log N := hlog
      _ ≤ |Real.log (2*Real.exp 1*C)| * N^ε+(k/ε)*N^ε := add_le_add hconst hm'
      _ = _ := by ring
  have hbracket : 3+2*Real.exp 1+4*Real.log (2*Real.exp 1*K) ≤
      (3+2*Real.exp 1+4*(|Real.log (2*Real.exp 1*C)|+k/ε))*N^ε := by
    nlinarith [Real.exp_pos (1 : ℝ)]
  calc
    _ ≤ K*(3+2*Real.exp 1+4*Real.log (2*Real.exp 1*K)) := squareVarianceScale_three_le hK
    _ ≤ K*((3+2*Real.exp 1+4*(|Real.log (2*Real.exp 1*C)|+k/ε))*N^ε) :=
      mul_le_mul_of_nonneg_left hbracket (by linarith)
    _ ≤ (C*N^k)*((3+2*Real.exp 1+4*(|Real.log (2*Real.exp 1*C)|+k/ε))*N^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := by rw [Real.rpow_add hN0]; ring

theorem mixedRowVarianceScale_log_horizon
    {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ H : ℝ≥0,
      (H : ℝ) ≤ b*Real.log n+1 →
      Concentration.squareVarianceScale (actualParisiFullMixedRowMGFProxy W β H) 3 ≤
        C*(n : ℝ)^(b/2+ε) := by
  obtain ⟨C, hC, hproxy⟩ := mixedRowMGFProxy_global_bound W β hβ
  let D := C*Real.exp (1/2)*(2+b/(ε/2))
  have hD : 0 < D := by dsimp [D]; positivity
  let k := b/2+ε/2
  refine ⟨D*(3+2*Real.exp 1+4*(|Real.log (2*Real.exp 1*D)|+k/(ε/2))),
    by dsimp [k]; positivity, ?_⟩
  intro n hn H hH
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := log_term_le (n : ℝ) H b (ε/2) hnR hb (by positivity) hH
  have hroot : Real.sqrt (1+(H : ℝ)) ≤ 1+(H : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [H.coe_nonneg]
  have he : Real.exp ((H : ℝ)/2) ≤ Real.exp (1/2)*(n : ℝ)^(b/2) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hK : (actualParisiFullMixedRowMGFProxy W β H : ℝ) ≤ D*(n : ℝ)^k := by
    calc
      _ ≤ C*Real.exp ((H : ℝ)/2)*Real.sqrt (1+(H : ℝ)) := hproxy H
      _ ≤ C*(Real.exp (1/2)*(n : ℝ)^(b/2))*((2+b/(ε/2))*(n : ℝ)^(ε/2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) (hroot.trans h1)
          (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by dsimp [D, k]; rw [Real.rpow_add hn0]; ring
  have hK1 : 1 ≤ (actualParisiFullMixedRowMGFProxy W β H : ℝ) := by
    unfold actualParisiFullMixedRowMGFProxy
    push_cast
    nlinarith [(actualParisiPosteriorRowMGFProxy W β H).coe_nonneg]
  have h := squareVarianceScale_le_power (n : ℝ) _ D k (ε/2) hnR hK1 hD
    (by dsimp [k]; positivity) (by positivity) hK
  convert h using 1
  congr 2
  dsimp [k]
  ring

theorem gramTailBudget_eventually
    (d : ℕ → ℕ) (K : ℕ → ℝ) (a γ v s Cd Cv : ℝ)
    (hγ : 0 ≤ γ) (_hCd : 0 ≤ Cd) (hCv : 0 < Cv)
    (ha : a < 1-2*γ-v) (hs : s < 1-2*γ-v) (he : 0 < 1-2*γ-v)
    (hd : ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ Cd*(n : ℝ)^a)
    (hv : ∀ᶠ n : ℕ in atTop,
      Concentration.squareVarianceScale (K n) 3 ≤ Cv*(n : ℝ)^v) :
    ∀ᶠ n : ℕ in atTop, gramTailBudget n (d n) (K n) ((n : ℝ)^(-γ)) ≤
      Real.exp (-((n : ℝ)^s))/4 := by
  filter_upwards [hd, hv, eventually_ge_atTop 1,
    exp_power_budget_absorb a (1-2*γ-v) s (Cd*Real.log 9) (1/(768*Cv)) 2
      ha hs he (by positivity) (by norm_num)] with n hdn hvn hn habs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gramTailBudget_power n (d n) (by omega) (K n) γ hγ]
  apply le_trans _ habs
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hdim := mul_le_mul_of_nonneg_right hdn (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9))
  have hvarpos : 0 < Concentration.squareVarianceScale (K n) 3 :=
    Concentration.squareVarianceScale_pos (by norm_num)
  have hdiv := div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le (1-2*γ))
    (by positivity : 0 < 768*Concentration.squareVarianceScale (K n) 3)
    (mul_le_mul_of_nonneg_left hvn (by norm_num : (0 : ℝ) ≤ 768))
  have hp : (n : ℝ)^(1-2*γ)/(768*(Cv*(n : ℝ)^v)) =
      (1/(768*Cv))*(n : ℝ)^(1-2*γ-v) := by
    rw [show (n : ℝ)^(1-2*γ-v) = (n : ℝ)^(1-2*γ)/(n : ℝ)^v from
      Real.rpow_sub hn0 (1-2*γ) v]
    ring
  rw [hp] at hdiv
  nlinarith

def ordinaryPsiTailBudget (n : ℕ) (z S : ℝ) : ℝ :=
  2*Real.exp (-(n : ℝ)*min (((n : ℝ)^(-z))^2/(8*S^2)) ((n : ℝ)^(-z)/(4*S)))

theorem ordinaryPsiTailBudget_power_le
    (n : ℕ) (hn : 1 ≤ n) (z ε S C : ℝ)
    (hz : 0 ≤ z) (hS : 1 ≤ S) (_hC : 0 < C) (hbound : S ≤ C*(n : ℝ)^ε) :
    ordinaryPsiTailBudget n z S ≤
      2*Real.exp (-((1/(8*C^2))*(n : ℝ)^(1-2*z-2*ε))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hηpos : 0 < (n : ℝ)^(-z) := Real.rpow_pos_of_pos hn0 _
  have hη : (n : ℝ)^(-z) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hcomp : ((n : ℝ)^(-z))^2/(8*S^2) ≤ (n : ℝ)^(-z)/(4*S) := by
    calc
      _ = ((n : ℝ)^(-z)/(4*S))*((n : ℝ)^(-z)/(2*S)) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity)
        ((div_le_one (by positivity)).2 (by linarith))
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ S) hbound 2
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg ((n : ℝ)^(-z)))
    (by positivity : 0 < 8*S^2) (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 8))
  have hmul := mul_le_mul_of_nonneg_left hdiv hn0.le
  have hp : (n : ℝ)*(((n : ℝ)^(-z))^2/(8*(C*(n : ℝ)^ε)^2)) =
      (1/(8*C^2))*(n : ℝ)^(1-2*z-2*ε) := by
    rw [show 1-2*z-2*ε = (1+(-z)*2)-ε*2 by ring,
      Real.rpow_sub hn0, Real.rpow_add hn0, Real.rpow_one,
      Real.rpow_mul hn0.le, Real.rpow_mul hn0.le, Real.rpow_two, Real.rpow_two]
    ring
  rw [hp] at hmul
  unfold ordinaryPsiTailBudget
  rw [min_eq_left hcomp]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact Real.exp_le_exp.mpr (by linarith)

end SKConstants.Completion.N13f
