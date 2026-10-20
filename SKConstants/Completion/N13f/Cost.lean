module

public import SKConstants.Completion.N13f.Budgets
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint

def coarseDyadicDepth (n : ℕ) : ℕ := Nat.clog 2 n

theorem coarseDyadicDepth_padding (p : Parameters) (n : ℕ) :
    queryCount p.a p.b n + (2^coarseDyadicDepth n-queryCount p.a p.b n) =
      2^coarseDyadicDepth n := by
  have hq : queryCount p.a p.b n ≤ n := by unfold queryCount; exact min_le_right _ _
  have hn : n ≤ 2^coarseDyadicDepth n := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) n
  omega

theorem coarseDyadicDepth_le_power (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ((coarseDyadicDepth n+1 : ℕ) : ℝ) ≤
      (2+1/(Real.log 2*ε))*(n : ℝ)^ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl0 : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hnR
  have hceil := (Nat.ceil_lt_add_one hl0).le
  change ((⌈Real.logb (2 : ℕ) (n : ℝ)⌉₊ : ℕ) : ℝ) ≤ _ at hceil
  rw [Real.natCeil_logb_natCast] at hceil
  have hlog := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ n) hε
  have hp : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow hnR hε.le
  have hdiv := (div_le_div_of_nonneg_right hlog hl2.le)
  unfold coarseDyadicDepth
  rw [Real.logb] at hceil
  push_cast
  calc
    _ ≤ 2+Real.log (n : ℝ)/Real.log 2 := by linarith
    _ ≤ 2+(n : ℝ)^ε/ε/Real.log 2 := add_le_add_right hdiv 2
    _ ≤ (2+1/(Real.log 2*ε))*(n : ℝ)^ε := by
      have he : (n : ℝ)^ε/ε/Real.log 2 = (1/(Real.log 2*ε))*(n : ℝ)^ε := by ring
      rw [he]
      nlinarith

theorem coarseDyadicDepth_small_eventually (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,
      16*((coarseDyadicDepth n+1 : ℕ) : ℝ)^2*(n : ℝ)^(-γ) ≤ 1 := by
  let ε := γ/4
  let C := 2+1/(Real.log 2*ε)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [constant_rpow_le_small_rpow (2*ε-γ) 0 (16*C^2) 1
    (by dsimp [ε]; linarith) (by positivity) (by norm_num),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hd := coarseDyadicDepth_le_power n hn1 ε hε
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (coarseDyadicDepth n+1 : ℕ)) hd 2
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 16))
    (Real.rpow_nonneg hn0.le (-γ))
  have he : 16*(C*(n : ℝ)^ε)^2*(n : ℝ)^(-γ) = 16*C^2*(n : ℝ)^(2*ε-γ) := by
    rw [mul_pow, show 2*ε-γ = ε*2+(-γ) by ring, Real.rpow_add hn0,
      Real.rpow_mul hn0.le, Real.rpow_two]
    ring
  rw [he] at hmul
  exact hmul.trans (by simpa using hn)

def coarseLikelihoodCost {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (p : Parameters) (n : ℕ) : ℝ :=
  (n : ℝ)*(actualParisiFullSusceptibilityExpected W β (readoutTime p.a p.b n))^2 +
    (n : ℝ)*(meshSize p.a n : ℝ) + (n : ℝ)*(n : ℝ)^(-p.z) +
    (n : ℝ)*((coarseDyadicDepth n+1 : ℕ) : ℝ)^4*((n : ℝ)^(-p.gamma))^2

theorem coarseLikelihoodCost_eventually
    {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C*coarseLikelihoodCost W β p n ≤ (n : ℝ)^(1-p.kb) := by
  obtain ⟨T, hT, htail⟩ := susceptibility_exp_tail W β hβ
  rcases hb with ⟨hb0, hbf, hz, hγ, hkb, hkz, hkγ, hka, hkb', hzsb, hγsb, hasb⟩
  let ε := (2*p.gamma-p.kb)/8
  let D := 2+1/(Real.log 2*ε)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hsch := coarse_schedule_bounds p hf
    ⟨hb0, hbf, hz, hγ, hkb, hkz, hkγ, hka, hkb', hzsb, hγsb, hasb⟩
  filter_upwards [hsch,
    constant_rpow_le_small_rpow (1-p.b) (1-p.kb) (C*T^2) (1/4) (by linarith) (by positivity) (by norm_num),
    constant_rpow_le_small_rpow (1-p.a) (1-p.kb) C (1/4) (by linarith) hC (by norm_num),
    constant_rpow_le_small_rpow (1-p.z) (1-p.kb) C (1/4) (by linarith) hC (by norm_num),
    constant_rpow_le_small_rpow (1+4*ε-2*p.gamma) (1-p.kb) (C*D^4) (1/4)
      (by dsimp [ε]; linarith) (by positivity) (by norm_num)] with n hn ht hm hz' hd
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hp := term_tail_le (n : ℝ) (readoutTime p.a p.b n)
    (actualParisiFullSusceptibilityExpected W β (readoutTime p.a p.b n)) T p.b hnR hb0.le hT
    hn.2.2.2.2.1 (actualParisiFullSusceptibilityExpected_nonneg W β _)
    (htail _ (readoutTime p.a p.b n).coe_nonneg)
  have hp' := mul_le_mul_of_nonneg_left hp hC
  have hd0 := coarseDyadicDepth_le_power n hn1 ε hε
  have hd4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (coarseDyadicDepth n+1 : ℕ)) hd0 4
  have hd' := mul_le_mul_of_nonneg_left hd4
    (by positivity : 0 ≤ C*(n : ℝ)*((n : ℝ)^(-p.gamma))^2)
  have hdepth : C*(n : ℝ)*((n : ℝ)^(-p.gamma))^2*(D*(n : ℝ)^ε)^4 =
      C*D^4*(n : ℝ)^(1+4*ε-2*p.gamma) := by
    rw [mul_pow, show 1+4*ε-2*p.gamma = 1+((-p.gamma)*2+ε*4) by ring,
      Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one,
      Real.rpow_mul hn0.le, Real.rpow_mul hn0.le, Real.rpow_two]
    norm_num only [Real.rpow_ofNat]
    ring
  rw [hdepth] at hd'
  have hmesh : (meshSize p.a n : ℝ) = (n : ℝ)^(-p.a) := by
    unfold meshSize paperGrowingQueryMeshSize
    rw [Real.coe_toNNReal _ (Real.rpow_nonneg hn0.le _)]
  have hpa (x : ℝ) : (n : ℝ)*(n : ℝ)^(-x) = (n : ℝ)^(1-x) := by
    rw [show 1-x = 1+(-x) by ring, Real.rpow_add hn0, Real.rpow_one]
  unfold coarseLikelihoodCost
  rw [hmesh, hpa p.a, hpa p.z]
  nlinarith

end SKConstants.Completion.N13f
