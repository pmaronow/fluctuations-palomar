module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.Blueprint.Experiment
public import SKConstants.ParisiScalarEnergyEntropyIdentity
public import SKConstants.ParisiScalarTerminalCorrection
public import SKConstants.ScalarProcessContinuationProfiles
public import SKConstants.Completion.LQ.ActualProfileBounds
public import SKConstants.GaussianPressureConcentration

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped NNReal ENNReal Topology unitInterval BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

theorem stopIndex_eq (a L : ℝ) (n : ℕ) (hn : 0 < n) :
    stopIndex a L n = paperGrowingQueryStop a L n hn := by
  simp [stopIndex, hn]

theorem stopIndex_pos (a L : ℝ) (hL : 0 < L) (ha : L / 4 ≤ a) (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ stopIndex a L n := by
  have hn0 : 0 < n := by omega
  rw [stopIndex_eq a L n hn0]
  by_contra h0
  have hJ : paperGrowingQueryStop a L n hn0 = 0 := by omega
  have hh := (paperGrowingQueryStop_horizon a L hL.le ha n hn0).1
  rw [hJ, growingQueryTime_zero] at hh
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  simp only [NNReal.coe_zero] at hh
  nlinarith

theorem stopIndex_le (a L : ℝ) (hL : 0 < L) (ha : L / 4 ≤ a) (n : ℕ) (hn : 0 < n) :
    (stopIndex a L n : ℝ) ≤ 8 * (n : ℝ) ^ a := by
  rw [stopIndex_eq a L n hn]
  exact paperGrowingQueryStop_count_bound a L hL.le ha n hn

theorem schedule_eventually (a L : ℝ) (hL : 0 < L) (ha : L / 4 ≤ a) (ha1 : a < 1) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ queryCount a L n + 1 = stopIndex a L n ∧ 0 < rankCount a L n := by
  filter_upwards [constant_rpow_le_small_rpow a 1 8 (1 / 2) ha1 (by norm_num) (by norm_num),
    eventually_ge_atTop 2] with n h8 hn
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hJ := stopIndex_le a L hL ha n hn0
  rw [Real.rpow_one] at h8
  have hJn : (stopIndex a L n : ℝ) < n := by linarith
  have hJn' : stopIndex a L n < n := by exact_mod_cast hJn
  have hJ1 := stopIndex_pos a L hL ha n hn
  refine ⟨hn, ?_, ?_⟩
  · unfold queryCount
    rw [min_eq_left (by omega)]
    omega
  · unfold rankCount queryCount
    rw [min_eq_left (by omega)]
    omega

theorem horizon_bounds (a L : ℝ) (hL : 0 < L) (ha : L / 4 ≤ a) (n : ℕ) (hn : 2 ≤ n)
    (hq : queryCount a L n + 1 = stopIndex a L n) :
    L * Real.log n ≤ (scalarGrowingSourceHorizon (meshSize a n) (queryCount a L n) : ℝ) ∧
      (scalarGrowingSourceHorizon (meshSize a n) (queryCount a L n) : ℝ) ≤ L * Real.log n + 1 := by
  have hn0 : 0 < n := by omega
  have h := paperGrowingQueryStop_horizon a L hL.le ha n hn0
  unfold scalarGrowingSourceHorizon
  rw [hq, stopIndex_eq a L n hn0]
  exact h

theorem duration_bound (a L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 2 ≤ n)
    (hq : queryCount a L n + 1 = stopIndex a L n) (j : ℕ) (hj : j ≤ queryCount a L n) :
    (growingQueryDuration (meshSize a n) j : ℝ) ≤ (n : ℝ) ^ (L / 4 - a) := by
  have hn0 : 0 < n := by omega
  have hjJ : j < paperGrowingQueryStop a L n hn0 := by
    rw [← stopIndex_eq a L n hn0]
    omega
  have h := growingQueryDuration_before_le _ (paperGrowingQueryMeshSize_pos a n hn0) _ j hjJ
  rw [paperGrowingQuery_scale_identity a L hL.le n hn0] at h
  exact h

theorem fine_kl_first_step (N δ q V j e P EF EH pV rV β C₁ : ℝ) (hN : 0 < N) (hβ : 0 < β)
    (hEF : EF ≤ N * P) (hId : Real.log 2 - j + β * e = P - β ^ 2 / 4 * pV ^ 2)
    (hEn : e - C₁ * (δ + ((q + 1) * (1 + V) + Real.sqrt q) / N + (q + 1) ^ 2 * V / (rV * N ^ 2)) ≤
      EH / N) :
    N * j - N * Real.log 2 + EF - β * EH ≤
      β ^ 2 / 4 * (N * pV ^ 2) + β * C₁ * (N * δ + ((q + 1) * (1 + V) + Real.sqrt q) +
        (q + 1) ^ 2 * V / (rV * N)) := by
  have h1 := mul_le_mul_of_nonneg_left hEn (show 0 ≤ β * N by positivity)
  have e1 : β * N * (EH / N) = β * EH := by field_simp
  have e2 : β * N * (e - C₁ * (δ + ((q + 1) * (1 + V) + Real.sqrt q) / N +
      (q + 1) ^ 2 * V / (rV * N ^ 2))) = β * N * e - β * C₁ * (N * δ +
        ((q + 1) * (1 + V) + Real.sqrt q) + (q + 1) ^ 2 * V / (rV * N)) := by
    field_simp
  rw [e1, e2] at h1
  have hj : j = Real.log 2 + β * e - P + β ^ 2 / 4 * pV ^ 2 := by linarith
  rw [hj]
  nlinarith

theorem term_tail_le (N V pV C₂ f : ℝ) (hN : 1 ≤ N) (hf : 0 ≤ f) (hC₂ : 0 < C₂)
    (hV : f * Real.log N ≤ V) (hp0 : 0 ≤ pV)
    (hp' : pV ≤ C₂ * Real.exp (-V / 2)) :
    N * pV ^ 2 ≤ C₂ ^ 2 * N ^ (1 - f) := by
  have hN0 : 0 < N := by linarith
  have hsq : pV ^ 2 ≤ C₂ ^ 2 * Real.exp (-V) := by
    have h := pow_le_pow_left₀ hp0 hp' 2
    rw [mul_pow, ← Real.exp_nat_mul] at h
    convert h using 3
    push_cast
    ring
  have hexp : Real.exp (-V) ≤ N ^ (-f) := by
    rw [Real.rpow_def_of_pos hN0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : N * N ^ (-f) = N ^ (1 - f) := by
    rw [show (1 : ℝ) - f = 1 + -f by ring, Real.rpow_add hN0, Real.rpow_one]
  calc N * pV ^ 2 ≤ N * (C₂ ^ 2 * N ^ (-f)) := by
        apply mul_le_mul_of_nonneg_left _ hN0.le
        exact hsq.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    _ = C₂ ^ 2 * N ^ (1 - f) := by rw [← hpow]; ring

theorem one_le_rpow_of_one_le (N x : ℝ) (hN : 1 ≤ N) (hx : 0 ≤ x) : 1 ≤ N ^ x :=
  Real.one_le_rpow hN hx

theorem log_term_le (N V f ε : ℝ) (hN : 1 ≤ N) (hf : 0 ≤ f) (hε : 0 < ε)
    (hV : V ≤ f * Real.log N + 1) :
    1 + V ≤ (2 + f / ε) * N ^ ε := by
  have hlog := Real.log_le_rpow_div (show 0 ≤ N by linarith) hε
  have h1 : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have h2 : f * Real.log N ≤ f / ε * N ^ ε := by
    calc f * Real.log N ≤ f * (N ^ ε / ε) := mul_le_mul_of_nonneg_left hlog hf
      _ = f / ε * N ^ ε := by ring
  nlinarith

theorem term_count_le (N V q f a ε : ℝ) (hN : 1 ≤ N) (hf : 0 ≤ f) (ha : 0 ≤ a) (hε : 0 < ε)
    (hq0 : 0 ≤ q) (hq : q ≤ 8 * N ^ a) (hV0 : 0 ≤ V) (hV : V ≤ f * Real.log N + 1) :
    (q + 1) * (1 + V) ≤ 9 * (2 + f / ε) * N ^ (a + ε) := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 ≤ N ^ a := Real.one_le_rpow hN ha
  have hq1 : q + 1 ≤ 9 * N ^ a := by linarith
  have hV1 := log_term_le N V f ε hN hf hε hV
  calc (q + 1) * (1 + V) ≤ (9 * N ^ a) * ((2 + f / ε) * N ^ ε) :=
        mul_le_mul hq1 hV1 (by linarith) (by positivity)
    _ = 9 * (2 + f / ε) * (N ^ a * N ^ ε) := by ring
    _ = 9 * (2 + f / ε) * N ^ (a + ε) := by rw [← Real.rpow_add hN0]

theorem term_sqrt_le (N q a : ℝ) (hN : 1 ≤ N) (hq0 : 0 ≤ q) (hq : q ≤ 8 * N ^ a) :
    Real.sqrt q ≤ 3 * N ^ (a / 2) := by
  have hN0 : 0 < N := by linarith
  have hpos : 0 ≤ N ^ (a / 2) := Real.rpow_nonneg hN0.le _
  have hsq : (3 * N ^ (a / 2)) ^ 2 = 9 * N ^ a := by
    rw [mul_pow, ← Real.rpow_natCast (N ^ (a / 2)) 2, ← Real.rpow_mul hN0.le]
    norm_num
  have : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le _
  calc Real.sqrt q ≤ Real.sqrt ((3 * N ^ (a / 2)) ^ 2) := Real.sqrt_le_sqrt (by rw [hsq]; linarith)
    _ = 3 * N ^ (a / 2) := Real.sqrt_sq (by positivity)

theorem rpow_two_mul_eq (N x : ℝ) (hN : 0 < N) : N ^ (2 * x) = (N ^ x) ^ 2 := by
  rw [show (2 : ℝ) * x = x * 2 by ring, Real.rpow_mul hN.le, Real.rpow_two]

theorem term_residual_le (N V q rV c₃ f a ε : ℝ) (hN : 1 ≤ N) (hf : 0 ≤ f) (ha : 0 ≤ a)
    (hε : 0 < ε) (hc₃ : 0 < c₃) (hq0 : 0 ≤ q) (hq : q ≤ 8 * N ^ a) (hV0 : 0 ≤ V)
    (hV : V ≤ f * Real.log N + 1)
    (hr : c₃ * (Real.exp (-V / 2) / Real.sqrt (1 + V)) ≤ rV) :
    (q + 1) ^ 2 * V / (rV * N) ≤
      81 * Real.exp (1 / 2) / c₃ * (2 + f / ε) ^ 2 * N ^ (2 * a + f / 2 - 1 + 2 * ε) := by
  have hN0 : 0 < N := by linarith
  have hs1 : 1 ≤ Real.sqrt (1 + V) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + V by linarith)
    rwa [Real.sqrt_one] at h
  have hspos : 0 < Real.sqrt (1 + V) := by linarith
  have hlow : 0 < c₃ * (Real.exp (-V / 2) / Real.sqrt (1 + V)) := by positivity
  have hrpos : 0 < rV := lt_of_lt_of_le hlow hr
  have hee : Real.exp (-V / 2) * Real.exp (V / 2) = 1 := by
    rw [← Real.exp_add, show -V / 2 + V / 2 = 0 by ring, Real.exp_zero]
  have hinv : 1 / rV ≤ Real.sqrt (1 + V) * Real.exp (V / 2) / c₃ := by
    rw [div_le_div_iff₀ hrpos hc₃, one_mul]
    have he : c₃ * (Real.exp (-V / 2) / Real.sqrt (1 + V)) * (Real.sqrt (1 + V) * Real.exp (V / 2)) =
        c₃ := by
      calc c₃ * (Real.exp (-V / 2) / Real.sqrt (1 + V)) * (Real.sqrt (1 + V) * Real.exp (V / 2))
          = c₃ * (Real.exp (-V / 2) * Real.exp (V / 2)) *
            (Real.sqrt (1 + V) / Real.sqrt (1 + V)) := by ring
        _ = c₃ := by rw [hee, div_self hspos.ne']; ring
    have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ Real.sqrt (1 + V) * Real.exp (V / 2) by
      positivity)
    rw [he] at hm
    linarith
  have h1 : 1 ≤ N ^ a := Real.one_le_rpow hN ha
  have hq1 : (q + 1) ^ 2 ≤ 81 * N ^ (2 * a) := by
    rw [rpow_two_mul_eq N a hN0]
    have h := pow_le_pow_left₀ (by linarith) (show q + 1 ≤ 9 * N ^ a by linarith) 2
    linarith [show (9 * N ^ a) ^ 2 = 81 * (N ^ a) ^ 2 by ring]
  have hsl : Real.sqrt (1 + V) ≤ 1 + V := by
    calc Real.sqrt (1 + V) ≤ Real.sqrt ((1 + V) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + V := Real.sqrt_sq (by linarith)
  have hVs : V * Real.sqrt (1 + V) ≤ (1 + V) ^ 2 := by
    calc V * Real.sqrt (1 + V) ≤ (1 + V) * (1 + V) :=
          mul_le_mul (by linarith) hsl hspos.le (by linarith)
      _ = (1 + V) ^ 2 := by ring
  have hlogt := log_term_le N V f ε hN hf hε hV
  have hVsq : (1 + V) ^ 2 ≤ (2 + f / ε) ^ 2 * N ^ (2 * ε) := by
    rw [rpow_two_mul_eq N ε hN0]
    have h := pow_le_pow_left₀ (by linarith) hlogt 2
    linarith [show ((2 + f / ε) * N ^ ε) ^ 2 = (2 + f / ε) ^ 2 * (N ^ ε) ^ 2 by ring]
  have hexp : Real.exp (V / 2) ≤ Real.exp (1 / 2) * N ^ (f / 2) := by
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hVr : V * (1 / rV) ≤ (2 + f / ε) ^ 2 * N ^ (2 * ε) * (Real.exp (1 / 2) * N ^ (f / 2)) / c₃ := by
    calc V * (1 / rV) ≤ V * (Real.sqrt (1 + V) * Real.exp (V / 2) / c₃) :=
          mul_le_mul_of_nonneg_left hinv hV0
      _ = V * Real.sqrt (1 + V) * Real.exp (V / 2) / c₃ := by ring
      _ ≤ (2 + f / ε) ^ 2 * N ^ (2 * ε) * (Real.exp (1 / 2) * N ^ (f / 2)) / c₃ := by
          apply div_le_div_of_nonneg_right _ hc₃.le
          exact mul_le_mul (hVs.trans hVsq) hexp (by positivity) (by positivity)
  have hall : (q + 1) ^ 2 * (V * (1 / rV)) ≤
      81 * N ^ (2 * a) * ((2 + f / ε) ^ 2 * N ^ (2 * ε) * (Real.exp (1 / 2) * N ^ (f / 2)) / c₃) :=
    mul_le_mul hq1 hVr (by positivity) (by positivity)
  have e1 : (q + 1) ^ 2 * V / (rV * N) = (q + 1) ^ 2 * (V * (1 / rV)) / N := by
    field_simp
  have hpow : N ^ (2 * a) * N ^ (2 * ε) * N ^ (f / 2) / N = N ^ (2 * a + f / 2 - 1 + 2 * ε) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, show 2 * a + f / 2 - 1 + 2 * ε =
      (2 * a + 2 * ε + f / 2) - 1 by ring, Real.rpow_sub_one hN0.ne']
  rw [e1, ← hpow]
  calc (q + 1) ^ 2 * (V * (1 / rV)) / N
      ≤ 81 * N ^ (2 * a) * ((2 + f / ε) ^ 2 * N ^ (2 * ε) * (Real.exp (1 / 2) * N ^ (f / 2)) / c₃)
        / N := div_le_div_of_nonneg_right hall hN0.le
    _ = 81 * Real.exp (1 / 2) / c₃ * (2 + f / ε) ^ 2 *
        (N ^ (2 * a) * N ^ (2 * ε) * N ^ (f / 2) / N) := by
        field_simp

theorem susceptibility_exp_tail {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      actualParisiFullSusceptibilityExpected W β t ≤ C * Real.exp (-t / 2) := by
  set vs := (parisiEquilibriumPhysicalEndpoint β : ℝ) with hvs
  have hvs0 : 0 ≤ vs := NNReal.coe_nonneg _
  refine ⟨4 * Real.exp ((vs + 1) / 2), by positivity, ?_⟩
  intro t ht
  have hp0 := actualParisiFullSusceptibilityExpected_nonneg W β t
  have hp1 : actualParisiFullSusceptibilityExpected W β t ≤ 1 := by
    have h1 := actualParisiFullSusceptibilityExpected_sq_le_squareExpected W β t
    have h2 := (actualParisiFullSusceptibilitySquareExpected_bounds W β t).2
    nlinarith
  by_cases hsmall : t < vs + 1
  · have he : Real.exp (-((vs + 1) / 2)) ≤ Real.exp (-t / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hone : Real.exp ((vs + 1) / 2) * Real.exp (-((vs + 1) / 2)) = 1 := by
      rw [← Real.exp_add, show (vs + 1) / 2 + -((vs + 1) / 2) = 0 by ring, Real.exp_zero]
    have : 1 ≤ 4 * Real.exp ((vs + 1) / 2) * Real.exp (-t / 2) := by
      have h4 : (4 : ℝ) * (Real.exp ((vs + 1) / 2) * Real.exp (-((vs + 1) / 2))) ≤
          4 * Real.exp ((vs + 1) / 2) * Real.exp (-t / 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left he (by positivity)
      rw [hone] at h4
      linarith
    linarith
  · set S := t - vs with hS
    have hS1 : 1 ≤ S := by linarith
    have hpost := actualParisiFullSusceptibilityExpected_post W β hβ S (by linarith)
    rw [show vs + S = t by rw [hS]; ring] at hpost
    have hsq := actualParisiContinuationP_square_le_exp W β hβ S hS1
    rw [← hpost] at hsq
    have hB : 0 < 4 * Real.exp (-S / 2) := by positivity
    have hBsq : (4 * Real.exp (-S / 2)) ^ 2 = 16 * Real.exp (-S) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf
    have hle : actualParisiFullSusceptibilityExpected W β t ≤ 4 * Real.exp (-S / 2) := by
      nlinarith
    have he : Real.exp (-S / 2) ≤ Real.exp ((vs + 1) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by rw [hS]; linarith)
    calc actualParisiFullSusceptibilityExpected W β t ≤ 4 * Real.exp (-S / 2) := hle
      _ ≤ 4 * (Real.exp ((vs + 1) / 2) * Real.exp (-t / 2)) :=
          mul_le_mul_of_nonneg_left he (by norm_num)
      _ = 4 * Real.exp ((vs + 1) / 2) * Real.exp (-t / 2) := by ring

theorem r_lower_of_continuation {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (c₃ : ℝ) (hc₃ : 0 < c₃)
    (hr : ∀ v : ℝ, 0 ≤ v → c₃ * (Real.exp (-v / 2) / Real.sqrt (1 + v)) ≤
      actualParisiContinuationR W β v) (V : ℝ)
    (hV : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ V) :
    c₃ * (Real.exp (-V / 2) / Real.sqrt (1 + V)) ≤
      actualParisiFullSusceptibilitySquareExpected W β V := by
  set vs := (parisiEquilibriumPhysicalEndpoint β : ℝ)
  have hvs : 0 ≤ vs := NNReal.coe_nonneg _
  rw [SKConstants.Completion.LQ.actual_square_profile_eq W β hβ V (le_trans hvs hV)]
  refine le_trans ?_ (hr (V - vs) (by linarith))
  apply mul_le_mul_of_nonneg_left _ hc₃.le
  have hs1 : 0 < Real.sqrt (1 + (V - vs)) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (1 + (V - vs)) ≤ Real.sqrt (1 + V) := Real.sqrt_le_sqrt (by linarith)
  have he : Real.exp (-V / 2) ≤ Real.exp (-(V - vs) / 2) := Real.exp_le_exp.mpr (by linarith)
  exact div_le_div₀ (Real.exp_pos _).le he hs1 hs2

theorem fineKL_of_nodes (hKL : ForwardKLStatement) (hEn : FineEnergyStatement)
    (hM : ProposalSpinMarginalStatement) : FineKLStatement := by
  intro p hfe Ω _ W β hβ
  obtain ⟨hfa, haf, hkf0, hkfa, hkff, hkf1⟩ := hfe
  have hf0 : 0 < p.f := by linarith
  have ha0 : 0 < p.a := by linarith
  have ha1 : p.a < 1 := by linarith
  have hβ0 : 0 < β := by linarith
  obtain ⟨C₁, hC₁, hE⟩ := hEn W β hβ
  obtain ⟨C₂, hC₂, hp⟩ := susceptibility_exp_tail W β hβ
  obtain ⟨c₃, hc₃, hr⟩ := actualParisiContinuationR_global_lower W β hβ
  set b := 1 - p.kf with hb
  set ε := (b - p.a) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hlogev : ∀ᶠ n : ℕ in atTop,
      (parisiEquilibriumPhysicalEndpoint β : ℝ) / p.f ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hdurev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (p.f / 4 - p.a) ≤ 1 / 8 := by
    have h := (tendsto_rpow_neg_atTop (show 0 < p.a - p.f / 4 by linarith)).comp
      tendsto_natCast_atTop_atTop
    have h' := h.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
    filter_upwards [h'] with n hn
    simpa only [Function.comp_def, neg_sub] using hn
  refine ⟨1, ?_⟩
  filter_upwards [schedule_eventually p.a p.f hf0 hfa.le ha1, hlogev, hdurev,
    constant_rpow_le_small_rpow (1 - p.f) b (β ^ 2 / 4 * C₂ ^ 2) (1 / 5) (by linarith)
      (by positivity) (by norm_num),
    constant_rpow_le_small_rpow (1 - p.a) b (β * C₁) (1 / 5) (by linarith)
      (by positivity) (by norm_num),
    constant_rpow_le_small_rpow (p.a + ε) b (β * C₁ * (9 * (2 + p.f / ε))) (1 / 5)
      (by rw [hεdef]; linarith) (by positivity) (by norm_num),
    constant_rpow_le_small_rpow (p.a / 2) b (β * C₁ * 3) (1 / 5) (by linarith)
      (by positivity) (by norm_num),
    constant_rpow_le_small_rpow (2 * p.a + p.f / 2 - 1 + 2 * ε) b
      (β * C₁ * (81 * Real.exp (1 / 2) / c₃ * (2 + p.f / ε) ^ 2)) (1 / 5)
      (by rw [hεdef]; linarith) (by positivity) (by norm_num)] with
    n hsched hlogn hdur bA bB bC bD bE
  obtain ⟨hn2, hqJ, hr₀⟩ := hsched
  have hn0 : 0 < n := by omega
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hN0 : (0 : ℝ) < n := by linarith
  set δ := meshSize p.a n with hδdef
  have hδpos : 0 < δ := paperGrowingQueryMeshSize_pos p.a n hn0
  have hδval : (δ : ℝ) = (n : ℝ) ^ (-p.a) := by
    rw [hδdef]
    exact paperGrowingQueryMeshSize_coe p.a n
  set q := queryCount p.a p.f n with hqdef
  set r₀ := rankCount p.a p.f n with hr₀def
  set V : ℝ := (scalarGrowingSourceHorizon δ q : ℝ) with hVdef
  obtain ⟨hV1, hV2⟩ := horizon_bounds p.a p.f hf0 hfa.le n hn2 hqJ
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hN
  have hV0 : 0 ≤ V := le_trans (mul_nonneg hf0.le hlog0) hV1
  have hVs : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ V := by
    have h := (div_le_iff₀' hf0).mp hlogn
    linarith
  have hq8 : (q : ℝ) ≤ 8 * (n : ℝ) ^ p.a := by
    have h := stopIndex_le p.a p.f hf0 hfa.le n hn0
    have : (q : ℝ) ≤ (stopIndex p.a p.f n : ℝ) := by exact_mod_cast (show q ≤ _ by omega)
    linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hdurq : ∀ j ≤ q, (growingQueryDuration δ j : ℝ) ≤ 1 / 8 := fun j hj =>
    (duration_bound p.a p.f hf0 n hn2 hqJ j hj).trans hdur
  have hKLn := hKL W β hβ δ hδpos r₀ q hr₀ (rankCount_add p.a p.f n)
  have hEnn := hE δ hδpos r₀ q hr₀ (rankCount_add p.a p.f n) hdurq
  have hId := actualParisi_scalar_entropy_energy_identity W β hβ V hVs
  have hEF := primitiveGOEPressure_mean_le_parisi hn0 β
  have hpV := hp V hV0
  have hpV0 := actualParisiFullSusceptibilityExpected_nonneg W β V
  have hrV := r_lower_of_continuation W β hβ c₃ hc₃ hr V hVs
  have hstep := fine_kl_first_step (n : ℝ) δ q V (actualParisiEntropyReference W β V)
    (actualParisiEnergyReference W β V)
    (parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ)))
    (∫ g, primitiveGOEPressure n β g ∂primLaw n)
    (∫ y, goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) y.1 y.2
      ∂replayProposalGen W β hβ δ r₀ q (rankCount_add p.a p.f n))
    (actualParisiFullSusceptibilityExpected W β V)
    (actualParisiFullSusceptibilitySquareExpected W β V) β C₁ hN0 hβ0 hEF hId hEnn
  have tA := term_tail_le n V _ C₂ p.f hN hf0.le hC₂ hV1 hpV0 hpV
  have tB : (n : ℝ) * δ = (n : ℝ) ^ (1 - p.a) := by
    rw [hδval, show (1 : ℝ) - p.a = 1 + -p.a by ring, Real.rpow_add hN0, Real.rpow_one]
  have tC := term_count_le n V q p.f p.a ε hN hf0.le ha0.le hε hq0 hq8 hV0 hV2
  have tD := term_sqrt_le n q p.a hN hq0 hq8
  have tE := term_residual_le n V q _ c₃ p.f p.a ε hN hf0.le ha0.le hε hc₃ hq0 hq8 hV0 hV2 hrV
  have hβC : 0 ≤ β * C₁ := by positivity
  have hsum : (n : ℝ) * actualParisiEntropyReference W β V - n * Real.log 2 +
      (∫ g, primitiveGOEPressure n β g ∂primLaw n) -
      β * (∫ y, goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) y.1 y.2
        ∂replayProposalGen W β hβ δ r₀ q (rankCount_add p.a p.f n)) ≤ 1 * (n : ℝ) ^ (1 - p.kf) := by
    refine hstep.trans ?_
    have hA := mul_le_mul_of_nonneg_left tA (show 0 ≤ β ^ 2 / 4 by positivity)
    have hB2 : β * C₁ * ((n : ℝ) * δ + ((q + 1) * (1 + V) + Real.sqrt q) +
        (q + 1) ^ 2 * V / (actualParisiFullSusceptibilitySquareExpected W β V * n)) ≤
        β * C₁ * ((n : ℝ) ^ (1 - p.a) + 9 * (2 + p.f / ε) * (n : ℝ) ^ (p.a + ε) +
          3 * (n : ℝ) ^ (p.a / 2) + 81 * Real.exp (1 / 2) / c₃ * (2 + p.f / ε) ^ 2 *
            (n : ℝ) ^ (2 * p.a + p.f / 2 - 1 + 2 * ε)) := by
      apply mul_le_mul_of_nonneg_left _ hβC
      rw [tB]
      linarith
    have e1 : β ^ 2 / 4 * (C₂ ^ 2 * (n : ℝ) ^ (1 - p.f)) = β ^ 2 / 4 * C₂ ^ 2 * (n : ℝ) ^ (1 - p.f) := by
      ring
    have e2 : β * C₁ * ((n : ℝ) ^ (1 - p.a) + 9 * (2 + p.f / ε) * (n : ℝ) ^ (p.a + ε) +
          3 * (n : ℝ) ^ (p.a / 2) + 81 * Real.exp (1 / 2) / c₃ * (2 + p.f / ε) ^ 2 *
            (n : ℝ) ^ (2 * p.a + p.f / 2 - 1 + 2 * ε)) =
        β * C₁ * (n : ℝ) ^ (1 - p.a) + β * C₁ * (9 * (2 + p.f / ε)) * (n : ℝ) ^ (p.a + ε) +
          β * C₁ * 3 * (n : ℝ) ^ (p.a / 2) +
          β * C₁ * (81 * Real.exp (1 / 2) / c₃ * (2 + p.f / ε) ^ 2) *
            (n : ℝ) ^ (2 * p.a + p.f / 2 - 1 + 2 * ε) := by ring
    rw [e1] at hA
    rw [e2] at hB2
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [fineProposal_eq_gen]
    exact hM W β hβ δ hδpos r₀ q hr₀ (rankCount_add p.a p.f n)
  · rw [fineProposal_eq_gen]
    unfold replayProposalGen
    have hX : Measurable (fun x : (Prim n × ReplayAux δ r₀ q) × (Fin n → I) =>
        replaySpinGen W β hβ δ r₀ q (rankCount_add p.a p.f n) x.1.1 x.1.2 x.2) :=
      (measurable_thresholdSpin n).comp
        (((measurable_castReplayMag W β hβ δ r₀ q (rankCount_add p.a p.f n)
          (scalarGrowingSourceHorizon δ q)).comp measurable_fst).prodMk measurable_snd)
    rw [Measure.snd_map_prodMk hX measurable_fst.fst]
    rw [show (fun x : (Prim n × ReplayAux δ r₀ q) × (Fin n → I) => x.1.1) =
      Prod.fst ∘ Prod.fst from rfl, ← Measure.map_map measurable_fst measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]
  · rw [fineProposal_eq_gen]
    exact hKLn.trans (ENNReal.ofReal_le_ofReal hsum)

end SKConstants.Blueprint
