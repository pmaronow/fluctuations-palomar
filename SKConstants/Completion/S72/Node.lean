module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.NScalar.Node
public import SKConstants.Completion.N13e.ScalarBounds
public import SKConstants.Completion.LW.DurationBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.S72
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type} [MeasurableSpace Ω]

theorem susceptibility_drop_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    actualParisiFullSusceptibilityExpected W β s -
        actualParisiFullSusceptibilityExpected W β t ≤
      (t - s) * actualParisiFullSusceptibilityExpected W β s := by
  have H := NScalar.susceptibility_exp_comparison W β hβ s t hs hst
  have hm := mul_le_mul_of_nonneg_left H (Real.exp_pos (-(t - s))).le
  have he : Real.exp (-(t - s)) * Real.exp (t - s) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hm
  have hex := Real.add_one_le_exp (-(t - s))
  have hp := actualParisiFullSusceptibilityExpected_nonneg W β s
  nlinarith [mul_le_mul_of_nonneg_right hex hp]

theorem growing_sqrt_duration_ratio_le_two (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ)
    (hsmall : growingQueryDuration δ j ≤ 1) :
    Real.sqrt (((growingQueryTime δ (j + 2) : ℝ) - growingQueryTime δ (j + 1)) /
      ((growingQueryTime δ (j + 1) : ℝ) - growingQueryTime δ j)) ≤ 2 := by
  rw [show j + 2 = j + 1 + 1 by omega, growingQueryTime_sub, growingQueryTime_sub]
  have hd : 0 < (growingQueryDuration δ j : ℝ) :=
    NNReal.coe_pos.mpr (growingQueryDuration_pos δ hδ j)
  change Real.sqrt (LQ.meshDuration δ (j + 1) / LQ.meshDuration δ j) ≤ 2
  rw [LQ.meshDuration_succ,
    mul_div_cancel_left₀ _ (show LQ.meshDuration δ j ≠ 0 from hd.ne'), ← Real.exp_half]
  have hs : (growingQueryDuration δ j : ℝ) ≤ 1 := by exact_mod_cast hsmall
  have he := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 8 by norm_num) (show (1 / 8 : ℝ) < 1 by norm_num)
  calc
    _ ≤ Real.exp (1 / 8) := Real.exp_le_exp.mpr (by dsimp [LQ.meshDuration]; linarith)
    _ ≤ 2 := he.trans (by norm_num)

theorem growing_residualCoarseA_eq_weight (W : BrownianSystem Ω) (β : ℝ)
    (δ : ℝ≥0) (K j : ℕ) (hj : j < K) :
    LJ.residualCoarseA W β (growingQueryTime δ) K j =
      LM4b.actualCoarseWeight W β (growingQueryTime δ) j := by
  rw [LJ.residualCoarseA, ite_eq_left hj]
  simp only [LJ.gridQueryMean, LQ.actualParisiQueryIntervalSpinMean,
    LJ.gridPosteriorScale, LM4b.actualCoarseWeight, LM4b.actualCoarseSpinMean,
    LM4b.actualCoarseScale, LM4b.actualQueryCellMean]
  congr 2
  apply intervalIntegral.integral_congr
  intro v _
  ring

theorem growing_residualCoarseA_abs_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K j : ℕ) (hj : j < K)
    (hsmall : growingQueryDuration δ j ≤ 1) :
    |LJ.residualCoarseA W β (growingQueryTime δ) K j| ≤
      2 * β * actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (j + 1)) := by
  let p := actualParisiFullSusceptibilityExpected W β
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let ρ := actualParisiQueryRho W β
  let a : ℝ := growingQueryTime δ j
  let b : ℝ := growingQueryTime δ (j + 1)
  let c : ℝ := growingQueryTime δ (j + 2)
  have ha : 0 ≤ a := (growingQueryTime δ j).coe_nonneg
  have hab : a < b := NNReal.coe_lt_coe.mpr (growingQueryTime_strictMono δ hδ (by omega))
  have hbc : b < c := NNReal.coe_lt_coe.mpr (growingQueryTime_strictMono δ hδ (by omega))
  have hb : 0 ≤ b := ha.trans hab.le
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  have hp : 0 ≤ p b := actualParisiFullSusceptibilityExpected_nonneg W β b
  have H := LW.adjacent_queryMean_div_posteriorScale_le r (fun v => p v * ρ v)
    hab hbc (mul_nonneg hβ0 hp) (LBase.actual_square_profile_pos W β hβ b hb)
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable a b)
    (((continuous_actualParisiFullSusceptibilityExpected W β).mul
      (continuous_actualParisiQueryRho W β)).intervalIntegrable b c)
    (fun v hv => LQ.actual_square_profile_antitone W β hβ (ha.trans hv.1) hb hv.2)
    (by
      intro v hv
      have hv0 := hb.trans hv.1
      refine ⟨(LQ.actual_query_integrand_bounds W β hβ v).1, ?_⟩
      dsimp only [ρ]
      rw [LQ.actual_rho_eq W β hβ v hv0]
      have hpp := LBase.actual_susceptibility_antitone W β hβ hb hv0 hv.1
      have hrr := Real.sqrt_le_sqrt (LQ.actual_square_profile_antitone W β hβ hb hv0 hv.1)
      calc
        p v * (β * Real.sqrt (r v)) = β * (p v * Real.sqrt (r v)) := by ring
        _ ≤ β * (p b * Real.sqrt (r b)) := mul_le_mul_of_nonneg_left
          (mul_le_mul hpp hrr (Real.sqrt_nonneg _) hp) hβ0
        _ = _ := by ring)
  have he : |LJ.residualCoarseA W β (growingQueryTime δ) K j| =
      |LQ.queryMean (fun v => p v * ρ v) b c| / LQ.posteriorScale r a b := by
    rw [LJ.residualCoarseA, ite_eq_left hj, abs_div]
    rw [abs_of_nonneg (show 0 ≤ LJ.gridPosteriorScale W β (growingQueryTime δ) j by
      exact (actualParisiPosteriorIntervalScale W β _ _).coe_nonneg)]
    congr 1
    exact actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _
      (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self j))
  rw [he]
  calc
    _ ≤ (β * p b) * Real.sqrt ((c - b) / (b - a)) := H
    _ ≤ (β * p b) * 2 := mul_le_mul_of_nonneg_left
      (growing_sqrt_duration_ratio_le_two δ hδ j hsmall) (mul_nonneg hβ0 hp)
    _ = _ := by ring

theorem growing_residualCoarseA_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K j : ℕ) (hj : j < K)
    (hsmall : growingQueryDuration δ (j + 1) ≤ 1)
    {v : ℝ} (hv : v ∈ Icc (growingQueryTime δ j : ℝ) (growingQueryTime δ (j + 1) : ℝ)) :
    |β * actualParisiFullSusceptibilityExpected W β v -
        LJ.residualCoarseA W β (growingQueryTime δ) K j| ≤
      32 * β * (growingQueryDuration δ (j + 1) : ℝ) *
        actualParisiFullSusceptibilityExpected W β (growingQueryTime δ j) := by
  let p := actualParisiFullSusceptibilityExpected W β
  let a : ℝ := growingQueryTime δ j
  let b : ℝ := growingQueryTime δ (j + 1)
  let h : ℝ := growingQueryDuration δ (j + 1)
  have ha : 0 ≤ a := (growingQueryTime δ j).coe_nonneg
  have hb : 0 ≤ b := (growingQueryTime δ (j + 1)).coe_nonneg
  have hv0 : 0 ≤ v := ha.trans hv.1
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  have hp0 : 0 ≤ p a := actualParisiFullSusceptibilityExpected_nonneg W β a
  have hpb : 0 ≤ p b := actualParisiFullSusceptibilityExpected_nonneg W β b
  have hpv : 0 ≤ p v := actualParisiFullSusceptibilityExpected_nonneg W β v
  have hvb : p b ≤ p v := LBase.actual_susceptibility_antitone W β hβ hv0 hb hv.2
  have hav : p v ≤ p a := LBase.actual_susceptibility_antitone W β hβ ha hv0 hv.1
  have hab : a ≤ b := NNReal.coe_le_coe.mpr
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j))
  have hpa : p b ≤ p a := LBase.actual_susceptibility_antitone W β hβ ha hb hab
  have hd : (growingQueryDuration δ j : ℝ) ≤ h := LQ.meshDuration_mono δ (Nat.le_succ j)
  have hspan : b - v ≤ h := by
    have ht := growingQueryTime_sub δ j
    change b - a = (growingQueryDuration δ j : ℝ) at ht
    linarith [hv.1]
  have hvar : |β * p v - β * p b| ≤ β * h * p a := by
    rw [abs_of_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hvb hβ0))]
    calc
      _ = β * (p v - p b) := by ring
      _ ≤ β * ((b - v) * p v) := mul_le_mul_of_nonneg_left
        (susceptibility_drop_le W β hβ v b hv0 hv.2) hβ0
      _ ≤ β * (h * p a) := mul_le_mul_of_nonneg_left
        (mul_le_mul hspan hav hpv (by positivity)) hβ0
      _ = _ := by ring
  by_cases hs : h ≤ 1 / 8
  · have hw := N13e.actualCoarseWeight_close NScalar.SusceptibilityProfileStatement_holds
      W β hβ δ hδ j hs
    rw [← growing_residualCoarseA_eq_weight W β δ K j hj, abs_sub_comm] at hw
    have hw' : |β * p b - LJ.residualCoarseA W β (growingQueryTime δ) K j| ≤
        10 * β * h * p a := hw.trans (mul_le_mul_of_nonneg_left hpa (by positivity))
    calc
      _ ≤ |β * p v - β * p b| +
          |β * p b - LJ.residualCoarseA W β (growingQueryTime δ) K j| := abs_sub_le _ _ _
      _ ≤ β * h * p a + 10 * β * h * p a := add_le_add hvar hw'
      _ ≤ _ := by nlinarith [show 0 ≤ β * h * p a by positivity]
  · have hs0 : growingQueryDuration δ j ≤ 1 := by exact_mod_cast hd.trans (by exact_mod_cast hsmall)
    have hw := growing_residualCoarseA_abs_le W β hβ δ hδ K j hj hs0
    have hw' : |LJ.residualCoarseA W β (growingQueryTime δ) K j| ≤ 2 * β * p a :=
      hw.trans (mul_le_mul_of_nonneg_left hpa (by positivity))
    calc
      _ ≤ |β * p v| + |LJ.residualCoarseA W β (growingQueryTime δ) K j| := abs_sub _ _
      _ ≤ β * p a + 2 * β * p a := by
        rw [abs_of_nonneg (mul_nonneg hβ0 hpv)]
        exact add_le_add (mul_le_mul_of_nonneg_left hav hβ0) hw'
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ 32 * h by linarith)
          (mul_nonneg hβ0 hp0)
        nlinarith only [hm]

theorem susceptibility_exp_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    actualParisiFullSusceptibilityExpected W β t ≤
      LBase.terminalTailConstant β * Real.exp (-t / 2) := by
  exact (LBase.actual_susceptibility_global_tail W β hβ t ht).trans
    (mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le
      (Real.one_le_sqrt.mpr (by linarith))) (LBase.terminalTailConstant_pos β).le)

theorem growing_susceptibility_adjacent_budget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (j : ℕ) (hsmall : growingQueryDuration δ j ≤ 1) :
    (growingQueryDuration δ j : ℝ) * (growingQueryDuration δ (j + 1) : ℝ) *
        actualParisiFullSusceptibilityExpected W β (growingQueryTime δ j) ≤
      LBase.terminalTailConstant β * Real.exp (1 / 4) * (δ : ℝ) ^ 2 := by
  let p := actualParisiFullSusceptibilityExpected W β
  have hp : 0 ≤ p (growingQueryTime δ j) := actualParisiFullSusceptibilityExpected_nonneg W β _
  have hd : 0 ≤ (growingQueryDuration δ j : ℝ) := (growingQueryDuration δ j).coe_nonneg
  have hh : (growingQueryDuration δ j : ℝ) ≤ 1 := by exact_mod_cast hsmall
  have H := LQ.mesh_profile_square_le p (LBase.terminalTailConstant β) δ j
    (susceptibility_exp_tail W β hβ _ (LQ.meshTime_nonneg δ j))
  have hnext : (growingQueryDuration δ (j + 1) : ℝ) ≤
      (growingQueryDuration δ j : ℝ) * Real.exp (1 / 4) := by
    change LQ.meshDuration δ (j + 1) ≤ LQ.meshDuration δ j * Real.exp (1 / 4)
    rw [LQ.meshDuration_succ]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by dsimp [LQ.meshDuration]; linarith)) hd
  calc
    _ ≤ (growingQueryDuration δ j : ℝ) *
        ((growingQueryDuration δ j : ℝ) * Real.exp (1 / 4)) * p (growingQueryTime δ j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnext hd) hp
    _ = (p (LQ.meshTime δ j) * LQ.meshDuration δ j ^ 2) * Real.exp (1 / 4) := by
      dsimp [LQ.meshTime, LQ.meshDuration]
      ring
    _ ≤ (LBase.terminalTailConstant β * (δ : ℝ) ^ 2) * Real.exp (1 / 4) :=
      mul_le_mul_of_nonneg_right H (Real.exp_pos _).le
    _ = _ := by ring

theorem growing_susceptibility_terminal_budget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (j : ℕ) :
    actualParisiFullSusceptibilityExpected W β (growingQueryTime δ j) *
        (growingQueryDuration δ j : ℝ) ≤ LBase.terminalTailConstant β * δ := by
  let t : ℝ := growingQueryTime δ j
  have ht : 0 ≤ t := (growingQueryTime δ j).coe_nonneg
  have hA := (LBase.terminalTailConstant_pos β).le
  rw [growingQueryDuration_coe]
  calc
    _ ≤ (LBase.terminalTailConstant β * Real.exp (-t / 2)) *
        ((δ : ℝ) * Real.exp (t / 4)) := mul_le_mul_of_nonneg_right
      (susceptibility_exp_tail W β hβ t ht) (by positivity)
    _ = (LBase.terminalTailConstant β * δ) * (Real.exp (-t / 2) * Real.exp (t / 4)) := by ring
    _ = (LBase.terminalTailConstant β * δ) * Real.exp (-t / 4) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by linarith))

theorem growing_coarse_coefficient_abs_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ i ≤ K, growingQueryDuration δ i ≤ 1)
    (j : ℕ) (_hj : j ≤ K) {v : ℝ}
    (hv : v ∈ Icc (growingQueryTime δ j : ℝ) (growingQueryTime δ (j + 1) : ℝ)) :
    |β * actualParisiFullSusceptibilityExpected W β v -
        LJ.residualCoarseA W β (growingQueryTime δ) K j| ≤ 32 * β := by
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  by_cases hlt : j < K
  · have H := growing_residualCoarseA_error W β hβ δ hδ K j hlt (hsmall (j + 1) (by omega)) hv
    have hq : (growingQueryDuration δ (j + 1) : ℝ) *
        actualParisiFullSusceptibilityExpected W β (growingQueryTime δ j) ≤ 1 :=
      (mul_le_of_le_one_right (growingQueryDuration δ (j + 1)).coe_nonneg
        (LBase.actual_susceptibility_le_one W β _)).trans
        (by exact_mod_cast hsmall (j + 1) (by omega))
    calc
      _ ≤ 32 * β * ((growingQueryDuration δ (j + 1) : ℝ) *
          actualParisiFullSusceptibilityExpected W β (growingQueryTime δ j)) := by
        simpa only [mul_assoc] using H
      _ ≤ 32 * β := mul_le_of_le_one_right (by positivity) hq
  · rw [LJ.residualCoarseA, ite_eq_right hlt, sub_zero,
      abs_of_nonneg (mul_nonneg hβ0 (actualParisiFullSusceptibilityExpected_nonneg W β v))]
    exact (mul_le_of_le_one_right hβ0 (LBase.actual_susceptibility_le_one W β v)).trans (by linarith)

def coarseCoefficientAbsBudgetConstant (β : ℝ) : ℝ :=
  (256 * β * Real.exp (1 / 4) + β) * LBase.terminalTailConstant β

theorem coarseCoefficientAbsBudgetConstant_pos (β : ℝ) (hβ : 1 < β) :
    0 < coarseCoefficientAbsBudgetConstant β := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hA := LBase.terminalTailConstant_pos β
  unfold coarseCoefficientAbsBudgetConstant
  positivity

theorem growing_coarse_coefficient_abs_integral_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ j ≤ K, growingQueryDuration δ j ≤ 1) :
    (∑ j ∈ Finset.range (K + 1),
      ∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        |β * actualParisiFullSusceptibilityExpected W β v -
          LJ.residualCoarseA W β (growingQueryTime δ) K j|) ≤
      coarseCoefficientAbsBudgetConstant β * δ := by
  let p := actualParisiFullSusceptibilityExpected W β
  let D := 32 * β * LBase.terminalTailConstant β * Real.exp (1 / 4)
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  have hA := (LBase.terminalTailConstant_pos β).le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ht (j : ℕ) : (growingQueryTime δ j : ℝ) ≤ growingQueryTime δ (j + 1) :=
    NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j))
  have hcell (j : ℕ) (hj : j < K) :
      (∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        |β * p v - LJ.residualCoarseA W β (growingQueryTime δ) K j|) ≤ D * (δ : ℝ) ^ 2 := by
    have hc : Continuous (fun v : ℝ =>
        |β * p v - LJ.residualCoarseA W β (growingQueryTime δ) K j|) :=
      ((continuous_const.mul (continuous_actualParisiFullSusceptibilityExpected W β)).sub
        continuous_const).abs
    have H := intervalIntegral.integral_mono_on (ht j) (hc.intervalIntegrable _ _)
      (intervalIntegrable_const (c := 32 * β * (growingQueryDuration δ (j + 1) : ℝ) *
        p (growingQueryTime δ j)) (μ := volume))
      (fun v hv => growing_residualCoarseA_error W β hβ δ hδ K j hj
        (hsmall (j + 1) (by omega)) hv)
    rw [intervalIntegral.integral_const, smul_eq_mul, growingQueryTime_sub] at H
    calc
      _ ≤ (growingQueryDuration δ j : ℝ) *
          (32 * β * (growingQueryDuration δ (j + 1) : ℝ) * p (growingQueryTime δ j)) := H
      _ = 32 * β * ((growingQueryDuration δ j : ℝ) *
          (growingQueryDuration δ (j + 1) : ℝ) * p (growingQueryTime δ j)) := by ring
      _ ≤ 32 * β * (LBase.terminalTailConstant β * Real.exp (1 / 4) * (δ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (growing_susceptibility_adjacent_budget W β hβ δ j (hsmall j hj.le)) (by positivity)
      _ = _ := by dsimp [D]; ring
  have hsum : (∑ j ∈ Finset.range K,
      ∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        |β * p v - LJ.residualCoarseA W β (growingQueryTime δ) K j|) ≤ 8 * D * δ := by
    have hcount := growingQuery_finite_count_bound δ hδ K (fun j hj => hsmall j hj.le)
    calc
      _ ≤ ∑ _j ∈ Finset.range K, D * (δ : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
      _ = (D * δ) * ((K : ℝ) * δ) := by simp; ring
      _ ≤ (D * δ) * 8 := mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = _ := by ring
  have hlast : (∫ v in (growingQueryTime δ K : ℝ)..(growingQueryTime δ (K + 1) : ℝ),
      |β * p v - LJ.residualCoarseA W β (growingQueryTime δ) K K|) ≤
        β * LBase.terminalTailConstant β * δ := by
    simp only [LJ.residualCoarseA, lt_self_iff_false, ↓reduceIte, sub_zero]
    have hp (v : ℝ) : 0 ≤ p v := actualParisiFullSusceptibilityExpected_nonneg W β v
    simp_rw [abs_of_nonneg (mul_nonneg hβ0 (hp _))]
    have H := intervalIntegral.integral_mono_on (ht K)
      (((continuous_actualParisiFullSusceptibilityExpected W β).const_mul β).intervalIntegrable _ _)
      (intervalIntegrable_const (c := β * p (growingQueryTime δ K)) (μ := volume))
      (fun v hv => mul_le_mul_of_nonneg_left
        (LBase.actual_susceptibility_antitone W β hβ (growingQueryTime δ K).coe_nonneg
          ((growingQueryTime δ K).coe_nonneg.trans hv.1) hv.1) hβ0)
    rw [intervalIntegral.integral_const, smul_eq_mul, growingQueryTime_sub] at H
    calc
      _ ≤ (growingQueryDuration δ K : ℝ) * (β * p (growingQueryTime δ K)) := H
      _ = β * (p (growingQueryTime δ K) * (growingQueryDuration δ K : ℝ)) := by ring
      _ ≤ β * (LBase.terminalTailConstant β * δ) :=
        mul_le_mul_of_nonneg_left (growing_susceptibility_terminal_budget W β hβ δ K) hβ0
      _ = _ := by ring
  rw [Finset.sum_range_succ]
  change _ + _ ≤ coarseCoefficientAbsBudgetConstant β * δ
  dsimp only [coarseCoefficientAbsBudgetConstant, D] at *
  nlinarith only [hsum, hlast]

theorem growing_coarse_coefficient_sq_integral_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ j ≤ K, growingQueryDuration δ j ≤ 1) :
    (∑ j ∈ Finset.range (K + 1),
      ∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        (β * actualParisiFullSusceptibilityExpected W β v -
          LJ.residualCoarseA W β (growingQueryTime δ) K j) ^ 2) ≤
      32 * β * coarseCoefficientAbsBudgetConstant β * δ := by
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  have hcell (j : ℕ) (hj : j ≤ K) :
      (∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        (β * actualParisiFullSusceptibilityExpected W β v -
          LJ.residualCoarseA W β (growingQueryTime δ) K j) ^ 2) ≤
      32 * β * (∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        |β * actualParisiFullSusceptibilityExpected W β v -
          LJ.residualCoarseA W β (growingQueryTime δ) K j|) := by
    let f := fun v : ℝ => β * actualParisiFullSusceptibilityExpected W β v -
      LJ.residualCoarseA W β (growingQueryTime δ) K j
    have hc : Continuous f :=
      (continuous_const.mul (continuous_actualParisiFullSusceptibilityExpected W β)).sub continuous_const
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on
      (NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j)))
      ((hc.pow 2).intervalIntegrable _ _) ((hc.abs.const_mul (32 * β)).intervalIntegrable _ _)
    intro v hv
    have H := growing_coarse_coefficient_abs_le W β hβ δ hδ K hsmall j hj hv
    change |f v| ≤ 32 * β at H
    have hm := mul_le_mul_of_nonneg_right H (abs_nonneg (f v))
    change (f v) ^ 2 ≤ 32 * β * |f v|
    nlinarith [sq_abs (f v)]
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), 32 * β *
        (∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
          |β * actualParisiFullSusceptibilityExpected W β v -
            LJ.residualCoarseA W β (growingQueryTime δ) K j|) :=
      Finset.sum_le_sum (fun j hj => hcell j (by have := Finset.mem_range.mp hj; omega))
    _ = 32 * β * (∑ j ∈ Finset.range (K + 1),
        ∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
          |β * actualParisiFullSusceptibilityExpected W β v -
            LJ.residualCoarseA W β (growingQueryTime δ) K j|) := by rw [Finset.mul_sum]
    _ ≤ 32 * β * (coarseCoefficientAbsBudgetConstant β * δ) :=
      mul_le_mul_of_nonneg_left
        (growing_coarse_coefficient_abs_integral_le W β hβ δ hδ K hsmall) (by positivity)
    _ = _ := by ring

theorem coarseCoefficientBudget_holds : Blueprint5a.CoarseCoefficientBudgetStatement := by
  intro Ω _ W β hβ
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hB := coarseCoefficientAbsBudgetConstant_pos β hβ
  refine ⟨(32 * β + 1) * coarseCoefficientAbsBudgetConstant β, by positivity, ?_⟩
  intro δ K hmesh
  have hs := growing_coarse_coefficient_sq_integral_le W β hβ δ hmesh.1 K hmesh.2.2.1
  have ha := growing_coarse_coefficient_abs_integral_le W β hβ δ hmesh.1 K hmesh.2.2.1
  have hδ : 0 ≤ coarseCoefficientAbsBudgetConstant β * (δ : ℝ) := by positivity
  constructor <;> dsimp only [Blueprint5a.mesh] <;> nlinarith only [hs, ha, hδ,
    mul_nonneg hβ0.le hδ]

end SKConstants.Completion.S72
