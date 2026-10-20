module

public import GeneralMacroScalarEndpoint
public import ComparisonMacroThermalClosure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def initialThermalBudget (tau epsilon t : ℝ) : ℝ := if t < tau then 1 else epsilon

theorem initialThermalBudget_intervalIntegrable (tau epsilon a b : ℝ) :
    IntervalIntegrable (initialThermalBudget tau epsilon) volume a b := by
  have hm : Measurable (initialThermalBudget tau epsilon) :=
    measurable_const.ite measurableSet_Iio measurable_const
  apply (intervalIntegrable_const (c := (1:ℝ)+|epsilon|)).mono_fun
    hm.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1:ℝ)+|epsilon|)]
  unfold initialThermalBudget
  split_ifs <;> simp

theorem initialThermalBudget_integral {tau epsilon : ℝ} (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    (∫t in (0:ℝ)..1,initialThermalBudget tau epsilon t)=tau+(1-tau)*epsilon := by
  have hleft : (∫t in (0:ℝ)..tau,initialThermalBudget tau epsilon t)=tau := by
    rw [intervalIntegral.integral_congr_Ioo_of_le htau
      (g := fun _ => (1:ℝ)) (fun t ht => by simp [initialThermalBudget,ht.2])]
    simp
  have hright : (∫t in tau..1,initialThermalBudget tau epsilon t)=(1-tau)*epsilon := by
    rw [intervalIntegral.integral_congr_Ioo_of_le htau1
      (g := fun _ => epsilon) (fun t ht => by simp [initialThermalBudget,not_lt.mpr ht.1.le])]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (initialThermalBudget_intervalIntegrable tau epsilon 0 tau)
    (initialThermalBudget_intervalIntegrable tau epsilon tau 1),hleft,hright]

theorem macroDensityFloor_tendsto_zero : Tendsto macroDensityFloor atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (n:ℝ)^(-(1:ℝ)/8)) atTop (𝓝 0)
  simpa only [Function.comp_def,neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem macroConstraintError_tendsto_zero :
    Tendsto (fun n : ℕ => macroDensityFloor n+(1/macroDensityCap n)^2) atTop (𝓝 0) := by
  simpa only [← macroDensityFloor_reciprocal,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using
    macroDensityFloor_tendsto_zero.add (macroDensityFloor_tendsto_zero.pow 2)

theorem eventually_general_macro_cost_bound (b h : ℝ → ℝ) {W bstar tau epsilon : ℝ}
    (hW : 0 ≤ W) (hbstar : 0 < bstar) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (heps : 0 < epsilon) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hbm : Measurable b)
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hbl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) :
    ∀ᶠ n : ℕ in atTop,
      generalMacroScalarEndpoint b h n-realOrderedSKPathPressure n b h 0 ≤
        (W/4)*(tau+epsilon+macroDensityFloor n+(1/macroDensityCap n)^2) := by
  filter_upwards [eventually_macroThermalDefect_uniform b h hbstar htau heps hb hh hbl hhn,
    eventually_gt_atTop (1:ℕ)] with n htherm hn
  let hη := macroDensityFloor_pos (n := n) (by omega)
  let hQ := macroDensityCap_gt_one hn
  have hcost := macro_minimum_cost_of_thermal_budget hη (macroDensityFloor_lt_one hn) hQ
    n (by omega) b h (initialThermalBudget tau epsilon) hW hbstar hb hh hbm hbb hbl hhn
    (initialThermalBudget_intervalIntegrable tau epsilon 0 1) (by
      intro t ht α _
      by_cases hlt : t < tau
      · simpa only [initialThermalBudget,if_pos hlt] using
          (macroThermalDefect_mem_Icc n (by omega) b h _ hb hh
            (macroInverseQuantile_monotone hη hQ α) (fun u hu => (hbb u hu).1)
            (fun u _ => (macroInverseQuantile_bounds hη hQ α u).1) ⟨ht.1.le,ht.2.le⟩).2
      · simpa only [initialThermalBudget,if_neg hlt] using
          (htherm hη hQ t ⟨not_lt.mp hlt,ht.2.le⟩ α).le)
  rw [macroMinimumValue_zero hη (macroDensityFloor_lt_one hn) hQ n (by omega)
    b h hW hb hh hbb hhn,initialThermalBudget_integral htau.le htau1] at hcost
  have hsmall : tau+(1-tau)*epsilon ≤ tau+epsilon := by
    nlinarith [mul_nonneg htau.le heps.le]
  rw [generalMacroScalarEndpoint,dif_pos hn]
  exact hcost.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

theorem generalMacroPressure_le_endpoint (b h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) {n : ℕ} (hn : 1 < n) :
    realOrderedSKPathPressure n b h 0 ≤ generalMacroScalarEndpoint b h n := by
  let hη := macroDensityFloor_pos (n := n) (by omega)
  let hQ := macroDensityCap_gt_one hn
  have hm := macroMinimumValue_monotone hη (macroDensityFloor_lt_one hn) hQ n (by omega)
    b h hW hb hh hbb hhn (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
    (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) zero_le_one
  rw [macroMinimumValue_zero hη (macroDensityFloor_lt_one hn) hQ n (by omega)
    b h hW hb hh hbb hhn] at hm
  simpa only [generalMacroScalarEndpoint,dif_pos hn] using hm

theorem generalMacroPressure_tendsto (b h : ℝ → ℝ) {W bstar : ℝ}
    (hW : 0 < W) (hbstar : 0 < bstar) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hbm : Measurable b)
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hbl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) :
    Tendsto (fun n : ℕ => realOrderedSKPathPressure n b h 0) atTop
      (𝓝 (generalScalarMinimum b h)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let a := min (1/2:ℝ) (ε/(W+1))
  have ha : 0 < a := lt_min (by norm_num) (div_pos hε (by positivity))
  have ha1 : a ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hWa : (W+1)*a ≤ ε := by
    have hp := (le_div_iff₀ (by positivity : 0 < W+1)).mp (min_le_right (1/2:ℝ) (ε/(W+1)))
    simpa only [mul_comm] using hp
  have hend := (generalMacroScalarEndpoint_tendsto b h hW hb hh hbb hhn).eventually
    (Metric.ball_mem_nhds (generalScalarMinimum b h) (show 0 < ε/2 by positivity))
  have hconstraint := macroConstraintError_tendsto_zero.eventually (eventually_le_nhds ha)
  filter_upwards [eventually_general_macro_cost_bound b h hW.le hbstar ha ha1 ha
      hb hh hbm hbb hbl hhn,hend,hconstraint,eventually_gt_atTop (1:ℕ)]
    with n hcost hendn hcn hn
  have hlo := generalMacroScalarEndpoint_lower b h hW.le hb hh hbb hhn n
  have hup := generalMacroPressure_le_endpoint b h hW.le hb hh hbb hhn hn
  have hcost' : generalMacroScalarEndpoint b h n-realOrderedSKPathPressure n b h 0 ≤
      (W/4)*(3*a) := hcost.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hgap : (W/4)*(3*a)<ε := by nlinarith [mul_nonneg hW.le ha.le]
  have hnear : |generalMacroScalarEndpoint b h n-generalScalarMinimum b h|<ε/2 := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hendn
  have hdiff := le_abs_self (generalMacroScalarEndpoint b h n-generalScalarMinimum b h)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem generalMacroPressure_tendsto_of_l1 (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (bseq hseq : ℕ → ℝ → ℝ) (b h : ℝ → ℝ)
    {W bstar : ℝ} (hW : 0 < W) (hbstar : 0 < bstar)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbm : Measurable b) (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hbl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (hbs : ∀ n, MonotoneOn (bseq n) (Icc (0:ℝ) 1))
    (hhs : ∀ n, MonotoneOn (hseq n) (Icc (0:ℝ) 1))
    (hbs0 : ∀ n, 0 ≤ bseq n 0) (hhs0 : ∀ n, 0 ≤ hseq n 0)
    (hbdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|bseq n u-b u|) atTop (𝓝 0))
    (hhdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|hseq n u-h u|) atTop (𝓝 0)) :
    Tendsto (fun n => realOrderedSKPathPressure (N n) (bseq n) (hseq n) 0) atTop
      (𝓝 (generalScalarMinimum b h)) := by
  have hfixed := (generalMacroPressure_tendsto b h hW hbstar hb hh hbm hbb hbl hhn).comp hN
  have hdist : Tendsto (fun n => realOrderedSKPathPressure (N n) (bseq n) (hseq n) 0-
      realOrderedSKPathPressure (N n) b h 0) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _
      (show Tendsto (fun n => (1/4:ℝ)*(∫u in (0:ℝ)..1,|bseq n u-b u|)+
        (1/2:ℝ)*(∫u in (0:ℝ)..1,|hseq n u-h u|)) atTop (𝓝 0) by
        simpa using (hbdist.const_mul (1/4:ℝ)).add (hhdist.const_mul (1/2:ℝ)))
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℕ))] with n hn
    exact realOrderedSKPathPressure_l1_comparison (N n) hn (bseq n) (hseq n) b h
      (hbs n) (hhs n) hb hh (hbs0 n) (hhs0 n) (hbb 0 (by norm_num)).1
      (hhn 0 (by norm_num)) 0
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hdist.add hfixed

theorem generalMacroPressure_le_scalarMinimum (b h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) (n : ℕ) (hn : 0 < n) :
    realOrderedSKPathPressure n b h 0 ≤ generalScalarMinimum b h := by
  apply le_csInf (generalScalarQuantileValues_nonempty b h)
  rintro v ⟨q,hq,rfl⟩
  have hm := macroInterpolationObjective_monotone n hn b h q hW hb hh hq.1 hbb hq.2 hhn
    (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) zero_le_one
  rw [macroInterpolationObjective_zero,
    macroInterpolationObjective_scalar_general_one n hn b h q hW hb hh hbb
      (hhn 0 (by norm_num)) hq] at hm
  exact hm

end OAI.SKFluctuations.LaplaceWindowFormalization
