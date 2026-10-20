module

public import ConcreteComparisonStrength

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter
open scoped Topology

theorem laplaceComparisonStrength_zero_cube_bound {d lam x : ℝ}
    (hd : 0<d) (hlam : 0 ≤ lam) (hx : 0<x) (hld : lam ≤ d^2) :
    lam^3 ≤ (laplaceComparisonStrength d lam x)^3+
      (laplaceComparisonStrength d lam x)^2*x^2 := by
  rcases eq_or_lt_of_le hlam with hzero | hp
  · rw [←hzero]
    simp [laplaceComparisonStrength,comparisonStrength]
  by_cases harg : lam*x/d^3 ≤ 1
  · have he : laplaceComparisonStrength d lam x=lam := by
      simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape,harg]
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg lam) (sq_nonneg x)]
  · have harg' : d^3<lam*x := by
      have hh := (lt_div_iff₀ (pow_pos hd 3)).mp (lt_of_not_ge harg)
      simpa only [one_mul] using hh
    have hmin : d^3/x ≤ lam := (div_le_iff₀ hx).mpr harg'.le
    have he : d^3/x ≤ laplaceComparisonStrength d lam x := by
      have hh := laplaceComparisonStrength_lower hd hp hx
      rw [min_eq_right hmin] at hh
      exact hh
    have hepos : 0 ≤ laplaceComparisonStrength d lam x := (laplaceComparisonStrength_pos d hp x).le
    have hex : d^3 ≤ laplaceComparisonStrength d lam x*x := (div_le_iff₀ hx).mp he
    have hsq := pow_le_pow_left₀ (pow_nonneg hd.le 3) hex 2
    have hcube := pow_le_pow_left₀ hp.le hld 3
    have hpow : (d^2)^3=(d^3)^2 := by ring
    have hp3 : 0 ≤ (laplaceComparisonStrength d lam x)^3 := pow_nonneg hepos 3
    rw [hpow] at hcube
    nlinarith

theorem laplaceComparisonStrength_zero_normalized_bound {d lam x : ℝ}
    (hd : 0<d) (hlam : 0 ≤ lam) (hx : 0<x) (hld : lam ≤ d^2) :
    (lam/x^2)^3 ≤ (laplaceComparisonStrength d lam x/x^2)^3+
      (laplaceComparisonStrength d lam x/x^2)^2 := by
  have hb := laplaceComparisonStrength_zero_cube_bound hd hlam hx hld
  have hm := div_le_div_of_nonneg_right hb (pow_nonneg hx.le 6)
  convert hm using 1 <;> field_simp <;> ring

theorem actual_zero_strength_small_of_working_strength
    {d lam x : ℕ→ℝ}
    (hdata : ∀ᶠ n in atTop,0<d n ∧ 0 ≤ lam n ∧ 0<x n ∧ lam n ≤ (d n)^2)
    (hsmall : Tendsto (fun n=>laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)
      atTop (𝓝 0)) :
    Tendsto (fun n=>laplaceComparisonStrength (d n) (lam n) 0/(x n)^2) atTop (𝓝 0) := by
  have he0 (n : ℕ) : laplaceComparisonStrength (d n) (lam n) 0=lam n := by
    simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]
  simp_rw [he0]
  have hrhs : Tendsto (fun n=>(laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)^3+
      (laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 3≠0),zero_pow (by norm_num : 2≠0),zero_add] using
      (hsmall.pow 3).add (hsmall.pow 2)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hdata] with n hn
    exact ha.trans_le (div_nonneg hn.2.1 (sq_nonneg _))
  · intro a ha
    have ha3 : 0<a^3 := pow_pos ha 3
    filter_upwards [hdata,hrhs.eventually (gt_mem_nhds ha3)] with n hn hbound
    have hb := laplaceComparisonStrength_zero_normalized_bound hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    have hq : 0 ≤ lam n/(x n)^2 := div_nonneg hn.2.1 (sq_nonneg _)
    have hc : (lam n/(x n)^2)^3<a^3 := hb.trans_lt hbound
    by_contra hnot
    have haq : a ≤ lam n/(x n)^2 := le_of_not_gt hnot
    have hp := pow_le_pow_left₀ ha.le haq 3
    exact not_lt_of_ge hp hc

end OAI.SKFluctuations.LaplaceWindowFormalization
