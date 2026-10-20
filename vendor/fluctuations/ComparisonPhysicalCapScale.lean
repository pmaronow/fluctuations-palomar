module

public import ComparisonReverseInterpolationSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 6400000

def comparisonConditionalCapLength (N d E : ℝ) : ℝ :=
  min (comparisonSmallMass N E) ((Real.sqrt N*E/d)^3/d^2)

theorem comparison_physical_cap_length_lower {N m gamma d E : ℝ}
    (hN : 1≤N) (hm : 0 ≤ m) (hgamma : 0<gamma) (hd : 0<d) (hd1 : d≤1)
    (hE : 0<E) (hlower : gamma*N^(-(2:ℝ)/3+m)*d≤E)
    (hupper : E≤d^2/Real.sqrt N) :
    min 1 (gamma^3)*N^(-(1:ℝ)/2)≤comparisonConditionalCapLength N d E := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hNp
  have hs2 := Real.sq_sqrt hNp.le
  have hd2 : d^2≤1 := by nlinarith
  have hNE : N*E≤Real.sqrt N := by
    have hh := (le_div_iff₀ hs).mp hupper
    have ht := mul_le_mul_of_nonneg_left (hh.trans hd2) hs.le
    nlinarith
  have hU : N^(-(1:ℝ)/2)≤comparisonSmallMass N E := by
    have hh := one_div_le_one_div_of_le (mul_pos hNp hE) hNE
    have he : 1/Real.sqrt N=N^(-(1:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow,show -(1:ℝ)/2=-((1:ℝ)/2) by ring,Real.rpow_neg hNp.le,one_div]
    exact he ▸ hh
  have ha : gamma*N^(-(1:ℝ)/6+m)≤Real.sqrt N*E/d := by
    apply (le_div_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hlower hs.le
    have he : Real.sqrt N*(gamma*N^(-(2:ℝ)/3+m)*d)=gamma*N^(-(1:ℝ)/6+m)*d := by
      rw [Real.sqrt_eq_rpow]
      calc
        _=gamma*(N^((1:ℝ)/2)*N^(-(2:ℝ)/3+m))*d := by ring
        _=_ := by rw [←Real.rpow_add hNp];congr 2;ring
    exact he ▸ hh
  have ha3 := pow_le_pow_left₀ (by positivity : 0≤gamma*N^(-(1:ℝ)/6+m)) ha 3
  have he3 : (gamma*N^(-(1:ℝ)/6+m))^3=gamma^3*N^(-(1:ℝ)/2+3*m) := by
    rw [mul_pow,←Real.rpow_mul_natCast hNp.le]
    congr 2
    norm_num
    ring
  rw [he3] at ha3
  have hpow := Real.rpow_le_rpow_of_exponent_le hN (show -(1:ℝ)/2≤-(1:ℝ)/2+3*m by linarith)
  have hlo := (mul_le_mul_of_nonneg_left hpow (pow_pos hgamma 3).le).trans ha3
  have hsecond : gamma^3*N^(-(1:ℝ)/2)≤(Real.sqrt N*E/d)^3/d^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
    have hh := mul_le_mul_of_nonneg_left hd2 (show 0≤gamma^3*N^(-(1:ℝ)/2) by positivity)
    nlinarith
  unfold comparisonConditionalCapLength
  apply le_min
  · exact (mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (gamma^3)) (Real.rpow_pos_of_pos hNp _).le).trans (by simpa using hU)
  · exact (mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (gamma^3)) (Real.rpow_pos_of_pos hNp _).le).trans hsecond

theorem comparison_physical_cap_length_eventually {m gamma : ℝ}
    (hm : 0 ≤ m) (hgamma : 0<gamma) :
    ∀ᶠ N : ℝ in atTop,∀d E : ℝ,0<d→d≤1→0<E→
      gamma*N^(-(2:ℝ)/3+m)*d≤E→E≤d^2/Real.sqrt N→
      N^(-(1:ℝ))≤comparisonConditionalCapLength N d E := by
  let c : ℝ := min 1 (gamma^3)
  have hc : 0<c := lt_min (by norm_num) (pow_pos hgamma 3)
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop (1/c)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with N hN hpow
  intro d E hd hd1 hE hlower hupper
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hb := comparison_physical_cap_length_lower hN hm hgamma hd hd1 hE hlower hupper
  have hh := mul_le_mul_of_nonneg_left hpow hc.le
  have hhc : 1≤c*N^((1:ℝ)/2) := by simpa only [mul_one_div_cancel hc.ne'] using hh
  have hmul := mul_le_mul_of_nonneg_right hhc (Real.rpow_pos_of_pos hNp (-1)).le
  have he : c*N^((1:ℝ)/2)*N^(-(1:ℝ))=c*N^(-(1:ℝ)/2) := by
    rw [mul_assoc,←Real.rpow_add hNp]
    norm_num
  rw [one_mul,he] at hmul
  exact hmul.trans hb

theorem comparison_cap_log_coefficient_lower {N U : ℝ}
    (hlog : 1≤Real.log N) (hU : 0<U) (hU1 : U≤1) :
    1≤9*Real.log N*Real.log ((1+U)/U) := by
  have hr : (2:ℝ)≤(1+U)/U := (le_div_iff₀ hU).mpr (by linarith)
  have hlog2 : (1:ℝ)/2≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hl := hlog2.trans (Real.log_le_log (by norm_num : (0:ℝ)<2) hr)
  have hh := mul_le_mul hlog hl (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤Real.log N)
  nlinarith

theorem comparison_physical_reverse_ratio {N delta U L y : ℝ}
    (hN : 1≤N) (hlog : 1≤Real.log N) (hU : 0<U) (hU1 : U≤1)
    (hL : N^(-(1:ℝ))≤L) (hy : 0≤y) (hyN : y≤N) :
    y/(9*Real.log N*((L/N^delta)*Real.log ((1+U)/U)))≤N^(delta+2) := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (Real.rpow_pos_of_pos hNp _).trans_le hL
  have hlogU : 0<Real.log ((1+U)/U) := Real.log_pos ((lt_div_iff₀ hU).mpr (by linarith))
  have hD : 0<9*Real.log N*((L/N^delta)*Real.log ((1+U)/U)) := by positivity
  have hlow : N^(-(delta+1))≤9*Real.log N*((L/N^delta)*Real.log ((1+U)/U)) := by
    have hh := mul_le_mul_of_nonneg_right (comparison_cap_log_coefficient_lower hlog hU hU1)
      (show 0≤L/N^delta by positivity)
    have hdiv := div_le_div_of_nonneg_right hL (Real.rpow_pos_of_pos hNp delta).le
    have he : N^(-(1:ℝ))/N^delta=N^(-(delta+1)) := by rw [←Real.rpow_sub hNp];congr 1;ring
    rw [he] at hdiv
    nlinarith
  have hh := comparison_reverse_ratio_of_scales hNp hD hy hlow (by simpa using hyN : y≤N^(1:ℝ))
  convert hh using 1 <;> congr 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
