module

public import ComparisonRadiusSizeRates
public import ComparisonNativeStarBandScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 5000000

theorem comparison_star_cubic_ratio {N m gamma d E : ℝ}
    (hN : 0 < N) (hgamma : 0 < gamma) (hd : 0 < d) (hE : 0 < E)
    (hlower : gamma*N^(-(2:ℝ)/3+m)*d ≤ E) :
    d^3/(N^2*E^3) ≤ (1/gamma^3)*N^(-3*m) := by
  have hc := pow_le_pow_left₀ (show 0≤gamma*N^(-(2:ℝ)/3+m)*d by positivity) hlower 3
  have hcN := mul_le_mul_of_nonneg_left hc (sq_nonneg N)
  have he : N^2*(gamma*N^(-(2:ℝ)/3+m)*d)^3=gamma^3*N^(3*m)*d^3 := by
    rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hN.le,←Real.rpow_natCast N 2]
    calc
      _=gamma^3*(N^(2:ℝ)*N^((-(2:ℝ)/3+m)*(3:ℝ)))*d^3 := by ring
      _=_ := by rw [←Real.rpow_add hN];congr 2;ring
  rw [he] at hcN
  have hp : (1/gamma^3)*N^(-3*m)*(gamma^3*N^(3*m)*d^3)=d^3 := by
    have hn : N^(-3*m)*N^(3*m)=1 := by rw [←Real.rpow_add hN];simp
    calc
      _=((1/gamma^3)*gamma^3)*(N^(-3*m)*N^(3*m))*d^3 := by ring
      _=_ := by rw [hn];field_simp
  apply (div_le_iff₀ (by positivity : 0 < N^2*E^3)).mpr
  have hh := mul_le_mul_of_nonneg_left hcN (show 0≤(1/gamma^3)*N^(-3*m) by positivity)
  rwa [hp] at hh

theorem comparison_star_small_scale_ratios {N d E : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E) (hupper : E ≤ d^2/Real.sqrt N) :
    comparisonSmallMass N E/comparisonLowerScale N E d ≤ d^3/(N^2*E^3) ∧
    (comparisonSmallMass N E)^2*d^2/(comparisonLowerScale N E d)^4=(d^3/(N^2*E^3))^2 := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hs2 := Real.sq_sqrt hN.le
  have hu : E*Real.sqrt N ≤ d^2 := (le_div_iff₀ hs).mp hupper
  have hu1 : E*Real.sqrt N/d^2 ≤ 1 := (div_le_one (sq_pos_of_pos hd)).mpr hu
  have heq : comparisonSmallMass N E/comparisonLowerScale N E d=
      (d^3/(N^2*E^3))*(E*Real.sqrt N/d^2) := by
    unfold comparisonSmallMass comparisonLowerScale
    field_simp
    nlinarith [congrArg (fun t=>d*N*E^2*t) hs2]
  refine ⟨?_,?_⟩
  · rw [heq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ d^3/(N^2*E^3))
  · unfold comparisonSmallMass comparisonLowerScale
    have hs4 : (Real.sqrt N)^4=N^2 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hs2]
    field_simp
    nlinarith [congrArg (fun t=>d^6*N^2*E^6*t) hs4]

theorem comparison_star_cap_ratio_three_gains {N delta d E v C : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E) (hC : 0 ≤ C)
    (hUv : comparisonSmallMass N E ≤ comparisonLowerScale N E d)
    (hav : comparisonLowerScale N E d ≤ v) :
    comparisonCap N delta (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (C*v)/(N*E*v)^2 ≤
      N^delta*((C+1)*(comparisonSmallMass N E/comparisonLowerScale N E d+
        (comparisonSmallMass N E)^2*d^2/(comparisonLowerScale N E d)^4)+
        (C+1)^2*(d^3/(N^2*E^3))) := by
  let U:=comparisonSmallMass N E
  let a:=comparisonLowerScale N E d
  let L:=comparisonConstraintLength N E d
  have hU : 0 < U := by dsimp only [U,comparisonSmallMass];positivity
  have ha : 0 < a := by dsimp only [a,comparisonLowerScale];positivity
  have hv : 0 < v := ha.trans_le hav
  have hL : 0 < L := comparisonConstraintLength_pos hN hE hd
  have hUle : U ≤ v := hUv.trans hav
  have hCv : C*v+U ≤ (C+1)*v := by nlinarith
  have hCv0 : 0 ≤ C*v+U := by positivity
  have hLinv : 1/L ≤ 1/U+d^2/a^3 := by
    dsimp only [L,comparisonConstraintLength]
    change 1/min U (a^3/d^2) ≤ 1/U+d^2/a^3
    by_cases hh : U ≤ a^3/d^2
    · rw [min_eq_left hh]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right (le_of_not_ge hh)]
      have he : 1/(a^3/d^2)=d^2/a^3 := by field_simp
      rw [he]
      exact le_add_of_nonneg_left (by positivity)
  have hfirst : (C*v+U)/L/(N*E*v)^2 ≤
      (C+1)*(U/a+U^2*d^2/a^4) := by
    have hnum : (C*v+U)*(1/L) ≤ ((C+1)*v)*(1/U+d^2/a^3) :=
      mul_le_mul hCv hLinv (by positivity) (by positivity)
    have hnum' := div_le_div_of_nonneg_right hnum (sq_nonneg (N*E*v))
    have heq : ((C+1)*v)*(1/U+d^2/a^3)/(N*E*v)^2=
        (C+1)*(U/v+U^2*d^2/(a^3*v)) := by
      dsimp only [U,comparisonSmallMass]
      field_simp
    have hu := div_le_div_of_nonneg_left hU.le ha hav
    have hden : a^4 ≤ a^3*v := by nlinarith [mul_le_mul_of_nonneg_left hav (pow_nonneg ha.le 3)]
    have hdv := div_le_div_of_nonneg_left (by positivity : 0 ≤ U^2*d^2) (pow_pos ha 4) hden
    have hg := mul_le_mul_of_nonneg_left (add_le_add hu hdv) (by positivity : 0 ≤ C+1)
    have hn : (C*v+U)/L/(N*E*v)^2 ≤ (C+1)*(U/v+U^2*d^2/(a^3*v)) := by
      simpa only [mul_one_div,heq] using hnum'
    exact hn.trans hg
  have hsecond : ((d^3/E)*(C*v+U)^2)/(N*E*v)^2 ≤ (C+1)^2*(d^3/(N^2*E^3)) := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCv0 hCv 2) (by positivity : 0 ≤ d^3/E)
    have hh := div_le_div_of_nonneg_right hp (sq_nonneg (N*E*v))
    have heq : ((d^3/E)*((C+1)*v)^2)/(N*E*v)^2=(C+1)^2*(d^3/(N^2*E^3)) := by field_simp
    simpa only [heq] using hh
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (Real.rpow_nonneg hN.le delta)
  convert hsum using 1
  · dsimp only [comparisonCap,U,L]
    ring

theorem eventually_comparison_star_cap_saving {m delta gamma C p : ℝ}
    (hm : 0 < m) (hgamma : 0 < gamma) (hC : 0 ≤ C) (hp : 0 < p) :
    ∀ᶠn : ℕ in atTop,∀d E v e:ℝ,
      0 < d → 0 < E → gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E →
      E ≤ d^2/Real.sqrt n → comparisonLowerScale n E d ≤ v →
      p*(n:ℝ)*E^2 ≤ e*v^2 →
      comparisonCap n delta (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (C*v)/
        ((n:ℝ)*e*v^4) ≤ ((2*(C+1)+(C+1)^2)/(p*gamma^3))*(n:ℝ)^(-(3*m-delta)) := by
  have ht := (tendsto_rpow_neg_atTop (by positivity : 0 < 3*m)).comp tendsto_natCast_atTop_atTop
  have ht0 := ht.const_mul (1/gamma^3)
  simp only [mul_zero] at ht0
  have hsmall := ht0.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hsmall,eventually_gt_atTop (0:ℕ)] with n hnsmall hn
  intro d E v e hd hE hlo hup hav hstrength
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn
  have ha : 0 < comparisonLowerScale n E d := by unfold comparisonLowerScale;positivity
  have hv : 0 < v := ha.trans_le hav
  have he : 0 < e := by nlinarith [mul_pos (mul_pos hp hN) (sq_pos_of_pos hE)]
  have hrat := comparison_star_cubic_ratio hN hgamma hd hE hlo
  have hsc := comparison_star_small_scale_ratios hN hd hE hup
  have hnsmall' : (1/gamma^3)*(n:ℝ)^(-3*m) ≤ 1 := by
    simpa only [Function.comp_def,show -(3*m)= -3*m by ring] using hnsmall
  have hrat1 : d^3/((n:ℝ)^2*E^3) ≤ 1 := hrat.trans hnsmall'
  have hUa : comparisonSmallMass n E ≤ comparisonLowerScale n E d :=
    (div_le_one ha).mp (hsc.1.trans hrat1)
  have hcap := comparison_star_cap_ratio_three_gains (delta:=delta) hN hd hE hC hUa hav
  have hr0 : 0 ≤ d^3/((n:ℝ)^2*E^3) := by positivity
  have hr2 : (d^3/((n:ℝ)^2*E^3))^2 ≤ d^3/((n:ℝ)^2*E^3) := by nlinarith
  have hsc2 : (comparisonSmallMass n E)^2*d^2/(comparisonLowerScale n E d)^4 ≤ d^3/((n:ℝ)^2*E^3) := by
    rw [hsc.2];exact hr2
  have hcost := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hsc.1 hsc2) (by positivity : 0 ≤ C+1))
      (le_rfl : (C+1)^2*(d^3/((n:ℝ)^2*E^3)) ≤ _)) (Real.rpow_nonneg hN.le delta)
  have hcap' : comparisonCap n delta (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (C*v)/(n*E*v)^2 ≤
      (n:ℝ)^delta*(2*(C+1)+(C+1)^2)*(d^3/((n:ℝ)^2*E^3)) := by
    apply hcap.trans
    convert hcost using 1 <;> ring
  have hcap0 : 0 ≤ comparisonCap n delta (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (C*v) :=
    comparisonCap_nonneg hN (by unfold comparisonSmallMass;positivity)
      (comparisonConstraintLength_pos hN hE hd) hE hd.le (mul_nonneg hC hv.le)
  have hden : p*(n*E*v)^2 ≤ (n:ℝ)*e*v^4 := by
    have hh := mul_le_mul_of_nonneg_left hstrength (by positivity : 0 ≤ (n:ℝ)*v^2)
    nlinarith
  have hstrengthCost := div_le_div_of_nonneg_left hcap0 (by positivity : 0 < p*(n*E*v)^2) hden
  have hupper := div_le_div_of_nonneg_right (hcap'.trans
    (mul_le_mul_of_nonneg_left hrat (by positivity : 0 ≤ (n:ℝ)^delta*(2*(C+1)+(C+1)^2)))) hp.le
  have heq : ((n:ℝ)^delta*(2*(C+1)+(C+1)^2)*((1/gamma^3)*(n:ℝ)^(-3*m)))/p=
      ((2*(C+1)+(C+1)^2)/(p*gamma^3))*(n:ℝ)^(-(3*m-delta)) := by
    rw [show -(3*m-delta)=delta+(-3*m) by ring,Real.rpow_add hN]
    ring
  exact hstrengthCost.trans (by simpa only [div_mul_eq_div_div,div_right_comm,heq] using hupper)

theorem eventually_comparison_star_actual_cap_saving {m delta gamma C : ℝ}
    (hm : 0 < m) (hdelta : 0 ≤ delta) (hgamma : 0 < gamma) (hC : 0 ≤ C) :
    ∀ᶠn : ℕ in atTop,∀d lam E x v:ℝ,
      0 < d → 0 < lam → lam ≤ d^2 → 0 < E →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt n →
      0 < x → (n:ℝ)^delta*Real.sqrt n*E/Real.sqrt lam ≤ x → x ≤ v →
      comparisonCap n delta (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (C*v)/
        ((n:ℝ)*laplaceComparisonStrength d lam v*v^4) ≤
      ((2*(C+1)+(C+1)^2)/gamma^3)*(n:ℝ)^(-(3*m-delta)) := by
  filter_upwards [eventually_comparison_star_cap_saving hm hgamma hC (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro d lam E x v hd hlam hld hE hlo hup hx hrange hxv
  have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hax := comparison_radius_target_above_lower_scale hN hdelta hd hlam hld hE hx hrange
  have hv := hx.trans_le hxv
  have hs := comparison_radius_target_strength_size hN hdelta hd hlam hld hE hup hv
    (by norm_num : (1:ℝ) ≤ 1) hv (by simp) (hrange.trans hxv)
  simp only [div_one] at hs
  have hstrength : (n:ℝ)*E^2 ≤ laplaceComparisonStrength d lam v*v^2 := by
    have hpow : 1 ≤ (n:ℝ)^delta := Real.one_le_rpow hN hdelta
    have hh := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (n:ℝ)*E^2)
    have hh' : (n:ℝ)*E^2 ≤ (n:ℝ)^delta*(n:ℝ)*E^2 := by simpa only [one_mul,mul_assoc] using hh
    simpa only [div_one] using hh'.trans hs
  simpa only [one_mul] using hn d E v (laplaceComparisonStrength d lam v) hd hE hlo hup (hax.trans hxv) (by simpa only [one_mul] using hstrength)

end OAI.SKFluctuations.LaplaceWindowFormalization
