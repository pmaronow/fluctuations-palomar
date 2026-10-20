module

public import ChildStrengthZero
public import ComparisonStationarityDensityScaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 2000000

theorem comparison_zero_strength_bound_of_working
    {d lam x K : ℝ} (hd : 0<d) (hlam : 0≤lam) (hx : 0<x)
    (hld : lam≤d^2) (hK : 0≤K)
    (hwork : laplaceComparisonStrength d lam x/x^2≤K) :
    lam/x^2≤K+1 := by
  have hcube := laplaceComparisonStrength_zero_normalized_bound hd hlam hx hld
  have he0 : 0≤laplaceComparisonStrength d lam x/x^2 := by
    unfold laplaceComparisonStrength comparisonStrength
    exact div_nonneg (mul_nonneg hlam (laplaceComparisonShape_pos _).le) (sq_nonneg _)
  have hq0 : 0≤lam/x^2 := div_nonneg hlam (sq_nonneg _)
  have h2 := pow_le_pow_left₀ he0 hwork 2
  have h3 := pow_le_pow_left₀ he0 hwork 3
  by_contra hnot
  have hq : K+1<lam/x^2 := lt_of_not_ge hnot
  have hq3 : (K+1)^3<(lam/x^2)^3 := pow_lt_pow_left₀ hq (by positivity) (by norm_num)
  nlinarith [sq_nonneg K]

theorem comparison_strength_uniform_bound_of_working
    {d lam x K : ℝ} (hd : 0<d) (hlam : 0≤lam) (hx : 0<x)
    (hld : lam≤d^2) (hK : 0≤K)
    (hwork : laplaceComparisonStrength d lam x/x^2≤K) (r : ℝ) :
    0≤laplaceComparisonStrength d lam r/x^2 ∧
      laplaceComparisonStrength d lam r/x^2≤K+1 := by
  refine ⟨?_,?_⟩
  · unfold laplaceComparisonStrength comparisonStrength
    exact div_nonneg (mul_nonneg hlam (laplaceComparisonShape_pos _).le) (sq_nonneg _)
  · exact (div_le_div_of_nonneg_right (laplaceComparisonStrength_le d hlam r)
      (sq_nonneg x)).trans
      (comparison_zero_strength_bound_of_working hd hlam hx hld hK hwork)

theorem comparison_strength_flat_derivative {d lam r : ℝ}
    (harg : lam*r/d^3≤1) :
    HasDerivAt (laplaceComparisonStrength d lam) 0 r := by
  change HasDerivAt (comparisonStrength laplaceComparisonShape d lam) 0 r
  have hh := hasDerivAt_comparisonStrength
    (laplaceComparisonShape_hasDerivAt (lam*r/d^3)).differentiableAt
  rw [(laplaceComparisonShape_hasDerivAt (lam*r/d^3)).deriv] at hh
  simpa only [laplaceComparisonShapeDeriv,ite_eq_left harg,zero_mul,mul_zero] using hh

theorem comparison_strength_flat_band_criterion
    {d lam x b : ℝ} (hd : 0<d) (hlam : 0<lam) (hx : 0<x)
    (hb : 0<b) (hld : lam≤d^2)
    (hlarge : b^2<laplaceComparisonStrength d lam x/x^2) :
    ∀t∈Icc (0:ℝ) b,
      laplaceComparisonStrength d lam (x*t)=lam ∧
      comparisonLogSlope (laplaceComparisonStrength d lam) (x*t)=0 ∧
      HasDerivAt (laplaceComparisonStrength d lam) 0 (x*t) := by
  have hwork : b^2*x^2<laplaceComparisonStrength d lam x :=
    (lt_div_iff₀ (sq_pos_of_pos hx)).mp hlarge
  have hsq : (b*x)^2<d^2 := by
    have he := laplaceComparisonStrength_le d hlam.le x
    nlinarith
  have hbx : b*x<d := (sq_lt_sq₀ (mul_nonneg hb.le hx.le) hd.le).mp hsq
  intro t ht
  have hxt : x*t≤b*x := by nlinarith [ht.2]
  have hnum : lam*(x*t)<d^3 := by
    calc
      lam*(x*t) ≤ d^2*(b*x) := mul_le_mul hld hxt (mul_nonneg hx.le ht.1) (sq_nonneg d)
      _ < d^2*d := mul_lt_mul_of_pos_left hbx (sq_pos_of_pos hd)
      _ = d^3 := by ring
  have harg : lam*(x*t)/d^3≤1 := ((div_lt_one (pow_pos hd 3)).mpr hnum).le
  refine ⟨?_,?_,comparison_strength_flat_derivative harg⟩
  · simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape,harg]
  · rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    simp [laplaceComparisonSlope,harg]

theorem comparison_strength_eventually_flat_of_divergence
    (d lam x : ℕ→ℝ)
    (hdata : ∀ᶠ n in atTop,0<d n ∧ 0<lam n ∧ 0<x n ∧ lam n≤(d n)^2)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)
      atTop atTop) {b : ℝ} (hb : 0<b) :
    ∀ᶠ n in atTop,∀t∈Icc (0:ℝ) b,
      laplaceComparisonStrength (d n) (lam n) (x n*t)=lam n ∧
      comparisonLogSlope (laplaceComparisonStrength (d n) (lam n)) (x n*t)=0 ∧
      HasDerivAt (laplaceComparisonStrength (d n) (lam n)) 0 (x n*t) := by
  filter_upwards [hdata,hlarge.eventually_gt_atTop (b^2)] with n hn hl
  exact comparison_strength_flat_band_criterion hn.1 hn.2.1 hn.2.2.1 hb hn.2.2.2 hl

theorem comparison_flat_native_gradient (alpha S B : ℝ→ℝ)
    {d lam r : ℝ} (hflat : laplaceComparisonStrength d lam r=lam)
    (hderiv : HasDerivAt (laplaceComparisonStrength d lam) 0 r) :
    radiusComparisonGradient (laplaceComparisonStrength d lam) alpha S B r =
      radiusComparisonGradient (fun _=>lam) alpha S B r := by
  simp only [radiusComparisonGradient,hflat,hderiv.deriv,deriv_const]

theorem comparison_high_strength_native_closure_eventually
    (d lam x : ℕ→ℝ) (Gamma alpha S B h0 b0 : ℕ→ℝ→ℝ)
    {T b : ℝ} (hT : T≠0) (hb : 0<b)
    (hdata : ∀ᶠ n in atTop,0<d n ∧ 0<lam n ∧ 0<x n ∧ lam n≤(d n)^2)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)
      atTop atTop) :
    ∀ᶠ n in atTop,∀t∈Icc (0:ℝ) b,
      radiusComparisonGradient (laplaceComparisonStrength (d n) (lam n))
        (alpha n) (S n) (B n) (x n*t)/(x n)^3 =
      -2*T*((Gamma n (comparisonNativeScalarClock (h0 n t) (b0 n t) (lam n)
        (x n*t) (S n (alpha n (x n*t))))-
        comparisonNativeScalarClock (h0 n t) (b0 n t) (lam n)
          (x n*t) (S n (alpha n (x n*t)))/T)/(x n)^3+
        (S n (alpha n (x n*t))-Gamma n (comparisonNativeScalarClock (h0 n t)
          (b0 n t) (lam n) (x n*t) (S n (alpha n (x n*t)))))/(x n)^3)-
      2*((b0 n t-T)*S n (alpha n (x n*t))+h0 n t)/(x n)^3 := by
  filter_upwards [hdata,comparison_strength_eventually_flat_of_divergence d lam x hdata hlarge hb]
    with n hn hf
  intro t ht
  rw [comparison_flat_native_gradient (alpha n) (S n) (B n) (hf t ht).1 (hf t ht).2.2]
  exact comparison_constant_strength_gradient_exact _ _ _ _ hT hn.2.2.1.ne'

theorem comparison_scaled_strength_lower_on_band
    {d lam x b c : ℝ} (hd : d≠0) (hlam : 0<lam) (hx : 0<x)
    (hb : 1≤b) (hxb : x*b≤1)
    (hwork : c≤laplaceComparisonStrength d lam x/x^2) :
    ∀t∈Icc (0:ℝ) b,c/b≤laplaceComparisonStrength d lam (x*t)/x^2 := by
  have hb0 : 0<b := zero_lt_one.trans_le hb
  have hx1 : x≤1 := (by nlinarith [mul_le_mul_of_nonneg_left hb hx.le] : x≤x*b).trans hxb
  have hmono := laplaceComparisonStrength_monotonicities hd hlam (r₀:=0) le_rfl
  intro t ht
  have hxt : x*t∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hx.le ht.1,(mul_le_mul_of_nonneg_left ht.2 hx.le).trans hxb⟩
  have he0 := (laplaceComparisonStrength_pos d hlam (x*t)).le
  have hcmp : laplaceComparisonStrength d lam x≤b*laplaceComparisonStrength d lam (x*t) := by
    by_cases ht1 : t≤1
    · have hxe : x*t≤x := by nlinarith
      have he := hmono.1 hxt ⟨hx.le,hx1⟩ hxe
      have hbmul := mul_le_mul_of_nonneg_right hb he0
      exact he.trans (by simpa only [one_mul] using hbmul)
    · have hxe : x≤x*t := by nlinarith [lt_of_not_ge ht1]
      have he := hmono.2 ⟨hx.le,hx1⟩ hxt hxe
      have he' : laplaceComparisonStrength d lam x≤t*laplaceComparisonStrength d lam (x*t) := by
        apply (mul_le_mul_iff_left₀ hx).mp
        nlinarith [he]
      exact he'.trans (mul_le_mul_of_nonneg_right ht.2 he0)
  apply (div_le_div_iff₀ hb0 (sq_pos_of_pos hx)).mpr
  have hw := (le_div_iff₀ (sq_pos_of_pos hx)).mp hwork
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
