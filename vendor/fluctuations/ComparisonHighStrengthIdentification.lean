module

public import ComparisonScalarClosureIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 2300000

theorem comparison_scalar_product_exact (Gamma : ℝ→ℝ)
    {h0 b0 e s T x t : ℝ} (hT : T≠0) (hx : x≠0) :
    (e/x^2)*(s/x-t) =
      T*(comparisonRescaledScalarResponse Gamma T x
        (comparisonNativeScalarClock h0 b0 e (x*t) s/(T*x))+
        (s-Gamma (comparisonNativeScalarClock h0 b0 e (x*t) s))/x^3)+
      ((b0-T)*s+h0)/x^3 := by
  have he := comparison_scalar_response_closure_exact Gamma
    (h0:=h0) (b0:=b0) (e:=e) (s:=s) (t:=t) hT hx
  have hh := congrArg (fun y:ℝ=>T*y) he
  convert hh using 1 <;> field_simp

theorem comparison_scalar_product_bound (Gamma : ℝ→ℝ)
    {h0 b0 e s T x t CG CR CZ : ℝ} (hT : T≠0) (hx : x≠0)
    (hG : |comparisonRescaledScalarResponse Gamma T x
      (comparisonNativeScalarClock h0 b0 e (x*t) s/(T*x))|≤CG)
    (hR : |(s-Gamma (comparisonNativeScalarClock h0 b0 e (x*t) s))/x^3|≤CR)
    (hZ : |((b0-T)*s+h0)/x^3|≤CZ) :
    |(e/x^2)*(s/x-t)|≤|T| *(CG+CR)+CZ := by
  rw [comparison_scalar_product_exact Gamma hT hx]
  calc
    _ ≤ |T*(comparisonRescaledScalarResponse Gamma T x
        (comparisonNativeScalarClock h0 b0 e (x*t) s/(T*x))+
        (s-Gamma (comparisonNativeScalarClock h0 b0 e (x*t) s))/x^3)|+
        |((b0-T)*s+h0)/x^3| := abs_add_le _ _
    _ ≤ |T| *(CG+CR)+CZ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((abs_add_le _ _).trans (add_le_add hG hR)) (abs_nonneg T)) hZ

theorem comparison_large_strength_spin_tendsto (e s x : ℕ→ℝ)
    {t C : ℝ}
    (hlarge : Tendsto (fun n=>e n/(x n)^2) atTop atTop)
    (hbudget : ∀ᶠ n in atTop,|(e n/(x n)^2)*(s n/x n-t)|≤C) :
    Tendsto (fun n=>s n/x n) atTop (𝓝 t) := by
  have hp := bdd_le_mul_tendsto_zero' C hbudget hlarge.inv_tendsto_atTop
  have hm : Tendsto (fun n=>s n/x n-t) atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [hlarge.eventually_gt_atTop 0] with n hn
    have he : e n/(x n)^2≠0 := hn.ne'
    change ((e n/(x n)^2)*(s n/x n-t))*(e n/(x n)^2)⁻¹=s n/x n-t
    rw [mul_right_comm,mul_inv_cancel₀ he,one_mul]
  simpa only [sub_add_cancel,zero_add] using hm.add_const t

theorem comparison_large_strength_clock_tendsto (h0 b0 e s x : ℕ→ℝ)
    {T t C : ℝ} (hT : T≠0) (hx0 : ∀n,x n≠0) (hx : Tendsto x atTop (𝓝 0))
    (hlarge : Tendsto (fun n=>e n/(x n)^2) atTop atTop)
    (hbudget : ∀ᶠ n in atTop,|(e n/(x n)^2)*(s n/x n-t)|≤C)
    (hb : Tendsto (fun n=>(b0 n-T)/(x n)^2) atTop (𝓝 0))
    (hh : Tendsto (fun n=>h0 n/(x n)^3) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n))
      atTop (𝓝 t) := by
  have hs := comparison_large_strength_spin_tendsto e s x hlarge hbudget
  have hz := comparison_scalar_bare_remainder_tendsto h0 b0 s x hx0 hs hb hh
  have hx2 : Tendsto (fun n=>(x n)^2/T) atTop (𝓝 0) := by
    simpa using (hx.pow 2).div_const T
  have hprod := bdd_le_mul_tendsto_zero' C hbudget hx2
  have hcorr : Tendsto (fun n=>(x n)^2/T*((e n/(x n)^2)*(s n/x n-t)-
      ((b0 n-T)*s n+h0 n)/(x n)^3)) atTop (𝓝 0) := by
    convert hprod.sub (hx2.mul hz) using 1
    · ext n;ring
    · simp
  have hfinal := hs.sub hcorr
  convert hfinal using 1
  · ext n
    exact comparison_scalar_clock_scaled_exact hT (hx0 n)
  · simp

theorem comparison_high_strength_clock_and_response_tendsto
    (Gamma : ℕ→ℝ→ℝ) (h0 b0 e s x : ℕ→ℝ) (g : ℝ→ℝ)
    {T t CG CR CZ : ℝ} {A : Set ℝ}
    (hT : T≠0) (hx0 : ∀n,x n≠0) (hx : Tendsto x atTop (𝓝 0))
    (hlarge : Tendsto (fun n=>e n/(x n)^2) atTop atTop)
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g atTop A)
    (hgc : ContinuousWithinAt g A t)
    (hKA : ∀ᶠ n in atTop,comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n)∈A)
    (hbound : ∀ᶠ n in atTop,
      |comparisonRescaledScalarResponse (Gamma n) T (x n)
        (comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n))|≤CG ∧
      |(s n-Gamma n (comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)))/(x n)^3|≤CR ∧
      |((b0 n-T)*s n+h0 n)/(x n)^3|≤CZ)
    (hb : Tendsto (fun n=>(b0 n-T)/(x n)^2) atTop (𝓝 0))
    (hh : Tendsto (fun n=>h0 n/(x n)^3) atTop (𝓝 0)) :
    Tendsto (fun n=>s n/x n) atTop (𝓝 t) ∧
    Tendsto (fun n=>comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n))
      atTop (𝓝 t) ∧
    Tendsto (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)
      (comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n)))
      atTop (𝓝 (g t)) := by
  have hbudget : ∀ᶠ n in atTop,|(e n/(x n)^2)*(s n/x n-t)|≤|T| *(CG+CR)+CZ := by
    filter_upwards [hbound] with n hn
    exact comparison_scalar_product_bound (Gamma n) hT (hx0 n) hn.1 hn.2.1 hn.2.2
  have hs := comparison_large_strength_spin_tendsto e s x hlarge hbudget
  have hk := comparison_large_strength_clock_tendsto h0 b0 e s x hT hx0 hx hlarge hbudget hb hh
  exact ⟨hs,hk,hG.tendsto_comp hgc (tendsto_nhdsWithin_iff.mpr ⟨hk,hKA⟩)⟩

theorem comparison_radius_cubic_residual_rescaling (E : ℝ→ℝ)
    {a b x : ℝ} (hab : a≤b) (hx : 0<x) :
    (∫t in Icc a b,|E (x*t)/x^3|)=(∫r in Icc (x*a) (x*b),|E r|)/x^4 := by
  simp_rw [abs_div,abs_of_pos (pow_pos hx 3)]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_div,intervalIntegral.integral_comp_mul_left (fun r=>|E r|) hx.ne',
    intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le),
    ←integral_Icc_eq_integral_Ioc,smul_eq_mul]
  field_simp

end OAI.SKFluctuations.LaplaceWindowFormalization
