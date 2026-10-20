module

public import ConcreteComparisonStrength
public import FiniteProfileRigidity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 2200000

def comparisonScaledStationarity (h p t s : ℝ) : ℝ :=
  h*((2-p)*t-2*(1-p)*s-p*s^2/t)

theorem comparison_gradient_scaled_exact (g alpha S B : ℝ→ℝ)
    {x t : ℝ} (hx : x≠0) (ht : t≠0) (hg : g (x*t)≠0) :
    radiusComparisonGradient g alpha S B (x*t)/x^3 =
      comparisonScaledStationarity (g (x*t)/x^2) (comparisonLogSlope g (x*t))
        t (S (alpha (x*t))/x) -
      (g (x*t)/x^2)*(comparisonLogSlope g (x*t))/t *
        ((B (alpha (x*t))-(S (alpha (x*t)))^2)/x^2) := by
  rw [comparison_gradient_slope (mul_ne_zero hx ht) hg]
  unfold comparisonScaledStationarity
  field_simp
  ring

theorem comparison_gradient_scaled_error_bound (g alpha S B : ℝ→ℝ)
    {x t a K : ℝ} (hx : 0<x) (ha : 0<a) (hat : a≤t)
    (hg : 0<g (x*t)) (hK : g (x*t)/x^2≤K)
    (hp : comparisonLogSlope g (x*t)∈Icc (0:ℝ) 1)
    (hB : (S (alpha (x*t)))^2≤B (alpha (x*t))) :
    |radiusComparisonGradient g alpha S B (x*t)/x^3-
      comparisonScaledStationarity (g (x*t)/x^2) (comparisonLogSlope g (x*t))
        t (S (alpha (x*t))/x)| ≤
      (K/a)*((B (alpha (x*t))-(S (alpha (x*t)))^2)/x^2) := by
  have ht := ha.trans_le hat
  have hh : 0≤g (x*t)/x^2 := div_nonneg hg.le (sq_nonneg _)
  have hK0 : 0≤K := hh.trans hK
  have hcoef : 0≤(g (x*t)/x^2)*comparisonLogSlope g (x*t)/t :=
    div_nonneg (mul_nonneg hh hp.1) ht.le
  have hcoefB : (g (x*t)/x^2)*comparisonLogSlope g (x*t)/t≤K/a := by
    calc
      _ ≤ (g (x*t)/x^2)/t := by
        exact div_le_div_of_nonneg_right (by nlinarith [hp.2]) ht.le
      _ ≤ K/t := div_le_div_of_nonneg_right hK ht.le
      _ ≤ K/a := div_le_div_of_nonneg_left hK0 ha hat
  have hD : 0≤(B (alpha (x*t))-(S (alpha (x*t)))^2)/x^2 := by positivity
  rw [comparison_gradient_scaled_exact g alpha S B hx.ne' ht.ne' hg.ne']
  rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg (mul_nonneg hcoef hD)]
  exact mul_le_mul_of_nonneg_right hcoefB hD

theorem laplace_gradient_scaled_error_bound (alpha S B : ℝ→ℝ)
    {d lam x t a K : ℝ} (hd : d≠0) (hlam : 0<lam)
    (hx : 0<x) (ha : 0<a) (hat : a≤t)
    (hK : laplaceComparisonStrength d lam (x*t)/x^2≤K)
    (hB : (S (alpha (x*t)))^2≤B (alpha (x*t))) :
    |radiusComparisonGradient (laplaceComparisonStrength d lam) alpha S B (x*t)/x^3-
      comparisonScaledStationarity (laplaceComparisonStrength d lam (x*t)/x^2)
        (comparisonLogSlope (laplaceComparisonStrength d lam) (x*t))
        t (S (alpha (x*t))/x)| ≤
      (K/a)*((B (alpha (x*t))-(S (alpha (x*t)))^2)/x^2) := by
  have hp := laplaceComparisonStrength_logSlope_mem hd hlam.ne' (x*t)
  exact comparison_gradient_scaled_error_bound _ alpha S B hx ha hat
    (laplaceComparisonStrength_pos d hlam _) hK ⟨hp.1,hp.2.le⟩ hB

theorem comparison_radius_rescaling_integral (D : ℝ→ℝ)
    {a b x : ℝ} (hab : a≤b) (hx : 0<x) :
    (∫t in Icc a b,D (x*t)/x^2) =
      (∫r in Icc (x*a) (x*b),D r)/x^3 := by
  have hscaled : x*a≤x*b := mul_le_mul_of_nonneg_left hab hx.le
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_div,intervalIntegral.integral_comp_mul_left D hx.ne',
    intervalIntegral.integral_of_le hscaled,←integral_Icc_eq_integral_Ioc,smul_eq_mul]
  field_simp

section Measure
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_density_L1_transfer (mu : Measure Ω)
    (F P L D : ℕ→Ω→ℝ) {C : ℝ} (_hC : 0≤C)
    (hFm : ∀n,AEStronglyMeasurable (F n) mu)
    (hPi : ∀n,Integrable (P n) mu) (hLi : ∀n,Integrable (L n) mu)
    (hDi : ∀n,Integrable (D n) mu)
    (_hD0 : ∀n,∀ᵐ t∂mu,0≤D n t)
    (herr : ∀n,∀ᵐ t∂mu,|F n t-P n t|≤C*D n t)
    (hP : Tendsto (fun n=>∫t,|P n t-L n t|∂mu) atTop (𝓝 0))
    (hD : Tendsto (fun n=>∫t,D n t∂mu) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t,|F n t-L n t|∂mu) atTop (𝓝 0) := by
  have hiFP n : Integrable (fun t=>F n t-P n t) mu := by
    apply ((hDi n).const_mul C).mono' ((hFm n).sub (hPi n).aestronglyMeasurable)
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using herr n
  have hiF n : Integrable (F n) mu := by
    convert (hiFP n).add (hPi n) using 1
    ext t; simp
  have hbound n : (∫t,|F n t-L n t|∂mu) ≤
      (∫t,|P n t-L n t|∂mu)+C*(∫t,D n t∂mu) := by
    have hh := integral_mono_ae ((hiF n).sub (hLi n)).abs
      (((hPi n).sub (hLi n)).abs.add ((hDi n).const_mul C)) (by
        filter_upwards [herr n] with t ht
        have htri := abs_add_le (F n t-P n t) (P n t-L n t)
        have he : F n t-P n t+(P n t-L n t)=F n t-L n t := by ring
        rw [he] at htri
        dsimp only [Pi.sub_apply,Pi.add_apply]
        linarith)
    dsimp only [Pi.add_apply] at hh
    rwa [integral_add ((hPi n).sub (hLi n)).abs ((hDi n).const_mul C),
      integral_const_mul] at hh
  have hlim : Tendsto (fun n=>(∫t,|P n t-L n t|∂mu)+C*(∫t,D n t∂mu))
      atTop (𝓝 0) := by simpa using hP.add (hD.const_mul C)
  exact squeeze_zero (fun n=>integral_nonneg (fun t=>abs_nonneg _)) hbound hlim

theorem comparison_density_dominated_L1 (mu : Measure Ω)
    (P : ℕ→Ω→ℝ) (L bound : Ω→ℝ)
    (hPm : ∀n,AEStronglyMeasurable (P n) mu)
    (hLm : AEStronglyMeasurable L mu) (hbi : Integrable bound mu)
    (hPb : ∀n,∀ᵐ t∂mu,|P n t|≤bound t)
    (hLb : ∀ᵐ t∂mu,|L t|≤bound t)
    (hlim : ∀ᵐ t∂mu,Tendsto (fun n=>P n t) atTop (𝓝 (L t))) :
    Tendsto (fun n=>∫t,|P n t-L t|∂mu) atTop (𝓝 0) := by
  have hpoint : ∀ᵐ t∂mu,Tendsto (fun n=>|P n t-L t|) atTop (𝓝 0) := by
    filter_upwards [hlim] with t ht
    simpa using (ht.sub_const (L t)).abs
  have hb n : ∀ᵐ t∂mu,‖|P n t-L t|‖≤2*bound t := by
    filter_upwards [hPb n,hLb] with t hp hl
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (by linarith)
  simpa only [integral_zero,Pi.sub_apply] using tendsto_integral_of_dominated_convergence
    (fun t=>2*bound t) (fun n=>continuous_abs.comp_aestronglyMeasurable ((hPm n).sub hLm)) (hbi.const_mul 2) hb hpoint
end Measure

theorem comparison_native_gradient_L1_tendsto
    (g alpha S B : ℕ→ℝ→ℝ) (x : ℕ→ℝ) (L : ℝ→ℝ)
    {a b K : ℝ} (ha : 0<a) (hab : a≤b) (hK : 0≤K)
    (hx : ∀n,0<x n)
    (hg : ∀n,∀t∈Icc a b,0<g n (x n*t))
    (hstrength : ∀n,∀t∈Icc a b,g n (x n*t)/(x n)^2≤K)
    (hp : ∀n,∀t∈Icc a b,comparisonLogSlope (g n) (x n*t)∈Icc (0:ℝ) 1)
    (hB : ∀n,∀t∈Icc a b,(S n (alpha n (x n*t)))^2≤B n (alpha n (x n*t)))
    (hGm : ∀n,AEStronglyMeasurable
      (fun t=>radiusComparisonGradient (g n) (alpha n) (S n) (B n) (x n*t)/(x n)^3)
      (volume.restrict (Icc a b)))
    (hPi : ∀n,IntegrableOn (fun t=>comparisonScaledStationarity
      (g n (x n*t)/(x n)^2) (comparisonLogSlope (g n) (x n*t))
      t (S n (alpha n (x n*t))/x n)) (Icc a b))
    (hLi : IntegrableOn L (Icc a b))
    (hDi : ∀n,IntegrableOn (fun t=>(B n (alpha n (x n*t))-
      (S n (alpha n (x n*t)))^2)/(x n)^2) (Icc a b))
    (hPlim : Tendsto (fun n=>∫t in Icc a b,|comparisonScaledStationarity
      (g n (x n*t)/(x n)^2) (comparisonLogSlope (g n) (x n*t))
      t (S n (alpha n (x n*t))/x n)-L t|) atTop (𝓝 0))
    (hDlim : Tendsto (fun n=>(∫r in Icc (x n*a) (x n*b),
      B n (alpha n r)-(S n (alpha n r))^2)/(x n)^3) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t in Icc a b,
      |radiusComparisonGradient (g n) (alpha n) (S n) (B n) (x n*t)/(x n)^3-L t|)
      atTop (𝓝 0) := by
  apply comparison_density_L1_transfer (volume.restrict (Icc a b)) _ _
    (fun _=>L) (fun n t=>(B n (alpha n (x n*t))-(S n (alpha n (x n*t)))^2)/(x n)^2)
    (div_nonneg hK ha.le) hGm hPi (fun _=>hLi) hDi
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg (sub_nonneg.mpr (hB n t ht)) (sq_nonneg _)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact comparison_gradient_scaled_error_bound _ _ _ _ (hx n) ha ht.1
      (hg n t ht) (hstrength n t ht) (hp n t ht) (hB n t ht)
  · exact hPlim
  · convert hDlim using 1
    ext n
    exact comparison_radius_rescaling_integral (fun r=>B n (alpha n r)-(S n (alpha n r))^2) hab (hx n)

def comparisonNativeScalarClock (h0 b0 e r s : ℝ) : ℝ := h0+e*r+(b0-e)*s

theorem comparison_scalar_clock_closure_exact
    (Gamma : ℝ→ℝ) {h0 b0 e r s T x : ℝ} (hT : T≠0) (hx : x≠0) :
    e*(s-r)/x^3 =
      T*((Gamma (comparisonNativeScalarClock h0 b0 e r s)-
        comparisonNativeScalarClock h0 b0 e r s/T)/x^3+
        (s-Gamma (comparisonNativeScalarClock h0 b0 e r s))/x^3)+
      ((b0-T)*s+h0)/x^3 := by
  unfold comparisonNativeScalarClock
  field_simp
  ring

theorem comparison_constant_strength_gradient_exact
    (Gamma alpha S B : ℝ→ℝ) {h0 b0 e r T x : ℝ}
    (hT : T≠0) (hx : x≠0) :
    radiusComparisonGradient (fun _=>e) alpha S B r/x^3 =
      -2*T*((Gamma (comparisonNativeScalarClock h0 b0 e r (S (alpha r)))-
        comparisonNativeScalarClock h0 b0 e r (S (alpha r))/T)/x^3+
        (S (alpha r)-Gamma (comparisonNativeScalarClock h0 b0 e r (S (alpha r))))/x^3)-
      2*((b0-T)*S (alpha r)+h0)/x^3 := by
  have he := comparison_scalar_clock_closure_exact Gamma
    (h0:=h0) (b0:=b0) (e:=e) (r:=r) (s:=S (alpha r)) hT hx
  simp only [radiusComparisonGradient,deriv_const,zero_mul,zero_add,zero_sub,add_zero]
  calc
    (-(2*e*S (alpha r))+2*e*r)/x^3 = -2*(e*(S (alpha r)-r)/x^3) := by ring
    _ = _ := by rw [he]; ring

theorem comparison_scaled_stationarity_bound {h p t s a b K : ℝ}
    (ha : 0<a) (ht : t∈Icc a b) (hh : h∈Icc (0:ℝ) K)
    (hp : p∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) K) :
    |comparisonScaledStationarity h p t s|≤K*(2*b+2*K+K^2/a) := by
  have ht0 := ha.trans_le ht.1
  have hK : 0≤K := hh.1.trans hh.2
  have hA : 0≤(2-p)*t := mul_nonneg (by linarith [hp.2]) ht0.le
  have hAb : (2-p)*t≤2*b := by nlinarith [mul_nonneg hp.1 ht0.le,ht.2]
  have hB : 0≤2*(1-p)*s := mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp.2)) hs.1
  have hBb : 2*(1-p)*s≤2*K := by nlinarith [mul_nonneg hp.1 hs.1,hs.2]
  have hC : 0≤p*s^2/t := div_nonneg (mul_nonneg hp.1 (sq_nonneg s)) ht0.le
  have hCb : p*s^2/t≤K^2/a := by
    calc
      _ ≤ s^2/t := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg s,hp.2]) ht0.le
      _ ≤ K^2/t := div_le_div_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 2) ht0.le
      _ ≤ K^2/a := div_le_div_of_nonneg_left (sq_nonneg K) ha ht.1
  have hbracket : |(2-p)*t-2*(1-p)*s-p*s^2/t|≤2*b+2*K+K^2/a := by
    apply (abs_le).mpr
    constructor <;> linarith
  unfold comparisonScaledStationarity
  rw [abs_mul,abs_of_nonneg hh.1]
  exact (mul_le_mul_of_nonneg_left hbracket hh.1).trans
    (mul_le_mul_of_nonneg_right hh.2 (by have hb := ht0.le.trans ht.2; positivity))

theorem comparison_scaled_stationarity_tendsto
    {h p s : ℕ→ℝ} {hl pl sl t : ℝ}
    (hh : Tendsto h atTop (𝓝 hl)) (hp : Tendsto p atTop (𝓝 pl))
    (hs : Tendsto s atTop (𝓝 sl)) :
    Tendsto (fun n=>comparisonScaledStationarity (h n) (p n) t (s n))
      atTop (𝓝 (comparisonScaledStationarity hl pl t sl)) := by
  unfold comparisonScaledStationarity
  exact hh.mul ((((tendsto_const_nhds.sub hp).mul_const t).sub
    (((tendsto_const_nhds.sub hp).const_mul 2).mul hs)).sub
    ((hp.mul (hs.pow 2)).div_const t))

theorem comparison_principal_density_L1_tendsto
    (h p s : ℕ→ℝ→ℝ) (hl pl sl : ℝ→ℝ)
    {a b K : ℝ} (ha : 0<a) (_hab : a≤b)
    (hhm : ∀n,Measurable (h n)) (hpm : ∀n,Measurable (p n))
    (hsm : ∀n,Measurable (s n))
    (hhlm : Measurable hl) (hplm : Measurable pl) (hslm : Measurable sl)
    (hh : ∀n,∀t∈Icc a b,h n t∈Icc (0:ℝ) K)
    (hp : ∀n,∀t∈Icc a b,p n t∈Icc (0:ℝ) 1)
    (hs : ∀n,∀t∈Icc a b,s n t∈Icc (0:ℝ) K)
    (hlim : ∀ᵐ t∂volume.restrict (Icc a b),
      Tendsto (fun n=>h n t) atTop (𝓝 (hl t)) ∧
      Tendsto (fun n=>p n t) atTop (𝓝 (pl t)) ∧
      Tendsto (fun n=>s n t) atTop (𝓝 (sl t))) :
    Tendsto (fun n=>∫t in Icc a b,
      |comparisonScaledStationarity (h n t) (p n t) t (s n t)-
        comparisonScaledStationarity (hl t) (pl t) t (sl t)|) atTop (𝓝 0) := by
  have hPm n : Measurable (fun t=>comparisonScaledStationarity (h n t) (p n t) t (s n t)) := by
    unfold comparisonScaledStationarity
    fun_prop
  have hLm : Measurable (fun t=>comparisonScaledStationarity (hl t) (pl t) t (sl t)) := by
    unfold comparisonScaledStationarity
    fun_prop
  apply comparison_density_dominated_L1 (volume.restrict (Icc a b)) _ _
    (fun _=>K*(2*b+2*K+K^2/a))
    (fun n=>(hPm n).aestronglyMeasurable) hLm.aestronglyMeasurable (integrable_const _)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact comparison_scaled_stationarity_bound ha ht (hh n t ht) (hp n t ht) (hs n t ht)
  · filter_upwards [hlim,ae_restrict_mem measurableSet_Icc] with t hlmt ht
    exact comparison_scaled_stationarity_bound ha ht
      (isClosed_Icc.mem_of_tendsto hlmt.1 (Eventually.of_forall (fun n=>hh n t ht)))
      (isClosed_Icc.mem_of_tendsto hlmt.2.1 (Eventually.of_forall (fun n=>hp n t ht)))
      (isClosed_Icc.mem_of_tendsto hlmt.2.2 (Eventually.of_forall (fun n=>hs n t ht)))
  · filter_upwards [hlim] with t ht
    exact comparison_scaled_stationarity_tendsto ht.1 ht.2.1 ht.2.2

end OAI.SKFluctuations.LaplaceWindowFormalization
