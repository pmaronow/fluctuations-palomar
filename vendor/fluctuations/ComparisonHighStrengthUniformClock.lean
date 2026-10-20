module

public import ComparisonHighStrengthDensityLimit
public import ComparisonScalarFloorCharge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 4000000

theorem comparison_uniform_of_abs_error_bound
    (F : ℕ→ℝ→ℝ) (f : ℝ→ℝ) (A : Set ℝ) (rate : ℕ→ℝ)
    (hr : Tendsto rate atTop (𝓝 0))
    (hbound : ∀ᶠn in atTop,∀t∈A,|F n t-f t| ≤ rate n) :
    TendstoUniformlyOn F f atTop A := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [hbound,hr.eventually (gt_mem_nhds heps)] with n hn hnr t ht
  simpa only [Real.dist_eq,abs_sub_comm] using (hn t ht).trans_lt hnr

theorem comparison_large_strength_uniform_spin_clock
    (h0 b0 s : ℕ→ℝ→ℝ) (e x : ℕ→ℝ) {T C : ℝ} {A : Set ℝ}
    (hT : 0 < T) (hx : ∀n,0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    (_hC : 0 ≤ C)
    (hlarge : Tendsto (fun n=>e n/(x n)^2) atTop atTop)
    (hbudget : ∀ᶠn in atTop,∀t∈A,|(e n/(x n)^2)*(s n t/x n-t)| ≤ C)
    (hz : TendstoUniformlyOn
      (fun n t=>((b0 n t-T)*s n t+h0 n t)/(x n)^3) (fun _=>0) atTop A) :
    TendstoUniformlyOn (fun n t=>s n t/x n) (fun t=>t) atTop A ∧
    TendstoUniformlyOn (fun n t=>comparisonNativeScalarClock (h0 n t) (b0 n t)
      (e n) (x n*t) (s n t)/(T*x n)) (fun t=>t) atTop A := by
  have Hr : Tendsto (fun n=>C/(e n/(x n)^2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using hlarge.inv_tendsto_atTop.const_mul C
  have Hspin : ∀ᶠn in atTop,∀t∈A,|s n t/x n-t| ≤ C/(e n/(x n)^2) := by
    filter_upwards [hbudget,hlarge.eventually_gt_atTop 0] with n hn hne t ht
    apply (le_div_iff₀ hne).mpr
    have H := hn t ht
    rw [abs_mul,abs_of_pos hne] at H
    simpa only [mul_comm] using H
  refine ⟨comparison_uniform_of_abs_error_bound _ _ _ _ Hr Hspin,?_⟩
  have Hrate : Tendsto (fun n=>C/(e n/(x n)^2)+(x n)^2/T*(C+1)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),zero_div,zero_mul,add_zero] using
      Hr.add (((hxlim.pow 2).div_const T).mul_const (C+1))
  apply comparison_uniform_of_abs_error_bound _ _ _ _ Hrate
  filter_upwards [Hspin,hbudget,(Metric.tendstoUniformlyOn_iff.mp hz) 1 (by norm_num)]
    with n hn hp hnz t ht
  have hz1 : |((b0 n t-T)*s n t+h0 n t)/(x n)^3| ≤ 1 := by
    simpa only [Real.dist_eq,sub_zero,zero_sub,abs_neg] using (hnz t ht).le
  rw [comparison_scalar_clock_scaled_exact hT.ne' (hx n).ne']
  have H := abs_sub (s n t/x n-t)
    ((x n)^2/T*((e n/(x n)^2)*(s n t/x n-t)-((b0 n t-T)*s n t+h0 n t)/(x n)^3))
  have Hinner := (abs_sub ((e n/(x n)^2)*(s n t/x n-t))
    (((b0 n t-T)*s n t+h0 n t)/(x n)^3)).trans (add_le_add (hp t ht) hz1)
  rw [abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg _) hT.le)] at H
  have Hmul := mul_le_mul_of_nonneg_left Hinner (div_nonneg (sq_nonneg (x n)) hT.le)
  have Heq : s n t/x n-(x n)^2/T*
      ((e n/(x n)^2)*(s n t/x n-t)-((b0 n t-T)*s n t+h0 n t)/(x n)^3)-t =
      (s n t/x n-t)-(x n)^2/T*
      ((e n/(x n)^2)*(s n t/x n-t)-((b0 n t-T)*s n t+h0 n t)/(x n)^3) := by ring
  rw [Heq]
  exact H.trans (add_le_add (hn t ht) Hmul)

theorem comparison_uniform_response_at_moving_clock
    (G : ℕ→ℝ→ℝ) (g : ℝ→ℝ) (q : ℕ→ℝ→ℝ) {Q : ℝ} {A : Set ℝ}
    (hA : A ⊆ Icc (0:ℝ) Q)
    (hG : TendstoUniformlyOn G g atTop (Icc (0:ℝ) Q))
    (hg : ContinuousOn g (Icc (0:ℝ) Q))
    (hq : TendstoUniformlyOn q (fun t=>t) atTop A)
    (hmem : ∀ᶠn in atTop,∀t∈A,q n t∈Icc (0:ℝ) Q) :
    TendstoUniformlyOn (fun n t=>G n (q n t)) g atTop A := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  obtain ⟨d,hd,Hd⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) (eps/2) (by positivity)
  filter_upwards [hmem,(Metric.tendstoUniformlyOn_iff.mp hG) (eps/2) (by positivity),
    (Metric.tendstoUniformlyOn_iff.mp hq) d hd] with n hm hn hqn t ht
  have H1 := hn (q n t) (hm t ht)
  have H2 := Hd t (hA ht) (q n t) (hm t ht) (hqn t ht)
  calc
    dist (g t) (G n (q n t)) ≤ dist (g t) (g (q n t))+dist (g (q n t)) (G n (q n t)) :=
      dist_triangle _ _ _
    _ < eps/2+eps/2 := add_lt_add H2 H1
    _ = eps := by ring

theorem comparison_uniform_abs_integral_tendsto_zero
    (F : ℕ→ℝ→ℝ) (f : ℝ→ℝ) {a b : ℝ}
    (hF : TendstoUniformlyOn F f atTop (Icc a b)) :
    Tendsto (fun n=>∫t in Icc a b,|F n t-f t|) atTop (𝓝 0) := by
  let mu := volume.restrict (Icc a b)
  have : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  apply tendsto_order.2
  refine ⟨fun l hl=>Eventually.of_forall (fun _=>hl.trans_le (integral_nonneg (fun _=>abs_nonneg _))),?_⟩
  intro u hu
  let eps := u/(mu.real univ+1)
  have hm : 0 ≤ mu.real univ := measureReal_nonneg
  have heps : 0 < eps := by dsimp only [eps];positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) eps heps] with n hn
  have H : (∫t,|F n t-f t|∂mu) ≤ mu.real univ*eps := by
    calc
      _ ≤ ∫_t,eps∂mu := integral_mono_of_nonneg
        (Eventually.of_forall (fun _=>abs_nonneg _)) (integrable_const eps) (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          simpa only [Real.dist_eq,abs_sub_comm] using (hn t ht).le)
      _ = _ := by rw [integral_const,smul_eq_mul]
  apply H.trans_lt
  dsimp only [eps]
  rw [←mul_div_assoc]
  exact (div_lt_iff₀ (by positivity : 0 < mu.real univ+1)).mpr (by nlinarith)

theorem comparison_scalar_density_eventual_L1_tendsto
    (F P rho zeta : ℕ→ℝ→ℝ) (g : ℝ→ℝ) (T a b : ℝ)
    (hFi : ∀ᶠn in atTop,IntegrableOn (F n) (Icc a b))
    (hPi : ∀n,IntegrableOn (P n) (Icc a b))
    (hri : ∀n,IntegrableOn (rho n) (Icc a b))
    (hzi : ∀n,IntegrableOn (zeta n) (Icc a b))
    (hgi : IntegrableOn g (Icc a b))
    (heq : ∀ᶠn in atTop,∀t∈Icc a b,F n t=-2*T*(P n t+rho n t)-2*zeta n t)
    (hP : TendstoUniformlyOn P g atTop (Icc a b))
    (hr : Tendsto (fun n=>∫t in Icc a b,|rho n t|) atTop (𝓝 0))
    (hz : TendstoUniformlyOn zeta (fun _=>0) atTop (Icc a b)) :
    Tendsto (fun n=>∫t in Icc a b,|F n t-(-2*T*g t)|) atTop (𝓝 0) := by
  have hPL1 := comparison_uniform_abs_integral_tendsto_zero P g hP
  have hzL1 : Tendsto (fun n=>∫t in Icc a b,|zeta n t|) atTop (𝓝 0) := by
    simpa only [sub_zero] using comparison_uniform_abs_integral_tendsto_zero zeta (fun _=>0) hz
  have Hbound : ∀ᶠn in atTop,(∫t in Icc a b,|F n t-(-2*T*g t)|) ≤
      2*|T| *(∫t in Icc a b,|P n t-g t|)+2*|T| *(∫t in Icc a b,|rho n t|)+
        2*(∫t in Icc a b,|zeta n t|) := by
    filter_upwards [hFi,heq] with n hfin hn
    have hi1 := ((hPi n).sub hgi).abs.const_mul (2*|T|)
    have hi2 := (hri n).abs.const_mul (2*|T|)
    have hi3 := (hzi n).abs.const_mul 2
    have H := integral_mono_ae (hfin.sub (hgi.const_mul (-2*T))).abs
      ((hi1.add hi2).add hi3) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact comparison_scalar_density_error_bound (hn t ht))
    have hadd1 := integral_add (hi1.add hi2) hi3
    have hadd2 := integral_add hi1 hi2
    simp only [Pi.add_apply,Pi.sub_apply] at hadd1 hadd2 H
    rw [hadd1,hadd2,integral_const_mul,integral_const_mul,integral_const_mul] at H
    exact H
  have Hlim : Tendsto (fun n=>2*|T| *(∫t in Icc a b,|P n t-g t|)+
      2*|T| *(∫t in Icc a b,|rho n t|)+2*(∫t in Icc a b,|zeta n t|)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using ((hPL1.const_mul (2*|T|)).add
      (hr.const_mul (2*|T|))).add (hzL1.const_mul 2)
  exact squeeze_zero' (Eventually.of_forall (fun _=>integral_nonneg (fun _=>abs_nonneg _))) Hbound Hlim

end OAI.SKFluctuations.LaplaceWindowFormalization
