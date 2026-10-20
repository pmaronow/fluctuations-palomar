module

public import SelectivePropagationWorkingTransfer
public import ComparisonNativeSuccessfulChildBarrier
public import ComparisonQuantileLinearLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 4000000

theorem comparison_native_upward_disagreement_selects_barrier_band
    {n : ℕ} {delta : ℝ} (a : NativeChildBarrierCall n delta)
    (J : ℕ) {leftBand rightBand step L q : ℝ}
    (ha : 0 ≤ leftBand) (hb : rightBand ≤ 1) (hstep : 0 < step)
    (hRupper : ∀ u ∈ Icc leftBand rightBand,
      4*a.R u ≤ (J : ℝ)*step) (hq : 0 ≤ q)
    (hwidth : q*((J : ℝ)+1)*step/2 ≤ L)
    (hbadmass : (J+1 : ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u ∈ Icc leftBand rightBand ∧ 3*step ≤ a.Z u-4*a.R u}) :
    ∃ y start stop finish : ℝ,
      0 < y ∧ y ≤ 1/4 ∧ step/4 ≤ y ∧ y ≤ ((J : ℝ)+1)*step/4 ∧
      start ∈ Icc leftBand rightBand ∧ finish ∈ Icc leftBand rightBand ∧
      0 ≤ start ∧ start < stop ∧ stop ≤ finish ∧ finish ≤ 1 ∧
      L < 2*(stop-start) ∧ q*y ≤ finish-stop ∧ 4*y ≤ a.Z start ∧
      (∀ u ∈ Icc stop finish, a.R u ≤ y) :=
  selective_propagation_upward_disagreement_selects_barrier_band a.R a.Z
    (comparisonSweepQuantile_monotone a.context.hc a.context.hk a.context.hkc
      a.context.hm a.context.hM a.alpha)
    (comparisonSweepQuantile_continuous a.context.hc a.context.hk a.context.hkc
      a.context.hm a.context.hM a.alpha)
    a.hZm a.hZc a.hZb J ha hb hstep
    (fun u hu => ⟨(comparisonSweepQuantile_bounds a.context.hc a.context.hk
      a.context.hkc a.context.hm a.context.hM a.alpha u).1,hRupper u hu⟩)
    hq hwidth hbadmass

theorem comparison_native_upward_disagreement_mass_le
    {n : ℕ} {delta : ℝ} (a : NativeChildBarrierCall n delta)
    (J : ℕ) {leftBand rightBand step L q cMove : ℝ}
    (ha : 0 ≤ leftBand) (hb : rightBand ≤ 1) (hstep : 0 < step)
    (hcMove : 0 < cMove) (hcMove1 : cMove ≤ 1) (hq : 0 < q)
    (hRupper : ∀ u ∈ Icc leftBand rightBand, 4*a.R u ≤ (J : ℝ)*step)
    (hwidth : q*((J : ℝ)+1)*step/2 ≤ L)
    (hymax1 : ((J : ℝ)+1)*step/4 ≤ 1)
    (hforce : inverseCapPrimitive a.context.M 1 ≤ step/16)
    (hspeed : (a.context.M 0)⁻¹+((J : ℝ)+1)*step/L ≤
      ((n : ℝ)^(2*delta)*a.context.U)^2/((n : ℝ)^delta*a.context.U^2))
    (hroute : cMove*(((J : ℝ)+1)*step/4) ≤ a.R leftBand ∨
      a.e 0 ≤ a.D (((J : ℝ)+1)*step/4))
    (herror : 4*a.err < (3*cMove*q/100)*
      min (a.e (((J : ℝ)+1)*step/4)) (a.D (((J : ℝ)+1)*step/4))*(step/4)^3) :
    volume {u | u ∈ Icc leftBand rightBand ∧ 3*step ≤ a.Z u-4*a.R u} ≤
      (J+1 : ℝ≥0∞)*ENNReal.ofReal L := by
  by_contra hlarge
  have hbadmass := lt_of_not_ge hlarge
  obtain ⟨y,start,stop,finish,hy,hy4,hylo,hymax,hstart,hfinish,hstart0,
      hstartstop,hstopfinish,hfinish1,hrampLength,hbandWidth,hZlarge,hRband⟩ :=
    comparison_native_upward_disagreement_selects_barrier_band a J ha hb hstep
      hRupper hq.le hwidth hbadmass
  let ymax : ℝ := ((J : ℝ)+1)*step/4
  have hymax0 : 0 < ymax := by dsimp [ymax]; positivity
  have hL : 0 < L := (by positivity : 0 < q*((J : ℝ)+1)*step/2).trans_le hwidth
  have hforceY : inverseCapPrimitive a.context.M 1 ≤ y/4 := by linarith
  have hspeedBound : 2*y/(stop-start) ≤ ((J : ℝ)+1)*step/L := by
    have hh := selective_propagation_reserved_ramp_speed_bound hL hy.le hymax hrampLength
    convert hh using 1 <;> ring
  have hspeedY : (a.context.M 0)⁻¹+2*y/(stop-start) ≤
      ((n : ℝ)^(2*delta)*a.context.U)^2/((n : ℝ)^delta*a.context.U^2) := by
    linarith [hspeedBound,hspeed]
  have hRm : Monotone a.R := comparisonSweepQuantile_monotone
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
  have hantiE := (laplaceComparisonStrength_monotonicities_nonneg
    a.context.hd.ne' a.hlam.le).1
  have hantiD := (laplaceComparisonStrength_monotonicities_nonneg
    a.hchildRadius a.hchildLam.le).1
  have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨hy.le,by linarith⟩
  have hymaxI : ymax ∈ Icc (0 : ℝ) 1 := ⟨hymax0.le,hymax1⟩
  have heSaving : a.e ymax ≤ a.e y := hantiE hyI hymaxI hymax
  have hDSaving : a.D ymax ≤ a.D y := hantiD hyI hymaxI hymax
  have hrouteY : (∀ u ∈ Icc start 1,cMove*y ≤ a.R u) ∨ a.e 0 ≤ a.D y := by
    rcases hroute with houter | hsmall
    · left
      intro u hu
      exact (mul_le_mul_of_nonneg_left hymax hcMove.le).trans
        (houter.trans (hRm (hstart.1.trans hu.1)))
    · right
      exact hsmall.trans hDSaving
  have hgain := comparison_native_upward_successful_child_error_lower a hcMove hcMove1
    hy hstart0 hstartstop hstopfinish hfinish1 hq.le hbandWidth hforceY hspeedY
    hZlarge hrouteY hRband
  have hmin : min (a.e ymax) (a.D ymax) ≤ min (a.e y) (a.D y) :=
    min_le_min heSaving hDSaving
  have hmin0 : 0 ≤ min (a.e y) (a.D y) := le_min
    (laplaceComparisonStrength_nonneg a.context.d y a.hlam.le)
    (laplaceComparisonStrength_nonneg a.childRadius y a.hchildLam.le)
  have hpower : (step/4)^3 ≤ y^3 := pow_le_pow_left₀ (by positivity) hylo 3
  have hproduct : min (a.e ymax) (a.D ymax)*(step/4)^3 ≤
      min (a.e y) (a.D y)*y^3 :=
    mul_le_mul hmin hpower (by positivity) hmin0
  have hgainUniform : (3*cMove*q/100)*min (a.e ymax) (a.D ymax)*(step/4)^3 ≤
      (3*cMove*q/100)*min (a.e y) (a.D y)*y^3 := by
    have hh := mul_le_mul_of_nonneg_left hproduct
      (by positivity : 0 ≤ 3*cMove*q/100)
    convert hh using 1 <;> ring
  exact not_lt_of_ge (hgainUniform.trans hgain) herror

theorem selective_propagation_transfer_working_child_locally_uniform
    (R Z : ℕ → ℝ → ℝ) (x : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hx : ∀ n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hR : ∀ n, MonotoneOn (R n) (Icc (0 : ℝ) 1))
    (hZ : ∀ n, MonotoneOn (Z n) (Icc (0 : ℝ) 1))
    (hchild : ∀ v : ℝ, 0 < v → Tendsto (fun n => Z n (x n*v)/x n)
      atTop (𝓝 (kappa*v)))
    (hagreement : ∀ a b eps theta : ℝ, 0 < a → a < b → 0 < eps → 0 < theta →
      ∀ᶠ n in atTop, volume (physicalPropagationDisagreementMassSet (R n) (Z n)
        (x n*a) (x n*b) (eps*x n)) < ENNReal.ofReal (theta*x n)) :
    TendstoLocallyUniformlyOn (fun n v => R n (x n*v)/x n)
      (fun v => kappa*v) atTop (Ioi (0 : ℝ)) := by
  have hparent := selective_propagation_transfer_working_child_linear_profile
    R Z x hkappa hx hx0 hR hZ hchild hagreement
  have hlimit : ∀ v > 0, Tendsto (fun n => R n (x n*v)/x n)
      atTop (𝓝 (v/kappa⁻¹)) := by
    intro v hv
    simpa only [div_inv_eq_mul,mul_comm] using hparent v hv
  have hresult := comparison_eventually_monotone_linear_limit_locally_uniform
    (fun n v => R n (x n*v)/x n) (inv_pos.mpr hkappa) ?_ hlimit
  · simpa only [div_inv_eq_mul,mul_comm] using hresult
  · intro radius hradius
    have ht : Tendsto (fun n => x n*radius) atTop (𝓝 0) := by
      simpa using hx0.mul_const radius
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    intro u hu v hv huv
    have hb w (hw : w ∈ Icc (0 : ℝ) radius) : x n*w ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg (hx n).le hw.1,
        (mul_le_mul_of_nonneg_left hw.2 (hx n).le).trans hn.le⟩
    exact div_le_div_of_nonneg_right
      (hR n (hb u hu) (hb v hv) (mul_le_mul_of_nonneg_left huv (hx n).le)) (hx n).le

end OAI.SKFluctuations.LaplaceWindowFormalization
