module

public import ComparisonActualHighWallCriticalCenteringL2Along
public import ComparisonActualHighWallCriticalScalarCalibration
public import ComparisonActualHighWallStarClockDistinct
public import ComparisonInitialIntegralGoodPoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem exists_abs_le_of_initial_square_integral_lt
    (f : ℝ→ℝ) {a b x : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hab : a < b)
    (hf : IntervalIntegrable (fun u=>(f u)^2) volume 0 (b*x))
    (hsmall : (∫u in 0..b*x,(f u)^2) < (b-a)*x^3) :
    ∃u∈Ioo (a*x) (b*x), |f u|≤x := by
  by_contra hnone
  push Not at hnone
  have hax : 0≤a*x := mul_nonneg ha hx.le
  have hband : a*x<b*x := mul_lt_mul_of_pos_right hab hx
  have hsub : uIcc (a*x) (b*x) ⊆ uIcc (0:ℝ) (b*x) := by
    rw [uIcc_of_le hband.le,uIcc_of_le (hax.trans hband.le)]
    exact Icc_subset_Icc hax le_rfl
  have hfband : IntervalIntegrable (fun u=>(f u)^2) volume (a*x) (b*x) := hf.mono_set hsub
  have Hlow : (b-a)*x^3 ≤ ∫u in a*x..b*x,(f u)^2 := by
    have H:=intervalIntegral.integral_mono_on_of_le_Ioo hband.le
      (show IntervalIntegrable (fun _ : ℝ=>x^2) volume (a*x) (b*x) from intervalIntegrable_const)
      hfband (fun u hu=>by
        have H:=hnone u hu
        have Hsq:=pow_le_pow_left₀ hx.le H.le 2
        simpa only [sq_abs] using Hsq)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at H
    convert H using 1; ring
  have Hup : (∫u in a*x..b*x,(f u)^2) ≤ ∫u in 0..b*x,(f u)^2 :=
    intervalIntegral.integral_mono_interval hax hband.le le_rfl
      (ae_of_all _ (fun _=>sq_nonneg _)) hf
  exact (not_lt_of_ge (Hlow.trans Hup)) hsmall

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_scalar_cdf_caps_of_centering_along
    {m delta cl cu Az C0 Ct D Bclock T0 : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hT0 : 0 < T0)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hT : ∀n,T0≤(M n).data.T)
    (hcenter : ∀C : ℝ,1 ≤ C→Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u)^2)/(M n).xs^3)
      atTop (𝓝 0)) :
    ∀R : ℝ,0 < R→∃A : ℝ,0 ≤ A ∧ ∀ᶠn in atTop,
      ((M n).data.scalarMassProfile (M n).alpha).val ((M n).xs*R)≤A*(M n).xs := by
  intro R hR
  let a:=max (starMassBandConstant cu Az) (cu*(R+3))
  let b:=a+1
  have hA := star_mass_band_constant_pos hcu hAz
  have ha : 0<a := hA.trans_le (le_max_left _ _)
  have ha1 : 1≤a := by
    have H : 0≤cu*Az := mul_nonneg hcu.le hAz
    dsimp only [a,starMassBandConstant] at *
    linarith [le_max_left (1+cu*Az) (cu*(R+3))]
  have hAs : starMassBandConstant cu Az≤a := le_max_left _ _
  have hRC : R+3≤a/cu := (le_div_iff₀ hcu).mpr (by
    simpa only [mul_comm] using (le_max_right (starMassBandConstant cu Az) (cu*(R+3))))
  have hab : a<b := by dsimp only [b]; linarith
  have hb : 1≤b := by dsimp only [b]; linarith
  have Hcent := hcenter b hb
  have Hsmall := Hcent.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  have Hunit := (hxlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ)<1 by simp))
  have Hsq := (hxlim.pow 2).eventually
    (eventually_le_nhds (show (0:ℝ)^2<T0 by simpa using hT0))
  refine ⟨b,zero_le_one.trans hb,?_⟩
  filter_upwards [Hsmall,Hunit,Hsq] with n hnSmall hnUnit hnSq
  let x:=(M n).xs
  let f:=fun u=>orderedPathS (dim n+1) (M n).bf (M n).hf u-
    (M n).data.wallRadius (M n).alpha u
  have hfi : IntervalIntegrable (fun u=>(f u)^2) volume 0 (b*x) :=
    (M n).full_mass_squared_mismatch_intervalIntegrable.mono_set (by
      rw [uIcc_of_le (mul_nonneg (by linarith : 0≤b) (M n).hxs.le),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnUnit)
  have Hsmall' : (∫u in 0..b*x,(f u)^2) < (b-a)*x^3 := by
    have H := (div_lt_iff₀ (pow_pos (M n).hxs 3)).mp hnSmall
    have Hsub : b-a=1 := by dsimp only [b]; ring
    rw [Hsub,one_mul]
    simpa only [b,a,f,x,one_mul] using H
  obtain ⟨u,hu,hgood⟩ := exists_abs_le_of_initial_square_integral_lt f
    (M n).hxs ha.le hab hfi Hsmall'
  have hu01 : u∈Icc (0:ℝ) 1 :=
    ⟨((mul_pos ha (M n).hxs).trans hu.1).le,hu.2.le.trans hnUnit⟩
  have huHigh : u∈Icc (M n).data.s 1 := by
    refine ⟨(M n).hsxs.trans ?_,hu01.2⟩
    have H := mul_le_mul_of_nonneg_right ha1 (M n).hxs.le
    simpa only [one_mul] using H.trans hu.1.le
  have hRlo := ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
    (M n).hxs le_rfl hAs hnUnit
    ((M n).hsxs.trans (by nlinarith only [ha1,(M n).hxs]))
    ⟨hu.1.le,hu.2.le⟩).1
  have hSlo : (R+2)*x ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u := by
    have H := (abs_le.mp hgood).1
    dsimp only [f] at H
    have HR := mul_le_mul_of_nonneg_right hRC (M n).hxs.le
    have Hbase := HR.trans hRlo
    have HS : (M n).data.wallRadius (M n).alpha u-(M n).xs ≤
        orderedPathS (dim n+1) (M n).bf (M n).hf u := by linarith only [H]
    calc
      (R+2)*x = (R+3)*(M n).xs-(M n).xs := by dsimp only [x]; ring
      _ ≤ (M n).data.wallRadius (M n).alpha u-(M n).xs := sub_le_sub_right Hbase _
      _ ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u := HS
  have hg : (M n).data.g ((M n).data.wallRadius (M n).alpha u)≤x^2 := by
    have H : (M n).data.g ((M n).data.wallRadius (M n).alpha u)≤(M n).data.d^2 :=
      laplaceComparisonStrength_le (M n).data.d (sq_nonneg (M n).data.d) _
    rw [←hfixed n] at H
    exact H
  have hclock : |actualMixedClock (dim n+1) (M n).bf (M n).hf u-
      (M n).data.T*orderedPathS (dim n+1) (M n).bf (M n).hf u|≤x^3 := by
    rw [(M n).high_mass_clock_compensation huHigh,abs_mul,
      abs_of_pos (laplaceComparisonStrength_pos (M n).data.d
        (sq_pos_of_pos (M n).data.hd) _),abs_sub_comm]
    have H := mul_le_mul hg hgood (abs_nonneg _) (sq_nonneg x)
    nlinarith only [H]
  have hx3 : x^3≤(M n).data.T*x := by
    have H := mul_le_mul_of_nonneg_right (hnSq.trans (hT n)) (M n).hxs.le
    nlinarith only [H]
  have hcut : x*R < actualMixedClock (dim n+1) (M n).bf (M n).hf u/(M n).data.T := by
    apply (lt_div_iff₀ (M n).data.hTpos).mpr
    have H1 := (abs_le.mp hclock).1
    have H2 := mul_le_mul_of_nonneg_left hSlo (M n).data.hTpos.le
    have H3 := mul_pos (M n).data.hTpos (M n).hxs
    nlinarith only [H1,H2,hx3,H3]
  have hv : u∈Ioc (0:ℝ) 1 := ⟨(mul_pos ha (M n).hxs).trans hu.1,hu01.2⟩
  have Hcdf := actualMixedMassProfile_cdf_cap (M n).data.hTpos (dim n+1)
    (M n).data.hn (M n).bf (M n).hf
    ((M n).data.bf_monotone (M n).alpha)
    ((M n).data.hf_monotone (M n).alpha)
    ((M n).data.total_clock_le (M n).alpha) hv hcut
  exact Hcdf.trans hu.2.le

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
