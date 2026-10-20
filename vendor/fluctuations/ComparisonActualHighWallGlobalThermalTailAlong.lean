module

public import ComparisonActualHighWallGlobalThermalTail
public import ComparisonActualHighWallUniformWholeThermalAlong
public import ComparisonActualHighWallTailAccumulation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

theorem eventually_actual_high_wall_global_thermal_tail_along
    {m delta cl cu Az C0 Ct D Bclock c : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hc : 0< c) (hcout : cu*Az< c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs≤(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀u : ℝ,2*c*(M n).data.d≤ u → u≤1 →
      (∫s in u..1,(M n).data.thermal (M n).alpha s)≤
        (M n).data.N^(-(actualMassSavingExponent m delta/4))*(M n).data.d^2 := by
  have hD : 0< D:=(M 0).data.hd.trans_le (M 0).hdD
  have HD:=eventually_actual_high_wall_uniform_whole_thermal_dyads_along hm hdelta hroom hcl hcu hAz
    hC0 hCt hD hc hcout dim hdim M hxsd hdlim hsRatio
  have HC:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-(actualMassSavingExponent m delta/2))
      (r:=-(actualMassSavingExponent m delta/4)) zero_lt_one
      (by linarith [actualMassSavingExponent_pos hm hdelta]))
  filter_upwards [HD,HC] with n hd hcN
  intro u hu hu1
  have HH:=(M n).thermal_tail_le_of_dyadic_bound (sigma:=actualMassSavingExponent m delta/2) hc hu hu1 (by
    intro v hv hv2 hvd
    rw [intervalIntegral.integral_of_le (by linarith only [hv]),integral_Ioc_eq_integral_Ioo]
    exact hd v hvd hv2)
  have HR : 2*(M n).data.N^(-(actualMassSavingExponent m delta/2))≤
      (M n).data.N^(-(actualMassSavingExponent m delta/4)):=by
    simpa only [Function.comp_apply,ActualHighWallData.N,one_mul] using hcN
  exact HH.trans (mul_le_mul_of_nonneg_right HR (sq_nonneg (M n).data.d))

theorem eventually_actual_high_wall_global_sqrt_thermal_tail_along
    {m delta cl cu Az C0 Ct D Bclock c : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hc : 0< c) (hcout : cu*Az< c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs≤(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀u : ℝ,2*c*(M n).data.d≤ u → u≤1 →
      (∫s in u..1,Real.sqrt ((M n).data.thermal (M n).alpha s))≤
        (M n).data.N^(-(actualMassSavingExponent m delta/8))*(M n).data.d := by
  filter_upwards [eventually_actual_high_wall_global_thermal_tail_along hm hdelta hroom hcl hcu hAz
    hC0 hCt hc hcout dim hdim M hxsd hdlim hsRatio] with n hn
  intro u hu hu1
  let a:=M n
  let eta:=actualMassSavingExponent m delta
  have hd:=a.data.hd
  have hu0 : 0≤ u:=(mul_pos (by positivity : 0<2*c) hd).le.trans hu
  have hfi:=a.physical_thermal_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hu1,uIcc_of_le zero_le_one];exact Icc_subset_Icc hu0 le_rfl)
  have HS:=interval_integral_sqrt_sq_le_length hu1 hfi
    (fun s hs=>a.data.thermal_nonneg a.alpha ⟨hu0.trans hs.1,hs.2⟩)
  have HT:=hn u hu hu1
  have HM:=mul_le_mul_of_nonneg_left HT (sub_nonneg.mpr hu1)
  have HL:=mul_le_mul_of_nonneg_right (show 1-u≤1 by linarith)
    (show 0≤ a.data.N^(-(eta/4))*a.data.d^2 by positivity)
  have HE : (a.data.N^(-(eta/8))*a.data.d)^2=a.data.N^(-(eta/4))*a.data.d^2:=by
    rw [mul_pow,←Real.rpow_mul_natCast a.data.hN.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-(eta/8))*(2:ℝ)=-(eta/4) by ring]
  have HH:=HS.trans (HM.trans HL)
  rw [one_mul,←HE] at HH
  have HR : 0≤ a.data.N^(-(eta/8))*a.data.d:=by positivity
  nlinarith only [HH,HR]

end OAI.SKFluctuations.LaplaceWindowFormalization
