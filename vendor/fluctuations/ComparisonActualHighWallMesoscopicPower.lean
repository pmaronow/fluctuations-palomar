module

public import ComparisonActualHighWallHighMassNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem physical_d_inverse_six_bound (hC0 : 0 < C0) :
    1/(a.data.N*a.data.d^6) ≤ C0^6*a.data.N^(-6*m) := by
  have Hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr
      (by simpa only [mul_comm] using a.hupper)
  have Hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hd := (comparison_parent_scale_lower_bounds a.data.hN (one_div_pos.mpr hC0)
    a.data.hd Hlower Hupper).1
  have H := mass_critical_inverse_power a.data.hN a.data.hd hC0 Hd 6
  norm_num at H ⊢
  exact H

theorem highMassHeight_le_on_selected_band
    {width c v : ℝ} (hc : 0 < c) (hvlo : c*a.xs ≤ v) :
    a.highMassHeight width v ≤ (1/c+width)*v := by
  have Hx : a.xs ≤ v/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  have He : v/c=(1/c)*v := by ring
  rw [He] at Hx
  unfold highMassHeight
  nlinarith [min_le_left (width*v) (1:ℝ)]

theorem highMassPower_lower_on_selected_band (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {width c v : ℝ} (hw : 0 ≤ width) (hc : 0 < c)
    (hdx : a.data.d ≤ a.xs) (hvlo : c*a.xs ≤ v) :
    a.data.N*a.data.d^3 ≤
      highMassEndpointConstant (Az:=Az) (cl:=cl) width c*a.highMassPower width v*v := by
  let K:=highMassEndpointConstant (Az:=Az) (cl:=cl) width c
  let r:=a.data.wallRadius a.alpha (min (width*v) 1)
  have hv : 0 < v:=(mul_pos hc a.hxs).trans_le hvlo
  have hK : 0 < K:=(one_div_pos.mpr hc).trans_le (le_max_left _ _)
  have hu : min (width*v) 1∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hw hv.le) zero_le_one,min_le_right _ _⟩
  have Hrad:=a.high_radius_le_threshold_add_mass hcl hu
  have Hx : a.xs ≤ v/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  have Hx' : a.xs ≤ (1/c)*v := by simpa only [div_eq_mul_inv,one_div,mul_comm,mul_one] using Hx
  have Hd : a.data.d ≤ K*v := by
    exact (hdx.trans Hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv.le)
  have Hr : r ≤ K*v := by
    have Hzd:=mul_le_mul_of_nonneg_left Hx' hAz
    have Hu:=div_le_div_of_nonneg_right (min_le_left (width*v) (1:ℝ)) hcl.le
    have Hcap:=mul_le_mul_of_nonneg_right (le_max_right (1/c) (Az/c+width/cl)) hv.le
    have Hzd' : Az*a.xs ≤ (Az/c)*v:=by convert Hzd using 1 <;> ring_nf
    have Hu' : min (width*v) 1/cl ≤ (width/cl)*v:=by convert Hu using 1 <;> ring_nf
    calc
      r ≤ a.z+min (width*v) 1/cl := Hrad
      _ ≤ Az*a.xs+(width/cl)*v := add_le_add a.hzxs Hu'
      _ ≤ (Az/c+width/cl)*v := by nlinarith only [Hzd']
      _ ≤ K*v := Hcap
  have hr : 0 < r:=a.data.hrbounds.1.trans_le (a.data.wallRadius_bounds a.alpha _).1
  have HG : a.data.d^3/(K*v) ≤ a.data.g r:=by
    apply le_trans _ (laplaceComparisonStrength_lower a.data.hd (sq_pos_of_pos a.data.hd) hr)
    apply le_min
    · apply (div_le_iff₀ (mul_pos hK hv)).mpr
      nlinarith [mul_le_mul_of_nonneg_left Hd (sq_nonneg a.data.d)]
    · exact div_le_div_of_nonneg_left (pow_nonneg a.data.hd.le 3) hr Hr
  have H:=mul_le_mul_of_nonneg_left ((div_le_iff₀ (mul_pos hK hv)).mp HG) a.data.hN.le
  dsimp only [highMassPower,K,r]
  nlinarith only [H]

theorem highMassPower_selected_six_gain (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {width c v : ℝ} (hw : 0 ≤ width) (hc : 0 < c)
    (hdx : a.data.d ≤ a.xs) (hvlo : c*a.xs ≤ v) :
    c*a.data.N*a.data.d^6 ≤
      highMassEndpointConstant (Az:=Az) (cl:=cl) width c*
        a.highMassPower width v*v^2*a.xs^2 := by
  have HP:=a.highMassPower_lower_on_selected_band hcl hAz hw hc hdx hvlo
  have Hv : c*a.data.d^3 ≤ v*a.xs^2 := by
    have Hx3:=pow_le_pow_left₀ a.data.hd.le hdx 3
    have Hmul:=mul_le_mul_of_nonneg_left hvlo (sq_nonneg a.xs)
    calc
      c*a.data.d^3 ≤ c*a.xs^3 := mul_le_mul_of_nonneg_left Hx3 hc.le
      _ = a.xs^2*(c*a.xs) := by ring
      _ ≤ a.xs^2*v := Hmul
      _ = v*a.xs^2 := by ring
  have Hmul:=mul_le_mul HP Hv (mul_nonneg hc.le (pow_nonneg a.data.hd.le 3))
    (mul_nonneg (mul_nonneg (le_max_of_le_left (le_of_lt (one_div_pos.mpr hc)))
      (a.highMassPower_pos width v).le) (le_of_lt ((mul_pos hc a.hxs).trans_le hvlo)))
  convert Hmul using 1 <;> ring

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
