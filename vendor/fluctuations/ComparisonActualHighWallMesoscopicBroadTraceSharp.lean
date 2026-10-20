module

public import ComparisonActualHighWallMesoscopicBroadTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem mass_high_point_noise_selected_le {N P W v x K : ℝ}
    (hN : 0<N) (hP : 0<P) (hW : 0<W) (hv : 0<v) (hx : 0<x)
    (hpower : N*W^3≤K*P*v) :
    1/(P*v^2*x^2) ≤ K/(N*W^3*v*x^2) := by
  apply (div_le_div_iff₀ (show 0<P*v^2*x^2 by positivity)
    (show 0<N*W^3*v*x^2 by positivity)).mpr
  have H:=mul_le_mul_of_nonneg_right hpower (show 0≤v*x^2 by positivity)
  nlinarith only [H]

theorem mass_high_inverse_geometry_selected_sharp_le {N W v x c : ℝ}
    (hN : 0<N) (hW : 0<W) (hv : 0<v) (hx : 0<x)
    (hc : 0<c) (hWx : W≤x) (hvlo : c*x≤v) :
    1/(N*W^3*v*x^2) ≤ (1/c)*(1/(N*W^6)) := by
  have Hx3:=pow_le_pow_left₀ hW.le hWx 3
  have H2:=mul_le_mul_of_nonneg_right hvlo (sq_nonneg x)
  have Hgeom : c*W^3≤v*x^2 := by
    calc
      c*W^3≤c*x^3:=mul_le_mul_of_nonneg_left Hx3 hc.le
      _=(c*x)*x^2:=by ring
      _≤v*x^2:=H2
  have Hden : c*(N*W^6)≤N*W^3*v*x^2 := by
    have H:=mul_le_mul_of_nonneg_left Hgeom (show 0≤N*W^3 by positivity)
    nlinarith only [H]
  have Hdirect : 1/(N*W^3*v*x^2)≤1/(c*(N*W^6)) :=
    (div_le_div_iff₀ (show 0<N*W^3*v*x^2 by positivity)
      (show 0<c*(N*W^6) by positivity)).mpr (by nlinarith only [Hden])
  convert Hdirect using 1 <;> field_simp

theorem mass_direct_test_energy_selected_sharp_le {N W x E Ce : ℝ}
    (hN : 0<N) (hW : 0<W) (hx : 0<x) (hCe : 0≤Ce) (hWx : W≤x)
    (henergy : E/(W*x^4)≤Ce/(Real.sqrt N*x^3)) :
    E/(W^3*x^2)≤Ce/(Real.sqrt N*W^3) := by
  have Hscale:=mul_le_mul_of_nonneg_left henergy (show 0≤x^2/W^2 by positivity)
  have Hmid : E/(W^3*x^2)≤Ce/(Real.sqrt N*W^2*x) := by
    convert Hscale using 1 <;> field_simp
  have Hden:=mul_le_mul_of_nonneg_left hWx (show 0≤Real.sqrt N*W^2 by positivity)
  have Hfrac : 1/(Real.sqrt N*W^2*x)≤1/(Real.sqrt N*W^3) :=
    (div_le_div_iff₀ (show 0<Real.sqrt N*W^2*x by positivity)
      (show 0<Real.sqrt N*W^3 by positivity)).mpr (by nlinarith only [Hden])
  exact Hmid.trans (by convert mul_le_mul_of_nonneg_left Hfrac hCe using 1 <;> ring)

theorem mass_high_broad_trace_noise_selected_sharp_le
    {N P W v x U E K c Cr Ce tlog rlog : ℝ}
    (hN : 0<N) (hP : 0<P) (hW : 0<W) (hv : 0<v) (hx : 0<x)
    (hU : 0<U) (hE : 0<E) (hK : 0≤K) (hc : 0<c)
    (hCr : 0≤Cr) (hCe : 0≤Ce) (hlog : 0≤tlog) (hrlog : 0≤rlog)
    (hWx : W≤x) (hvlo : c*x≤v) (hpower : N*W^3≤K*P*v)
    (hUeq : U=1/(N*E)) (hr : rlog≤Cr*tlog)
    (henergy : E/(W*x^4)≤Ce/(Real.sqrt N*x^3)) :
    (1025+25*(1+v/U)*rlog)/(P*v^2*x^2) ≤
      K*(1025*((1/c)*(1/(N*W^6)))+
        25*(Cr*tlog)*((1/c)*(1/(N*W^6))+Ce/(Real.sqrt N*W^3))) := by
  have Htau:=mass_high_point_noise_selected_le hN hP hW hv hx hpower
  have Hgeom:=mass_high_inverse_geometry_selected_sharp_le hN hW hv hx hc hWx hvlo
  have Henergy:=mass_direct_test_energy_selected_sharp_le hN hW hx hCe hWx henergy
  have Hn:=mul_le_mul_of_nonneg_left Htau
    (show 0≤1025+25*(1+v/U)*rlog by positivity)
  have HE : (1025+25*(1+v/U)*rlog)*(K/(N*W^3*v*x^2))=
      K*(1025*(1/(N*W^3*v*x^2))+25*rlog*(1/(N*W^3*v*x^2)+E/(W^3*x^2))) := by
    rw [hUeq]
    field_simp
  rw [HE] at Hn
  have Hn' : (1025+25*(1+v/U)*rlog)/(P*v^2*x^2) ≤
      K*(1025*(1/(N*W^3*v*x^2))+25*rlog*(1/(N*W^3*v*x^2)+E/(W^3*x^2))) := by
    convert Hn using 1 <;> ring
  apply Hn'.trans
  gcongr

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem physical_d_inverse_three_bound
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) :
    1/(Real.sqrt a.data.N*a.data.d^3)≤C0^3*a.data.N^(-3*m) := by
  have Hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr
      (by simpa only [mul_comm] using a.hupper)
  have Hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hd := (comparison_parent_scale_lower_bounds a.data.hN (one_div_pos.mpr hC0)
    a.data.hd Hlower Hupper).1
  have H:=mass_critical_inverse_power a.data.hN a.data.hd hC0 Hd 3
  simpa only [Nat.cast_ofNat,show (3:ℝ)/6=(1:ℝ)/2 by norm_num,Real.sqrt_eq_rpow] using H

theorem mesoscopicBroad_trace_noise_bound_sharp
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    {c v : ℝ} (hc : 0 < c) (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hdx : a.data.d ≤ a.xs) (hv : 0 < v) (hv1 : v ≤ 1) (hvlo : c*a.xs ≤ v)
    (hUv : comparisonSmallMass a.data.N a.data.E ≤ v) :
    (((32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1)/
      (a.criticalBroadMassPower v*v^2*a.xs^2))/Real.log a.data.N ≤
      criticalBroadTraceConstant Az cl c C0 Ct D*a.data.N^(-3*m) := by
  let K:=highMassEndpointConstant (Az:=Az) (cl:=cl) 16 c
  let Cr:=1+Real.log (1+D^2)
  let L:=Real.log a.data.N
  let U:=comparisonSmallMass a.data.N a.data.E
  let loss:=(32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
  have hP : 0<a.criticalBroadMassPower v:=a.highMassPower_pos 16 v
  have hK : 0≤K:=(one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have hCr : 0≤Cr:=by dsimp [Cr];have :=Real.log_nonneg (by nlinarith [sq_nonneg D] : (1:ℝ)≤1+D^2);linarith
  have hL : 0<L:=zero_lt_one.trans_le hlog
  have Hr0 : 0≤Real.log ((1+U)/U):=Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
  have Hpower:=a.highMassPower_lower_on_selected_band hcl hAz (width:=16) (by norm_num) hc hdx hvlo
  have Henergy:=mass_direct_test_energy_over_band a.data.hN a.data.hE a.hxs a.data.hd hCt
    a.htest (laplaceComparisonStrength_le _ (sq_nonneg _) _)
  have Hbase:=mass_high_broad_trace_noise_selected_sharp_le a.data.hN hP a.data.hd hv a.hxs
    a.data.hU a.data.hE hK hc hCr (show 0≤Ct+1 by linarith) hL.le Hr0
    hdx hvlo Hpower rfl (a.criticalBroad_trace_log_le hN hlog) Henergy
  have Hinv6:=a.physical_d_inverse_six_bound hC0
  have Hinv3:=a.physical_d_inverse_three_bound hC0
  have Hpow : a.data.N^(-6*m)≤a.data.N^(-3*m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have Hsix:=Hinv6.trans (mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 6))
  have Hsmall:=mul_le_mul_of_nonneg_left Hsix (show 0≤1/c by positivity)
  have HenergyInv:=mul_le_mul_of_nonneg_left Hinv3 (show 0≤Ct+1 by linarith)
  have HlogOne:=le_mul_of_one_le_left (show 0≤(1/c)*(C0^6*a.data.N^(-3*m)) by positivity) hlog
  have Hsaved : (1025+25*(1+v/U)*Real.log ((1+U)/U))/
        (a.criticalBroadMassPower v*v^2*a.xs^2) ≤
      (K*(1025*(C0^6/c)+25*Cr*(C0^6/c+(Ct+1)*C0^3)))*L*a.data.N^(-3*m) := by
    apply Hbase.trans
    have H1:=mul_le_mul_of_nonneg_left (Hsmall.trans HlogOne) (by norm_num : (0:ℝ)≤1025)
    have He : (Ct+1)/(Real.sqrt a.data.N*a.data.d^3)≤(Ct+1)*(C0^3*a.data.N^(-3*m)):=by
      convert HenergyInv using 1;ring
    have H2:=mul_le_mul_of_nonneg_left (add_le_add Hsmall He) (show 0≤25*(Cr*L) by positivity)
    have H3:=mul_le_mul_of_nonneg_left (add_le_add H1 H2) hK
    convert H3 using 1 <;> ring
  have Hloss0:=mul_le_mul_of_nonneg_right (a.criticalBroad_loss_le hv hv1 hUv)
    (by positivity : 0≤1/(a.criticalBroadMassPower v*v^2*a.xs^2))
  have Hloss : loss/(a.criticalBroadMassPower v*v^2*a.xs^2) ≤
      criticalBroadOriginLossFactor*((1025+25*(1+v/U)*Real.log ((1+U)/U))/
        (a.criticalBroadMassPower v*v^2*a.xs^2)) := by
    convert Hloss0 using 1 <;> dsimp only [loss,U] <;> ring
  have HS:=mul_le_mul_of_nonneg_left Hsaved criticalBroadOriginLossFactor_pos.le
  apply (div_le_iff₀ hL).mpr
  apply Hloss.trans
  convert HS using 1 <;> dsimp only [criticalBroadTraceConstant,K,Cr,L,loss,U] <;> ring

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
