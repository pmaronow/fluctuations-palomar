module

public import ComparisonActualHighWallMesoscopicPower
public import ComparisonActualHighWallCriticalBroadTraceNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem mass_high_inverse_geometry_selected_le
    {N W v x c : ℝ} (hN : 0<N) (hW : 0<W) (hv : 0<v) (hx : 0<x)
    (hc : 0<c) (hWx : W≤x) (hvlo : c*x≤v) :
    1/(N*W*v*x^4) ≤ (1/c)*(1/(N*W^6)) := by
  have Hx5 := pow_le_pow_left₀ hW.le hWx 5
  have H2 := mul_le_mul_of_nonneg_right hvlo (pow_nonneg hx.le 4)
  have Hgeom : c*W^5≤v*x^4 := by
    calc
      c*W^5≤c*x^5 := mul_le_mul_of_nonneg_left Hx5 hc.le
      _ = (c*x)*x^4 := by ring
      _ ≤ v*x^4 := H2
  have Hden : c*(N*W^6)≤N*W*v*x^4 := by
    have H:=mul_le_mul_of_nonneg_left Hgeom (show 0≤N*W by positivity)
    nlinarith only [H]
  have Hdirect : 1/(N*W*v*x^4)≤1/(c*(N*W^6)) :=
    (div_le_div_iff₀ (show 0<N*W*v*x^4 by positivity)
      (show 0<c*(N*W^6) by positivity)).mpr (by nlinarith only [Hden])
  convert Hdirect using 1 <;> field_simp

theorem mass_high_broad_trace_noise_selected_le
    {N P W v x U E tau K c Cr Ce tlog rlog : ℝ}
    (hN : 0<N) (hP : 0<P) (hW : 0<W) (hv : 0<v) (hx : 0<x)
    (hU : 0<U) (hE : 0<E) (hK : 0≤K) (hc : 0<c)
    (hCr : 0≤Cr) (_hCe : 0≤Ce) (hlog : 0≤tlog) (hrlog : 0≤rlog)
    (hWx : W≤x) (hvlo : c*x≤v) (hpower : N*W^3≤K*P*v)
    (hUeq : U=1/(N*E)) (hr : rlog≤Cr*tlog)
    (htau : tau≤(W^2/x^4)/(P*v^2))
    (henergy : E/(W*x^4)≤Ce/(Real.sqrt N*x^3)) :
    (1025+25*(1+v/U)*rlog)*tau ≤
      K*(1025*((1/c)*(1/(N*W^6)))+
        25*(Cr*tlog)*((1/c)*(1/(N*W^6))+Ce/(Real.sqrt N*x^3))) := by
  have Htau:=htau.trans (mass_high_point_noise_le hN hP hW hv hx hpower)
  have Hgeom:=mass_high_inverse_geometry_selected_le hN hW hv hx hc hWx hvlo
  have Hn:=mul_le_mul_of_nonneg_left Htau
    (show 0≤1025+25*(1+v/U)*rlog by positivity)
  have HE : (1025+25*(1+v/U)*rlog)*(K/(N*W*v*x^4))=
      K*(1025*(1/(N*W*v*x^4))+25*rlog*(1/(N*W*v*x^4)+E/(W*x^4))) := by
    rw [hUeq]
    field_simp
  rw [HE] at Hn
  apply Hn.trans
  gcongr

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mesoscopicBroad_trace_noise_bound
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    {c v : ℝ} (hc : 0 < c) (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hdx : a.data.d ≤ a.xs) (hv : 0 < v) (hv1 : v ≤ 1) (hvlo : c*a.xs ≤ v)
    (hUv : comparisonSmallMass a.data.N a.data.E ≤ v) :
    (((32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1)*
      (a.data.d^2/(a.criticalBroadMassPower v*v^2*a.xs^4)))/Real.log a.data.N ≤
      criticalBroadTraceConstant Az cl c C0 Ct D*a.data.N^(-3*m) := by
  let K:=highMassEndpointConstant (Az:=Az) (cl:=cl) 16 c
  let Cr:=1+Real.log (1+D^2)
  let L:=Real.log a.data.N
  let U:=comparisonSmallMass a.data.N a.data.E
  let tau:=a.data.d^2/(a.criticalBroadMassPower v*v^2*a.xs^4)
  have hP : 0<a.criticalBroadMassPower v:=a.highMassPower_pos 16 v
  have hK : 0≤K:=(one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have hCr : 0≤Cr:=by dsimp [Cr];have :=Real.log_nonneg (by nlinarith [sq_nonneg D] : (1:ℝ)≤1+D^2);linarith
  have hL : 0<L:=zero_lt_one.trans_le hlog
  have Hr0 : 0≤Real.log ((1+U)/U):=Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
  have Hpower:=a.highMassPower_lower_on_selected_band hcl hAz (width:=16) (by norm_num) hc hdx hvlo
  have Henergy:=mass_direct_test_energy_over_band a.data.hN a.data.hE a.hxs a.data.hd hCt
    a.htest (laplaceComparisonStrength_le _ (sq_nonneg _) _)
  have Hbase:=mass_high_broad_trace_noise_selected_le (tau:=tau) a.data.hN hP a.data.hd hv a.hxs
    a.data.hU a.data.hE hK hc hCr (show 0≤Ct+1 by linarith) hL.le Hr0
    hdx hvlo Hpower rfl (a.criticalBroad_trace_log_le hN hlog)
    (by dsimp [tau];ring_nf;exact le_refl _) Henergy
  have Hinv6:=a.physical_d_inverse_six_bound hC0
  have Hinv3:=a.high_mass_inverse_power hC0 3
  simp only [Nat.cast_ofNat,show (3:ℝ)/6=(1:ℝ)/2 by norm_num] at Hinv3
  have Hinv3' : 1/(Real.sqrt a.data.N*a.xs^3)≤C0^3*a.data.N^(-3*m):=by
    simpa only [Real.sqrt_eq_rpow] using Hinv3
  have Hpow : a.data.N^(-6*m)≤a.data.N^(-3*m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have Hsix:=Hinv6.trans (mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 6))
  have Hsmall:=mul_le_mul_of_nonneg_left Hsix (show 0≤1/c by positivity)
  have HenergyInv:=mul_le_mul_of_nonneg_left Hinv3' (show 0≤Ct+1 by linarith)
  have HlogOne:=le_mul_of_one_le_left (show 0≤(1/c)*(C0^6*a.data.N^(-3*m)) by positivity) hlog
  have Hsaved : (1025+25*(1+v/U)*Real.log ((1+U)/U))*tau ≤
      (K*(1025*(C0^6/c)+25*Cr*(C0^6/c+(Ct+1)*C0^3)))*L*a.data.N^(-3*m) := by
    apply Hbase.trans
    have H1:=mul_le_mul_of_nonneg_left (Hsmall.trans HlogOne) (by norm_num : (0:ℝ)≤1025)
    have He : (Ct+1)/(Real.sqrt a.data.N*a.xs^3)≤(Ct+1)*(C0^3*a.data.N^(-3*m)):=by
      convert HenergyInv using 1;ring
    have H2:=mul_le_mul_of_nonneg_left (add_le_add Hsmall He) (show 0≤25*(Cr*L) by positivity)
    have H3:=mul_le_mul_of_nonneg_left (add_le_add H1 H2) hK
    convert H3 using 1 <;> ring
  have Hloss:=mul_le_mul_of_nonneg_right (a.criticalBroad_loss_le hv hv1 hUv)
    (show 0≤tau by dsimp [tau];positivity)
  have HS:=mul_le_mul_of_nonneg_left Hsaved criticalBroadOriginLossFactor_pos.le
  apply (div_le_iff₀ hL).mpr
  apply Hloss.trans
  convert HS using 1 <;> dsimp only [criticalBroadTraceConstant,K,Cr,L,tau,U] <;> ring

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
