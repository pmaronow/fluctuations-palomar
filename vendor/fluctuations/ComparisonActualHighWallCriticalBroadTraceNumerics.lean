module

public import ComparisonActualHighWallCriticalBroadBudgets
public import ComparisonActualHighWallHighMassNumerics
public import ComparisonCapSideTraceAggregate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def criticalBroadOriginLossFactor : ℝ := 1+1/Real.log 2

theorem criticalBroadOriginLossFactor_pos : 0 < criticalBroadOriginLossFactor := by
  unfold criticalBroadOriginLossFactor
  positivity [Real.log_pos (by norm_num : (1:ℝ)<2)]

theorem criticalBroad_origin_trace_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v V : ℝ} (hv : 0<v) (hUv : comparisonSmallMass a.data.N a.data.E ≤ v)
    (hV : 0≤V) (hVv : V≤4*v) :
    a.data.M V*a.data.rmin/v ≤ (25/2)*(v/comparisonSmallMass a.data.N a.data.E) := by
  let U:=comparisonSmallMass a.data.N a.data.E
  have hU : 0<U:=a.data.hU
  have hK : 1≤5*v/U := (le_div_iff₀ hU).mpr (by nlinarith only [hUv,hU])
  have hband : V+U≤(5*v/U)*(a.data.s+U) := by
    have hs:=mul_nonneg (show 0≤5*v/U by positivity) a.data.hs.1.le
    have he : (5*v/U)*U=5*v:=by field_simp
    nlinarith only [hVv,hUv,hs,he]
  have Hratio : a.data.M V/a.data.M a.data.s ≤ (5*v/U)^2 := by
    exact comparisonCap_normalized_factor_le a.data.hN hU a.data.hL a.data.hE
      a.data.hd.le a.data.hs.1.le hV hK hband
  have hMs : 0<a.data.M a.data.s :=
    (comparisonCap_first_term a.data.hN a.data.hU a.data.hL a.data.hE
      a.data.hd.le a.data.hs.1.le).1
  have he : a.data.M V*a.data.rmin/v=(U/(2*v))*(a.data.M V/a.data.M a.data.s) := by
    change a.data.M V*(U/(2*a.data.M a.data.s))/v=_
    field_simp
  rw [he]
  apply (mul_le_mul_of_nonneg_left Hratio (by positivity : 0≤U/(2*v))).trans_eq
  change (U/(2*v))*(5*v/U)^2=(25/2)*(v/U)
  field_simp
  ring

theorem criticalBroad_loss_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v : ℝ} (hv : 0<v) (hv1 : v≤1)
    (hUv : comparisonSmallMass a.data.N a.data.E ≤ v) :
    (32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1 ≤
      criticalBroadOriginLossFactor*(1025+25*(1+v/comparisonSmallMass a.data.N a.data.E)*
        Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E)) := by
  let U:=comparisonSmallMass a.data.N a.data.E
  let rlog:=Real.log ((1+U)/U)
  have hU : 0<U:=a.data.hU
  have hlog2 : 0<Real.log 2:=Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlog : Real.log 2≤rlog := by
    apply Real.log_le_log (by norm_num : (0:ℝ)<2)
    exact (le_div_iff₀ hU).mpr (by linarith [hUv.trans hv1])
  have hr0 : 0≤rlog:=hlog2.le.trans hlog
  have hratio : 0≤v/U:=by positivity
  have H:=a.criticalBroad_origin_trace_le hv hUv
    (le_min (by positivity) zero_le_one) (min_le_left _ _)
  have HX : 25*(v/U)≤(25*(1+v/U)*rlog)/Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    have HH:=mul_le_mul_of_nonneg_left hlog (show 0≤25*(1+v/U) by positivity)
    nlinarith only [HH,hratio,hlog2]
  have HB : (25*(1+v/U)*rlog)/Real.log 2 ≤
      (1025+25*(1+v/U)*rlog)/Real.log 2 := by gcongr;norm_num
  unfold criticalBroadTraceLoss criticalBroadOriginLossFactor
  change 32^2+((4+1)^2*(1+v/U)*rlog+a.data.M (min (4*v) 1)*a.data.rmin/v)+1≤_
  have Hfactor : (1+1/Real.log 2)*(1025+25*(1+v/U)*rlog)=
      (1025+25*(1+v/U)*rlog)+(1025+25*(1+v/U)*rlog)/Real.log 2 := by ring
  rw [Hfactor]
  nlinarith only [H,HX,HB,hratio]

theorem criticalBroad_trace_log_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) :
    Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E) ≤
      (1+Real.log (1+D^2))*Real.log a.data.N := by
  have hE : a.data.E≤D^2 := by
    have Hsqrt : 1≤Real.sqrt a.data.N:=(Real.one_le_sqrt).mpr hN
    have HE : a.data.E≤a.data.d^2 := by nlinarith [a.hupper,a.data.hE]
    exact HE.trans (pow_le_pow_left₀ a.data.hd.le a.hdD 2)
  have he : (1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E=
      1+a.data.N*a.data.E := by unfold comparisonSmallMass;field_simp [a.data.hE.ne'];ring
  have hsize : 1+a.data.N*a.data.E≤a.data.N*(1+D^2) := by
    nlinarith [mul_le_mul_of_nonneg_left hE a.data.hN.le]
  have HL:=Real.log_le_log (show 0<1+a.data.N*a.data.E by nlinarith [mul_pos a.data.hN a.data.hE]) hsize
  rw [he]
  apply HL.trans
  rw [Real.log_mul a.data.hN.ne' (by positivity : (1+D^2:ℝ)≠0)]
  have hlogD : 0≤Real.log (1+D^2):=Real.log_nonneg (by nlinarith [sq_nonneg D])
  nlinarith [mul_nonneg hlogD (sub_nonneg.mpr hlog)]

def criticalBroadTraceConstant (Az cl c C0 Ct D : ℝ) : ℝ :=
  criticalBroadOriginLossFactor*highMassEndpointConstant (Az:=Az) (cl:=cl) 16 c*
    (1025*(C0^6/c)+25*(1+Real.log (1+D^2))*(C0^6/c+(Ct+1)*C0^3))

theorem criticalBroad_trace_noise_bound
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    {c v : ℝ} (hc : 0<c) (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N)
    (hfixed : a.xs=a.data.d) (hv : 0<v) (hv1 : v≤1) (hvlo : c*a.data.d≤v)
    (hUv : comparisonSmallMass a.data.N a.data.E≤v) :
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
  have Hpower:=a.highMassPower_lower hcl hAz (width:=16) (by norm_num) hc hfixed.le hvlo
  have Henergy:=mass_direct_test_energy_over_band a.data.hN a.data.hE a.hxs a.data.hd hCt
    a.htest (laplaceComparisonStrength_le _ (sq_nonneg _) _)
  have Hbase:=mass_high_broad_trace_noise_le (tau:=tau) a.data.hN hP a.data.hd hv a.hxs
    a.data.hU a.data.hE hK hc hCr (show 0 ≤ Ct+1 by linarith) hL.le Hr0
    hfixed.le hvlo Hpower rfl (a.criticalBroad_trace_log_le hN hlog)
    (by dsimp [tau];ring_nf;exact le_refl _) Henergy
  have Hinv6:=a.high_mass_inverse_power hC0 6
  have Hinv3:=a.high_mass_inverse_power hC0 3
  simp only [Nat.cast_ofNat,show (6:ℝ)/6=1 by norm_num,Real.rpow_one] at Hinv6
  simp only [Nat.cast_ofNat,show (3:ℝ)/6=(1:ℝ)/2 by norm_num] at Hinv3
  have Hinv3' : 1/(Real.sqrt a.data.N*a.xs^3)≤C0^3*a.data.N^(-3*m):=by
    simpa only [Real.sqrt_eq_rpow] using Hinv3
  have Hpow : a.data.N^(-6*m)≤a.data.N^(-3*m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have Hsix:=Hinv6.trans (mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 6))
  have Hsmall:=mul_le_mul_of_nonneg_left Hsix (show 0≤1/c by positivity)
  have HenergyInv:=mul_le_mul_of_nonneg_left Hinv3' (show 0 ≤ Ct+1 by linarith)
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
