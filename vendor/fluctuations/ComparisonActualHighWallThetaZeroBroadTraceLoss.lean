module

public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonCapSideTraceNormalized

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def criticalBroadOriginLossFactor : ℝ := 1+1/Real.log 2

theorem criticalBroadOriginLossFactor_pos : 0 < criticalBroadOriginLossFactor := by
  unfold criticalBroadOriginLossFactor
  positivity [Real.log_pos (by norm_num : (1:ℝ)<2)]

theorem criticalBroad_origin_trace_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v V : ℝ} (hv : 0<v) (hUv : comparisonSmallMass a.data.N a.data.E ≤ v)
    (hV : 0≤V) (hVv : V≤4*v) :
    a.data.M V*a.data.rmin/v ≤ (25/2)*(v/comparisonSmallMass a.data.N a.data.E) := by
  let U := comparisonSmallMass a.data.N a.data.E
  have hU : 0 < U := a.data.hU
  have hUv' : U ≤ v := hUv
  have hK : 1 ≤ 5*v/U := (le_div_iff₀ hU).mpr (by linarith only [hUv',hv])
  have hTU : (5*v/U)*U = 5*v := div_mul_cancel₀ _ hU.ne'
  have hband : V+U ≤ (5*v/U)*(a.data.s+U) := by
    calc
      _ ≤ 5*v := by linarith only [hVv,hUv']
      _ = (5*v/U)*U := hTU.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left a.data.hs.1.le) (by positivity)
  have Hratio : a.data.M V/a.data.M a.data.s ≤ (5*v/U)^2 :=
    comparisonCap_normalized_factor_le a.data.hN hU a.data.hL a.data.hE
      a.data.hd.le a.data.hs.1.le hV hK hband
  have hMs : 0 < a.data.M a.data.s :=
    (comparisonCap_first_term a.data.hN a.data.hU a.data.hL a.data.hE
      a.data.hd.le a.data.hs.1.le).1
  have he : a.data.M V*a.data.rmin/v =
      (U/(2*v))*(a.data.M V/a.data.M a.data.s) := by
    change a.data.M V*(U/(2*a.data.M a.data.s))/v = _
    field_simp [hv.ne',hMs.ne'] <;> ring
  calc
    _ = (U/(2*v))*(a.data.M V/a.data.M a.data.s) := he
    _ ≤ (U/(2*v))*(5*v/U)^2 :=
      mul_le_mul_of_nonneg_left Hratio (by positivity)
    _ = (25/2)*(v/U) := by field_simp [hU.ne',hv.ne'] <;> ring

theorem criticalBroad_loss_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v : ℝ} (hv : 0<v) (hv1 : v≤1)
    (hUv : comparisonSmallMass a.data.N a.data.E ≤ v) :
    (32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1 ≤
      criticalBroadOriginLossFactor*(1025+25*(1+v/comparisonSmallMass a.data.N a.data.E)*
        Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E)) := by
  let U := comparisonSmallMass a.data.N a.data.E
  let rlog := Real.log ((1+U)/U)
  have hU : 0 < U := a.data.hU
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlog : Real.log 2 ≤ rlog := by
    apply Real.log_le_log (by norm_num : (0:ℝ)<2)
    exact (le_div_iff₀ hU).mpr (by linarith [hUv.trans hv1])
  have hratio : 0 ≤ v/U := by positivity
  have H := a.criticalBroad_origin_trace_le hv hUv
    (le_min (by positivity) zero_le_one) (min_le_left _ _)
  have HX : 25*(v/U) ≤ (25*(1+v/U)*rlog)/Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    have HH := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 25*(1+v/U) by positivity)
    nlinarith only [HH,hratio,hlog2]
  have HB : (25*(1+v/U)*rlog)/Real.log 2 ≤
      (1025+25*(1+v/U)*rlog)/Real.log 2 := by gcongr; norm_num
  have Horigin : a.data.M (min (4*v) 1)*a.data.rmin/v ≤
      (1025+25*(1+v/U)*rlog)/Real.log 2 :=
    ((H.trans (by nlinarith only [hratio])).trans HX).trans HB
  unfold criticalBroadTraceLoss criticalBroadOriginLossFactor
  change 32^2+((4+1)^2*(1+v/U)*rlog+
    a.data.M (min (4*v) 1)*a.data.rmin/v)+1 ≤ _
  have Hfactor : (1+1/Real.log 2)*(1025+25*(1+v/U)*rlog) =
      (1025+25*(1+v/U)*rlog)+(1025+25*(1+v/U)*rlog)/Real.log 2 := by ring
  rw [Hfactor]
  nlinarith only [Horigin]

theorem criticalBroad_trace_log_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) :
    Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E) ≤
      (1+Real.log (1+D^2))*Real.log a.data.N := by
  have hE : a.data.E ≤ D^2 := by
    have Hsqrt : 1 ≤ Real.sqrt a.data.N := (Real.one_le_sqrt).mpr hN
    have Hmul := mul_le_mul_of_nonneg_right Hsqrt a.data.hE.le
    have HE : a.data.E ≤ a.data.d^2 :=
      (show a.data.E ≤ Real.sqrt a.data.N*a.data.E by
        simpa only [one_mul] using Hmul).trans a.hupper
    exact HE.trans (pow_le_pow_left₀ a.data.hd.le a.hdD 2)
  have he : (1+comparisonSmallMass a.data.N a.data.E)/
      comparisonSmallMass a.data.N a.data.E = 1+a.data.N*a.data.E := by
    unfold comparisonSmallMass
    field_simp [a.data.hN.ne',a.data.hE.ne'] <;> ring
  have hsize : 1+a.data.N*a.data.E ≤ a.data.N*(1+D^2) := by
    calc
      _ ≤ a.data.N+a.data.N*D^2 :=
        add_le_add hN (mul_le_mul_of_nonneg_left hE a.data.hN.le)
      _ = _ := by ring
  have hpos : 0 < 1+a.data.N*a.data.E :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_pos a.data.hN a.data.hE).le
  have HL := Real.log_le_log hpos hsize
  rw [he]
  apply HL.trans
  rw [Real.log_mul a.data.hN.ne' (by positivity : (1+D^2:ℝ)≠0)]
  have hlogD : 0 ≤ Real.log (1+D^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg D])
  have Hmul := mul_le_mul_of_nonneg_left hlog hlogD
  nlinarith only [Hmul]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
