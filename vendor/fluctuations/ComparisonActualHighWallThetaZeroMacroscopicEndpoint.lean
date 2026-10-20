module

public import ComparisonActualHighWallThetaZeroMacroscopicAllMassExclusion
public import ComparisonActualHighOnlyMacroscopicChildEndpoint
public import ComparisonMacroscopicShellEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem theta_zero_changed_endpoint_cost_le :
    comparisonEndpointL1Cost M.data.T M.changedBare M.changedField ≤
      M.data.s*M.data.epsilon/4+(3/4:ℝ)*M.lam := by
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  have Hclocks:=P.clockAdmissible M.alpha
  have he0 (u:ℝ):0≤P.coefficient M.alpha u:=by
    change 0≤omittedStrengthCoefficient M.data.d M.data.s
      (M.data.wallRadius M.alpha) M.lam u
    unfold omittedStrengthCoefficient
    split_ifs
    · exact (laplaceComparisonStrength_pos M.data.d M.hlam _).le
    · exact le_rfl
  have he (u:ℝ):P.coefficient M.alpha u≤M.lam:=by
    change omittedStrengthCoefficient M.data.d M.data.s
      (M.data.wallRadius M.alpha) M.lam u≤M.lam
    unfold omittedStrengthCoefficient
    split_ifs
    · exact laplaceComparisonStrength_le M.data.d M.hlam.le _
    · exact M.hlam.le
  have hbM:IntervalIntegrable P.b volume 0 1:=by
    change IntervalIntegrable M.data.thetaZeroHighOnlyData.b volume 0 1
    exact (show MonotoneOn M.data.thetaZeroHighOnlyData.b (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.data.thetaZeroHighOnlyData.hb).intervalIntegrable
  have hhM:IntervalIntegrable P.h volume 0 1:=by
    change IntervalIntegrable (fun _ : ℝ=>0) volume 0 1
    exact intervalIntegrable_const
  have hbc:IntervalIntegrable M.changedBare volume 0 1:=by
    apply (show MonotoneOn M.changedBare (uIcc (0:ℝ) 1) from ?_).intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    change MonotoneOn (fun u=>P.b u-P.coefficient M.alpha u) (Icc (0:ℝ) 1)
    exact Hclocks.1
  have hhc:IntervalIntegrable M.changedField volume 0 1:=by
    apply (show MonotoneOn M.changedField (uIcc (0:ℝ) 1) from ?_).intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    change MonotoneOn (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) (Icc (0:ℝ) 1)
    exact Hclocks.2.1
  have HB:=intervalIntegral.integral_mono_on zero_le_one (hbc.sub intervalIntegrable_const).abs
    ((hbM.sub intervalIntegrable_const).abs.add (intervalIntegrable_const (c:=M.lam))) (fun u hu=>by
      have Htri:=abs_add_le (P.b u-M.data.T) (-P.coefficient M.alpha u)
      rw [abs_neg,abs_of_nonneg (he0 u)] at Htri
      have Heq:M.changedBare u-M.data.T=(P.b u-M.data.T)+(-P.coefficient M.alpha u):=by
        dsimp only [changedBare]
        ring
      rw [Heq]
      linarith only [Htri,he u])
  have HH:=intervalIntegral.integral_mono_on zero_le_one hhc.abs
    (hhM.abs.add (intervalIntegrable_const (c:=M.lam))) (fun u hu=>by
      have HR:=omittedSweepQuantile_bounds M.data.hr ⟨M.data.hs.1.le,M.data.hs1⟩
        M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u
      have Htri:=abs_add_le (P.h u) (P.coefficient M.alpha u*P.R M.alpha u)
      have HR0:0≤P.R M.alpha u:=M.data.hrbounds.1.le.trans HR.1
      rw [abs_of_nonneg (mul_nonneg (he0 u) HR0)] at Htri
      have Hmul:=mul_le_mul_of_nonneg_left HR.2 (he0 u)
      change P.coefficient M.alpha u*P.R M.alpha u≤P.coefficient M.alpha u*1 at Hmul
      have Heq:M.changedField u=P.h u+P.coefficient M.alpha u*P.R M.alpha u:=rfl
      rw [Heq]
      linarith only [Htri,Hmul,he u])
  rw [intervalIntegral.integral_add (hbM.sub intervalIntegrable_const).abs intervalIntegrable_const] at HB
  rw [intervalIntegral.integral_add hhM.abs intervalIntegrable_const] at HH
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at HB HH
  have hbare:P.b=initialShellMatrixClock M.data.T M.data.epsilon M.data.s:=by
    funext u
    change wallBareMatrix M.data.T M.data.epsilon 0 M.data.s u=
      initialShellMatrixClock M.data.T M.data.epsilon M.data.s u
    by_cases hs:u<M.data.s <;> simp [wallBareMatrix,initialShellMatrixClock,hs]
  have hfield:P.h=(fun _=>0):=rfl
  have Hbase:comparisonEndpointL1Cost M.data.T P.b P.h=
      M.data.s*M.data.epsilon/4:=by
    rw [hbare,hfield]
    exact shell_comparisonEndpointL1Cost M.data.hepsilon.1.le ⟨M.data.hs.1.le,M.data.hs1⟩
  unfold comparisonEndpointL1Cost at Hbase ⊢
  linarith only [HB,HH,Hbase]

end ActualThetaZeroOverlapMinimum

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T:ℝ} {N:ℕ→ℕ}

theorem theta_zero_changed_endpoint_cost_tendsto_zero_of_weak_bounded_call
    (M:(j:ℕ)→ActualThetaZeroOverlapMinimum (N j+1) m delta cl cu Az C0 Ct D Bclock)
    (hunit:∀ᶠj in atTop,(M j).xs≤1)
    (hT:∀j,(M j).data.T=T)
    (hs:Tendsto (fun j=>(M j).data.s) atTop (𝓝 0))
    (hweak:Tendsto (fun j=>laplaceComparisonStrength (M j).data.d (M j).lam (M j).xs/(M j).xs^2)
      atTop (𝓝 0)):
    Tendsto (fun j=>comparisonEndpointL1Cost T (M j).changedBare (M j).changedField)
      atTop (𝓝 0):=by
  have hlam:=actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (hunit.mono fun j hj=>⟨(M j).data.hd,(M j).hlam.le,(M j).hxs,hj,(M j).hld⟩) hweak
  have Hupper:Tendsto (fun j=>T*(M j).data.s/4+(3/4:ℝ)*(M j).lam) atTop (𝓝 0):=by
    simpa only [mul_zero,zero_div,add_zero] using
      (hs.const_mul T |>.div_const 4).add (hlam.const_mul (3/4:ℝ))
  apply squeeze_zero (fun j=>actual_high_only_endpoint_l1_cost_nonneg T
      (M j).changedBare (M j).changedField) (fun j=>by
    have H:=(M j).theta_zero_changed_endpoint_cost_le
    have Hs:0≤(M j).data.s:=(M j).data.hs.1.le
    have He:=(M j).data.hepsilon.2.le
    rw [hT j] at He H
    have Hmul:=mul_le_mul_of_nonneg_left He Hs
    nlinarith only [H,Hmul]) Hupper

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
