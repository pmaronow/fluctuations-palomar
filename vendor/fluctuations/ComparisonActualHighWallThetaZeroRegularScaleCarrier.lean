module

public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualHighWallData
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (a:ActualHighWallData (n+1) delta)

theorem theta_zero_regular_scale_carrier
    (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2) (alpha:a.Profile)
    (hminimum:∀beta:a.Profile,
      (a.thetaZeroShiftedParentData lam hlam hld).objective alpha ≤
        (a.thetaZeroShiftedParentData lam hlam hld).objective beta)
    (hdelta:0 ≤ delta)
    (hsA:a.s ≤ comparisonConditionalScale a.N delta a.E lam)
    (hrA:a.rmin ≤ comparisonConditionalScale a.N delta a.E lam)
    (hdD:a.d ≤ D) (hupper:Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower:a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
    (hT:a.T ≤ Bclock) (hAz:2 ≤ Az) (hCt:1 ≤ Ct)
    (hregular:∀r∈Icc (min (2*comparisonConditionalScale a.N delta a.E lam) 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) :
    ∃M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data=a ∧ M.lam=lam ∧ HEq M.alpha alpha ∧
      M.xs=comparisonConditionalScale a.N delta a.E lam ∧
      M.z=min (2*comparisonConditionalScale a.N delta a.E lam) 1 := by
  let A:=comparisonConditionalScale a.N delta a.E lam
  have hA:0<A:=comparison_conditional_scale_pos (delta:=delta) a.hN a.hE hlam
  have hN1:1 ≤ a.N:=by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hscale:comparisonLowerScale a.N a.E a.d≤A:=
    comparison_conditional_scale_ge_lower hN1 hdelta a.hE a.hd hlam hld
  have htest:a.N*a.E^2 ≤ Ct*laplaceComparisonStrength a.d lam A*A^2:=by
    have H:=comparison_selected_scale_direct_test hN1 hdelta a.hE a.hd hlam hld hupper hA le_rfl
    have HM:=mul_le_mul_of_nonneg_right hCt
      (mul_nonneg (laplaceComparisonStrength_pos a.d hlam A).le (sq_nonneg A))
    exact H.trans (by simpa only [one_mul,mul_assoc] using HM)
  have hz:a.rmin ≤ min (2*A) 1:=by
    apply le_min _ a.hr
    linarith only [hrA,hA]
  let M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock:={
    data:=a,lam:=lam,hlam:=hlam,hld:=hld,alpha:=alpha,minimum:=hminimum,
    xs:=A,z:=min (2*A) 1,hxs:=hA,hscale:=hscale,hsxs:=hsA,
    hz:=⟨hz,min_le_right _ _⟩,
    hzxs:=(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hAz hA.le),
    hdD:=hdD,hupper:=hupper,hlower:=hlower,htest:=htest,regular:=hregular,hT:=hT}
  exact ⟨M,rfl,rfl,HEq.rfl,rfl,rfl⟩

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
