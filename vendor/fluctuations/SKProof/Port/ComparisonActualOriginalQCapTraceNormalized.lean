module

public import ComparisonActualHighWallThetaZeroCapUnitTracePositiveOrigin
public import ComparisonCapSideTraceLocalizedBroad

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem mass_lower : a.data.M (a.alpha.val.val c.left)*(c.right-c.left)≤
    a.alpha.val.val c.right-a.alpha.val.val c.left := by
  have hsub : Icc c.left c.right⊆Icc a.data.rmin 1:=Icc_subset_Icc c.hleft c.hright
  have hLip : LipschitzOnWith ⟨a.data.M 1,a.data.hM⟩ a.alpha.val.val (uIcc c.left c.right):=by
    simpa only [uIcc_of_le c.hlt.le] using
      (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).mono hsub
  have hac:=hLip.absolutelyContinuousOnInterval
  have hden:=P.cap_density_on_interval a c.hleft c.hright c.negative
  have hbound : ∀ᵐr∂volume.restrict (Icc c.left c.right),
      a.data.M (a.alpha.val.val c.left)≤ deriv a.alpha.val.val r:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hden] with r hr hd
    rw [hd hr]
    exact a.data.hm (a.alpha.val.property.1 c.left) (a.alpha.val.property.1 r)
      (a.alpha.val.property.2 hr.1)
  have HH:=intervalIntegral.integral_mono_ae_restrict c.hlt.le intervalIntegrable_const
    hac.intervalIntegrable_deriv hbound
  simpa only [intervalIntegral.integral_const,smul_eq_mul,hac.integral_deriv_eq_sub,
    mul_comm (c.right-c.left)] using HH

theorem unit_trace_eventually
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hl : a.data.rmin<c.left) (hleft : P.H c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam c.right)
    ∀ᶠj in atTop,(∫r in Ioo c.left c.right,deriv a.alpha.val.val r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      (a.data.M (a.alpha.val.val c.right)/a.data.M (a.alpha.val.val c.left))*
        ((9*Real.log a.data.N)/F)*(a.alpha.val.val c.right-a.alpha.val.val c.left)+ε := by
  exact c.unit_trace_eventually_strict hN hlog hnd dphys e hl hleft hright
    as mesh ho hend hmesh hmesh0 hlim hε

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
