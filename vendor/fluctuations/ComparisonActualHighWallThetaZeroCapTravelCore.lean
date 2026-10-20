module

public import ComparisonActualHighWallThetaZeroCapDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
theorem Potential.cap_interval_travel (P:Q.Potential)
    {l r:ℝ} (hl:Q.data.rmin≤l) (hlr:l≤r) (hr:r≤1)
    (hnegative:∀t∈Ioo l r,P.H t<0):
    (∫u in Q.alpha.val.val l..Q.alpha.val.val r,1/Q.data.M u)=r-l ∧
    r-l≤Q.cavityCapTravel ∧
    ∀v>0,v≤Q.alpha.val.val l+comparisonSmallMass Q.data.N Q.data.E→
      r-l≤(Q.alpha.val.val r-Q.alpha.val.val l)*Q.data.E/
        (Q.data.N^delta*Q.data.d^3*v^2):=by
  let a:=Q.data
  have hsub:Icc l r⊆Icc a.rmin 1:=Icc_subset_Icc hl hr
  have hα:=(inverseIntegralConstraints_lipschitz a.hm a.hM Q.alpha.property).mono hsub
  have hm:=(inverseConstraint_strictMonoOn a.hc a.hk a.hkc Q.alpha.property).mono hsub
  have hden:=P.cap_density_on_interval Q hl hr hnegative
  have hαr (t:ℝ) (ht:t∈Icc l r):Q.alpha.val.val t∈Icc (0:ℝ) 1:=by
    have H:=inverseConstraint_mass_mem a.hr a.hc a.hk a.hkc Q.alpha (hsub ht)
    exact ⟨a.hs.1.le.trans H.1,H.2⟩
  have hM (u:ℝ) (hu:u∈Icc (0:ℝ) 1):0<a.M u:=
    (comparisonCap_first_term (δ:=delta) a.hN a.hU a.hL a.hE a.hd.le hu.1).1
  have heq:=cap_travel_identity hlr hα hm (fun t ht=>hM _ (hαr t ht)) hden
  have ht:=cap_travel_le_total hlr hα hm hαr
    (comparisonCap_continuous a.N delta (comparisonSmallMass a.N a.E)
      (comparisonConstraintLength a.N a.E a.d) a.E a.d).continuousOn hM hden
  have hW:(∫u in (0:ℝ)..1,1/a.M u)≤Q.cavityCapTravel:=by
    simpa only [cavityCapTravel,ActualHighWallData.M,concreteWallCap,a,zero_add] using
      comparisonCap_log_travel (δ:=delta) a.hN a.hU a.hL a.hE a.hd.le
        (a:=0) (b:=1) le_rfl zero_le_one
  refine ⟨heq,ht.trans hW,?_⟩
  intro v hv hva
  rw [←heq]
  exact comparisonCap_band_travel (δ:=delta) a.hN a.hU a.hL a.hE a.hd
    hv hva (hαr l ⟨le_rfl,hlr⟩).1
    (hm.monotoneOn ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩ hlr)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
