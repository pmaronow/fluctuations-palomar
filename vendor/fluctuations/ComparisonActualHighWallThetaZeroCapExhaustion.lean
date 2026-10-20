module

public import ComparisonActualHighWallThetaZeroCapFamily
public import ComparisonShiftedNativeThermalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.cap_contact_thermal_exhaustion
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃F : ℕ→Finset (ordConnectedSection P.negativeSet),Monotone F ∧
      (∀t : ordConnectedSection P.negativeSet,∃j,t∈F j) ∧
      Tendsto (fun j=>∫u in 0..1,
        (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) atTop
        (𝓝 (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)) := by
  have hH : ContinuousOn P.H (Icc Q.data.rmin 1):=by
    simpa only [uIcc_of_le Q.data.hr] using P.hH.continuousOn
  obtain ⟨F,hF,hcover,hlim⟩:=Q.shiftedNativeModel.cap_thermal_exhaustion P.negativeSet_open
    P.negativeSet_subset P.H hH A hA
  have hfixed j u :
      (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left P.negativeSet (F j))
        (NativeCapExhaustion.right P.negativeSet (F j)) P.H).indicator (fun _=>(1:ℝ))
          (Q.shiftedNativeModel.R u)=
      (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
        (fun _=>(1:ℝ)) (Q.shiftedNativeModel.R u):=by
    rw [NativeCapExhaustion.fixedSupport_eq P.negativeSet_open P.negativeSet_subset,
      P.capFamily_union (F j)]
    have hr:=Q.shiftedNativeModel.R_bounds u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  have hfull u :
      (A∩(P.negativeSet∪{r | P.H r=0})).indicator (fun _=>(1:ℝ)) (Q.shiftedNativeModel.R u)=
      (A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>(1:ℝ)) (Q.shiftedNativeModel.R u):=by
    have hr:=Q.shiftedNativeModel.R_bounds u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  simp_rw [hfixed,hfull] at hlim
  exact ⟨F,hF,hcover,hlim⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
