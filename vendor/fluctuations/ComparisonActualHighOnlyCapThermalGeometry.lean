module

public import ComparisonActualHighOnlyAllCapMismatch
public import ComparisonShiftedNativeThermalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.capFamily
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (t : F) :
    ShiftedCapInterval a P where
  left:=NativeCapExhaustion.left P.negativeSet F t
  right:=NativeCapExhaustion.right P.negativeSet F t
  hleft:=(NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).1 t |>.1
  hlt:=(NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).1 t |>.2.1
  hright:=(NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).1 t |>.2.2
  negative:=by
    intro r hr
    have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
      (ordConnectedSection_subset t.val.property)
    exact (ordConnectedComponent_subset (HH.2.2.2.2.1.symm ▸ hr)).2

theorem Potential.capFamily_union
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) :
    (⋃t : F,Ioo (P.capFamily F t).left (P.capFamily F t).right)=wholeCapFiniteUnion P.negativeSet F := by
  ext r
  constructor
  · intro hr
    obtain ⟨t,ht⟩:=mem_iUnion.mp hr
    have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
      (ordConnectedSection_subset t.val.property)
    exact mem_iUnion₂.mpr ⟨t.val,t.property,HH.2.2.2.2.1.symm ▸ ht⟩
  · intro hr
    obtain ⟨t,ht,hr⟩:=mem_iUnion₂.mp hr
    have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
      (ordConnectedSection_subset t.property)
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,HH.2.2.2.2.1 ▸ hr⟩

theorem Potential.capFamily_disjoint
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) :
    Pairwise (fun s t : F=>Disjoint (Ioo (P.capFamily F s).left (P.capFamily F s).right)
      (Ioo (P.capFamily F t).left (P.capFamily F t).right)) :=
  (NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).2

theorem Potential.capFamily_contacts
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (t : F) :
    (P.H (P.capFamily F t).left=0 ∨ (P.capFamily F t).left=(0:ℝ)) ∧
      (P.H (P.capFamily F t).right=0 ∨ (P.capFamily F t).right=1) := by
  obtain ⟨c,hl,hr,_,hcases⟩:=P.negative_component_endpoints
    (ordConnectedSection_subset t.val.property)
  change (P.H (sInf _)=0 ∨ sInf _=(0:ℝ)) ∧ (P.H (sSup _)=0 ∨ sSup _=1)
  simpa only [hl,hr] using hcases

theorem Potential.cap_contact_thermal_exhaustion
    {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃F : ℕ→Finset (ordConnectedSection P.negativeSet),Monotone F ∧
      (∀t : ordConnectedSection P.negativeSet,∃j,t∈F j) ∧
      Tendsto (fun j=>∫u in 0..1,
        (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) atTop
        (𝓝 (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)) := by
  have hH : ContinuousOn P.H (Icc (0:ℝ) 1):=by
    simpa only [uIcc_of_le zero_le_one] using P.hH.continuousOn
  obtain ⟨F,hF,hcover,hlim⟩:=a.shiftedNativeModel.cap_thermal_exhaustion P.negativeSet_open
    P.negativeSet_subset P.H hH A hA
  have hfixed j u :
      (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left P.negativeSet (F j))
        (NativeCapExhaustion.right P.negativeSet (F j)) P.H).indicator (fun _=>(1:ℝ))
          (a.shiftedNativeModel.R u)=
      (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
        (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u):=by
    rw [NativeCapExhaustion.fixedSupport_eq P.negativeSet_open P.negativeSet_subset,
      P.capFamily_union (F j)]
    have hr:=a.shiftedNativeModel.R_bounds u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  have hfull u :
      (A∩(P.negativeSet∪{r | P.H r=0})).indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)=
      (A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u):=by
    have hr:=a.shiftedNativeModel.R_bounds u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  simp_rw [hfixed,hfull] at hlim
  exact ⟨F,hF,hcover,hlim⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
