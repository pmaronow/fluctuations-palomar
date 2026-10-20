module

public import ComparisonActualHighWallThetaZeroCapComponents

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

def Potential.capFamily
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (t : F) :
    ShiftedCapInterval Q P where
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
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet)) :
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
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet)) :
    Pairwise (fun s t : F=>Disjoint (Ioo (P.capFamily F s).left (P.capFamily F s).right)
      (Ioo (P.capFamily F t).left (P.capFamily F t).right)) :=
  (NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).2

theorem Potential.capFamily_contacts
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (t : F) :
    (P.H (P.capFamily F t).left=0 ∨ (P.capFamily F t).left=Q.data.rmin) ∧
      (P.H (P.capFamily F t).right=0 ∨ (P.capFamily F t).right=1) := by
  obtain ⟨c,hl,hr,_,hcases⟩:=P.negative_component_endpoints
    (ordConnectedSection_subset t.val.property)
  change (P.H (sInf _)=0 ∨ sInf _=Q.data.rmin) ∧ (P.H (sSup _)=0 ∨ sSup _=1)
  simpa only [hl,hr] using hcases

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
