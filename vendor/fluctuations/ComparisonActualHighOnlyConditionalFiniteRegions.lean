module

public import ComparisonActualHighOnlyConditionalLowRegionError
public import ComparisonActualHighOnlyLocalCapAssembly

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable {a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

abbrev ConditionalHighOrdinaryDyad (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock):=
  {j:comparisonMassDyadicIndices a.data.U // 2*a.data.s < a.data.U*(2:ℝ)^(j:ℕ)}

def Potential.conditionalHighOrdinaryUnion (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)):Set ℝ:=
  ⋃j:ConditionalHighOrdinaryDyad a,P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val

def Potential.conditionalInitialSmallCapUnion (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)):Set ℝ:=
  ⋃t:{t:F // (P.capFamily F t).left=0 ∧ a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s},
    Ioo (P.capFamily F t.val).left (P.capFamily F t.val).right

theorem Potential.conditionalHighOrdinaryUnion_measurable (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)):
    MeasurableSet (P.conditionalHighOrdinaryUnion F):=
  MeasurableSet.iUnion (fun j=>P.ordinaryGroup_measurable _ _ _ _)

theorem Potential.conditionalInitialSmallCapUnion_measurable (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)):
    MeasurableSet (P.conditionalInitialSmallCapUnion F):=
  MeasurableSet.iUnion (fun _=>measurableSet_Ioo)

theorem Potential.conditional_contact_region_cover_U_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (hsU:a.data.s < a.data.U) :
    Ioo (0:ℝ) 1∩P.contactSet⊆a.conditionalLowRadiusRegion (min (16*a.data.U) 1)∪P.conditionalHighOrdinaryUnion F := by
  intro r hr
  have H:=P.conditional_contact_region_dichotomy (P.capFamily F) (Ioo (0:ℝ) 1) hr.1 hr.2
  rcases H with H|H|⟨j,hj,hrj⟩
  · exact Or.inl ⟨hr.1,H.2⟩
  · exact False.elim (hsU.not_ge H.1)
  · exact Or.inr (mem_iUnion.mpr ⟨⟨j,hj⟩,hrj⟩)

theorem Potential.conditional_contact_region_cover_wall_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (hUs:a.data.U ≤ a.data.s) :
    Ioo (0:ℝ) 1∩P.contactSet⊆(P.conditionalWallSupport F∪P.conditionalHighOrdinaryUnion F)∪
      {r|a.alpha.val.val r=min (32*a.data.s) 1} := by
  intro r hr
  have H:=P.conditional_contact_region_dichotomy (P.capFamily F) (Ioo (0:ℝ) 1) hr.1 hr.2
  rcases H with H|H|⟨j,hj,hrj⟩
  · exact False.elim (H.1.not_ge hUs)
  · by_cases he:a.alpha.val.val r=min (32*a.data.s) 1
    · exact Or.inr he
    · exact Or.inl (Or.inl (P.conditional_wall_contact_mem_high_only F hr.1 hr.2 H.2 he))
  · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨j,hj⟩,hrj⟩))

theorem Potential.conditional_comparable_region_cover_U_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (hsU:a.data.s < a.data.U) :
    relevantComparableCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)⊆
      a.conditionalLowRadiusRegion (min (16*a.data.U) 1)∪P.conditionalHighOrdinaryUnion F := by
  intro r hr
  obtain ⟨i,hi⟩:=mem_iUnion.mp hr
  have hrI:r∈Ioo (0:ℝ) 1:=⟨(P.capFamily F i.val).hleft.trans_lt hi.1,hi.2.trans_le (P.capFamily F i.val).hright⟩
  have H:=P.conditional_comparable_region_dichotomy (P.capFamily F) (Ioo (0:ℝ) 1) i
  rcases H with H|H|⟨j,hj,hrj⟩
  · exact Or.inl ⟨hrI,(a.alpha.val.property.2 hi.2.le).trans H.2⟩
  · exact False.elim (hsU.not_ge H.1)
  · exact Or.inr (mem_iUnion.mpr ⟨⟨j,hj⟩,hrj hi⟩)

theorem Potential.conditional_comparable_region_cover_wall_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (hUs:a.data.U ≤ a.data.s) :
    relevantComparableCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)⊆
      P.conditionalWallSupport F∪P.conditionalHighOrdinaryUnion F := by
  intro r hr
  obtain ⟨i,hi⟩:=mem_iUnion.mp hr
  have H:=P.conditional_comparable_region_dichotomy (P.capFamily F) (Ioo (0:ℝ) 1) i
  rcases H with H|H|⟨j,hj,hrj⟩
  · exact False.elim (H.1.not_ge hUs)
  · exact Or.inl (P.conditional_wall_cap_mem_high_only F i.val H.2.1 H.2.2 hi)
  · exact Or.inr (mem_iUnion.mpr ⟨⟨j,hj⟩,hrj hi⟩)

theorem Potential.conditional_small_region_cover_U_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (hsU:a.data.s < a.data.U) :
    conditionalSmallCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)⊆a.conditionalLowRadiusRegion (min (16*a.data.U) 1) := by
  intro r hr
  obtain ⟨i,hi⟩:=mem_iUnion.mp hr
  have H:=conditional_small_cap_endpoint_le_U (P.capFamily F) (Ioo (0:ℝ) 1) hsU.le i
  refine ⟨⟨(P.capFamily F i.val).hleft.trans_lt hi.1,hi.2.trans_le (P.capFamily F i.val).hright⟩,?_⟩
  exact le_min ((a.alpha.val.property.2 hi.2.le).trans (H.trans (by have HU:=a.data.hU;linarith)))
    (a.alpha.val.property.1 _).2

theorem Potential.conditional_small_region_cover_wall_high_only (P:a.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (hUs:a.data.U ≤ a.data.s) :
    conditionalSmallCapUnion (P.capFamily F) (Ioo (0:ℝ) 1)⊆P.conditionalWallSupport F∪P.conditionalInitialSmallCapUnion F := by
  intro r hr
  obtain ⟨i,hi⟩:=mem_iUnion.mp hr
  have H:=conditional_small_cap_endpoint_le_wall (P.capFamily F) (Ioo (0:ℝ) 1) hUs i
  by_cases hleft:(P.capFamily F i.val).left=0
  · exact Or.inr (mem_iUnion.mpr ⟨⟨i.val,hleft,H⟩,hi⟩)
  · have hlpos:0 < (P.capFamily F i.val).left:=lt_of_le_of_ne (P.capFamily F i.val).hleft
      (fun hh=>hleft hh.symm)
    have Hupper:a.alpha.val.val (P.capFamily F i.val).right ≤ min (32*a.data.s) 1:=
      le_min (H.trans (by have HS:=a.data.hs.1;linarith)) (a.alpha.val.property.1 _).2
    exact Or.inl (P.conditional_wall_cap_mem_high_only F i.val hlpos Hupper hi)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
