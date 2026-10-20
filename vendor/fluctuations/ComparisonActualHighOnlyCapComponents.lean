module

public import ComparisonActualHighOnlyContactGeometry
public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.negativeSet
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : Set ℝ:=Ioo (0:ℝ) 1∩P.H ⁻¹' Iio 0

def Potential.contactSet
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : Set ℝ:=Icc (0:ℝ) 1∩P.H ⁻¹' {0}

theorem Potential.negativeSet_open
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : IsOpen P.negativeSet := by
  have hc : ContinuousOn P.H (Icc (0:ℝ) 1):=by
    simpa only [uIcc_of_le zero_le_one] using P.hH.continuousOn
  exact (hc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem Potential.negativeSet_subset
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : P.negativeSet⊆Icc (0:ℝ) 1 :=
  inter_subset_left.trans Ioo_subset_Icc_self

theorem Potential.contactSet_measurable
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : MeasurableSet P.contactSet := by
  have hc : ContinuousOn P.H (Icc (0:ℝ) 1):=by
    simpa only [uIcc_of_le zero_le_one] using P.hH.continuousOn
  exact (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet

structure ShiftedCapInterval
    (a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock)
    (P : a.Potential) where
  left : ℝ
  right : ℝ
  hleft : (0:ℝ)≤ left
  hlt : left< right
  hright : right≤1
  negative : ∀r∈Ioo left right,P.H r<0

theorem Potential.negative_component_endpoints
    {a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {r : ℝ} (hr : r∈P.negativeSet) :
    let C:=ordConnectedComponent P.negativeSet r
    ∃c : ShiftedCapInterval a P,c.left=sInf C ∧ c.right=sSup C ∧ Ioo c.left c.right=C ∧
      (P.H c.left=0 ∨ c.left=(0:ℝ)) ∧ (P.H c.right=0 ∨ c.right=1) := by
  dsimp only
  let C:=ordConnectedComponent P.negativeSet r
  have hp:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset hr
  have hC : C=Ioo (sInf C) (sSup C):=hp.2.2.2.2.1
  have hnon : C.Nonempty:=nonempty_ordConnectedComponent.mpr hr
  have hsub : C⊆Icc (0:ℝ) 1:=ordConnectedComponent_subset.trans P.negativeSet_subset
  have hc : ContinuousOn P.H (Icc (0:ℝ) 1):=by
    simpa only [uIcc_of_le zero_le_one] using P.hH.continuousOn
  have hclosed : IsClosed (Icc (0:ℝ) 1∩P.H ⁻¹' Iic 0):=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hCsub : C⊆Icc (0:ℝ) 1∩P.H ⁻¹' Iic 0:=by
    intro t ht
    have H : P.H t<0:=(ordConnectedComponent_subset ht).2
    exact ⟨hsub ht,H.le⟩
  have hlo : BddBelow C:=⟨(0:ℝ),fun t ht=>(hsub ht).1⟩
  have hhi : BddAbove C:=⟨1,fun t ht=>(hsub ht).2⟩
  have hleft0 : P.H (sInf C)≤0:=
    (hclosed.closure_subset_iff.mpr hCsub (csInf_mem_closure hnon hlo)).2
  have hright0 : P.H (sSup C)≤0:=
    (hclosed.closure_subset_iff.mpr hCsub (csSup_mem_closure hnon hhi)).2
  have hleft : P.H (sInf C)=0 ∨ sInf C=(0:ℝ):=by
    by_cases hl:sInf C=(0:ℝ)
    · exact Or.inr hl
    · apply Or.inl
      apply le_antisymm hleft0
      by_contra hbad
      have ht : sInf C∈P.negativeSet:=
        ⟨⟨lt_of_le_of_ne hp.1 (fun he=>hl he.symm),
          (hp.2.1.trans hp.2.2.1).trans_le hp.2.2.2.1⟩,lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.1 ht
  have hright : P.H (sSup C)=0 ∨ sSup C=1:=by
    by_cases hz:sSup C=1
    · exact Or.inr hz
    · apply Or.inl
      apply le_antisymm hright0
      by_contra hbad
      have ht : sSup C∈P.negativeSet:=
        ⟨⟨hp.1.trans_lt (hp.2.1.trans hp.2.2.1),lt_of_le_of_ne hp.2.2.2.1 hz⟩,lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.2 ht
  let c : ShiftedCapInterval a P:={
    left:=sInf C
    right:=sSup C
    hleft:=hp.1
    hlt:=hp.2.1.trans hp.2.2.1
    hright:=hp.2.2.2.1
    negative:=fun t ht=>(ordConnectedComponent_subset (hC.symm ▸ ht)).2 }
  exact ⟨c,rfl,rfl,hC.symm,hleft,hright⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
