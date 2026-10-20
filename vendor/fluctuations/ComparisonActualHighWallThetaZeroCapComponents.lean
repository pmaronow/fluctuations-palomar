module

public import ComparisonActualHighWallThetaZeroCapDensity
public import ComparisonNativeWholeCapDyadicCover

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

def Potential.negativeSet
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) : Set ℝ:=Ioo Q.data.rmin 1∩P.H ⁻¹' Iio 0

def Potential.contactSet
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) : Set ℝ:=Icc Q.data.rmin 1∩P.H ⁻¹' {0}

theorem Potential.negativeSet_open
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) : IsOpen P.negativeSet := by
  have hc : ContinuousOn P.H (Icc Q.data.rmin 1):=by
    simpa only [uIcc_of_le Q.data.hr] using P.hH.continuousOn
  exact (hc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem Potential.negativeSet_subset
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) : P.negativeSet⊆Icc Q.data.rmin 1 :=
  inter_subset_left.trans Ioo_subset_Icc_self

theorem Potential.contactSet_measurable
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) : MeasurableSet P.contactSet := by
  have hc : ContinuousOn P.H (Icc Q.data.rmin 1):=by
    simpa only [uIcc_of_le Q.data.hr] using P.hH.continuousOn
  exact (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet

structure ShiftedCapInterval
    (Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (P : Q.Potential) where
  left : ℝ
  right : ℝ
  hleft : Q.data.rmin≤ left
  hlt : left< right
  hright : right≤1
  negative : ∀r∈Ioo left right,P.H r<0

theorem Potential.negative_component_endpoints
    {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) {r : ℝ} (hr : r∈P.negativeSet) :
    let C:=ordConnectedComponent P.negativeSet r
    ∃c : ShiftedCapInterval Q P,c.left=sInf C ∧ c.right=sSup C ∧ Ioo c.left c.right=C ∧
      (P.H c.left=0 ∨ c.left=Q.data.rmin) ∧ (P.H c.right=0 ∨ c.right=1) := by
  dsimp only
  let C:=ordConnectedComponent P.negativeSet r
  have hp:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset hr
  have hC : C=Ioo (sInf C) (sSup C):=hp.2.2.2.2.1
  have hnon : C.Nonempty:=nonempty_ordConnectedComponent.mpr hr
  have hsub : C⊆Icc Q.data.rmin 1:=ordConnectedComponent_subset.trans P.negativeSet_subset
  have hc : ContinuousOn P.H (Icc Q.data.rmin 1):=by
    simpa only [uIcc_of_le Q.data.hr] using P.hH.continuousOn
  have hclosed : IsClosed (Icc Q.data.rmin 1∩P.H ⁻¹' Iic 0):=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hCsub : C⊆Icc Q.data.rmin 1∩P.H ⁻¹' Iic 0:=by
    intro t ht
    have H : P.H t<0:=(ordConnectedComponent_subset ht).2
    exact ⟨hsub ht,H.le⟩
  have hlo : BddBelow C:=⟨Q.data.rmin,fun t ht=>(hsub ht).1⟩
  have hhi : BddAbove C:=⟨1,fun t ht=>(hsub ht).2⟩
  have hleft0 : P.H (sInf C)≤0:=
    (hclosed.closure_subset_iff.mpr hCsub (csInf_mem_closure hnon hlo)).2
  have hright0 : P.H (sSup C)≤0:=
    (hclosed.closure_subset_iff.mpr hCsub (csSup_mem_closure hnon hhi)).2
  have hleft : P.H (sInf C)=0 ∨ sInf C=Q.data.rmin:=by
    by_cases hl:sInf C=Q.data.rmin
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
  let c : ShiftedCapInterval Q P:={
    left:=sInf C
    right:=sSup C
    hleft:=hp.1
    hlt:=hp.2.1.trans hp.2.2.1
    hright:=hp.2.2.2.1
    negative:=fun t ht=>(ordConnectedComponent_subset (hC.symm ▸ ht)).2 }
  exact ⟨c,rfl,rfl,hC.symm,hleft,hright⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
