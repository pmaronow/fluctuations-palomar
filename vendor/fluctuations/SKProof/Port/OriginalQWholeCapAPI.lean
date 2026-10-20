module

public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.Port.ComparisonActualOriginalQBroadSliceIndex
public import ComparisonActualHighWallThetaZeroWholeCapCoverPositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}

abbrev massCoverBase (a : ActualThetaZeroOverlapMinimum
    (n+1) margin delta cl cu Az C0 Ct D Bclock) : ℝ := a.positiveOriginMassCoverBase

theorem massCoverBase_pos : 0 < a.massCoverBase := positiveOriginMassCoverBase_pos

abbrev RelevantComparableCap {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ):=
  {i:ι // (¬8*max (a.alpha.val.val (c i).left) a.massCoverBase<a.alpha.val.val (c i).right ∧
    8*a.massCoverBase<a.alpha.val.val (c i).right) ∧ (A∩Ioo (c i).left (c i).right).Nonempty}
abbrev relevantComparableCapUnion {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ): Set ℝ:=
  ⋃i:RelevantComparableCap c A,Ioo (c i.val).left (c i.val).right
abbrev RelevantBroadSlice {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ):=
  {p:ActualBroadSliceIndex c // (A∩actualBroadSlice c p).Nonempty}

theorem local_finite_cap_cover_ae {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) :
    ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),
      a.shiftedNativeModel.R u∈A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet) →
      a.shiftedNativeModel.R u∈A∩P.contactSet ∨
      a.shiftedNativeModel.R u∈relevantComparableCapUnion c A ∨
      (∃p:RelevantBroadSlice c A,a.shiftedNativeModel.R u∈actualBroadSlice c p.val) ∨
      u ≤ min (8*a.massCoverBase) 1 := by
  let m:=a.shiftedNativeModel
  have hae : ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),∀i:BroadCapIndex c,
      m.R u∈Ioo (c i.val).left (c i.val).right →
        u ≤ min a.massCoverBase 1 ∨∃j,m.R u∈(actualBroadCapSampler c i).slice j:=
    ae_all_iff.mpr (fun i=>(actualBroadCapSampler c i).actual_cover_ae)
  filter_upwards [ae_restrict_mem measurableSet_Icc,hae] with u hu hcover hfull
  rcases hfull.2 with hcap|hcontact
  · obtain ⟨i,hi⟩:=mem_iUnion.mp hcap
    by_cases hb : 8*max (a.alpha.val.val (c i).left) a.massCoverBase<a.alpha.val.val (c i).right
    · rcases hcover ⟨i,hb⟩ hi with hl|⟨j,hj⟩
      · exact Or.inr (Or.inr (Or.inr (hl.trans (min_le_min (by
          have hp : 0 < a.massCoverBase := massCoverBase_pos
          linarith) le_rfl))))
      · exact Or.inr (Or.inr (Or.inl ⟨⟨⟨⟨i,hb⟩,j⟩,⟨m.R u,hfull.1,hj⟩⟩,hj⟩))
    · by_cases hsmall:a.alpha.val.val (c i).right≤8*a.massCoverBase
      · have huHigh : u∈Icc a.data.s 1:=⟨(m.R_high_mass ((c i).hleft.trans_lt hi.1)).le,hu.2⟩
        have hr:=m.R_bounds u
        have hz:=(inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property)
          hr ⟨(c i).hleft.trans (c i).hlt.le,(c i).hright⟩ hi.2
        rw [m.R_spec huHigh] at hz
        exact Or.inr (Or.inr (Or.inr (le_min (hz.le.trans hsmall) hu.2)))
      · exact Or.inr (Or.inl (mem_iUnion.mpr
          ⟨⟨i,⟨hb,lt_of_not_ge hsmall⟩,⟨m.R u,hfull.1,hi⟩⟩,hi⟩))
  · exact Or.inl ⟨hfull.1,hcontact⟩

abbrev LocalCompleteMassDyad (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (lo hi : ℝ):=
  {j:comparisonMassDyadicIndices a.data.U // lo/16≤a.data.U*(2:ℝ)^(j.val:ℕ) ∧
    a.data.U*(2:ℝ)^(j.val:ℕ)≤hi}

theorem relevant_comparable_cap_dyadic_scale {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {lo hi : ℝ}
    (hA : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi)
    (i : RelevantComparableCap c A) :
    ∃j:LocalCompleteMassDyad a lo hi,
      a.data.U*(2:ℝ)^(j.val:ℕ)≤a.alpha.val.val (c i.val).left ∧
      a.alpha.val.val (c i.val).right ≤ min (16*(a.data.U*(2:ℝ)^(j.val:ℕ))) 1 := by
  obtain ⟨r,hrA,hr⟩:=i.property.2
  have hp:=hA r hrA
  have hl:=a.alpha.val.property.2 hr.1.le
  have hz:=a.alpha.val.property.2 hr.2.le
  have hco:=le_of_not_gt i.property.1.1
  have hbase : a.massCoverBase≤a.alpha.val.val (c i.val).left:=by
    by_contra hh
    rw [max_eq_right (le_of_not_ge hh)] at hco
    exact i.property.1.2.not_ge hco
  have hUA:=(le_max_left a.data.U a.data.s).trans hbase
  rw [max_eq_left hbase] at hco
  obtain ⟨j,hj,hj'⟩:=comparison_mass_dyadic_cover a.data.hU hUA (a.alpha.val.property.1 _).2
  refine ⟨⟨j,?_,hj.trans (hl.trans hp.2)⟩,hj,?_⟩
  · linarith [hp.1]
  · exact le_min (by linarith) (a.alpha.val.property.1 _).2

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
