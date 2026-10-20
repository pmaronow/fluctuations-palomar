module

public import ComparisonActualHighWallCriticalBroadSliceIndex
public import ComparisonActualHighWallOrdinaryGroupData
public import ComparisonShiftedNativeRadiusWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}

namespace CriticalWholeCapBroadSampler
variable {cap : ShiftedCapInterval a P}
theorem actual_cover_ae (f : CriticalWholeCapBroadSampler cap) :
    ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),a.shiftedNativeModel.R u∈Ioo cap.left cap.right →
      u ≤ min (8*a.criticalMassCoverBase) 1 ∨∃i:Fin f.count,a.shiftedNativeModel.R u∈f.slice i := by
  let m:=a.shiftedNativeModel
  have hfinite : (Set.range (fun i:Fin f.count=>f.node (i.val+1))).Countable:=
    (Set.finite_range _).countable
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    hfinite.ae_notMem (volume.restrict (Icc (0:ℝ) 1))] with u hu hcuts hcap
  have huHigh : u∈Icc a.data.s 1:=⟨(m.R_high_mass (cap.hleft.trans_lt hcap.1)).le,hu.2⟩
  have hr:=m.R_bounds u
  have hs:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property
  have hA:=hs ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩ hr hcap.1
  have hB:=hs hr ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩ hcap.2
  rw [m.R_spec huHigh] at hA hB
  by_cases hlow:u≤a.criticalMassCoverBase
  · exact Or.inl (le_min (by linarith [(criticalMassCoverBase_pos (a:=a))]) hu.2)
  · have hret : u∈Ioc (max (a.alpha.val.val cap.left) a.criticalMassCoverBase)
      (a.alpha.val.val cap.right):=⟨max_lt hA (lt_of_not_ge hlow),hB.le⟩
    obtain ⟨i,hi⟩:=nativeBroadSlice_cover a.criticalMassCoverBase
      (max (a.alpha.val.val cap.left) a.criticalMassCoverBase) (a.alpha.val.val cap.right) f.hgap hret
    refine Or.inr ⟨i,?_⟩
    exact (m.massSlice_quantile_mem (f.nodes_mem i).1 (f.nodes_mem i).2 hu).mpr
      ⟨hi.1,lt_of_le_of_ne hi.2 (fun he=>hcuts ⟨i,he.symm⟩)⟩
end CriticalWholeCapBroadSampler

abbrev CriticalRelevantComparableCap {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ):=
  {i:ι // (¬8*max (a.alpha.val.val (c i).left) a.criticalMassCoverBase<a.alpha.val.val (c i).right ∧
    8*a.criticalMassCoverBase<a.alpha.val.val (c i).right) ∧ (A∩Ioo (c i).left (c i).right).Nonempty}
abbrev criticalRelevantComparableCapUnion {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ): Set ℝ:=
  ⋃i:CriticalRelevantComparableCap c A,Ioo (c i.val).left (c i.val).right
abbrev CriticalRelevantBroadSlice {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ):=
  {p:ActualCriticalBroadSliceIndex c // (A∩actualCriticalBroadSlice c p).Nonempty}

theorem critical_local_finite_cap_cover_ae {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) :
    ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),
      a.shiftedNativeModel.R u∈A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet) →
      a.shiftedNativeModel.R u∈A∩P.contactSet ∨
      a.shiftedNativeModel.R u∈criticalRelevantComparableCapUnion c A ∨
      (∃p:CriticalRelevantBroadSlice c A,a.shiftedNativeModel.R u∈actualCriticalBroadSlice c p.val) ∨
      u ≤ min (8*a.criticalMassCoverBase) 1 := by
  let m:=a.shiftedNativeModel
  have hae : ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),∀i:CriticalBroadCapIndex c,
      m.R u∈Ioo (c i.val).left (c i.val).right →
        u ≤ min (8*a.criticalMassCoverBase) 1 ∨∃j,m.R u∈(actualCriticalBroadCapSampler c i).slice j:=
    ae_all_iff.mpr (fun i=>(actualCriticalBroadCapSampler c i).actual_cover_ae)
  filter_upwards [ae_restrict_mem measurableSet_Icc,hae] with u hu hcover hfull
  rcases hfull.2 with hcap|hcontact
  · obtain ⟨i,hi⟩:=mem_iUnion.mp hcap
    by_cases hb : 8*max (a.alpha.val.val (c i).left) a.criticalMassCoverBase<a.alpha.val.val (c i).right
    · rcases hcover ⟨i,hb⟩ hi with hl|⟨j,hj⟩
      · exact Or.inr (Or.inr (Or.inr hl))
      · exact Or.inr (Or.inr (Or.inl ⟨⟨⟨⟨i,hb⟩,j⟩,⟨m.R u,hfull.1,hj⟩⟩,hj⟩))
    · by_cases hsmall:a.alpha.val.val (c i).right≤8*a.criticalMassCoverBase
      · have huHigh : u∈Icc a.data.s 1:=⟨(m.R_high_mass ((c i).hleft.trans_lt hi.1)).le,hu.2⟩
        have hr:=m.R_bounds u
        have hz:=(inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property)
          hr ⟨(c i).hleft.trans (c i).hlt.le,(c i).hright⟩ hi.2
        rw [m.R_spec huHigh] at hz
        exact Or.inr (Or.inr (Or.inr (le_min (hz.le.trans hsmall) hu.2)))
      · exact Or.inr (Or.inl (mem_iUnion.mpr
          ⟨⟨i,⟨hb,lt_of_not_ge hsmall⟩,⟨m.R u,hfull.1,hi⟩⟩,hi⟩))
  · exact Or.inl ⟨hfull.1,hcontact⟩

abbrev CriticalCompleteMassDyad (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (lo hi : ℝ):=
  {j:comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E) // lo/16≤(comparisonSmallMass a.data.N a.data.E)*(2:ℝ)^(j.val:ℕ) ∧
    (comparisonSmallMass a.data.N a.data.E)*(2:ℝ)^(j.val:ℕ)≤hi}

theorem critical_relevant_comparable_cap_dyadic_scale {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {lo hi : ℝ}
    (hA : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi)
    (i : CriticalRelevantComparableCap c A) :
    ∃j:CriticalCompleteMassDyad a lo hi,
      (comparisonSmallMass a.data.N a.data.E)*(2:ℝ)^(j.val:ℕ)≤a.alpha.val.val (c i.val).left ∧
      a.alpha.val.val (c i.val).right ≤ min (16*((comparisonSmallMass a.data.N a.data.E)*(2:ℝ)^(j.val:ℕ))) 1 := by
  obtain ⟨r,hrA,hr⟩:=i.property.2
  have hp:=hA r hrA
  have hl:=a.alpha.val.property.2 hr.1.le
  have hz:=a.alpha.val.property.2 hr.2.le
  have hco:=le_of_not_gt i.property.1.1
  have hbase : a.criticalMassCoverBase≤a.alpha.val.val (c i.val).left:=by
    by_contra hh
    rw [max_eq_right (le_of_not_ge hh)] at hco
    exact i.property.1.2.not_ge hco
  have hUA:=(le_max_left (comparisonSmallMass a.data.N a.data.E) (8*a.data.s)).trans hbase
  rw [max_eq_left hbase] at hco
  obtain ⟨j,hj,hj'⟩:=comparison_mass_dyadic_cover a.data.hU hUA (a.alpha.val.property.1 _).2
  refine ⟨⟨j,?_,hj.trans (hl.trans hp.2)⟩,hj,?_⟩
  · linarith [hp.1]
  · exact le_min (by linarith) (a.alpha.val.property.1 _).2

theorem critical_relevant_broad_slice_scale_bounds {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {lo hi : ℝ}
    (hA : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi)
    (p : CriticalRelevantBroadSlice c A) : lo/4≤actualCriticalBroadSliceScale c p.val ∧ actualCriticalBroadSliceScale c p.val≤2*hi := by
  obtain ⟨r,hrA,hr⟩:=p.property
  let f:=actualCriticalBroadCapSampler c p.val.1
  let i:=p.val.2
  have hg:=f.geometry i
  have hn:=f.nodes_mem i
  have hm:=a.shiftedNativeModel.massSlice_profile_mem hn.1 hn.2 hr
  have ha:=hA r hrA
  change lo/4≤f.scale i ∧ f.scale i≤2*hi
  constructor <;> linarith [hg.2.2.1,hg.2.2.2.1,hm.1,hm.2]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
