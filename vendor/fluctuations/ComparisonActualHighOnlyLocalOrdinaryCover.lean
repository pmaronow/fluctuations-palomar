module

public import ComparisonActualHighOnlyWholeCapCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.relevant_comparable_mem_ordinary_group (P : a.Potential)
    {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P) (A : Set ℝ) {lo hi : ℝ}
    (hA : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi) :
    relevantComparableCapUnion c A⊆⋃j:LocalCompleteMassDyad a lo hi,P.ordinaryGroup c A 16 j.val := by
  intro r hr
  obtain ⟨i,hi⟩:=mem_iUnion.mp hr
  obtain ⟨j,hjl,hjr⟩:=relevant_comparable_cap_dyadic_scale c A hA i
  exact mem_iUnion.mpr ⟨j,Or.inr (mem_iUnion.mpr ⟨⟨i.val,i.property.2,hjl,hjr⟩,hi⟩)⟩

theorem Potential.contact_mem_ordinary_group (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) (hAD : A⊆Ioo (0:ℝ) 1)
    {lo hi : ℝ} (hU : a.data.U≤lo) (hstart : 32*a.data.s<lo)
    (hA : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi) :
    A∩P.contactSet⊆⋃j:LocalCompleteMassDyad a lo hi,P.ordinaryGroup c A 16 j.val := by
  intro r hr
  let m:=a.shiftedNativeModel
  have hrI:=hAD hr.1
  have hm:=hA r hr.1
  have hmI : a.alpha.val.val r∈Icc a.data.s 1:=
    (inverseConstraintMap a.alpha (⟨r,Ioo_subset_Icc_self hrI⟩)).property
  have hm1 : a.alpha.val.val r<1:=by
    have H:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property
      (Ioo_subset_Icc_self hrI) ⟨by norm_num,le_rfl⟩ hrI.2
    simpa only [a.alpha.property.2.1] using H
  obtain ⟨j,hj,hjNext⟩:=comparison_mass_dyadic_cover a.data.hU (hU.trans hm.1)
    (a.alpha.val.property.1 r).2
  let v:=a.data.U*(2:ℝ)^(j:ℕ)
  have hv:=(comparison_mass_dyadic_scale a.data.hU j).1
  have hjlo : lo/16≤v:=by dsimp only [v];linarith
  have hvHigh : a.data.s<v/2:=by dsimp only [v] at *;linarith
  have hmin : a.alpha.val.val r < min (16*v) 1:=lt_min
    (by dsimp only [v] at *;linarith) hm1
  have hloHigh : v/2∈Icc a.data.s 1:=⟨hvHigh.le,by
    have HH:=(comparison_mass_dyadic_scale a.data.hU j).2.2
    dsimp only [v];linarith⟩
  have hhiHigh : min (16*v) 1∈Icc a.data.s 1:=⟨hmI.1.trans hmin.le,min_le_right _ _⟩
  have hLow:=m.R_strictMonoOn hloHigh hmI
    (show v/2<a.alpha.val.val r by dsimp only [v] at *;linarith)
  have hHigh:=m.R_strictMonoOn hmI hhiHigh hmin
  rw [m.R_inverse (Ioo_subset_Icc_self hrI)] at hLow hHigh
  exact mem_iUnion.mpr ⟨⟨j,hjlo,hj.trans hm.2⟩,Or.inl ⟨hr.2,⟨hLow,hHigh⟩⟩⟩

theorem local_complete_mass_dyad_card_le_log (lo hi : ℝ) :
    Fintype.card (LocalCompleteMassDyad a lo hi)≤Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1 := by
  have hs : Fintype.card (LocalCompleteMassDyad a lo hi)≤Fintype.card (comparisonMassDyadicIndices a.data.U):=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hi : (comparisonMassDyadicIndices a.data.U).card≤Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1:=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  exact hs.trans (by simpa only [Fintype.card_coe] using hi)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
