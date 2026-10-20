module

public import ComparisonOriginalQEq7BroadFourPerScaleDirectDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

abbrev eq7InnerBroadDyadIndexDirect {ι : Type*}
    (c : ι → ShiftedCapInterval Q P)
    (p : Eq7InnerBroadSliceIndex c) : ℕ :=
  let f := eq7InnerBroadSampler c p.1
  if p.2.val=0 then f.k+1 else f.k+1+p.2.val

theorem eq7_inner_broad_scale_eq_dyad_direct_draft
    {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    (p : Eq7InnerBroadSliceIndex c) :
    (eq7InnerBroadSampler c p.1).scale p.2 =
      nativeDyadicMass Q.positiveOriginMassCoverBase
        (eq7InnerBroadDyadIndexDirect c p) := by
  simp only [PositiveOriginWholeCapBroadSampler.scale,
    nativeBroadSliceScale,eq7InnerBroadDyadIndexDirect]
  split_ifs <;> rfl

theorem eq7_inner_broad_scale_le_one_direct_draft
    {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    (p : Eq7InnerBroadSliceIndex c) :
    (eq7InnerBroadSampler c p.1).scale p.2 ≤ 1 := by
  have hg := (eq7InnerBroadSampler c p.1).geometry p.2
  have hn := (eq7InnerBroadSampler c p.1).nodes_mem p.2
  linarith [hg.2.1,hn.1.1,hn.2.2]

theorem eq7_inner_broad_dyad_log_bound_direct_draft
    {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    (p : Eq7InnerBroadSliceIndex c) :
    (eq7InnerBroadDyadIndexDirect c p:ℝ)*Real.log 2 ≤
      Real.log (1/Q.positiveOriginMassCoverBase) := by
  have hh := Real.log_le_log
    ((positiveOriginMassCoverBase_pos (a:=Q)).trans_le
      ((eq7InnerBroadSampler c p.1).contracts p.2).1)
      (eq7_inner_broad_scale_le_one_direct_draft c p)
  change Real.log ((eq7InnerBroadSampler c p.1).scale p.2) ≤
    Real.log 1 at hh
  rw [eq7_inner_broad_scale_eq_dyad_direct_draft c p,nativeDyadicMass,
    Real.log_mul (positiveOriginMassCoverBase_pos (a:=Q)).ne'
      (pow_ne_zero _ (by norm_num)),Real.log_pow,Real.log_one] at hh
  rw [Real.log_div (by norm_num : (1:ℝ)≠0)
    (positiveOriginMassCoverBase_pos (a:=Q)).ne',Real.log_one,zero_sub]
  linarith

theorem eq7_inner_broad_dyad_card_le_four_direct_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right))) (k : ℕ) :
    (Finset.univ.filter (fun p : Eq7InnerBroadSliceIndex c =>
      eq7InnerBroadDyadIndexDirect c p=k)).card ≤ 4 := by
  have hs : (Finset.univ.filter (fun p : Eq7InnerBroadSliceIndex c =>
        eq7InnerBroadDyadIndexDirect c p=k)) ⊆
      (Finset.univ.filter (fun p : Eq7InnerBroadSliceIndex c =>
        (eq7InnerBroadSampler c p.1).scale p.2 =
          nativeDyadicMass Q.positiveOriginMassCoverBase k)) := by
    intro p hp
    obtain ⟨hpu,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpu,by
      rw [eq7_inner_broad_scale_eq_dyad_direct_draft c p,hp]⟩
  exact (Finset.card_le_card hs).trans
    ((eq7_inner_broad_four_per_scale_direct_draft c hd)
      (nativeDyadicMass Q.positiveOriginMassCoverBase k)
      (nativeDyadicMass_pos (positiveOriginMassCoverBase_pos (a:=Q)) k)
      ((show Q.data.s ≤ Q.positiveOriginMassCoverBase from
        le_max_right _ _).trans
        (nativeDyadicMass_ge_base
          (positiveOriginMassCoverBase_pos (a:=Q)).le k)))

theorem eq7_inner_broad_dyad_le_log_ceil_direct_draft
    {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    (p : Eq7InnerBroadSliceIndex c) :
    eq7InnerBroadDyadIndexDirect c p ≤
      Nat.ceil (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hh := (le_div_iff₀ hlog).mpr
    (eq7_inner_broad_dyad_log_bound_direct_draft c p)
  have hc := hh.trans
    (Nat.le_ceil (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2))
  exact_mod_cast hc

theorem eq7_inner_broad_slice_card_le_base_log_direct_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right))) :
    Fintype.card (Eq7InnerBroadSliceIndex c) ≤
      4*(Nat.ceil
        (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2)+1) := by
  let K := Nat.ceil
    (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2)
  let units := fun k => Finset.univ.filter
    (fun p : Eq7InnerBroadSliceIndex c =>
      eq7InnerBroadDyadIndexDirect c p=k)
  have hcover : (Finset.univ : Finset (Eq7InnerBroadSliceIndex c)) ⊆
      (Finset.range (K+1)).biUnion units := by
    intro p hp
    apply Finset.mem_biUnion.mpr
    refine ⟨eq7InnerBroadDyadIndexDirect c p,
      Finset.mem_range.mpr ?_,?_⟩
    · exact Nat.lt_succ_of_le
        (eq7_inner_broad_dyad_le_log_ceil_direct_draft c p)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have hc := (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le_card_mul (Finset.range (K+1)) units 4
      (fun k _ => eq7_inner_broad_dyad_card_le_four_direct_draft c hd k))
  simpa only [Finset.card_univ,Finset.card_range,mul_comm,K] using hc

theorem eq7_inner_relevant_broad_slice_card_le_base_log_direct_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P) (h : ℝ)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right))) :
    Fintype.card (Eq7InnerRelevantBroadSlice c h) ≤
      4*(Nat.ceil
        (Real.log (1/Q.positiveOriginMassCoverBase)/Real.log 2)+1) := by
  exact (Fintype.card_le_of_injective Subtype.val
    Subtype.val_injective).trans
      (eq7_inner_broad_slice_card_le_base_log_direct_draft c hd)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
