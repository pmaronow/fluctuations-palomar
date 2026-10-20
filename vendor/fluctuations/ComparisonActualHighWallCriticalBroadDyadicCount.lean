module

public import ComparisonActualHighWallCriticalBroadScaleCount

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
abbrev actualCriticalBroadDyadIndex {ι:Type*} (c:ι→ShiftedCapInterval a P)
    (p:ActualCriticalBroadSliceIndex c) : ℕ :=
  let f := actualCriticalBroadCapSampler c p.1
  if p.2.val=0 then f.k+1 else f.k+1+p.2.val

theorem actualCriticalBroadSliceScale_eq_dyad {ι:Type*} (c:ι→ShiftedCapInterval a P) (p:ActualCriticalBroadSliceIndex c) :
    actualCriticalBroadSliceScale c p=nativeDyadicMass a.criticalMassCoverBase (actualCriticalBroadDyadIndex c p) := by
  simp only [actualCriticalBroadSliceScale,CriticalWholeCapBroadSampler.scale,nativeBroadSliceScale,
    actualCriticalBroadDyadIndex]
  split_ifs <;> rfl

theorem actualCriticalBroadSliceScale_le_one {ι:Type*} (c:ι→ShiftedCapInterval a P) (p:ActualCriticalBroadSliceIndex c) :
    actualCriticalBroadSliceScale c p≤1 := by
  have hg := (actualCriticalBroadCapSampler c p.1).geometry p.2
  have hn := (actualCriticalBroadCapSampler c p.1).nodes_mem p.2
  linarith [hg.2.1,hn.1.1,hn.2.2]

theorem actualCriticalBroadDyadIndex_log_bound {ι:Type*} (c:ι→ShiftedCapInterval a P) (p:ActualCriticalBroadSliceIndex c) :
    (actualCriticalBroadDyadIndex c p:ℝ)*Real.log 2≤ Real.log (1/a.criticalMassCoverBase) := by
  have hh := Real.log_le_log ((criticalMassCoverBase_pos (a:=a)).trans_le
    ((actualCriticalBroadCapSampler c p.1).contracts p.2).1)
      (actualCriticalBroadSliceScale_le_one c p)
  change Real.log (actualCriticalBroadSliceScale c p)≤Real.log 1 at hh
  rw [actualCriticalBroadSliceScale_eq_dyad c p,nativeDyadicMass,
    Real.log_mul (criticalMassCoverBase_pos (a:=a)).ne' (pow_ne_zero _ (by norm_num)),Real.log_pow,Real.log_one] at hh
  rw [Real.log_div (by norm_num : (1:ℝ)≠0) (criticalMassCoverBase_pos (a:=a)).ne',Real.log_one,zero_sub]
  linarith

theorem actualCriticalBroadDyadIndex_card_le_four {ι:Type*} [Fintype ι]
    (c:ι→ShiftedCapInterval a P)
    (hd:Pairwise (fun i j=>Disjoint (Ioo (c i).left (c i).right) (Ioo (c j).left (c j).right))) (k:ℕ) :
    (Finset.univ.filter (fun p:ActualCriticalBroadSliceIndex c=>actualCriticalBroadDyadIndex c p=k)).card≤4 := by
  have hs : (Finset.univ.filter (fun p:ActualCriticalBroadSliceIndex c=>actualCriticalBroadDyadIndex c p=k))⊆
      (Finset.univ.filter (fun p:ActualCriticalBroadSliceIndex c=>actualCriticalBroadSliceScale c p=nativeDyadicMass a.criticalMassCoverBase k)) := by
    intro p hp
    obtain ⟨hpu,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpu,by rw [actualCriticalBroadSliceScale_eq_dyad c p,hp]⟩
  exact (Finset.card_le_card hs).trans
    (actualCriticalBroadSlice_common_scale_card_le_four c hd (nativeDyadicMass_pos (criticalMassCoverBase_pos (a:=a)) k)
      ((show a.data.s ≤ a.criticalMassCoverBase from (by linarith [a.data.hs.1] : a.data.s ≤ 8*a.data.s).trans (le_max_right _ _)).trans (nativeDyadicMass_ge_base (criticalMassCoverBase_pos (a:=a)).le k)))

theorem actualCriticalBroadDyadIndex_le_log_ceil {ι:Type*} (c:ι→ShiftedCapInterval a P) (p:ActualCriticalBroadSliceIndex c) :
    actualCriticalBroadDyadIndex c p≤ Nat.ceil (Real.log (1/a.criticalMassCoverBase)/Real.log 2) := by
  have hlog:0< Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hh := (le_div_iff₀ hlog).mpr (actualCriticalBroadDyadIndex_log_bound c p)
  have hc := hh.trans (Nat.le_ceil (Real.log (1/a.criticalMassCoverBase)/Real.log 2))
  exact_mod_cast hc

theorem actualCriticalBroadSlice_card_le_log_count {ι:Type*} [Fintype ι]
    (c:ι→ShiftedCapInterval a P)
    (hd:Pairwise (fun i j=>Disjoint (Ioo (c i).left (c i).right) (Ioo (c j).left (c j).right))) :
    Fintype.card (ActualCriticalBroadSliceIndex c)≤4*(Nat.ceil (Real.log (1/a.criticalMassCoverBase)/Real.log 2)+1) := by
  let K := Nat.ceil (Real.log (1/a.criticalMassCoverBase)/Real.log 2)
  let units := fun k=>Finset.univ.filter (fun p:ActualCriticalBroadSliceIndex c=>actualCriticalBroadDyadIndex c p=k)
  have hcover : (Finset.univ:Finset (ActualCriticalBroadSliceIndex c))⊆
      (Finset.range (K+1)).biUnion units := by
    intro p hp
    apply Finset.mem_biUnion.mpr
    refine ⟨actualCriticalBroadDyadIndex c p,Finset.mem_range.mpr ?_,?_⟩
    · exact Nat.lt_succ_of_le (actualCriticalBroadDyadIndex_le_log_ceil c p)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have hc := (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le_card_mul (Finset.range (K+1)) units 4
      (fun k _=>actualCriticalBroadDyadIndex_card_le_four c hd k))
  simpa only [Finset.card_univ,Finset.card_range,mul_comm,K] using hc

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
