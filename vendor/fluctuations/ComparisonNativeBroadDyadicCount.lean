module

public import ComparisonNativeBroadScaleCount

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3200000
attribute [local instance] Classical.propDecidable

abbrev nativeActualBroadDyadIndex {ι:Type*} (m:NativeBandModel) (c:ι→NativeActualCapInterval m)
    (p:nativeActualBroadSliceIndex m c) : ℕ :=
  let f := nativeActualBroadCapSampler m c p.1
  if p.2.val=0 then f.k+1 else f.k+1+p.2.val

theorem nativeActualBroadSliceScale_eq_dyad {ι:Type*} (m:NativeBandModel)
    (c:ι→NativeActualCapInterval m) (p:nativeActualBroadSliceIndex m c) :
    nativeActualBroadSliceScale m c p=nativeDyadicMass m.U (nativeActualBroadDyadIndex m c p) := by
  simp only [nativeActualBroadSliceScale,NativeWholeCapBroadSampler.scale,nativeBroadSliceScale,
    nativeActualBroadDyadIndex]
  split_ifs <;> rfl

theorem nativeActualBroadSliceScale_le_one {ι:Type*} (m:NativeBandModel)
    (c:ι→NativeActualCapInterval m) (p:nativeActualBroadSliceIndex m c) :
    nativeActualBroadSliceScale m c p≤1 := by
  have hg := (nativeActualBroadCapSampler m c p.1).geometry p.2
  have hn := (nativeActualBroadCapSampler m c p.1).nodes_mem p.2
  linarith [hg.2.1,hn.1.1,hn.2.2]

theorem nativeActualBroadDyadIndex_log_bound {ι:Type*} (m:NativeBandModel)
    (c:ι→NativeActualCapInterval m) (p:nativeActualBroadSliceIndex m c) :
    (nativeActualBroadDyadIndex m c p:ℝ)*Real.log 2≤ Real.log (1/m.U) := by
  have hh := Real.log_le_log (m.hU.trans_le
    ((nativeActualBroadCapSampler m c p.1).contracts p.2).1)
      (nativeActualBroadSliceScale_le_one m c p)
  change Real.log (nativeActualBroadSliceScale m c p)≤Real.log 1 at hh
  rw [nativeActualBroadSliceScale_eq_dyad m c p,nativeDyadicMass,
    Real.log_mul m.hU.ne' (pow_ne_zero _ (by norm_num)),Real.log_pow,Real.log_one] at hh
  rw [Real.log_div (by norm_num : (1:ℝ)≠0) m.hU.ne',Real.log_one,zero_sub]
  linarith

theorem nativeActualBroadDyadIndex_card_le_four {ι:Type*} [Fintype ι]
    (m:NativeBandModel) (c:ι→NativeActualCapInterval m)
    (hd:Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z))) (k:ℕ) :
    (Finset.univ.filter (fun p:nativeActualBroadSliceIndex m c=>nativeActualBroadDyadIndex m c p=k)).card≤4 := by
  have hs : (Finset.univ.filter (fun p:nativeActualBroadSliceIndex m c=>nativeActualBroadDyadIndex m c p=k))⊆
      (Finset.univ.filter (fun p:nativeActualBroadSliceIndex m c=>nativeActualBroadSliceScale m c p=nativeDyadicMass m.U k)) := by
    intro p hp
    obtain ⟨hpu,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpu,by rw [nativeActualBroadSliceScale_eq_dyad m c p,hp]⟩
  exact (Finset.card_le_card hs).trans
    (nativeActualBroadSlice_common_scale_card_le_four m c hd (nativeDyadicMass_pos m.hU k))

end OAI.SKFluctuations.LaplaceWindowFormalization
