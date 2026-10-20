module

public import ComparisonNativeBroadDyadicCount

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3200000
attribute [local instance] Classical.propDecidable

theorem NativeWholeCapBroadSampler.scale_inside_original_mass {m:NativeBandModel}
    {c:NativeActualCapInterval m} (f:NativeWholeCapBroadSampler m c) (i:Fin f.count) :
    f.scale i∈Ioo (m.alpha.val.val c.a) (m.alpha.val.val c.z) :=
  nativeBroadSlice_scale_inside_original m.hU (le_max_left _ _) f.hnear f.hnearNext
    f.hright f.hrightNext f.hgap i

theorem nativeActualBroadDyadIndex_le_log_ceil {ι:Type*} (m:NativeBandModel)
    (c:ι→NativeActualCapInterval m) (p:nativeActualBroadSliceIndex m c) :
    nativeActualBroadDyadIndex m c p≤ Nat.ceil (Real.log (1/m.U)/Real.log 2) := by
  have hlog:0< Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hh := (le_div_iff₀ hlog).mpr (nativeActualBroadDyadIndex_log_bound m c p)
  have hc := hh.trans (Nat.le_ceil (Real.log (1/m.U)/Real.log 2))
  exact_mod_cast hc

theorem nativeActualBroadSlice_card_le_log_count {ι:Type*} [Fintype ι]
    (m:NativeBandModel) (c:ι→NativeActualCapInterval m)
    (hd:Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z))) :
    Fintype.card (nativeActualBroadSliceIndex m c)≤4*(Nat.ceil (Real.log (1/m.U)/Real.log 2)+1) := by
  let K := Nat.ceil (Real.log (1/m.U)/Real.log 2)
  let units := fun k=>Finset.univ.filter (fun p:nativeActualBroadSliceIndex m c=>nativeActualBroadDyadIndex m c p=k)
  have hcover : (Finset.univ:Finset (nativeActualBroadSliceIndex m c))⊆
      (Finset.range (K+1)).biUnion units := by
    intro p hp
    apply Finset.mem_biUnion.mpr
    refine ⟨nativeActualBroadDyadIndex m c p,Finset.mem_range.mpr ?_,?_⟩
    · exact Nat.lt_succ_of_le (nativeActualBroadDyadIndex_le_log_ceil m c p)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have hc := (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le_card_mul (Finset.range (K+1)) units 4
      (fun k _=>nativeActualBroadDyadIndex_card_le_four m c hd k))
  simpa only [Finset.card_univ,Finset.card_range,mul_comm,K] using hc

end OAI.SKFluctuations.LaplaceWindowFormalization
