module

public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3200000
attribute [local instance] Classical.propDecidable

abbrev nativeDyadicRadiusGroupLeft (m : NativeBandModel) (v : ℝ) := m.R (v/2)
abbrev nativeDyadicRadiusGroupRight (m : NativeBandModel) (v : ℝ) := m.R (min (16*v) 1)

theorem native_actual_dyadic_radius_group (m : NativeBandModel) {v:ℝ}
    (hv : 0< v) (hv1 : v≤1) :
    0< nativeDyadicRadiusGroupLeft m v ∧
      nativeDyadicRadiusGroupLeft m v≤ nativeDyadicRadiusGroupRight m v ∧
      nativeDyadicRadiusGroupRight m v≤1 ∧
      m.alpha.val.val (nativeDyadicRadiusGroupLeft m v)=v/2 ∧
      m.alpha.val.val (nativeDyadicRadiusGroupRight m v)=min (16*v) 1 ∧
      min (16*v) 1+m.U≤32*(v/2+m.U) := by
  have hlo : v/2∈Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hhi : min (16*v) 1∈Icc (0:ℝ) 1 :=
    ⟨(lt_min (by linarith) zero_lt_one).le,min_le_right _ _⟩
  have hs := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
  have hpos := hs (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) hlo (by linarith : 0< v/2)
  have hR0 : m.R 0=0 := by
    simpa only [m.alpha.property.1] using
      comparisonSweepQuantile_at_profile m.hc m.hk m.hkc m.hm m.hM m.alpha
        (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  change m.R 0< m.R (v/2) at hpos
  rw [hR0] at hpos
  refine ⟨hpos,?_,(comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha _).2,
    comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hlo,
    comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hhi,?_⟩
  · exact comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha
      (le_min (by linarith) hlo.2)
  · have hh := min_le_left (16*v) 1
    linarith [m.hU]

theorem native_actual_comparable_cap_group (m : NativeBandModel)
    (c : NativeActualCapInterval m) {v:ℝ} (hv:0< v) (hvl:v≤ m.alpha.val.val c.a)
    (hB:m.alpha.val.val c.z≤16*v) :
    nativeDyadicRadiusGroupLeft m v≤ c.a ∧ c.z≤ nativeDyadicRadiusGroupRight m v ∧
      v≤ m.alpha.val.val c.a ∧ m.alpha.val.val c.z≤ min (16*v) 1 := by
  have ha : c.a∈Icc (0:ℝ) 1 := ⟨c.ha,c.haz.le.trans c.hz⟩
  have hz : c.z∈Icc (0:ℝ) 1 := ⟨c.ha.trans c.haz.le,c.hz⟩
  have hb := le_min hB (m.alpha.val.property.1 c.z).2
  have hl := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha
    (show v/2≤ m.alpha.val.val c.a by linarith)
  have hr := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hb
  rw [comparisonSweepQuantile_at_profile m.hc m.hk m.hkc m.hm m.hM m.alpha ha] at hl
  rw [comparisonSweepQuantile_at_profile m.hc m.hk m.hkc m.hm m.hM m.alpha hz] at hr
  exact ⟨hl,hr,hvl,hb⟩

theorem NativeWholeCapBroadSampler.actual_dyadic_group {m : NativeBandModel}
    {c : NativeActualCapInterval m} (f : NativeWholeCapBroadSampler m c) (i:Fin f.count) :
    let v := f.scale i
    m.U≤ v ∧ v≤1 ∧
      nativeDyadicRadiusGroupLeft m v≤ m.R (f.node i.val) ∧
      m.R (f.node (i.val+1))≤ nativeDyadicRadiusGroupRight m v ∧
      f.slice i⊆Ioo (nativeDyadicRadiusGroupLeft m v) (nativeDyadicRadiusGroupRight m v) ∧
      m.alpha.val.val (nativeDyadicRadiusGroupLeft m v)=v/2 ∧
      m.alpha.val.val (nativeDyadicRadiusGroupRight m v)=min (16*v) 1 ∧
      min (16*v) 1+m.U≤32*(v/2+m.U) := by
  dsimp only
  have hg := f.geometry i
  have hn := f.nodes_mem i
  have hv : 0< f.scale i := m.hU.trans_le hg.1
  have hv1 : f.scale i≤1 := by linarith [hg.2.1,hn.1.1,hn.2.2]
  have hgrp := native_actual_dyadic_radius_group m hv hv1
  have hl := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hg.2.2.1
  have hb : f.node (i.val+1)≤ min (16*f.scale i) 1 :=
    le_min (hg.2.2.2.1.trans (by linarith)) hn.2.2
  have hr := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hb
  exact ⟨hg.1,hv1,hl,hr,Ioo_subset_Ioo hl hr,hgrp.2.2.2.1,hgrp.2.2.2.2.1,hgrp.2.2.2.2.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
