module

public import ComparisonNativeLocalDyadicThermalDomination

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

namespace NativeActualCapInterval

def reassign {m : NativeBandModel} (c : NativeActualCapInterval m)
    (b : NativeBandModel) (hH : b.H=m.H) : NativeActualCapInterval b where
  a := c.a
  z := c.z
  ha := c.ha
  haz := c.haz
  hz := c.hz
  negative := by intro r hr; rw [hH]; exact c.negative r hr

theorem reassign_boundary {m : NativeBandModel} (c : NativeActualCapInterval m)
    (b : NativeBandModel) (hH : b.H=m.H)
    (hc : (m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1)) :
    (b.H (c.reassign b hH).a=0 ∧ b.H (c.reassign b hH).z=0) ∨
      ((c.reassign b hH).a=0 ∧ b.H (c.reassign b hH).z=0) ∨
      (b.H (c.reassign b hH).a=0 ∧ (c.reassign b hH).z=1) := by
  simpa only [reassign,hH] using hc

end NativeActualCapInterval

namespace NativeWholeCapBroadSampler

def reassign {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (b : NativeBandModel)
    (hH : b.H=m.H) (hU : b.U=m.U) (ha : b.alpha.val.val=m.alpha.val.val) :
    NativeWholeCapBroadSampler b (c.reassign b hH) where
  k := f.k
  j := f.j
  hnear := by change nativeDyadicMass b.U f.k ≤ max (b.alpha.val.val c.a) b.U
              rw [hU,ha]; exact f.hnear
  hnearNext := by change max (b.alpha.val.val c.a) b.U < nativeDyadicMass b.U (f.k+1)
                  rw [hU,ha]; exact f.hnearNext
  hright := by change nativeDyadicMass b.U f.j ≤ b.alpha.val.val c.z
               rw [hU,ha]; exact f.hright
  hrightNext := by change b.alpha.val.val c.z < nativeDyadicMass b.U (f.j+1)
                   rw [hU,ha]; exact f.hrightNext
  hgap := f.hgap

@[simp] theorem reassign_count {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (b : NativeBandModel) hH hU ha :
    (f.reassign b hH hU ha).count=f.count := rfl

@[simp] theorem reassign_node {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (b : NativeBandModel) hH hU ha (i : ℕ) :
    (f.reassign b hH hU ha).node i=f.node i := by
  dsimp only [node,reassign,NativeActualCapInterval.reassign]
  rw [hU,ha]

@[simp] theorem reassign_scale {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (b : NativeBandModel) hH hU ha (i : Fin f.count) :
    (f.reassign b hH hU ha).scale i=f.scale i := by
  dsimp only [scale,reassign]
  rw [hU]

theorem reassign_slice {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (b : NativeBandModel) hH hU ha
    (hR : b.R=m.R) (i : Fin f.count) :
    (f.reassign b hH hU ha).slice i=f.slice i := by
  change Ioo (b.R ((f.reassign b hH hU ha).node i.val))
    (b.R ((f.reassign b hH hU ha).node (i.val+1))) =
    Ioo (m.R (f.node i.val)) (m.R (f.node (i.val+1)))
  rw [reassign_node,reassign_node,hR]

theorem reassign_original_thermal_integral {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (b : NativeBandModel) hH hU ha
    (hR : b.R=m.R) (hT : b.thermal=m.thermal) (i : Fin f.count) :
    (∫u in 0..1,((f.reassign b hH hU ha).slice i).indicator
      (fun _=>1) (b.R u)*b.thermal u) =
      ∫u in 0..1,(f.slice i).indicator (fun _=>1) (m.R u)*m.thermal u := by
  rw [reassign_slice f b hH hU ha hR i,hR,hT]

end NativeWholeCapBroadSampler
end OAI.SKFluctuations.LaplaceWindowFormalization
