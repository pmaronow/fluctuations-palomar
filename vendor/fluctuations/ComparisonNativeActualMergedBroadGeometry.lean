module

public import ComparisonNativeActualMinimumOrdinaryBudget
public import ComparisonNativePositiveBroadConsumers
public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem constraint_length_calibration
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    a.context.d^3*a.context.L*a.context.U ≤ a.context.E := by
  let N := a.context.N
  let d := a.context.d
  let E := a.context.E
  have hN : 0 < N := a.context.hN
  have hd : 0 < d := a.context.hd
  have hE : 0 < E := a.context.hE
  have hs : (Real.sqrt N)^2 = N := Real.sq_sqrt hN.le
  have hs3 : (Real.sqrt N)^3 = N*Real.sqrt N := by
    calc
      _ = (Real.sqrt N)^2*Real.sqrt N := by ring
      _ = _ := by rw [hs]
  have hL : a.context.L ≤ (comparisonLowerScale N E d)^3/d^2 := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ d^3))
    a.context.hU.le
  have he : d^3*((comparisonLowerScale N E d)^3/d^2)*a.context.U =
      Real.sqrt N*E^2/d^2 := by
    change d^3*((comparisonLowerScale N E d)^3/d^2)*comparisonSmallMass N E = _
    unfold comparisonLowerScale comparisonSmallMass
    rw [div_pow,mul_pow,hs3]
    field_simp
  rw [he] at hmul
  have hupper : Real.sqrt N*E ≤ d^2 := a.hupper
  have hr : Real.sqrt N*E^2/d^2 ≤ E := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  exact hmul.trans hr

end NativeOverlapMinimum

namespace NativeWholeCapBroadSampler

def toSliceGeometry {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (i : Fin f.count)
    (hboundary : (m.H c.a=0 ∧ m.H c.z=0) ∨
      (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1))
    (hag : m.ag=m.R (f.scale i/2))
    (hzg : m.zg=m.R (min (16*f.scale i) 1))
    (hcal : m.d^3*m.Lcap*m.U ≤ m.E) : NativeBroadSliceGeometry m := by
  have hg := f.geometry i
  have hn := f.nodes_mem i
  have hv : 0 < f.scale i := m.hU.trans_le hg.1
  have hmono := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha
  have hstrict := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
  have hcapA : c.a ≤ m.R (f.node i.val) := by
    have hh := hmono ((le_max_left _ _).trans hg.2.2.2.2.1)
    simpa only [comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha
      (show c.a∈Icc (0:ℝ) 1 from ⟨c.ha,c.haz.le.trans c.hz⟩)] using hh
  have hcapZ : m.R (f.node (i.val+1)) ≤ c.z := by
    have hh := hmono hg.2.2.2.2.2.1
    simpa only [comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha
      (show c.z∈Icc (0:ℝ) 1 from ⟨c.ha.trans c.haz.le,c.hz⟩)] using hh
  refine {
    capA := c.a
    capZ := c.z
    ha := c.ha
    haz := c.haz
    hz := c.hz
    hboundary := hboundary
    hnegative := c.negative
    a := m.R (f.node i.val)
    b := m.R (f.node (i.val+1))
    hab := hstrict hn.1 hn.2 hg.2.2.2.2.2.2
    haCap := hcapA
    hbCap := hcapZ
    haGroup := ?_
    hbGroup := ?_
    scale := f.scale i
    ceiling := f.node (i.val+1)
    hscale := hg.1
    hceiling := hn.2
    hcomparable := hg.2.2.2.1
    hceilingMass := ?_
    hmass := (f.contracts i).2.2.2.2.2
    hcal := hcal }
  · rw [hag]
    exact hmono hg.2.2.1
  · rw [hzg]
    apply hmono
    exact le_min (by linarith [hg.2.2.2.1]) hn.2.2
  · exact (comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hn.2).le

@[simp] theorem toSliceGeometry_slice {m : NativeBandModel} {c : NativeActualCapInterval m}
    (f : NativeWholeCapBroadSampler m c) (i : Fin f.count) hboundary hag hzg hcal :
    Ioo (f.toSliceGeometry i hboundary hag hzg hcal).a
      (f.toSliceGeometry i hboundary hag hzg hcal).b = f.slice i := rfl

end NativeWholeCapBroadSampler
end OAI.SKFluctuations.LaplaceWindowFormalization
