module

public import ComparisonActualHighOnlyChildBarrierCall
public import ComparisonNativeActualChildConstruction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

structure ActualShiftedParentData (n : ℕ) (delta : ℝ) where
  numerics : NativeChildBarrierParameters n delta
  r0 : ℝ
  s : ℝ
  hr0 : 0 ≤ r0
  hr1 : r0 ≤ 1
  hs : s∈Icc (0:ℝ) 1
  lam : ℝ
  hlam : 0 < lam
  hld : lam ≤ numerics.d^2
  b : ℝ→ℝ
  h : ℝ→ℝ
  clockAdmissible : ∀alpha : inverseIntegralConstraints r0 s numerics.k numerics.M,
    let R:=omittedSweepQuantile hr1 hs numerics.hc
      (numerics.hk.mono (Icc_subset_Icc hr0 le_rfl))
      (fun r hr=>numerics.hkc r ⟨hr0.trans hr.1,hr.2⟩) numerics.hm numerics.hM alpha
    let e:=omittedStrengthCoefficient numerics.d s R lam
    MonotoneOn (fun u=>b u-e u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>h u+e u*R u) (Icc (0:ℝ) 1) ∧
      (∀u∈Icc (0:ℝ) 1,0 ≤ b u-e u) ∧ (∀u∈Icc (0:ℝ) 1,0 ≤ h u+e u*R u)

namespace ActualShiftedParentData
variable {n : ℕ} {delta : ℝ} (a : ActualShiftedParentData n delta)
abbrev E:=a.numerics.E
abbrev d:=a.numerics.d
abbrev N:=a.numerics.N
abbrev U:=a.numerics.U
abbrev L:=a.numerics.L
abbrev k:=a.numerics.k
abbrev M:=a.numerics.M
abbrev hn:=a.numerics.hn
abbrev hN:=a.numerics.hN
abbrev hE:=a.numerics.hE
abbrev hd:=a.numerics.hd
abbrev hc:=a.numerics.hc
abbrev hk:=a.numerics.hk.mono (Icc_subset_Icc a.hr0 le_rfl)
abbrev hkc:=fun r (hr:r∈Icc a.r0 1)=>a.numerics.hkc r ⟨a.hr0.trans hr.1,hr.2⟩
abbrev hm:=a.numerics.hm
abbrev hM:=a.numerics.hM
abbrev hU:=a.numerics.hU
abbrev Profile:=inverseIntegralConstraints a.r0 a.s a.k a.M
abbrev R (alpha:a.Profile):=omittedSweepQuantile a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM alpha
abbrev coefficient (alpha:a.Profile):=omittedStrengthCoefficient a.d a.s (a.R alpha) a.lam
abbrev objective (alpha:a.Profile):=pathCompensatedPressure n a.b a.h (a.coefficient alpha) (a.R alpha) 0

theorem radius_before (alpha:a.Profile) {u:ℝ} (hu:u ≤ a.s):a.R alpha u=a.r0:=by
  have H:=omittedSweepQuantile_monotone a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM alpha hu
  rw [omittedSweepQuantile_left a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM alpha] at H
  exact le_antisymm H (omittedSweepQuantile_bounds a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM alpha u).1
end ActualShiftedParentData

structure ActualShiftedParentMinimum {n : ℕ} {delta : ℝ} (a:ActualShiftedParentData n delta) where
  alpha:a.Profile
  minimum:∀gamma:a.Profile,a.objective alpha ≤ a.objective gamma

structure ActualShiftedParentChildCall (n:ℕ) (delta:ℝ) where
  context:ActualShiftedParentData n delta
  optimizer:ActualShiftedParentMinimum context
  childData:ActualHighOnlyComparisonData n delta
  childLam:ℝ
  hchildLam:0 < childLam
  hchildLd:childLam ≤ childData.d^2
  childOptimizer:ActualHighOnlyComparisonMinimum childData childLam
  sameInitialMass:childData.s=context.s
  childBareMatrix:childData.b=(fun u=>context.b u-context.coefficient optimizer.alpha u)
  childBareField:childData.h=(fun u=>context.h u+context.coefficient optimizer.alpha u*context.R optimizer.alpha u)
  err:ℝ
  childSuccess:childData.objective childLam childOptimizer.alpha ≤
    realOrderedSKPathPressure n childData.b childData.h 0+err

end OAI.SKFluctuations.LaplaceWindowFormalization
