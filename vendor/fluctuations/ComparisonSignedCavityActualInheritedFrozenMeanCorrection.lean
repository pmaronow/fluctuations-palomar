module

public import ComparisonSignedCavityActualClockFrozenMeanCorrection
public import ComparisonSignedCavityActualInheritedClockMeanSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Filter Set LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem eventually_actual_inherited_clock_frozen_resource_correction
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0≤Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)→M.h 0=0→
      ∀us : List PositiveMass,(∀u∈us,u.val≤1)→∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
        ∀(K : ℕ→ℝ) (i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P→T.leaves≤r→
        ∀A x W ε : ℝ,0<A→0<x→0<W→0<ε→i ≤ star→star<as.length→
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as b h 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε→
        |nativeOriginalClockResourceResponse P.freeze U k K b
          (nativePhysicalResourceCenter n M.bf M.hf as)
          0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
          0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 W|≤
          (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*
            (((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) := by
  filter_upwards [eventually_actual_inherited_original_clock_longitudinal_mean_saving r Bclock Temp
    hTemp hm hC0] with n hn
  intro M htotal hroot us hus
  filter_upwards [hn M htotal hroot us hus] with j hj
  dsimp only at hj ⊢
  intro K i star U k seed T P hP hT A x W ε hA hx hW hε hi hstar hbudget
  exact nativeOriginalClockResourceResponse_freeze_abs_le hP (finiteCutMasses_ordered us hus j)
    K _ _ _ A x W ε _ hA hx hW hε hi hstar hbudget (hj K T U P.live.test.target hT)

end OAI.SKFluctuations.Cavity
