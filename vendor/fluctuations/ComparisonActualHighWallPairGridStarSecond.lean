module

public import ComparisonActualHighWallSquarePairRetainedAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000

theorem ActualHighWallSquareResourcePairBudgetsOnGrid.star_second_moment
    {n degree : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass M u as)
    (hd : 1 ≤ degree) (U : ℕ) (hs : retainedMassPrefixIndex u.val as < U)
    (hU : U ≤ as.length) (a t : ℝ) (ha : a∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeOriginalSquareCenteredMoment n 1 U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
      (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
      (retainedMassPrefixIndex u.val as)
      (nativePhysicalResourceCenter n M.bf M.hf as (retainedMassPrefixIndex u.val as)) a t ≤
      (A*(((n+1:ℕ):ℝ)^(-saving)*M.data.d))^2 := by
  let star:=retainedMassPrefixIndex u.val as
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let projected:=base.projection (hs.le.trans hU)
  have Hbase : NativeActualResourceGenerated 0 star U [] base.generation base.tree base.term:=
    .physical (.constant as hU)
  have HG : NativeActualResourceGenerated 0 star U [] 1 projected.tree projected.term:=
    Hbase.projection (hs.le.trans hU)
  have HM:=H.1 U 0 1 projected.tree projected.term HG hd a t ha ht
  let e : Fin projected.term.live.factors.length:=⟨0,by change 0 < 1;norm_num⟩
  have HX:=HM.1 e
  change nativeOriginalSquareCenteredMoment n 1 U as
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
    (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) star
    (nativePhysicalResourceCenter n M.bf M.hf as star) a t ≤ _ at HX
  exact HX

end OAI.SKFluctuations.Cavity
