module

public import ComparisonSignedCavityActualResourceScalarScale
public import ComparisonSignedCavityActualResourceGaReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_resource_Ga_restoration_normalized_profile_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (hdepth : seed.length+k ≤ degree) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < as.length)
    {A x W ε price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε)
    (Hlive : |nativeActualGProjectedRestoration T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))| ≤
      nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceGaRestoration M U P| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  have hx0:=M.hxs.trans_le hx
  have hW:=hx0.trans_le hxW
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
    0 (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as)
    A x W ε hA hx0 hW hε hε1 hi hs Hpair
  let scalar:=nativeActualResourceOriginalScalar M U P
  let live:=nativeActualGProjectedRestoration T P.live.test star U M
    (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
      (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  have H:=mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))
  have HF:=mul_le_mul_of_nonneg_right HS hprice
  change |live| ≤ _ at Hlive
  calc
    |(W⁻¹)^k*nativeActualResourceGaRestoration M U P|=
      |(W⁻¹)^k*scalar| *|live| := by
        dsimp only [nativeActualResourceGaRestoration,scalar,live]
        rw [←abs_mul]
        congr 1
        ring
    _ ≤ |(W⁻¹)^k*scalar| *(nativeResourceScale x W 1 P.live.tags*price) := H
    _ ≤ _ := by simpa only [mul_assoc] using HF

end OAI.SKFluctuations.Cavity
