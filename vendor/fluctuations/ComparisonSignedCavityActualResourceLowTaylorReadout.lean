module

public import ComparisonSignedCavityActualLowTaylorLinearity
public import ComparisonSignedCavityActualResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

def nativeActualResourceThirdLowPart
  {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
  {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
  (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) (l t : ℝ) : ℝ :=
 let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
 let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
 let K:=nativeContinuumMixedClock n M.bf M.hf as
 let C:=nativePhysicalResourceCenter n M.bf M.hf as
 let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
 let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
 nativeActualCenteredThirdLowPart n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C) a z l t

theorem actual_resource_third_LOW_normalized_profile_le
  {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
  {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
  {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
  (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
  (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star < as.length)
  (a z : T.Slot) (l t : ℝ)
  {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
  (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
   (finitePhysicalCavitySquareVariance n U as
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
   (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
   (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W 1)
  (Hlive :
   let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
   let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
   let K:=nativeContinuumMixedClock n M.bf M.hf as
   let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
   let G:=nativeActualResourceCanonicalShape P.live hi hstar
   |nativeActualCenteredThirdLowPart n q U b h K T
    (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct a z l t| ≤
    nativeResourceScale x W 1 P.live.tags*price) :
  |(W⁻¹)^k*nativeActualResourceThirdLowPart M U P a z l t| ≤
   |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
 let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
 let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
 let K:=nativeContinuumMixedClock n M.bf M.hf as
 let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
 let G:=nativeActualResourceCanonicalShape P.live hi hstar
 let scalar:=nativeActualResourceOriginalScalar M U P
 let F:=(G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct
 have HE : nativeActualResourceThirdLowPart M U P a z l t=
   scalar*nativeActualCenteredThirdLowPart n q U b h K T F a z l t := by
  unfold nativeActualResourceThirdLowPart
  dsimp only
  have HP : nativeActualResourceRestValue P 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (nativePhysicalResourceCenter n M.bf M.hf as)=(fun σ=>scalar*F σ):=by
   funext σ
   dsimp only [F,G]
   rw [native_actual_resource_canonical_rest_product_eq_live]
   unfold nativeActualResourceRestValue
   congr 1
   apply congrArg List.prod
   apply List.map_congr_left
   intro e he
   simp [deletedOverlap,joinSpin]
  rw [HP,actual_nativeActualCenteredThirdLowPart_const_mul_test]
 have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
  (fullWeight_pos n) (fullFeature n) ho 0
  (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
  (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
  (nativePhysicalResourceCenter n M.bf M.hf as)
  A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
  zero_lt_one le_rfl hi hstar Hpair
 change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
 dsimp only at Hlive
 rw [HE,mul_assoc,←mul_assoc,abs_mul]
 apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
 simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
