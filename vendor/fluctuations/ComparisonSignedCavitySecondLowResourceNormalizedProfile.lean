module

public import ComparisonSignedCavitySecondLowScalarResourceReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_resource_B0_mod_replacement_normalized_profile_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < as.length) (hU : U ≤ as.length)
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
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      |nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T P.live.test.target star hU
        (nativeOriginalCenteredRestTest n q U b h K T
          (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct)| ≤
          nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualOriginalCenteredResourceB0MinusCReplacement M U hU P| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let scalar:=nativeActualResourceOriginalScalar M U P
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as)
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  rw [native_actual_resource_centered_B0_minus_c_replacement_eq_scalar_canonical P hi hs M U hU,
    ←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
