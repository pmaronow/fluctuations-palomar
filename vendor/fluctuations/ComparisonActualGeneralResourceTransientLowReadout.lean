module

public import ComparisonActualGeneralResourceJointLowRestorationReadout
public import ComparisonSignedCavityActualLowTaylorLinearity
public import ComparisonSignedCavityTransientLowErrorParts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_nativeTransientLowErrorPartJet_add_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (part : NativeTransientLowErrorPart) (k : ℕ) (l t : ℝ) :
    nativeTransientLowErrorPartJet n q i star U b h K T (fun σ=>P σ+Q σ) x part k l t=
      nativeTransientLowErrorPartJet n q i star U b h K T P x part k l t+
      nativeTransientLowErrorPartJet n q i star U b h K T Q x part k l t := by
  exact actual_disorderProfileJets_add _ _ _ _ _ _ _ _ _

theorem actual_nativeTransientLowErrorPartJet_const_mul_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (part : NativeTransientLowErrorPart) (k : ℕ) (l t c : ℝ) :
    nativeTransientLowErrorPartJet n q i star U b h K T (fun σ=>c*P σ) x part k l t=
      c*nativeTransientLowErrorPartJet n q i star U b h K T P x part k l t := by
  exact disorderProfileJets_const_mul _ _ _ _ _ _ _ _ _

theorem actual_nativeTransientCenteredLowErrorPart_add_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (part : NativeTransientLowErrorPart) (l t : ℝ) :
    nativeTransientCenteredLowErrorPart n q i star U b h K T (fun σ=>P σ+Q σ)
        (sitePair T a z) 0 part l t=
      nativeTransientCenteredLowErrorPart n q i star U b h K T P (sitePair T a z) 0 part l t+
      nativeTransientCenteredLowErrorPart n q i star U b h K T Q (sitePair T a z) 0 part l t := by
  unfold nativeTransientCenteredLowErrorPart
  simp only [add_mul,actual_nativeTransientLowErrorPartJet_add_test,actual_productJet3_add_right]
  ring

theorem actual_nativeTransientCenteredLowErrorPart_const_mul_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (i star U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (part : NativeTransientLowErrorPart) (l t c : ℝ) :
    nativeTransientCenteredLowErrorPart n q i star U b h K T (fun σ=>c*P σ)
        (sitePair T a z) 0 part l t=
      c*nativeTransientCenteredLowErrorPart n q i star U b h K T P (sitePair T a z) 0 part l t := by
  unfold nativeTransientCenteredLowErrorPart
  simp only [mul_assoc,actual_nativeTransientLowErrorPartJet_const_mul_test,actual_productJet3_const_mul_right]
  ring

def actualGeneralResourceTransientLowPart
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot)
    (part : NativeTransientLowErrorPart) (l t : ℝ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeTransientCenteredLowErrorPart n q i star U b h K T
    (nativeActualResourceRestValue P 0 qfull 0 C) (sitePair T a z) 0 part l t

theorem actual_general_resource_transient_LOW_normalized_price_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star < as.length)
    (a z : T.Slot) (part : NativeTransientLowErrorPart) (l t : ℝ)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : 0 < x) (hxW : x ≤ W) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n bf hf as) 0 A x W 1)
    (Hlive :
      let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n bf hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hstar
      |nativeTransientCenteredLowErrorPart n q i star U b h K T
        (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct
        (sitePair T a z) 0 part l t| ≤ nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*actualGeneralResourceTransientLowPart bf hf U P a z part l t| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  let F:=(G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : actualGeneralResourceTransientLowPart bf hf U P a z part l t=
      scalar*nativeTransientCenteredLowErrorPart n q i star U b h K T F (sitePair T a z) 0 part l t := by
    have HP : nativeActualResourceRestValue P 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [actual_general_resource_canonical_rest_product_eq_live]
      unfold nativeActualResourceRestValue
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro e he
      simp [deletedOverlap,joinSpin,C]
    unfold actualGeneralResourceTransientLowPart
    dsimp only
    rw [HP,actual_nativeTransientCenteredLowErrorPart_const_mul_test]
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C
    A x W 1 hA hx (hx.trans_le hxW) zero_lt_one le_rfl hi hstar Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
