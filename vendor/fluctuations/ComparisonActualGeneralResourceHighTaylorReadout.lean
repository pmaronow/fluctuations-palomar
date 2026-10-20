module

public import ComparisonSignedCavityActualHighTaylorParts
public import ComparisonActualGeneralResourceCanonicalShape
public import ComparisonActualGeneralResourceJointLowRestorationReadout
public import ComparisonSignedCavityActualResourceGaReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def actualGeneralResourceHigherHighPart
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (part : Fin 3) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeActualHigherHighPart part n q U b h K T
    (P.value (fullWeight n) (fullFeature n) 0 qfull
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0) a z l t

def actualGeneralOriginalCenteredResourceHigherHighPart
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (part : Fin 3) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T
    (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeActualHigherHighPart part n q U b h K T (fun σ=>Pc (T.cavityAssignment σ).1) a z l t

theorem actual_general_original_centered_resource_HIGH_part_eq_two_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (part : Fin 3) (a z : T.Slot) (l t : ℝ) :
    actualGeneralOriginalCenteredResourceHigherHighPart bf hf U P part a z l t=
      actualGeneralResourceHigherHighPart bf hf U P part a z l t+
      actualGeneralResourceHigherHighPart bf hf U P.freeze part a z l t := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have H:=actual_higher_HIGH_part_original_centered_resource_eq_two_terms P ho part q U b h K C a z l t
  dsimp only at H
  rw [HQ] at H
  exact H

theorem actual_general_resource_HIGH_part_normalized_profile_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < as.length)
    (part : Fin 3) (a z : T.Slot) (l t : ℝ)
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
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      |nativeActualHigherHighPart part n q U b h K T
        (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).product a z l t| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*actualGeneralResourceHigherHighPart bf hf U P part a z l t| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hs
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  let F:=(G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).product
  have HE : actualGeneralResourceHigherHighPart bf hf U P part a z l t=
      scalar*nativeActualHigherHighPart part n q U b h K T F a z l t := by
    unfold actualGeneralResourceHigherHighPart
    dsimp only
    have HP : P.value (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1)
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n bf hf as) 0=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [actual_general_resource_canonical_product_eq_live]
      rfl
    rw [HP,native_actual_higher_HIGH_part_const_mul_test]
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n bf hf as)
    A x W 1 hA hx (hx.trans_le hxW)
    zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
