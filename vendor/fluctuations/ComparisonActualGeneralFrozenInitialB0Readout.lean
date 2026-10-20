module

public import ComparisonActualGeneralResourceFullB0Readout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 12000000

theorem native_resource_scale_no_initial
    (rs : List NativeResourceMark) (h : NativeResourceMark.initial∉rs)
    (x y W : ℝ) : nativeResourceScale x W 1 rs=nativeResourceScale y W 1 rs := by
  induction rs with
  | nil => rfl
  | cons mark rs ih =>
    have hm : mark≠.initial:=by
      intro he
      apply h
      simp only [he,List.mem_cons, true_or]
    have hr : NativeResourceMark.initial∉rs:=by
      intro he
      exact h (List.mem_cons_of_mem _ he)
    cases mark with
    | initial => exact False.elim (hm rfl)
    | oldStar =>
      change W*nativeResourceScale x W 1 rs=W*nativeResourceScale y W 1 rs
      rw [ih hr]
    | markedStar j =>
      change (1*W)*nativeResourceScale x W 1 rs=(1*W)*nativeResourceScale y W 1 rs
      rw [ih hr]

theorem actual_general_frozen_initial_full_B0_normalized_profile_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [.initial] k T P)
    (hdepth : 1+k≤degree) (hNo : NativeResourceMark.initial∉P.live.tags)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star<as.length)
    {A x W price : ℝ} (hA : 1≤A) (hx : 0<x) (hW : 0<W) (hprice : 0≤price)
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
      |nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
        (nativeOriginalCenteredRestTest n q U b h K T
          (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct)| ≤
        nativeResourceScale W W 1 P.live.tags*price) :
    |(W⁻¹)^k*actualGeneralOriginalCenteredResourceB0 bf hf U P|≤
      |P.coefficient| * A^degree*x*price := by
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n bf hf as)
    A x W 1 hA hx hW zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| * nativeResourceScale x W 1 P.live.tags≤_ at HS
  have Hscale:=native_resource_scale_no_initial P.live.tags hNo x W W
  dsimp only at Hlive
  rw [←Hscale] at Hlive
  rw [actual_general_resource_centered_full_B0_eq_scalar_canonical P hi hs bf hf U,
    ←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  have HH:=mul_le_mul_of_nonneg_right HS hprice
  have Hseed : nativeResourceScale x W 1 [.initial]=x:=by
    simp [nativeResourceScale,NativeResourceMark.savedScale]
  rw [Hseed] at HH
  simpa only [mul_assoc] using HH

end OAI.SKFluctuations.Cavity
