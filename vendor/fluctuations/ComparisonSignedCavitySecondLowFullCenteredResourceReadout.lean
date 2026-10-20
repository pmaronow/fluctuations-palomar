module

public import ComparisonSignedCavitySecondLowResourceNormalizedProfile
public import ComparisonSignedCavitySecondLowResourceCategoryReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

def nativeSecondLowFreshFullB0Source
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star : ℕ) (P : T.cavityLeft.Assignment→ℝ) : ℝ:=
  let g:=nativeFreshAtSlot T 0 s star
  nativeSecondLowJointLedger n q U b h K g.tree (fun σ=>P (g.restRestrict σ)) [g.embed s,g.mark]/2

theorem native_second_low_fresh_full_B0_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star : ℕ) (P : T.cavityLeft.Assignment→ℝ) (A : ℝ) :
    nativeSecondLowFreshFullB0Source n q U b h K T s star (fun σ=>A*P σ)=
      A*nativeSecondLowFreshFullB0Source n q U b h K T s star P := by
  unfold nativeSecondLowFreshFullB0Source
  dsimp only
  rw [native_second_low_joint_ledger_const_mul]
  ring

def nativeActualOriginalCenteredResourceB0
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ:=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
    (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))

theorem native_actual_resource_centered_full_B0_eq_scalar_canonical
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (hi : i ≤ star) (hs : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) :
    nativeActualOriginalCenteredResourceB0 M U P=
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      nativeActualResourceOriginalScalar M U P*nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
        (nativeOriginalCenteredRestTest n q U b h K T
          (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct) := by
  unfold nativeActualOriginalCenteredResourceB0
  dsimp only
  rw [native_actual_resource_B0_rest_value_eq_scalar_canonical P hi hs M U,
    native_original_B0_centered_test_const_mul,native_second_low_fresh_full_B0_const_mul]

theorem native_actual_full_resource_B0_eq_mod_replacement_add_true_replacement
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (hU : U ≤ as.length) (P : NativeResourceTerm i star T) :
    nativeActualOriginalCenteredResourceB0 M U P=
      nativeActualOriginalCenteredResourceB0MinusCReplacement M U hU P+
        nativeActualOriginalCenteredResourceCReplacement M U hU P := by
  dsimp only [nativeActualOriginalCenteredResourceB0,nativeActualOriginalCenteredResourceB0MinusCReplacement,
    nativeActualOriginalCenteredResourceCReplacement,nativeSecondLowFreshB0MinusCReplacementSource,
    nativeSecondLowFreshFullB0Source]
  ring

theorem native_actual_four_second_low_eq_two_full_resource_sources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) (hs : star < U)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourOtherCategoryContrast M U st .secondLow=
      nativeActualOriginalCenteredResourceB0 M U st.term-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceB0 M U (st.term.retarget 0) := by
  have H:=native_actual_four_second_low_minus_c_replacement_eq_two_resource_sources M U hU ho hs st
  have H0:=native_actual_full_resource_B0_eq_mod_replacement_add_true_replacement M U hU st.term
  have H1:=native_actual_full_resource_B0_eq_mod_replacement_add_true_replacement M U hU (st.term.retarget 0)
  unfold nativeActualOriginalFourCReplacementContrast at H
  linear_combination H-H0+(1/2:ℝ)*H1

theorem actual_resource_full_B0_normalized_profile_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < as.length)
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
      |nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
        (nativeOriginalCenteredRestTest n q U b h K T
          (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct)| ≤
          nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualOriginalCenteredResourceB0 M U P| ≤
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
  rw [native_actual_resource_centered_full_B0_eq_scalar_canonical P hi hs M U,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
