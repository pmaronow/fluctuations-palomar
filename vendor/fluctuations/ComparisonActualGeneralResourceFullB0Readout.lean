module

public import ComparisonActualGeneralFullB0Ledger
public import ComparisonActualGeneralResourceCanonicalShape
public import ComparisonActualGeneralResourceJointLowRestorationReadout
public import ComparisonActualGeneralFourCategories
public import ComparisonSignedCavityActualCenteredResourceFreshRestReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def actualGeneralOriginalCenteredResourceB0
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ:=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
    (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))

theorem actual_general_resource_centered_full_B0_eq_scalar_canonical
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (hi : i ≤ star) (hs : star < as.length)
    (bf hf : ℝ→ℝ≥0) (U : ℕ) :
    actualGeneralOriginalCenteredResourceB0 bf hf U P=
      let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n bf hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      actualGeneralResourceOriginalScalar bf hf U P*nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
        (nativeOriginalCenteredRestTest n q U b h K T
          (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct) := by
  unfold actualGeneralOriginalCenteredResourceB0
  dsimp only
  let G:=nativeActualResourceCanonicalShape P.live hi hs
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n bf hf as
  have HP : nativeActualResourceRestValue P 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C=
      fun sigma=>scalar*(G.canonicalPhysicalSource bf hf (fun _=>.centered)).restProduct sigma:=by
    funext sigma
    dsimp only [G]
    rw [actual_general_resource_canonical_rest_product_eq_live]
    unfold nativeActualResourceRestValue
    congr 1
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    simp [deletedOverlap,joinSpin,C]
  rw [HP,native_original_B0_centered_test_const_mul,native_second_low_fresh_full_B0_const_mul]

theorem actual_general_resource_full_B0_normalized_profile_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < as.length)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : 0<x) (hxW : x ≤ W) (hprice : 0 ≤ price)
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
          nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*actualGeneralOriginalCenteredResourceB0 bf hf U P| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n bf hf as)
    A x W 1 hA hx (hx.trans_le hxW)
    zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  rw [actual_general_resource_centered_full_B0_eq_scalar_canonical P hi hs bf hf U,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

theorem actual_general_second_low_resource_category_eq_full_B0
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (hU : U≤as.length) (ho : MassOrdered 0 as) (hs : star<U)
    (P : NativeResourceTerm i star T) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualOriginalOtherSourceCategory .secondLow n q U b h K C T
      (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))
      P.live.test.target star=actualGeneralOriginalCenteredResourceB0 bf hf U P := by
  dsimp only [actualGeneralOriginalCenteredResourceB0,nativeSecondLowFreshFullB0Source]
  exact native_actual_second_low_category_eq_joint_ledger_half _ _ _ _ _ _ _ T ho _ _ star hs hU

theorem actual_general_four_second_low_eq_two_full_resource_sources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U≤as.length)
    (ho : MassOrdered 0 as) (hs : star<U)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    actualGeneralFourCategoryContrast bf hf U st .secondLow=
      actualGeneralOriginalCenteredResourceB0 bf hf U st.term-
        (1/2:ℝ)*actualGeneralOriginalCenteredResourceB0 bf hf U (st.term.retarget 0) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_general_second_low_resource_category_eq_full_B0 bf hf U hU ho hs st.term
  have H1:=actual_general_second_low_resource_category_eq_full_B0 bf hf U hU ho hs (st.term.retarget 0)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  dsimp only at Hread H0 H1
  rw [HQ] at Hread
  rw [Hread] at H1
  change nativeActualOriginalOtherSourceCategory .secondLow n q U b h K C g.tree
    (fun sigma=>nativeOriginalCenteredRestTest n q U b h K st.tree
      (nativeActualResourceRestValue st.term 0 qfull 0 C) (g.restRestrict sigma)) g.mark star=
    actualGeneralOriginalCenteredResourceB0 bf hf U (st.term.retarget 0) at H1
  unfold actualGeneralFourCategoryContrast
  dsimp only
  rw [H0]
  change _-(1/2:ℝ)*nativeActualOriginalOtherSourceCategory .secondLow n q U b h K C g.tree
    (fun sigma=>nativeOriginalCenteredRestTest n q U b h K st.tree
      (nativeActualResourceRestValue st.term 0 qfull 0 C) (g.restRestrict sigma)) g.mark star=_
  rw [H1]

end OAI.SKFluctuations.Cavity
