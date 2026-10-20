module

public import ComparisonSignedCavitySecondLowScalarResourceReadout
public import ComparisonSignedCavitySecondLowFullCenteredResourceReadout
public import ComparisonSignedCavitySecondLowResourceCategoryReadout
public import ComparisonSignedCavitySecondLowActualHistoryFullHalfRetargetB0ModulusAlong
public import ComparisonSignedCavitySecondLowActualConstantResourceFactorGeometry
public import ComparisonActualHighOnlyResourcePhysicalFactories

@[expose] public section
noncomputable section
set_option maxHeartbeats 32000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
 theorem native_actual_resource_B0_rest_value_eq_scalar_canonical_high_only
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (hi : i ≤ star) (hs : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) :
    nativeActualResourceRestValue P 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      0 (nativePhysicalResourceCenter n M.bf M.hf as)=
      fun σ=>nativeActualResourceOriginalScalar_high_only M U P*
        ((nativeActualResourceCanonicalShape P.live hi hs).canonicalHighOnlySource M
          (fun _=>NativeSourceFactorForm.centered)).restProduct σ := by
  funext σ
  rw [native_actual_resource_canonical_rest_product_eq_live_high_only]
  unfold nativeActualResourceRestValue nativeActualResourceOriginalScalar_high_only
  congr 1
  apply congrArg (fun R=>nativeRestGeneratedTestValue T P.live.test R _ σ)
  funext s t
  simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]

def nativeActualOriginalCenteredResourceB0_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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

theorem native_actual_resource_centered_full_B0_eq_scalar_canonical_high_only
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (hi : i ≤ star) (hs : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) :
    nativeActualOriginalCenteredResourceB0_high_only M U P=
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      nativeActualResourceOriginalScalar_high_only M U P*nativeSecondLowFreshFullB0Source n q U b h K T P.live.test.target star
        (nativeOriginalCenteredRestTest n q U b h K T
          (G.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)).restProduct) := by
  unfold nativeActualOriginalCenteredResourceB0_high_only
  dsimp only
  rw [native_actual_resource_B0_rest_value_eq_scalar_canonical_high_only P hi hs M U,
    native_original_B0_centered_test_const_mul,native_second_low_fresh_full_B0_const_mul]

 theorem native_actual_second_low_resource_category_eq_full_B0_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (hU : U ≤ as.length) (ho : MassOrdered 0 as) (hs : star < U)
    (P : NativeResourceTerm i star T) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualOriginalOtherSourceCategory .secondLow n q U b h K C T
      (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))
      P.live.test.target star=
        nativeActualOriginalCenteredResourceB0_high_only M U P := by
  dsimp only
  rw [native_actual_second_low_category_eq_joint_ledger_half _ _ _ _ _ _ _ T ho _ _ star hs hU]
  rfl

 theorem native_actual_four_second_low_eq_two_full_resource_sources_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) (hs : star < U)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourOtherCategoryContrast_high_only M U st .secondLow=
      nativeActualOriginalCenteredResourceB0_high_only M U st.term-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceB0_high_only M U (st.term.retarget 0) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have HC:nativeOriginalCenteredRestTest n q U b h K g.tree
      (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C)=
      fun σ=>nativeOriginalCenteredRestTest n q U b h K st.tree
        (nativeActualResourceRestValue st.term 0 qfull 0 C) (g.restRestrict σ):=by
    rw [native_actual_resource_rest_value_retarget]
    exact native_original_centered_rest_test_fresh n q U b h K st.tree ho _ _ star
  have H0:=native_actual_second_low_resource_category_eq_full_B0_high_only M U hU ho hs st.term
  have H1:=native_actual_second_low_resource_category_eq_full_B0_high_only M U hU ho hs (st.term.retarget 0)
  dsimp only at H0 H1
  rw [HC] at H1
  have Htarget:(st.term.retarget 0).live.test.target=g.mark:=rfl
  rw [Htarget] at H1
  dsimp only [b,h,K,C,q,qfull,g] at H1
  unfold nativeActualOriginalFourOtherCategoryContrast_high_only
  dsimp only
  linear_combination H0-(1/2:ℝ)*H1

theorem actual_resource_full_B0_normalized_profile_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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
          (G.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)).restProduct)| ≤
          nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualOriginalCenteredResourceB0_high_only M U P| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let scalar:=nativeActualResourceOriginalScalar_high_only M U P
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as)
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  rw [native_actual_resource_centered_full_B0_eq_scalar_canonical_high_only P hi hs M U,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

theorem native_actual_original_full_four_second_low_abs_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) (hs : star < U)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (W B : ℝ)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0_high_only M U st.term| ≤ B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0_high_only M U (st.term.retarget 0)| ≤ B) :
    |(W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_high_only M U st .secondLow| ≤ (3/2:ℝ)*B := by
  rw [native_actual_four_second_low_eq_two_full_resource_sources_high_only M U hU ho hs st]
  have HE : (W⁻¹)^st.generation*(nativeActualOriginalCenteredResourceB0_high_only M U st.term-
      (1/2:ℝ)*nativeActualOriginalCenteredResourceB0_high_only M U (st.term.retarget 0))=
      (W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0_high_only M U st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0_high_only M U (st.term.retarget 0)):=by ring
  rw [HE,sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul (1/2:ℝ) _,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  exact (add_le_add H0 (mul_le_mul_of_nonneg_left H1 (by norm_num))).trans_eq (by ring)

theorem native_actual_constant_resource_canonical_source_radius_gate_high_only
    {n i star U : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (hi : i ≤ star) (hs : star<as.length) (bound : ℝ)
    (Hstar : M.R (partitionPoint 0 as star) ≤ bound) (e : Fin P.live.factors.length) :
    M.R ((nativeActualResourceCanonicalShape P.live hi hs).sourceLowMass e) ≤ bound := by
  rw [native_actual_constant_resource_canonical_source_mass_eq_star hP hi hs]
  exact Hstar

theorem native_actual_constant_resource_frozen_canonical_source_radius_gate_high_only
    {n i star U : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource (Spin n×Bool) as i star) (hF : F∈P.frozen)
    (hi : i ≤ star) (hs : star<as.length) (bound : ℝ)
    (Hstar : M.R (partitionPoint 0 as star) ≤ bound) (e : Fin F.monomial.factors.length) :
    M.R ((nativeActualResourceCanonicalShape F.monomial hi hs).sourceLowMass e) ≤ bound := by
  rw [native_actual_constant_resource_frozen_canonical_source_mass_eq_star hP F hF hi hs]
  exact Hstar

end OAI.SKFluctuations.Cavity
