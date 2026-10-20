module

public import ComparisonSignedCavitySecondLowCenteredReplacementSource
public import ComparisonSignedCavityActualResourceCanonicalShape
public import ComparisonSignedCavityActualResourceScalarScale
public import ComparisonSignedCavityActualResourceGaReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

private theorem b0_rest_disorder_const_mul {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (q : ℕ→RestCoordinate n→ℝ)
    (P : T.Assignment→ℝ) (c : ℝ) :
    T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>c*P σ) 0=
      c*T.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  unfold ClockTree.disorderExpect
  simp only [mul_left_comm,←Finset.mul_sum]

 theorem native_second_low_double_average_const_mul {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (F : (p : MarkedPlacement T)→MarkedPlacement p.tree→ℝ) (c : ℝ) :
    nativeSecondLowDoubleAverage T (fun p r=>c*F p r)=c*nativeSecondLowDoubleAverage T F := by
  unfold nativeSecondLowDoubleAverage
  simp only [mul_left_comm,List.sum_map_mul_left]
  ring

 theorem native_second_low_joint_ledger_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) (c : ℝ) :
    nativeSecondLowJointLedger n q U b h K T (fun σ=>c*P σ) es=
      c*nativeSecondLowJointLedger n q U b h K T P es := by
  have Htest (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
      (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) :
      nativeSecondLowJointRestTest n U b h K (fun σ=>c*P σ) p r s t=
        fun τ=>c*nativeSecondLowJointRestTest n U b h K P p r s t τ := by
    funext τ
    rw [native_second_low_joint_rest_test_product,native_second_low_joint_rest_test_product]
    ring
  unfold nativeSecondLowJointLedger
  simp_rw [Htest,b0_rest_disorder_const_mul,mul_assoc]
  simp_rw [native_second_low_double_average_const_mul]

 theorem native_second_low_unweighted_c_replacement_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (f c z : T.Slot)
    (P : T.cavityLeft.Assignment→ℝ) (a : ℝ) :
    nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z (fun σ=>a*P σ)=
      a*nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z P := by
  have Htest (p : MarkedPlacement T) :
      (fun τ=>nativeSecondLowUnweightedCPayload n U b h K T f c z (fun σ=>a*P σ) p τ-
        nativeSecondLowUnweightedCOldPayload n U b h K T f c z (fun σ=>a*P σ) (p.restRestrict τ))=
      fun τ=>a*(nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
        nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ)) := by
    funext τ
    unfold nativeSecondLowUnweightedCPayload nativeSecondLowUnweightedCOldPayload
    ring
  unfold nativeSecondLowUnweightedCReplacementRow
  simp_rw [Htest,b0_rest_disorder_const_mul,mul_left_comm]
  rw [List.sum_map_mul_left]

 theorem native_second_low_canonical_c_replacement_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c z : T.Slot) (A : ℝ) :
    nativeSecondLowCanonicalCReplacementSource n q U b h K T (fun σ=>A*P σ) a c z=
      A*nativeSecondLowCanonicalCReplacementSource n q U b h K T P a c z := by
  unfold nativeSecondLowCanonicalCReplacementSource
  simp_rw [native_second_low_unweighted_c_replacement_const_mul,mul_left_comm]
  rw [List.sum_map_mul_left]

 theorem native_second_low_fresh_c_replacement_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment→ℝ) (A : ℝ) :
    nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU (fun σ=>A*P σ)=
      A*nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P := by
  unfold nativeSecondLowFreshOccupiedCReplacementSource
  simp_rw [native_second_low_canonical_c_replacement_const_mul]
  rw [Finset.mul_sum]

 theorem native_second_low_fresh_B0_minus_c_replacement_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment→ℝ) (A : ℝ) :
    nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU (fun σ=>A*P σ)=
      A*nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU P := by
  unfold nativeSecondLowFreshB0MinusCReplacementSource
  simp_rw [native_second_low_joint_ledger_const_mul,native_second_low_fresh_c_replacement_const_mul]
  ring

 theorem native_original_B0_mean_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (A : ℝ) :
    nativeOriginalRestTestExpectation n q U b h K T (fun σ=>A*P σ)=
      A*nativeOriginalRestTestExpectation n q U b h K T P := by
  unfold nativeOriginalRestTestExpectation ClockTree.disorderExpect
  simp only [mul_left_comm,←Finset.mul_sum]

 theorem native_original_B0_centered_test_const_mul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (A : ℝ) :
    nativeOriginalCenteredRestTest n q U b h K T (fun σ=>A*P σ)=
      fun σ=>A*nativeOriginalCenteredRestTest n q U b h K T P σ := by
  funext σ
  unfold nativeOriginalCenteredRestTest
  rw [native_original_B0_mean_const_mul]
  ring

 theorem native_actual_resource_B0_rest_value_eq_scalar_canonical
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (hi : i ≤ star) (hs : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) :
    nativeActualResourceRestValue P 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      0 (nativePhysicalResourceCenter n M.bf M.hf as)=
      fun σ=>nativeActualResourceOriginalScalar M U P*
        ((nativeActualResourceCanonicalShape P.live hi hs).canonicalMinimumSource M
          (fun _=>NativeSourceFactorForm.centered)).restProduct σ := by
  funext σ
  rw [native_actual_resource_canonical_rest_product_eq_live]
  unfold nativeActualResourceRestValue nativeActualResourceOriginalScalar
  congr 1
  apply congrArg (fun R=>nativeRestGeneratedTestValue T P.live.test R _ σ)
  funext s t
  simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]

 def nativeActualOriginalCenteredResourceB0MinusCReplacement
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (hU : U ≤ as.length) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T P.live.test.target star hU
    (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))

 theorem native_actual_resource_centered_B0_minus_c_replacement_eq_scalar_canonical
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceTerm i star T) (hi : i ≤ star) (hs : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (hU : U ≤ as.length) :
    nativeActualOriginalCenteredResourceB0MinusCReplacement M U hU P=
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      nativeActualResourceOriginalScalar M U P*
        nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T P.live.test.target star hU
          (nativeOriginalCenteredRestTest n q U b h K T
            ((nativeActualResourceCanonicalShape P.live hi hs).canonicalMinimumSource M
              (fun _=>NativeSourceFactorForm.centered)).restProduct) := by
  unfold nativeActualOriginalCenteredResourceB0MinusCReplacement
  dsimp only
  rw [native_actual_resource_B0_rest_value_eq_scalar_canonical P hi hs M U,
    native_original_B0_centered_test_const_mul,native_second_low_fresh_B0_minus_c_replacement_const_mul]

end OAI.SKFluctuations.Cavity
