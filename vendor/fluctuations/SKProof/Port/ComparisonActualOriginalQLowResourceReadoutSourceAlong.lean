module

public import ComparisonSignedCavityActualResourceLowTaylorReadout
public import ComparisonSignedCavityActualCenteredResourceLowTaylorReadout
public import ComparisonSignedCavityActualFreshResourceLowTaylorReadout
public import ComparisonSignedCavityActualResourceGammaRestorationReadout
public import ComparisonSignedCavityActualResourceJointLowRestorationReadout
public import ComparisonSignedCavityActualCenteredResourceJointLowRestorationReadout
public import ComparisonSignedCavityActualFreshResourceJointLowRestorationReadout
public import ComparisonSignedCavityActualFourJointLowRestorationProfile
public import ComparisonSignedCavityActualJointLowRestorationCategorySum
public import ComparisonSignedCavityActualFourGammaRestorationReadout
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQFourReadoutPrimitives
public import SKProof.Port.ComparisonActualOriginalQPhysicalTaylorProfiles

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
def nativeActualResourceThirdLowPart_original_q
  {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
  {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
  (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) (l t : ℝ) : ℝ :=
 let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
 let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
 let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
 let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
 let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
 let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
 nativeActualCenteredThirdLowPart n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C) a z l t

theorem actual_resource_third_LOW_normalized_profile_le_original_q
  {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
  {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
  {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
  (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
  (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star < as.length)
  (a z : T.Slot) (l t : ℝ)
  {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
  (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
   (finitePhysicalCavitySquareVariance n U as
    (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
   (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
   (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1)
  (Hlive :
   let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
   let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
   let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
   let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
   let G:=nativeActualResourceCanonicalShape P.live hi hstar
   |nativeActualCenteredThirdLowPart n q U b h K T
    (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct a z l t| ≤
    nativeResourceScale x W 1 P.live.tags*price) :
  |(W⁻¹)^k*nativeActualResourceThirdLowPart_original_q M U P a z l t| ≤
   |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
 let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
 let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
 let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
 let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
 let G:=nativeActualResourceCanonicalShape P.live hi hstar
 let scalar:=nativeActualResourceOriginalScalar_original_q M U P
 let F:=(G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct
 have HE : nativeActualResourceThirdLowPart_original_q M U P a z l t=
   scalar*nativeActualCenteredThirdLowPart n q U b h K T F a z l t := by
  unfold nativeActualResourceThirdLowPart_original_q
  dsimp only
  have HP : nativeActualResourceRestValue P 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)=(fun σ=>scalar*F σ):=by
   funext σ
   dsimp only [F,G]
   rw [native_actual_resource_canonical_rest_product_eq_live_original_q]
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
  (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)
  A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
  zero_lt_one le_rfl hi hstar Hpair
 change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
 dsimp only at Hlive
 rw [HE,mul_assoc,←mul_assoc,abs_mul]
 apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
 simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

def nativeActualOriginalCenteredResourceThirdLowPart_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeActualCenteredThirdLowPart n q U b h K T Pc a z l t

theorem native_actual_original_centered_resource_third_LOW_eq_two_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (a z : T.Slot) (l t : ℝ) :
    nativeActualOriginalCenteredResourceThirdLowPart_original_q M U P a z l t=
      nativeActualResourceThirdLowPart_original_q M U P a z l t+
      nativeActualResourceThirdLowPart_original_q M U P.freeze a z l t := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_resource_original_centered_rest_eq_two_resources (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalCenteredResourceThirdLowPart_original_q nativeActualResourceThirdLowPart_original_q
  dsimp only
  rw [Hread,actual_nativeActualCenteredThirdLowPart_add_test]

theorem native_actual_original_fresh_resource_third_LOW_eq_centered_retarget_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (l t : ℝ) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceThirdLowPart_original_q M U P l t=
      nativeActualOriginalCenteredResourceThirdLowPart_original_q M U (P.retarget 0)
        (g.embed P.live.test.target) g.mark l t := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalFreshResourceThirdLowPart_original_q nativeActualOriginalCenteredResourceThirdLowPart_original_q
  dsimp only
  rw [Hread]

def nativeActualResourceJointLowRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeCenteredLowGammaLowRestoration n q U b h K C T (nativeActualResourceRestValue P 0 qfull 0 C) a z

theorem actual_resource_joint_LOW_normalized_price_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star<as.length) (hU : U ≤ as.length)
    (a z : T.Slot)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1)
    (Hlive :
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hstar
      |nativeCenteredLowGammaLowRestoration n q U b h K C T
        (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct a z| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceJointLowRestoration_original_q M U P a z| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let scalar:=nativeActualResourceOriginalScalar_original_q M U P
  let F:=(G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : nativeActualResourceJointLowRestoration_original_q M U P a z=
      scalar*nativeCenteredLowGammaLowRestoration n q U b h K C T F a z := by
    have HP : nativeActualResourceRestValue P 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [native_actual_resource_canonical_rest_product_eq_live_original_q]
      unfold nativeActualResourceRestValue
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro e he
      simp [deletedOverlap,joinSpin,C]
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    unfold nativeActualResourceJointLowRestoration_original_q
    dsimp only
    rw [HP]
    exact native_centered_low_gamma_low_restoration_const_mul n q U b h K C T ho F a z scalar
      (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
      (by intro x;cases x <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm hU
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi hstar Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

def nativeActualOriginalCenteredResourceJointLowRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeCenteredLowGammaLowRestoration n q U b h K C T Pc a z

theorem native_actual_original_centered_resource_joint_LOW_restoration_eq_two_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (hU : U ≤ as.length)
    (a z : T.Slot) :
    nativeActualOriginalCenteredResourceJointLowRestoration_original_q M U P a z=
      nativeActualResourceJointLowRestoration_original_q M U P a z+
      nativeActualResourceJointLowRestoration_original_q M U P.freeze a z := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_resource_original_centered_rest_eq_two_resources (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalCenteredResourceJointLowRestoration_original_q nativeActualResourceJointLowRestoration_original_q
  dsimp only
  rw [Hread]
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  exact native_centered_low_gamma_low_restoration_add n q U b h K C T ho _ _ a z
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm hU

def nativeActualOriginalFreshResourceJointLowRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeCenteredLowGammaLowRestoration n q U b h K C g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark

theorem native_actual_original_fresh_resource_joint_LOW_restoration_eq_centered_retarget_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceJointLowRestoration_original_q M U P=
      nativeActualOriginalCenteredResourceJointLowRestoration_original_q M U (P.retarget 0)
        (g.embed P.live.test.target) g.mark := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalFreshResourceJointLowRestoration_original_q nativeActualOriginalCenteredResourceJointLowRestoration_original_q
  dsimp only
  rw [Hread]

theorem native_actual_four_joint_LOW_restoration_contrast_eq_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    nativeActualOriginalFourOtherCategoryContrast_original_q M U st .jointLowRestoration=
      -(nativeActualOriginalFreshResourceJointLowRestoration_original_q M U st.term-
        (1/2:ℝ)*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U (st.term.retarget 0)) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalFourOtherCategoryContrast_original_q nativeActualOriginalOtherSourceCategory
    nativeActualOriginalFreshResourceJointLowRestoration_original_q
  dsimp only
  rw [Hread]
  dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,
    NativeGeneratedTest.retarget]
  ring

def nativeActualOriginalFourJointLowRestorationError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U st .jointLowRestoration)

theorem actual_minimum_four_joint_LOW_restoration_error_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U ≤ as.length)
    {W cK B : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourJointLowRestorationError_original_q M U W st| ≤
      |st.term.coefficient| *(2/(Real.exp (-4*(Temp+2*Cf))*cK))*B := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  obtain ⟨hden,_,hdenlo⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q M
    hCf HS hxs hW hcK ho hs hU hstarK
  have hterm : 0 ≤ |st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U st.term) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by linarith
  unfold nativeActualOriginalFourJointLowRestorationError_original_q
  dsimp only
  rw [native_actual_four_joint_LOW_restoration_contrast_eq_resources_original_q M U st ho,mul_neg,mul_neg,abs_neg,mul_sub]
  have Hring : (W⁻¹)^st.generation*((1/2:ℝ)*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U (st.term.retarget 0))=
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration_original_q M U (st.term.retarget 0)):=by ring
  rw [Hring,abs_mul,abs_of_pos (div_pos zero_lt_one hden)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (div_nonneg zero_le_one hden.le)).trans
  have Hfrac : 1/(chi*K star) ≤ 1/(Cd*W):=div_le_div_of_nonneg_left zero_le_one (mul_pos hCd hW) hdenlo
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  dsimp only [Cd]
  field_simp

theorem actual_joint_LOW_restoration_category_signed_sum_abs_le_error_sum_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U Q .jointLowRestoration)).sum|/
      (chi*K star) ≤ (xs.map (fun Q=>|nativeActualOriginalFourJointLowRestorationError_original_q M U W Q|)).sum := by
  dsimp only
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q M hCf HS hxs hW hcK ho hs hU hstarK
  have H:=native_abs_sum_map_le xs (nativeActualOriginalFourJointLowRestorationError_original_q M U W)
  unfold nativeActualOriginalFourJointLowRestorationError_original_q at H
  dsimp only at H
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [nativeActualOriginalFourJointLowRestorationError_original_q,one_div,one_mul,mul_comm,div_eq_mul_inv] using H

theorem actual_gamma_restoration_category_signed_sum_abs_le_error_sum_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) (high : Bool) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U Q
      (nativeActualGammaRestorationCategory high))).sum|/(chi*K star) ≤
      (xs.map (fun Q=>|nativeActualOriginalFourGammaRestorationError_original_q M U W Q high|)).sum := by
  dsimp only
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q M hCf HS hxs hW hcK ho hs hU hstarK
  have H:=native_abs_sum_map_le xs (fun Q=>nativeActualOriginalFourGammaRestorationError_original_q M U W Q high)
  unfold nativeActualOriginalFourGammaRestorationError_original_q at H
  dsimp only at H
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [nativeActualOriginalFourGammaRestorationError_original_q,one_div,one_mul,mul_comm,div_eq_mul_inv] using H

end OAI.SKFluctuations.Cavity
