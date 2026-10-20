module

public import ComparisonSignedCavityJointLowRestorationLinearity
public import ComparisonSignedCavityActualResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

def nativeActualResourceJointLowRestoration
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeCenteredLowGammaLowRestoration n q U b h K C T (nativeActualResourceRestValue P 0 qfull 0 C) a z

theorem actual_resource_joint_LOW_normalized_price_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star<as.length) (hU : U ≤ as.length)
    (a z : T.Slot)
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
      let C:=nativePhysicalResourceCenter n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hstar
      |nativeCenteredLowGammaLowRestoration n q U b h K C T
        (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct a z| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceJointLowRestoration M U P a z| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let scalar:=nativeActualResourceOriginalScalar M U P
  let F:=(G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : nativeActualResourceJointLowRestoration M U P a z=
      scalar*nativeCenteredLowGammaLowRestoration n q U b h K C T F a z := by
    have HP : nativeActualResourceRestValue P 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [native_actual_resource_canonical_rest_product_eq_live]
      unfold nativeActualResourceRestValue
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro e he
      simp [deletedOverlap,joinSpin,C]
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.inherited_bf_monotone hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.inherited_hf_monotone hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    have HKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    unfold nativeActualResourceJointLowRestoration
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

end OAI.SKFluctuations.Cavity
