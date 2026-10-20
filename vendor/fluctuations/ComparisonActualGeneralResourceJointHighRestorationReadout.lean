module

public import ComparisonSignedCavityJointHighRestorationSource
public import ComparisonActualGeneralResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

def actualGeneralResourceJointHighRestoration
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeJointHighRestorationSource kind n q U b h K C T (nativeActualResourceRestValue P 0 qfull 0 C) a z

theorem actual_general_resource_joint_HIGH_normalized_price_le
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star<as.length)
    (a z : T.Slot)
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
      let C:=nativePhysicalResourceCenter n bf hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hstar
      |nativeJointHighRestorationSource kind n q U b h K C T
        (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct a z| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*actualGeneralResourceJointHighRestoration kind bf hf U P a z| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  let F:=(G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : actualGeneralResourceJointHighRestoration kind bf hf U P a z=
      scalar*nativeJointHighRestorationSource kind n q U b h K C T F a z := by
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
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (bf u:ℝ) ≤ bf v from hbf hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (hf u:ℝ) ≤ hf v from hhf hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
    have HKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
    unfold actualGeneralResourceJointHighRestoration
    dsimp only
    rw [HP]
    have H:=native_joint_HIGH_restoration_source_test_linear kind n q U b h K C T ho F F a z scalar 0
      (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
      (by intro x;cases x <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm
    simpa only [zero_mul,add_zero] using H

  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C
    A x W 1 hA hx (hx.trans_le hxW)
    zero_lt_one le_rfl hi hstar Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
