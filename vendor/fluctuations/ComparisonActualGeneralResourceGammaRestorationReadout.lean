module

public import ComparisonSignedCavityActualGammaRestorationAffine
public import ComparisonActualGeneralResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def actualGeneralResourceGammaSecondRestoration
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (high : Bool) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeGammaProjectedSecondRestoration high T P.live.test.target star U q b h K
    (restCenteredFixedForkKernel n b C star 0) Pc

theorem actual_general_resource_gamma_second_restoration_normalized_profile_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < U)
    (high : Bool)
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
      let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
      |nativeGammaProjectedSecondRestoration high T P.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0)
        (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*actualGeneralResourceGammaSecondRestoration bf hf U P high| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
  let scalar:=actualGeneralResourceOriginalScalar bf hf U P
  let F:=(G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : actualGeneralResourceGammaSecondRestoration bf hf U P high=
      scalar*nativeGammaProjectedSecondRestoration high T P.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0) F := by
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let c:=-nativeOriginalRestTestExpectation n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    have HP : nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)=
        (fun σ=>scalar*F σ+c) := by
      funext σ
      let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
      have Hτ : (T.cavityAssignment τ).1=σ := by simp only [τ,Equiv.apply_symm_apply]
      have Hlive:=actual_general_resource_canonical_product_eq_live P.live hi
        (hs.trans_le hP.highCut_le_length) bf hf τ
      rw [ActualNaturalBoundaryShape.product_eq_restProduct,Hτ] at Hlive
      unfold nativeOriginalCenteredRestTest
      rw [←Hτ,native_actual_resource_rest_value_eq_full]
      change P.scalar (fullWeight n) (fullFeature n) 0 qfull
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0*
          P.live.test.value (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C τ-
          nativeOriginalRestTestExpectation n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)=_
      rw [←Hlive]
      rw [Hτ]
      change scalar*F σ- _=scalar*F σ+c
      rfl
    unfold actualGeneralResourceGammaSecondRestoration
    dsimp only
    rw [HP]
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (bf u:ℝ) ≤ bf v from hbf hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (hf u:ℝ) ≤ hf v from hhf hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
    have HKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
    exact native_actual_generated_gamma_second_restoration_affine hP hi hs ho q b h K
      (restCenteredFixedForkKernel n b C star 0) F scalar c
      (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
      (by intro x;cases x <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm high
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n bf hf as)
    A x W 1 hA hx (hx.trans_le hxW)
    zero_lt_one le_rfl hi (hs.trans_le hP.highCut_le_length) Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
