module

public import SKProof.Port.ComparisonActualOriginalQCurrentGOriginalLawRestoration
public import ComparisonSignedCavityActualFourGaReadout
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQActualResourceGaReadout

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem nativeActualResourceGa_eq_rest_readout_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualResourceGa_original_q M U P=
      nativeActualOriginalGProjectedResampling T P.live.test.target star U K b C 0
        (cutFullVariance n q U 1 1 b h K) 0
        (fun σ τ=>(∑j,spinValue (σ.1 j)*spinValue (τ.1 j))/(n+1:ℕ))
        (fun σ=>nativeActualResourceRestValue P 0 qfull 0 C (T.cavityAssignment σ).1) := by
  dsimp only
  rw [native_actual_resource_rest_function_eq_full]
  unfold NativeResourceTerm.value
  have H:=native_original_G_resampling_affine_test T P.live.test.target star U
    (nativeContinuumMixedClock n M.sweepBf M.sweepHf as)
    (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0
    (cutFullVariance n (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
      (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))) U 1 1
      (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
      (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ))
      (nativeContinuumMixedClock n M.sweepBf M.sweepHf as)) 0
    (fun σ τ=>(∑j,spinValue (σ.1 j)*spinValue (τ.1 j))/(n+1:ℕ))
    (P.live.test.value (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as))
    (nativeActualResourceOriginalScalar_original_q M U P) 0
  simp only [sub_zero] at H
  unfold nativeActualResourceOriginalScalar_original_q at H
  rw [H]
  unfold nativeActualResourceGa_original_q nativeActualCoupledGProjectedResampling_original_q nativeActualResourceOriginalScalar_original_q
  simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  rfl

theorem actual_minimum_resource_centered_Ga_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeActualOriginalGProjectedResampling T P.live.test.target star U K b C 0
      (cutFullVariance n q U 1 1 b h K) 0
      (fun σ τ=>restCenteredFixedForkKernel n b C star 0 σ.1 τ.1)
      (fun σ=>Pc (T.cavityAssignment σ).1)=b star*nativeActualResourceGa_original_q M U P := by
  dsimp only
  rw [nativeActualResourceGa_eq_rest_readout_original_q]
  dsimp only
  have HK (b C : ℕ→ℝ) :
      (fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b C star 0 σ.1 τ.1)=
        fun σ τ=>b star*((∑j,spinValue (σ.1 j)*spinValue (τ.1 j))/(n+1:ℕ)-C star) := by
    funext σ τ
    rfl
  rw [HK,native_original_G_resampling_affine_kernel]
  congr 1
  unfold nativeOriginalCenteredRestTest
  simpa only [one_mul] using native_original_G_resampling_affine_test T P.live.test.target star U
    (nativeContinuumMixedClock n M.sweepBf M.sweepHf as)
    (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)
    0 _ 0 _ (fun σ=>nativeActualResourceRestValue P 0 _ 0 _ (T.cavityAssignment σ).1) 1 _

end OAI.SKFluctuations.Cavity
