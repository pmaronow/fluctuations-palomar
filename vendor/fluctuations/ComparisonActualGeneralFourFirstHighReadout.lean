module

public import ComparisonActualGeneralResourceFirstHighReadout
public import ComparisonSignedCavityActualFourFirstHighReadout

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_generated_first_high_sub_const
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (c : ℝ) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A (fun σ=>P σ-c)=
      nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A P := by
  dsimp only
  rw [actual_general_generated_Gamma_first_high_eq_paired_source bf hf hbf hhf hP hi hs ho,
    actual_general_generated_Gamma_first_high_eq_paired_source bf hf hbf hhf hP hi hs ho]
  congr 1
  congr 1
  apply List.map_congr_left
  intro p hp
  have H : nativeRestProjectedPairedTest T P₀.live.test.target star A (fun σ=>P σ-c) p=
      nativeRestProjectedPairedTest T P₀.live.test.target star A P p := by
    funext σ
    dsimp only [nativeRestProjectedPairedTest]
    ring
  rw [H]

theorem actual_general_resource_first_high_eq_rest_readout
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (_hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (_hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    actualGeneralResourceFirstHigh bf hf U P=
      nativeGammaProjectedFirstHighDisplacement T P.live.test.target star U
        (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
        (fun σ τ=>(∑j,spinValue (σ j)*spinValue (τ j))/(n+1:ℕ))
        (nativeActualResourceRestValue P 0 qfull 0 C) := by
  dsimp only
  unfold actualGeneralResourceFirstHigh actualGeneralGeneratedFirstHigh
  rw [←native_gamma_first_high_const_mul]
  unfold nativeActualResourceRestValue actualGeneralResourceOriginalScalar
  simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]

theorem actual_general_resource_centered_first_high
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeGammaProjectedFirstHighDisplacement T P.live.test.target star U q b h K
      (restCenteredFixedForkKernel n b C star 0) Pc=
      b star*actualGeneralResourceFirstHigh bf hf U P := by
  dsimp only
  rw [actual_general_resource_first_high_eq_rest_readout bf hf hbf hhf]
  dsimp only
  have HK (b C : ℕ→ℝ) : restCenteredFixedForkKernel n b C star 0=
      fun σ τ=>b star*((∑j,spinValue (σ j)*spinValue (τ j))/(n+1:ℕ)-C star) := by
    funext σ τ
    rfl
  rw [HK,native_gamma_first_high_affine_kernel]
  congr 1
  exact actual_general_generated_first_high_sub_const bf hf hbf hhf hP hi hs ho _ _ _
