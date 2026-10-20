module

public import ComparisonActualGeneralGammaFirstHighPairedSource
public import ComparisonActualGeneralResourceGaReadout
public import ComparisonSignedCavityActualGammaFirstHighBoundedDegree

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

def actualGeneralGeneratedFirstHigh {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (star U : ℕ)
    (P : NativeGeneratedTest T) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  nativeGammaProjectedFirstHighDisplacement T P.target star U
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h
    (nativeContinuumMixedClock n bf hf as) A
    (nativeRestGeneratedTestValue T P A (nativePhysicalResourceCenter n bf hf as))

theorem actual_general_generated_first_high_empty_live
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (hempty : P₀.live.test.edges=[]) :
    actualGeneralGeneratedFirstHigh bf hf T star U P₀.live.test=0 := by
  unfold actualGeneralGeneratedFirstHigh
  dsimp only
  have HE (A : Spin n→Spin n→ℝ) (C : ℕ→ℝ) :
      nativeRestGeneratedTestValue T P₀.live.test A C=fun _=>1 := by
    funext σ
    simp only [nativeRestGeneratedTestValue,hempty,List.map_nil,List.prod_nil]
  rw [HE,actual_general_generated_Gamma_first_high_eq_paired_source bf hf hbf hhf hP hi hs ho]
  simp only [native_rest_projected_paired_constant_zero,retained_signed_jets_zero_test,
    mul_zero,List.map_const',List.sum_replicate,nsmul_zero]

def actualGeneralResourceFirstHigh
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ:=
  actualGeneralResourceOriginalScalar bf hf U P *
    actualGeneralGeneratedFirstHigh bf hf T star U P.live.test

end OAI.SKFluctuations.Cavity
