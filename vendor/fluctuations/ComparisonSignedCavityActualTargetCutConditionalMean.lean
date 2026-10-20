module

public import ComparisonSignedCavityActualMinimumConstantMeanExchange
public import ComparisonSignedCavityOriginalLongitudinalConditionalReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_constant_gap_eq_twice_conditional_insertion
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    finitePhysicalMean (n+1) as b h i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      chi^2*b i*(finitePhysicalMean (n+1) as b h i-
        finitePhysicalMean (n+1) as b h i/(n+1:ℕ)-C i)+
      2*b i*chi*nativeOriginalConditionalLongitudinalPair T s i U K b C 0 qfull 0 A+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have H:=actual_minimum_constant_gap_eq_twice_old_longitudinal M as i U hi hU ho
  dsimp only at H
  have HL:=native_original_longitudinal_pair_eq_conditional_insertion
    (single (S:=Spin n×Bool) as) ho (singleSlot as) i U hi hU
    (nativeContinuumMixedClock n M.bf M.hf as)
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n M.bf M.hf as)
    0 (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun u v : Spin n×Bool=>deletedOverlap n (joinSpin u) (joinSpin v)-
      nativePhysicalResourceCenter n M.bf M.hf as i)
  dsimp only at HL
  rw [HL] at H
  exact H

theorem actual_minimum_continuum_gap_eq_conditional_insertion_and_corrections
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    C i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      -(chi^2*b i*finitePhysicalMean (n+1) as b h i/(n+1:ℕ))+
      (chi^2*b i-1)*(finitePhysicalMean (n+1) as b h i-C i)+
      2*b i*chi*nativeOriginalConditionalLongitudinalPair T s i U K b C 0 qfull 0 A+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have H:=actual_minimum_constant_gap_eq_twice_conditional_insertion M as i U hi hU ho
  dsimp only at H
  linear_combination H

end OAI.SKFluctuations.Cavity
