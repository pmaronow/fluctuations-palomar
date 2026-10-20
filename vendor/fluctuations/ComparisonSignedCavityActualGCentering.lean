module

public import ComparisonSignedCavityActualOriginalMeanSaving
public import ComparisonSignedCavityActualGInsertionTerminal

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem nativeActualResourceGInsertion_freeze_eq_original_mean
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ) (W : ℝ) :
    let b := fun j => (M.bf (partitionPoint 0 as j):ℝ)
    let h := fun j => (M.hf (partitionPoint 0 as j):ℝ)
    let K := finitePhysicalMixedClock (n+1) as b h
    let q := finitePhysicalCavitySquareVariance n U as b h 1 1
    let C := nativePhysicalResourceCenter n M.bf M.hf as
    nativeActualResourceGInsertion M P.freeze U k 0 q 0 W =
      -(W⁻¹)^k*T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (P.value (fullWeight n) (fullFeature n) 0 q
          (fun σ τ => deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0) 0*
        nativeOriginalLongitudinalMean T U K b h C P.live.test.target := by
  dsimp only
  let b := fun j => (M.bf (partitionPoint 0 as j):ℝ)
  let h := fun j => (M.hf (partitionPoint 0 as j):ℝ)
  let K := finitePhysicalMixedClock (n+1) as b h
  let q := finitePhysicalCavitySquareVariance n U as b h 1 1
  let C := nativePhysicalResourceCenter n M.bf M.hf as
  let mean := T.disorderExpect (fullWeight n) (fullFeature n) 0 q
    (P.value (fullWeight n) (fullFeature n) 0 q
      (fun σ τ => deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0) 0
  have Hatom (g : NativeOriginalGMarkedWord T) :
      g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ => (W⁻¹)^k*((g.liftResource P.freeze).value (fullWeight n) (fullFeature n) 0 q
          (fun σ τ => deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ*
          g.atom M U P.freeze.live.test.target σ)) 0 =
        (-(W⁻¹)^k*mean)*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
          (g.atom M U P.live.test.target) 0 := by
    simp_rw [g.liftResource_value,P.freeze_value (fullWeight_pos n) (fullFeature n) ho]
    have HF : (fun σ => (W⁻¹)^k*(-mean*g.atom M U P.freeze.live.test.target σ)) =
        fun σ => (-(W⁻¹)^k*mean)*g.atom M U P.live.test.target σ := by
      funext σ
      change (W⁻¹)^k*(-mean*g.atom M U P.live.test.target σ)=_
      ring
    rw [HF,g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  unfold nativeActualResourceGInsertion
  change ((nativeOriginalGMarkedWords T).map (fun g => g.coefficient*
    g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ => (W⁻¹)^k*((g.liftResource P.freeze).value (fullWeight n) (fullFeature n) 0 q
        (fun σ τ => deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ*
        g.atom M U P.freeze.live.test.target σ)) 0)).sum =
    -(W⁻¹)^k*mean*nativeOriginalLongitudinalMean T U K b h C P.live.test.target
  simp_rw [Hatom]
  have Hsum :
      ((nativeOriginalGMarkedWords T).map (fun g => g.coefficient*
        ((-(W⁻¹)^k*mean)*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
          (g.atom M U P.live.test.target) 0))).sum =
      (-(W⁻¹)^k*mean)*((nativeOriginalGMarkedWords T).map (fun g => g.coefficient*
        g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
          (g.atom M U P.live.test.target) 0)).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro g _
    ring
  rw [Hsum]
  congr 1
  simpa only [NativeOriginalGMarkedWord.atom,NativeOriginalGMarkedWord.tree,
    nativeMinimumOriginalHighGAtom,nativeOriginalLongitudinalMean,q,K,b,h,C,
    finitePhysicalCavitySquareVariance] using nativeOriginalGMarkedWords_weighted_kernel_sum T
      (fun p r z => z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (nativeOriginalHighGAtom z.tree U K b C
          (z.embed (r.embed (p.embed P.live.test.target))) (z.embed (r.embed p.mark))
          (z.embed r.mark) z.mark) 0)

end OAI.SKFluctuations.Cavity
