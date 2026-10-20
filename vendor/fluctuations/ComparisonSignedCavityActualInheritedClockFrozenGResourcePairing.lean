module

public import ComparisonSignedCavityActualClockFrozenGResourcePairing
public import ComparisonSignedCavityActualInheritedClockGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem NativeOriginalGMarkedWord.actual_clock_frozen_normalized_resource_pairing_abs_le_of_total_clock
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (g : NativeOriginalGMarkedWord T)
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (a : T.Slot)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) y A x W ε) :
    |g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ*g.clockAtom M K U a σ)) y|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) := by
  exact hP.normalized_frozen_transported_terminal_pairing_abs_le (g.liftResource P)
    (g.liftResource_resources P) (g.liftResource_coefficient P)
    (fullWeight_pos n) (fullFeature n) ho v₀ q₀ x₀ v q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) y A x W ε hA hx hW hε hi hstar
    (g.liftResource_pairMomentBudget P v₀ q₀ _ _ x₀ A x W ε hm₀)
    (g.liftResource_pairMomentBudget P v q _ _ y A x W ε hm).1
    (g.clockAtom M K U a) (2*Temp) (by positivity)
    (g.actual_clock_second_moment_le_of_total_clock M K hTemp htotal ho U a v q y)

theorem nativeActualClockFrozenResourceResponse_abs_le_of_total_clock
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (r : ℕ) (hr : T.leaves≤r)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) y A x W ε) :
    |nativeOriginalClockResourceResponse P U k K
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n M.bf M.hf as) v₀ q₀ x₀ v q y W|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp)*
        nativeActualGInsertionCost r := by
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  rw [←nativeActualClockFrozenResourceGInsertion_eq_clock_response M K P ho]
  unfold nativeActualClockFrozenResourceGInsertion
  apply (nativeActualWeightedTerminalSum_abs_le _ _ _ (by
    intro g hg
    exact g.actual_clock_frozen_normalized_resource_pairing_abs_le_of_total_clock M K hTemp htotal hP ho
      P.live.test.target v₀ q₀ x₀ v q y A x W ε hA hx hW hε hi hstar hm₀ hm)).trans
  have HV:=mul_le_mul_of_nonneg_right (nativeOriginalGMarkedWords_variation_le T ho r hr)
    (show 0≤|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) by positivity)
  simpa only [nativeActualGInsertionCost,mul_comm] using HV

end OAI.SKFluctuations.Cavity
