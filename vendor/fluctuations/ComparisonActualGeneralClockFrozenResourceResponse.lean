module

public import ComparisonActualGeneralClockGAtomBounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
theorem NativeOriginalGMarkedWord.actual_general_clock_frozen_normalized_resource_pairing_abs_le_of_total_clock
    {n : ℕ} {Temp : ℝ}
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (g : NativeOriginalGMarkedWord T)
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (a : T.Slot)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0 < A) (hx : 0 < x) (hW : 0 < W) (hε : 0 < ε)
    (hi : i  ≤  star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n bf hf as) x₀ A x W ε)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n bf hf as) y A x W ε) :
    |g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n bf hf as) x₀ σ*g.physicalClockAtom bf hf K U a σ)) y| ≤ 
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) := by
  exact hP.normalized_frozen_transported_terminal_pairing_abs_le (g.liftResource P)
    (g.liftResource_resources P) (g.liftResource_coefficient P)
    (fullWeight_pos n) (fullFeature n) ho v₀ q₀ x₀ v q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n bf hf as) y A x W ε hA hx hW hε hi hstar
    (g.liftResource_pairMomentBudget P v₀ q₀ _ _ x₀ A x W ε hm₀)
    (g.liftResource_pairMomentBudget P v q _ _ y A x W ε hm).1
    (g.physicalClockAtom bf hf K U a) (2*Temp) (by positivity)
    (g.actual_general_clock_second_moment_le_of_total_clock bf hf K hbf hhf hTemp htotal ho U a v q y)

def actualGeneralClockFrozenResourceGInsertion
    {n : ℕ} 
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (U k : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) : ℝ :=
  ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n bf hf as) x₀ σ*
          g.physicalClockAtom bf hf K U P.live.test.target σ)) x)).sum

 theorem actual_general_clock_frozen_resource_g_insertion_eq_clock_response
    {n : ℕ} 
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    actualGeneralClockFrozenResourceGInsertion bf hf K P U k v₀ q₀ x₀ v q x W=
      nativeOriginalClockResourceResponse P U k K
        (fun j=>(bf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n bf hf as) v₀ q₀ x₀ v q x W := by
  have Hatom (g : NativeOriginalGMarkedWord T) :
      g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n bf hf as) x₀ σ*g.physicalClockAtom bf hf K U P.live.test.target σ)) x=
        (W⁻¹)^k*g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P.value (fullWeight n) (fullFeature n) v₀ q₀
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
            (nativePhysicalResourceCenter n bf hf as) x₀
            (g.p.restrict (g.r.restrict (g.z.restrict σ)))*g.physicalClockAtom bf hf K U P.live.test.target σ) x := by
    simp_rw [g.liftResource_value]
    rw [g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  unfold actualGeneralClockFrozenResourceGInsertion
  simp_rw [Hatom]
  unfold nativeOriginalClockResourceResponse
  have H:=nativeOriginalGMarkedWords_weighted_kernel_sum T
    (fun p r z=>z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n bf hf as) x₀ (p.restrict (r.restrict (z.restrict σ)))*
          nativeOriginalHighGAtom z.tree U
            K
            (fun j=>(bf (partitionPoint 0 as j):ℝ))
            (nativePhysicalResourceCenter n bf hf as)
            (z.embed (r.embed (p.embed P.live.test.target)))
            (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x)
  conv_rhs =>
    unfold nativeOriginalLongitudinalPairing
    rw [←H,←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  simp only [NativeOriginalGMarkedWord.physicalClockAtom,NativeOriginalGMarkedWord.tree,
    actualGeneralClockHighGAtom]
  ring

theorem actual_general_clock_frozen_resource_response_abs_le_of_total_clock
    {n : ℕ} {Temp : ℝ}
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (r : ℕ) (hr : T.leaves ≤ r)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0 < A) (hx : 0 < x) (hW : 0 < W) (hε : 0 < ε)
    (hi : i  ≤  star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n bf hf as) x₀ A x W ε)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n bf hf as) y A x W ε) :
    |nativeOriginalClockResourceResponse P U k K
        (fun j=>(bf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n bf hf as) v₀ q₀ x₀ v q y W| ≤ 
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp)*
        nativeActualGInsertionCost r := by
  have hscale : 0 ≤ nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  rw [←actual_general_clock_frozen_resource_g_insertion_eq_clock_response bf hf K P ho]
  unfold actualGeneralClockFrozenResourceGInsertion
  apply (nativeActualWeightedTerminalSum_abs_le _ _ _ (by
    intro g hg
    exact g.actual_general_clock_frozen_normalized_resource_pairing_abs_le_of_total_clock bf hf K hbf hhf hTemp htotal hP ho
      P.live.test.target v₀ q₀ x₀ v q y A x W ε hA hx hW hε hi hstar hm₀ hm)).trans
  have HV:=mul_le_mul_of_nonneg_right (nativeOriginalGMarkedWords_variation_le T ho r hr)
    (show 0 ≤ |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) by positivity)
  simpa only [nativeActualGInsertionCost,mul_comm] using HV

end OAI.SKFluctuations.Cavity
