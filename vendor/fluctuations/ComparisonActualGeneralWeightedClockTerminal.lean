module

public import ComparisonActualGeneralClockFrozenResourceResponse
public import ComparisonSignedCavityActualWeightedGTerminal

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem actual_general_weighted_clock_frontier_terminal_abs_le_of_pair_budgets
    {n : ℕ} {Temp : ℝ}
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hTemp : 0 ≤ Temp) (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (Gamma : (st : NativeHighSwitchState (Spin n×Bool) as)→MarkedPlacement st.tree→ℝ)
    (hGamma : ∀st p,p∈st.tree.markedAttach 0→|Gamma st p| ≤ 1)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    {Cweight : ℝ} (hCweight : 0 ≤ Cweight)
    (hw : ∀st b,b∈branches→|weight st b.1| ≤ Cweight)
    (L : ℕ) (hL : ∀b∈branches,b.2.length ≤ L)
    (increment : ℕ) (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)
    (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (r : ℕ) (hr : st.tree.leaves ≤ r)
    (v0 : FullCoordinate n→ℝ) (q0 : ℕ→FullCoordinate n→ℝ) (x0 : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W epsilon : ℝ) (hA : 0 < A) (hx : 0 < x) (hW : 0 < W) (hepsilon : 0 < epsilon)
    (hm0 : ∀Q∈nativeActualWeightedFrontier Gamma hs (hs.le.trans hU) branches weight depth st,
      Q.term.PairMomentBudget (fullWeight n) (fullFeature n) v0 q0
        (fun sigma tau=>deletedOverlap n (joinSpin sigma) (joinSpin tau))
        (nativePhysicalResourceCenter n bf hf as) x0 A x W epsilon)
    (hm : ∀Q∈nativeActualWeightedFrontier Gamma hs (hs.le.trans hU) branches weight depth st,
      Q.term.PairMomentBudget (fullWeight n) (fullFeature n) v q
        (fun sigma tau=>deletedOverlap n (joinSpin sigma) (joinSpin tau))
        (nativePhysicalResourceCenter n bf hf as) y A x W epsilon) :
    let k:=st.generation+depth*increment
    |((nativeActualWeightedFrontier Gamma hs (hs.le.trans hU) branches weight depth st).map
      (nativeOriginalClockStateResponse U K (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (nativePhysicalResourceCenter n bf hf as) v0 q0 x0 v q y W)).sum| ≤
      |st.term.coefficient| *nativeActualWeightedFrontierCost branches Cweight L r depth*
        (A^(seed.length+k)*nativeResourceScale x W epsilon seed*epsilon^k*(2*Temp)*
          nativeActualGInsertionCost (r+2*depth*L)) := by
  dsimp only
  have hscale : 0 ≤ nativeResourceScale x W epsilon seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hepsilon).le
  have hcost:=nativeActualGInsertionCost_nonneg (r+2*depth*L)
  apply nativeActualWeightedFrontier_terminal_abs_le ho Gamma hGamma hs (hs.le.trans hU)
    branches weight hCweight hw L hL depth st hr _ (by positivity)
  intro Q hQ
  have HG:=nativeActualWeightedFrontier_valid Gamma hs (hs.le.trans hU)
    branches weight depth st hst Q hQ
  have HD:=nativeActualWeightedFrontier_generation Gamma hs (hs.le.trans hU)
    branches weight increment hinc depth st Q hQ
  have HL:=nativeActualWeightedFrontier_leaves_le Gamma hs (hs.le.trans hU)
    branches weight L hL depth st Q hr hQ
  have HP:=actual_general_clock_frozen_resource_response_abs_le_of_total_clock
    bf hf K hbf hhf hTemp htotal HG ho _ HL v0 q0 x0 v q y A x W epsilon
    hA hx hW hepsilon hi (hs.trans_le hU) (hm0 Q hQ) (hm Q hQ)
  change |nativeOriginalClockStateResponse U K (fun j=>(bf (partitionPoint 0 as j):ℝ))
    (nativePhysicalResourceCenter n bf hf as) v0 q0 x0 v q y W Q| ≤ _ at HP
  simpa only [HD,mul_assoc] using HP

end OAI.SKFluctuations.Cavity
