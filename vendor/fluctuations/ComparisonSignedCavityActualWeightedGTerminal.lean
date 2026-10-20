module

public import ComparisonSignedCavityActualWeightedVariation
public import ComparisonSignedCavityActualGInsertionTerminal

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualWeightedFrontier_terminal_abs_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hw : ∀st b,b∈branches→|weight st b.1|≤C)
    (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (depth : ℕ) (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (F : NativeActualResourceState S as i star→ℝ) {B : ℝ} (hB : 0≤B)
    (hF : ∀Q∈nativeActualWeightedFrontier Γ hs hl branches weight depth st,|F Q|≤|Q.term.coefficient| *B) :
    |((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map F).sum|≤
      |st.term.coefficient| *nativeActualWeightedFrontierCost branches C L r depth*B := by
  let frontier:=nativeActualWeightedFrontier Γ hs hl branches weight depth st
  have HA : |(frontier.map F).sum|≤(frontier.map (fun Q=>|F Q|)).sum := by
    clear hF
    induction frontier with
    | nil=>simp
    | cons Q frontier ih=>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
  apply HA.trans
  apply (List.sum_le_sum (fun Q hQ=>hF Q hQ)).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualWeightedFrontier_coefficient_variation_le ho Γ hΓ hs hl branches weight hC hw L hL depth st hr) hB

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem nativeActualWeightedFrontier_g_insertion_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
    (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hw : ∀st b,b∈branches→|weight st b.1|≤C)
    (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (increment : ℕ) (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)
    (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star) (hg0 : st.generation=0)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (r : ℕ) (hr : st.tree.leaves≤r)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hm : ∀Q∈nativeActualWeightedFrontier Γ hs (by omega) branches weight depth st,
      Q.term.PairMomentBudget (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε) :
    let k:=depth*increment
    |((nativeActualWeightedFrontier Γ hs (by omega) branches weight depth st).map
      (nativeActualGResourceResponse M U v q x₀ W)).sum|≤
        |st.term.coefficient| *nativeActualWeightedFrontierCost branches C L r depth*
          (A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp)*
            nativeActualGInsertionCost (r+2*depth*L)) := by
  dsimp only
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  have hcost:=nativeActualGInsertionCost_nonneg (r+2*depth*L)
  apply nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs (by omega) branches weight
    hC hw L hL depth st hr _ (by positivity)
  intro Q hQ
  have HG:=nativeActualWeightedFrontier_valid Γ hs (by omega) branches weight depth st hst Q hQ
  have HD:=nativeActualWeightedFrontier_generation Γ hs (by omega) branches weight increment hinc depth st Q hQ
  rw [hg0,zero_add] at HD
  have HL:=nativeActualWeightedFrontier_leaves_le Γ hs (by omega) branches weight L hL depth st Q hr hQ
  have HP:=nativeActualResourceGInsertion_abs_le M hcl hAz hTemp hb hh HG ho _ HL
    v q x₀ A x W ε hA hx hW hε hi (by omega) (hm Q hQ)
  change |nativeActualGResourceResponse M U v q x₀ W Q|≤_ at HP
  rw [HD] at HP
  simpa only [mul_assoc] using HP

end OAI.SKFluctuations.Cavity
