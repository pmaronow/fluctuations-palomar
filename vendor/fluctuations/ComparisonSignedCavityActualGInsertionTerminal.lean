module

public import ComparisonSignedCavityActualExpansionInitialTerminal
public import ComparisonSignedCavityActualExpansionLeafBound
public import ComparisonSignedCavityActualMarkedGResourcePairing
public import ComparisonSignedCavityActualTerminalGWords

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualGInsertionCost (r : ℕ) : ℝ := 8*(r:ℝ)*(r+1)*(r+2)

theorem nativeActualGInsertionCost_nonneg (r : ℕ) : 0≤nativeActualGInsertionCost r := by
  unfold nativeActualGInsertionCost
  positivity

def nativeActualResourceGInsertion
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (U k : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (W : ℝ) : ℝ :=
  ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ*
          g.atom M U P.live.test.target σ)) x₀)).sum

theorem nativeActualResourceGInsertion_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (r : ℕ) (hr : T.leaves≤r)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε) :
    |nativeActualResourceGInsertion M P U k v q x₀ W|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp)*
        nativeActualGInsertionCost r := by
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  unfold nativeActualResourceGInsertion
  apply (nativeActualWeightedTerminalSum_abs_le _ _ _ (by
    intro g hg
    exact g.actual_normalized_resource_pairing_abs_le M hcl hAz hTemp hb hh hP ho
      P.live.test.target v q x₀ A x W ε hA hx hW hε hi hstar hm)).trans
  have HV:=mul_le_mul_of_nonneg_right (nativeOriginalGMarkedWords_variation_le T ho r hr)
    (show 0≤|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) by positivity)
  simpa only [nativeActualGInsertionCost,mul_comm] using HV

theorem nativeActualResourceExpansion_g_insertion_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
    (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (hg0 : st.generation=0)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (r : ℕ) (hr : st.tree.leaves≤r)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hm : ∀Q∈nativeActualResourceExpansion Γ hs (by omega) ops st,
      Q.term.PairMomentBudget (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε) :
    let k:=nativeActualExpansionMarkedCount ops
    |((nativeActualResourceExpansion Γ hs (by omega) ops st).map
      (fun Q=>nativeActualResourceGInsertion M Q.term U k v q x₀ W)).sum|≤
        |st.term.coefficient| *nativeActualExpansionVariation r ops*
          (A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp)*
            nativeActualGInsertionCost (r+2*ops.length)) := by
  dsimp only
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  have hcost:=nativeActualGInsertionCost_nonneg (r+2*ops.length)
  have H:=nativeActualResourceExpansion_terminal_abs_le ho Γ hΓ hs (by omega) ops st
    (fun Q=>nativeActualResourceGInsertion M Q.term U (nativeActualExpansionMarkedCount ops) v q x₀ W)
    (B:=A^(seed.length+nativeActualExpansionMarkedCount ops)*nativeResourceScale x W ε seed*
      ε^(nativeActualExpansionMarkedCount ops)*(2*Temp)*nativeActualGInsertionCost (r+2*ops.length))
    (by positivity) (by
      intro Q hQ
      have HG:=nativeActualResourceExpansion_valid Γ hs (by omega) ops st hst Q hQ
      have HD:=nativeActualResourceExpansion_generation Γ hs (by omega) ops st Q hQ
      rw [hg0,zero_add] at HD
      have HL:=nativeActualResourceExpansion_leaves_le Γ hs (by omega) ops st Q hr hQ
      have HP:=nativeActualResourceGInsertion_abs_le M hcl hAz hTemp hb hh HG ho _ HL
        v q x₀ A x W ε hA hx hW hε hi (by omega) (hm Q hQ)
      rw [HD] at HP
      simpa only [mul_assoc] using HP)
  apply H.trans
  have HV:=nativeActualExpansionVariation_mono ops hr
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HV (abs_nonneg _)) (by positivity)

end OAI.SKFluctuations.Cavity
