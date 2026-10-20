module

public import ComparisonSignedCavityActualExpansionVariation
public import ComparisonSignedCavityActualResourceTerminalMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 11000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def NativeActualExpansionOp.markedIncrement : NativeActualExpansionOp → ℕ
  | .projection => 1
  | .highRow => 1
  | _ => 0

def nativeActualExpansionMarkedCount (ops : List NativeActualExpansionOp) : ℕ :=
  (ops.map NativeActualExpansionOp.markedIncrement).sum

theorem nativeActualResourceStep_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceStep Γ hs hl op st) :
    Q.generation=st.generation+op.markedIncrement := by
  cases op with
  | center =>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with rfl|rfl <;> rfl
  | reweight c => obtain rfl:=List.mem_singleton.mp hQ; rfl
  | retarget => obtain rfl:=List.mem_singleton.mp hQ; rfl
  | projection => obtain rfl:=List.mem_singleton.mp hQ; rfl
  | highRow =>
    obtain ⟨p,hp,hQ⟩:=List.mem_flatMap.mp hQ
    split_ifs at hQ with hh
    · obtain rfl:=List.mem_singleton.mp hQ; rfl
    · cases hQ

theorem nativeActualResourceExpansion_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceExpansion Γ hs hl ops st) :
    Q.generation=st.generation+nativeActualExpansionMarkedCount ops := by
  induction ops generalizing st with
  | nil => obtain rfl:=List.mem_singleton.mp hQ; rfl
  | cons op ops ih =>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    have H:=ih P hQ
    rw [nativeActualResourceStep_generation Γ hs hl op st P hP] at H
    simpa [nativeActualExpansionMarkedCount,Nat.add_assoc] using H

theorem nativeActualResourceExpansion_terminal_abs_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star)
    (F : NativeActualResourceState S as i star → ℝ) {B : ℝ} (hB : 0≤B)
    (hF : ∀Q∈nativeActualResourceExpansion Γ hs hl ops st,
      |F Q|≤|Q.term.coefficient| *B) :
    |((nativeActualResourceExpansion Γ hs hl ops st).map F).sum| ≤
      |st.term.coefficient| *nativeActualExpansionVariation st.tree.leaves ops*B := by
  let L:=nativeActualResourceExpansion Γ hs hl ops st
  have Habs : |(L.map F).sum|≤(L.map (fun Q=>|F Q|)).sum := by
    induction L with
    | nil=>simp
    | cons Q L ih=>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
  have Hsum := List.sum_le_sum (fun Q hQ=>hF Q hQ)
  have Hvar := mul_le_mul_of_nonneg_right
    (nativeActualResourceExpansion_coefficient_variation_le ho Γ hΓ hs hl ops st (le_refl _)) hB
  exact Habs.trans (Hsum.trans (by simpa only [List.sum_map_mul_right] using Hvar))

variable {ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem nativeActualResourceExpansion_normalized_terminal_pairing_abs_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length) (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) (hg0 : st.generation=0)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ) (C : ℕ → ℝ)
    (x₀ : ι → ℝ) (A x W ε B : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε) (hB : 0≤B)
    (G : (Q : NativeActualResourceState S as i star) → Q.tree.Assignment → ℝ)
    (hm : ∀Q∈nativeActualResourceExpansion Γ hs (by omega) ops st,
      Q.term.PairMomentBudget w φ v q R C x₀ A x W ε)
    (hG : ∀Q∈nativeActualResourceExpansion Γ hs (by omega) ops st,
      Q.tree.disorderExpect w φ v q (fun σ=>(G Q σ)^2) x₀≤B^2) :
    let k:=nativeActualExpansionMarkedCount ops
    |((nativeActualResourceExpansion Γ hs (by omega) ops st).map
      (fun Q=>Q.tree.disorderExpect w φ v q
        (fun σ=>(W⁻¹)^k*(Q.term.value w φ v q R C x₀ σ*G Q σ)) x₀)).sum| ≤
      |st.term.coefficient| *nativeActualExpansionVariation st.tree.leaves ops*
        (A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B) := by
  dsimp only
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  apply nativeActualResourceExpansion_terminal_abs_le ho Γ hΓ hs (by omega) ops st _ (by positivity)
  intro Q hQ
  have HG := nativeActualResourceExpansion_valid Γ hs (by omega) _ st hst Q hQ
  have hdepth := nativeActualResourceExpansion_generation Γ hs (by omega) ops st Q hQ
  rw [hg0,zero_add] at hdepth
  have H := HG.normalized_terminal_pairing_sq_le hw φ ho v q R C x₀ A x W ε
    hA hx hW hε hi (by omega) (hm Q hQ) (G Q) B (hG Q hQ)
  rw [hdepth] at H
  have Habs := (sq_le_sq₀ (abs_nonneg _)
    (show 0≤|Q.term.coefficient| *A^(seed.length+nativeActualExpansionMarkedCount ops)*
      nativeResourceScale x W ε seed*ε^(nativeActualExpansionMarkedCount ops)*B by positivity)).mp
      (by simpa only [sq_abs] using H)
  simpa only [mul_assoc] using Habs

end OAI.SKFluctuations.Hierarchy.ClockTree
