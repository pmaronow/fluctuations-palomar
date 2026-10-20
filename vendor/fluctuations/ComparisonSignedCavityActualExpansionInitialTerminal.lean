module

public import ComparisonSignedCavityActualExpansionTerminal

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
variable {as : List PositiveMass} {i star U : ℕ}

omit [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι] in
theorem nativeActualExpansionVariation_mono (ops : List NativeActualExpansionOp) :
    Monotone (fun r=>nativeActualExpansionVariation r ops) := by
  induction ops with
  | nil => intro r s hrs; exact le_rfl
  | cons op ops ih =>
    intro r s hrs
    have HC : op.coefficientCost r≤op.coefficientCost s := by
      cases op with
      | highRow =>
        change 4*(r:ℝ)+1≤4*(s:ℝ)+1
        have H : (r:ℝ) ≤ s := by exact_mod_cast hrs
        linarith
      | center => exact le_rfl
      | reweight c => exact le_rfl
      | retarget => exact le_rfl
      | projection => exact le_rfl
    have Hcost : 0≤op.coefficientCost s := by
      cases op <;> simp only [NativeActualExpansionOp.coefficientCost] <;> positivity
    exact mul_le_mul HC (ih (by omega))
      (nativeActualExpansionVariation_nonneg _ _) Hcost

omit [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι] in
theorem nativeActualInitialState_leaves_le (as : List PositiveMass) (i star : ℕ)
    (a : ℝ) (hi : i≤as.length) :
    (nativeActualInitialState (S:=S) as i star a hi).tree.leaves≤2 := by
  have H:=(single (S:=S) as).markedAttach_leaves a _
    (nativeFreshAtSlot_mem (single as) a (singleSlot as) i)
  simpa only [nativeActualInitialState,single_leaves_exact] using H

theorem nativeActualInitialExpansion_normalized_terminal_pairing_abs_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length) (ops : List NativeActualExpansionOp)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ) (C : ℕ → ℝ)
    (x₀ : ι → ℝ) (A x W ε B : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε) (hB : 0≤B)
    (G : (Q : NativeActualResourceState S as i star) → Q.tree.Assignment → ℝ)
    (hm : ∀Q∈nativeActualResourceExpansion Γ hs (by omega) ops
        (nativeActualInitialState as i star 0 (by omega)),
      Q.term.PairMomentBudget w φ v q R C x₀ A x W ε)
    (hG : ∀Q∈nativeActualResourceExpansion Γ hs (by omega) ops
        (nativeActualInitialState as i star 0 (by omega)),
      Q.tree.disorderExpect w φ v q (fun σ=>(G Q σ)^2) x₀≤B^2) :
    let k:=nativeActualExpansionMarkedCount ops
    |((nativeActualResourceExpansion Γ hs (by omega) ops
        (nativeActualInitialState as i star 0 (by omega))).map
      (fun Q=>Q.tree.disorderExpect w φ v q
        (fun σ=>(W⁻¹)^k*(Q.term.value w φ v q R C x₀ σ*G Q σ)) x₀)).sum| ≤
      nativeActualExpansionVariation 2 ops*(A^(1+k)*x*ε^k*B) := by
  dsimp only
  let st:=nativeActualInitialState (S:=S) as i star 0 (by omega : i≤as.length)
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term :=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (by change i≤as.length;omega))
  have H:=nativeActualResourceExpansion_normalized_terminal_pairing_abs_le ho Γ hΓ hi hs hU
    ops st rfl hst hw φ v q R C x₀ A x W ε B hA hx hW hε hB G hm hG
  dsimp only at H
  have HV:=nativeActualExpansionVariation_mono ops (nativeActualInitialState_leaves_le (S:=S) as i star 0 (by omega))
  have Hcost:=mul_le_mul_of_nonneg_right HV (show 0≤A^(1+nativeActualExpansionMarkedCount ops)*x*
      ε^(nativeActualExpansionMarkedCount ops)*B by positivity)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    List.length_singleton,nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,NativeResourceMark.savedScale,mul_one] at H
  exact H.trans Hcost

end OAI.SKFluctuations.Hierarchy.ClockTree
