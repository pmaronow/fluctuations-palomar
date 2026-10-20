module

public import ComparisonSignedCavityActualFourRestorationSeedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem native_actual_constant_child_family_wholeProfile_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p| ≤ 1)
    (hs : star < U) (hU : U ≤ as.length) (chi : ℝ) (hchi : |chi| ≤ 1)
    (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
    let base:=nativeActualConstantState (S:=S) as i star
    let children:=(base.projection (hs.le.trans hU)).reweight chi::
      nativeActualResourceStep Γ hs (hs.le.trans hU) .highRow base
    (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      (1+nativeActualProfileOpVariation 1 .highRow)*edgeBudget 0 as f := by
  dsimp only
  let base:=nativeActualConstantState (S:=S) as i star
  let proj:=(base.projection (hs.le.trans hU)).reweight chi
  have Hrow:=nativeActualResourceStep_wholeProfile_le ho Γ hΓ hs (hs.le.trans hU)
    .highRow base 1 (show base.tree.leaves ≤ 1 by
      simp only [base,nativeActualConstantState,single_leaves_exact,le_refl]) f hf hlo
  have Hb : base.term.coefficient=1:=rfl
  have HF : base.tree.forkCost f=0:=single_forkCost as f
  rw [Hb,HF,abs_one,one_mul,zero_add] at Hrow
  have HP : proj.tree.forkCost f=0:=actual_projected_constant_four_seed_high_fork_free i star U hs hU f hlo
  have HC : proj.term.coefficient=chi:=by change chi*1=chi;ring
  have HB:=edgeBudget_nonneg ho hf
  have Hproj:=mul_le_mul_of_nonneg_right hchi HB
  simp only [List.map_cons,List.sum_cons]
  change |proj.term.coefficient| *(proj.tree.forkCost f+edgeBudget 0 as f)+_ ≤ _
  rw [HC,HP,zero_add]
  have H:=add_le_add Hproj Hrow
  simpa only [one_mul,add_mul] using H

theorem native_actual_constant_child_family_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p| ≤ 1)
    (hs : star < U) (hU : U ≤ as.length) (chi : ℝ) (hchi : |chi| ≤ 1) :
    let base:=nativeActualConstantState (S:=S) as i star
    let children:=(base.projection (hs.le.trans hU)).reweight chi::
      nativeActualResourceStep Γ hs (hs.le.trans hU) .highRow base
    (children.map (fun Q=>|Q.term.coefficient|)).sum ≤
      1+NativeActualExpansionOp.coefficientCost 1 .highRow := by
  dsimp only
  let base:=nativeActualConstantState (S:=S) as i star
  let proj:=(base.projection (hs.le.trans hU)).reweight chi
  have Hrow:=nativeActualResourceStep_coefficient_variation_le ho Γ hΓ hs (hs.le.trans hU)
    .highRow base (show base.tree.leaves ≤ 1 by
      simp only [base,nativeActualConstantState,single_leaves_exact,le_refl])
  have Hb : base.term.coefficient=1:=rfl
  rw [Hb,abs_one,one_mul] at Hrow
  have HC : proj.term.coefficient=chi:=by change chi*1=chi;ring
  simp only [List.map_cons,List.sum_cons]
  change |proj.term.coefficient|+_ ≤ _
  rw [HC]
  exact add_le_add hchi Hrow

end OAI.SKFluctuations.Hierarchy.ClockTree
