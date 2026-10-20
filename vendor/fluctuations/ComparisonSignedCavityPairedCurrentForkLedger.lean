module

public import ComparisonSignedCavityActualGeneratedPairedSource
public import ComparisonSignedCavityActualOriginalHighProfileRows

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_paired_current_rows_high_profile_le
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) {star U r : ℕ} (hs : star < U)
    (hr : T.leaves ≤ r) (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j<U→f j=0)
    (E : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree→ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0,
      |E p| ≤ C*(p.tree.forkCost f+edgeBudget 0 as f)) :
    |(1/2:ℝ)*(((nativeFreshAtSlot T 0 s star).tree.markedAttach 0).map
      (fun p=>p.coeff*E p)).sum| ≤
      (C/2)*(4*((r:ℝ)+1)+1)*(T.forkCost f+edgeBudget 0 as f) := by
  let g:=nativeFreshAtSlot T 0 s star
  have HB:=edgeBudget_nonneg ho hf
  have HT:=g.tree.forkCost_nonneg hf
  have HH:=g.tree.markedAttach_forkCost_le ho hf
  have HV:=g.tree.markedAttach_variation ho
  have HL:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s star)
  have Hcast : (g.tree.leaves:ℝ) ≤ (r:ℝ)+1:=by exact_mod_cast HL.trans (by omega : T.leaves+1 ≤ r+1)
  have Hrows : ((g.tree.markedAttach 0).map
      (fun p=>|p.coeff| *(p.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      (4*((r:ℝ)+1)+1)*(g.tree.forkCost f+edgeBudget 0 as f) := by
    simp only [mul_add,List.sum_map_add,List.sum_map_mul_right,HV,sub_zero]
    have Hx:=mul_nonneg (sub_nonneg.mpr Hcast) (add_nonneg HT HB)
    nlinarith
  have HE : |((g.tree.markedAttach 0).map (fun p=>p.coeff*E p)).sum| ≤
      C*((g.tree.markedAttach 0).map (fun p=>|p.coeff| *(p.tree.forkCost f+edgeBudget 0 as f))).sum := by
    have Habs : |((g.tree.markedAttach 0).map (fun p=>p.coeff*E p)).sum| ≤
        ((g.tree.markedAttach 0).map (fun p=>|p.coeff*E p|)).sum := by
      induction g.tree.markedAttach 0 with
      | nil=>simp
      | cons p ps ih=>
        simp only [List.map_cons,List.sum_cons]
        exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
    apply Habs.trans
    rw [←List.sum_map_mul_left]
    apply List.sum_le_sum
    intro x hx
    rw [abs_mul]
    have H:=mul_le_mul_of_nonneg_left (hE x hx) (abs_nonneg x.coeff)
    nlinarith only [H]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have H:=mul_le_mul_of_nonneg_left (HE.trans (mul_le_mul_of_nonneg_left Hrows hC))
    (by norm_num : (0:ℝ)≤1/2)
  rw [nativeFreshAtSlot_high_forkCost T 0 s hs f hlo] at H
  nlinarith only [H]

end OAI.SKFluctuations.Cavity
