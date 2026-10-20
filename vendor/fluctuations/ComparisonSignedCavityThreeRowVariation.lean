module

public import ComparisonSignedCavityOriginalEndpointMean

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree

theorem marked_three_row_abs_le {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) → MarkedPlacement r.tree → ℝ)
    {D : ℝ} (hD : 0 ≤ D)
    (hF : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,∀z∈r.tree.markedAttach 0,|F p r z| ≤ D) :
    |((T.markedAttach 0).map (fun p => p.coeff*
      ((p.tree.markedAttach 0).map (fun r => r.coeff*
        ((r.tree.markedAttach 0).map (fun z => z.coeff*F p r z)).sum)).sum)).sum| ≤
      (8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2))*D := by
  have Hin (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      |((r.tree.markedAttach 0).map (fun z => z.coeff*F p r z)).sum| ≤
        2*((T.leaves:ℝ)+2)*D := by
    have H := marked_list_weight_abs_le (r.tree.markedAttach 0) (F p r) (hF p hp r hr)
    rw [r.tree.markedAttach_variation ho,sub_zero] at H
    have Hle : r.tree.leaves ≤ T.leaves+2 := by
      have H1 := T.markedAttach_leaves 0 p hp
      have H2 := p.tree.markedAttach_leaves 0 r hr
      omega
    have Hler : (r.tree.leaves:ℝ) ≤ (T.leaves:ℝ)+2 := by exact_mod_cast Hle
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hler (by norm_num)) hD)
  have H := T.signedPair_abs_le_pairAbsSum (fun p r =>
    ((r.tree.markedAttach 0).map (fun z => z.coeff*F p r z)).sum)
  have HH := T.pairAbsSum_mono Hin
  have HB := T.pairAbsSum_constant_le ho (le_refl T.leaves)
    (show 0 ≤ 2*((T.leaves:ℝ)+2)*D by positivity)
  have Htotal := H.trans (HH.trans HB)
  convert Htotal using 1
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree
