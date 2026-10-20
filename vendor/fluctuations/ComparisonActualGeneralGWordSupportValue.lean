module

public import ComparisonActualGeneralTripleGValue
public import ComparisonSignedCavityGWordSupportValue

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_triple_spine_G_value_zero_of_not_support
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    (bf hf : ℝ→ℝ≥0)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ) (hU : U≤(pre++(mid++tail)).length)
    (p : MarkedPlacement B) (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0) (q : ℕ→RestCoordinate n→ℝ)
    (hs : ¬(U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
      U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
      U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
      z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark)) :
    actualGeneralTripleSpineGValue spine bf hf U p r z q=0 := by
  apply native_G_spine_word_zero_of_not_support spine _ ho U hU (by
    simp only [NativeObservedDiagram.observe,NativeObservedDiagram.identity,
      List.length_cons,List.length_map,List.length_nil];omega)
  rwa [native_three_mark_G_support_iff base.target U p r hr z hz]

end OAI.SKFluctuations.Cavity
