module

public import ComparisonActualGeneralCurrentGRestoration
public import ComparisonActualGeneralGTripleRowSupport
public import ComparisonSignedCavityActualGProjectedRowLaw

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_decoupled_G_projected_resampling_eq_spine_row
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ) (hRadius : Monotone radius) (hbf : MonotoneOn bf (Icc 0 1)) (hhf : MonotoneOn hf (Icc 0 1))
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length)
    (V : ℝ) (hV : V≤radius (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) :
    actualGeneralDecoupledGProjectedResampling T P (pre.length+mid.length) U bf hf q=
      actualGeneralTripleSpineGRow spine bf hf radius U V q := by
  have HC (j) :=native_ordered_source_center_eq_completed n bf hf
    hbf hhf
    (partitionPoint_mem (pre++(mid++tail)) ho j)
  unfold actualGeneralDecoupledGProjectedResampling
  dsimp only
  rw [native_decoupled_G_spine_resampling_eq_conditional_word spine ho U hs hU q _ _ _ _
    (by intro j;rw [HC])
    (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
    (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))]
  rw [native_observed_high_word_sum_three]
  exact actual_general_triple_spine_G_high_sum_eq_row spine bf hf radius hRadius ho U hs hU V hV q

end OAI.SKFluctuations.Cavity
