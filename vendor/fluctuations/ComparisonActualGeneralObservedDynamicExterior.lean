module

public import ComparisonActualGeneralCanonicalResetProducts
public import ComparisonSignedCavityActualObservedProjectionFactorization

@[expose] public section
noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_observed_generated_dynamic_exterior_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    (hc : U≤T.splitIndex c P.live.test.target)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (bf hf : ℝ→ℝ≥0)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    let hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    Nonempty (NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed c))
      ((G.retainOnMarked a p hp).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)) v q x) := by
  dsimp only
  apply native_actual_generated_dynamic_canonical_exterior_source n _ pre mid tail hP hmid hU a p hp c hh ho
  intro j
  simpa only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.canonicalPhysicalSource]
    using native_generated_exterior_marked_labels_low n P.live.test P.live.ancestry
      (by omega) hU (hh.trans (p.tree.splitIndex_le_clockLength _ _)) a p hp c hc j

end OAI.SKFluctuations.Cavity
