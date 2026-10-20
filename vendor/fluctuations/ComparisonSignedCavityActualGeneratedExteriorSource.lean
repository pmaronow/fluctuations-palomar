module

public import ComparisonSignedCavityGeneratedExteriorShape
public import ComparisonSignedCavityActualCanonicalTwoLevelProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_observed_generated_exterior_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    (hc : U ≤ T.splitIndex c P.live.test.target)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    let hlen : U ≤ (pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    Nonempty (NativeCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed c))
      ((G.retainOnMarked a p hp).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)) v q x) := by
  dsimp only
  apply native_actual_generated_canonical_exterior_source n _ pre mid tail hP hmid hU a p hp c hh ho
  intro j
  simpa only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.canonicalMinimumSource]
    using native_generated_exterior_marked_labels_low n P.live.test P.live.ancestry
      (by omega) hU (hh.trans (p.tree.splitIndex_le_clockLength _ _)) a p hp c hc j

theorem native_actual_observed_exterior_source_mass
    (n : ℕ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star : ℕ} (P : NativeResourceTerm i star T)
    (hi : i ≤ star) (hlen : star < as.length)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (Cmass x W : ℝ) (hmi : partitionPoint 0 as i ≤ Cmass*x)
    (hms : partitionPoint 0 as star ≤ Cmass*W)
    (e : Fin P.live.test.exterior.length) :
    ((nativeGeneratedExteriorShape n P.live.test P.live.ancestry hi hlen).retainOnMarked a p hp).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (nativeGeneratedExteriorInitial P.live.test i) e := by
  rw [ActualNaturalBoundaryShape.retained_source_mass]
  exact native_generated_exterior_source_mass n P.live.test P.live.ancestry hi hlen Cmass x W hmi hms e

end OAI.SKFluctuations.Cavity
