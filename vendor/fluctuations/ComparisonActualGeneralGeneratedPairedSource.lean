module

public import ComparisonActualGeneralGammaPairedCanonicalSource
public import ComparisonActualGeneralCanonicalResetProducts
public import ComparisonSignedCavityActualGeneratedPairedSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

theorem physical_generated_paired_source_eq_endpoint_retarget
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P.target star).tree.markedAttach 0)
    (hhigh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark)
    (bf hf : ℝ→ℝ≥0)
    (σ : p.tree.cavityLeft.Assignment) :
    let g:=nativeFreshAtSlot T 0 P.target star
    let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
    let GP:=nativeFreshObservedShape G P.target star p hp
    let js:=nativeFreshObservedReplacementSlots G P.target star p
    let Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
    nativeRestProjectedPairedTest T P.target star
      (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
      (nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))) p σ=
      nativeRestEndpointDifference n p.tree (p.embed g.mark) p.mark (p.embed (g.embed P.target)) σ*
        ((GP.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct σ-
          ((GP.retarget js Hgeom.2.1).canonicalPhysicalSource bf hf
            (fun _=>NativeSourceFactorForm.centered)).restProduct σ) := by
  dsimp only
  let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
  have Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
  have H:=physical_paired_canonical_source_eq_endpoint_retarget G P.target star Hgeom.1 p hp
    Hgeom.2.1 Hgeom.2.2.1 bf hf (fun _=>NativeSourceFactorForm.centered) σ
  have Heq : (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)):=
    funext (actual_general_generated_complete_canonical_rest_product n P hP hi (hs.trans_le hlen) bf hf)
  rw [Heq] at H
  exact H

end OAI.SKFluctuations.Cavity
