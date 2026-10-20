module

public import ComparisonSignedCavityExteriorForestNativeLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

def nativeExteriorForestDisorderRootLaw (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ) :
    Measure ((((ι→ℝ)×(ι→ℝ))×(ι→ℝ))) :=
  nativeExteriorForestRootLaw w φ pre mid tail
    (cumulativeIncrements (q 0) (fun j=>q (j+1)))
    (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
    (fun y=>x+y) (measurable_const.add measurable_id)

theorem nativeExteriorForestDisorderRootLaw_probability
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ) :
    IsProbabilityMeasure (nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) := by
  unfold nativeExteriorForestDisorderRootLaw
  exact nativeExteriorForestRootLaw_probability hw φ pre mid tail ho _ _ _ _

theorem nativeExteriorForest_disorder_law_eq_conditional (pre mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (x : ι→ℝ) :
    (nativeExteriorForestTree pre mid Ei Es D).disorderExpect w φ v q
      (nativeExteriorForestRead pre mid Ei Es D Q) x =
    ∫ z,nativeExteriorForestConditionalTest Ei Es D w φ
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
      Q (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x := by
  rw [(nativeExteriorForestTree pre mid Ei Es D).disorderExpect_integral hw φ ho]
  change (∫ y,(nativeExteriorForestTree pre mid Ei Es D).expect w φ
      (cumulativeIncrements (q 0) (fun k=>q (k+1)))
      (nativeExteriorForestRead pre mid Ei Es D Q) (x+y)
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))) = _
  exact nativeExteriorForest_original_law_eq_conditional pre mid hw φ Ei Es D ho _ Q
    (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
    (fun y=>x+y) (measurable_const.add measurable_id)

theorem nativeExteriorForest_four_tooth_disorder_law (pre mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (x : ι→ℝ) :
    (nativeExteriorForestTree pre mid (ClockTree.exteriorQuadNative Ei)
      (ClockTree.exteriorQuadNative Es) D).disorderExpect w φ v q
      (nativeExteriorForestRead pre mid (ClockTree.exteriorQuadNative Ei)
        (ClockTree.exteriorQuadNative Es) D
        (fun η ζ σ=>Q η.1.1 ζ.1.1 σ*Q η.1.2 ζ.1.2 σ*
          Q η.2.1 ζ.2.1 σ*Q η.2.2 ζ.2.2 σ)) x =
    ∫ z,nativeExteriorForestAveragedFourth Ei Es D w φ
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
      Q (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x := by
  rw [(nativeExteriorForestTree pre mid (ClockTree.exteriorQuadNative Ei)
    (ClockTree.exteriorQuadNative Es) D).disorderExpect_integral hw φ ho]
  change (∫ y,(nativeExteriorForestTree pre mid (ClockTree.exteriorQuadNative Ei)
      (ClockTree.exteriorQuadNative Es) D).expect w φ
      (cumulativeIncrements (q 0) (fun k=>q (k+1)))
      (nativeExteriorForestRead pre mid (ClockTree.exteriorQuadNative Ei)
        (ClockTree.exteriorQuadNative Es) D
        (fun η ζ σ=>Q η.1.1 ζ.1.1 σ*Q η.1.2 ζ.1.2 σ*
          Q η.2.1 ζ.2.1 σ*Q η.2.2 ζ.2.2 σ)) (x+y)
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))) = _
  exact nativeExteriorForest_four_tooth_original_law pre mid hw φ Ei Es D ho _ Q
    (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
    (fun y=>x+y) (measurable_const.add measurable_id)

end OAI.SKFluctuations.Cavity
