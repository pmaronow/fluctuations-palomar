module

public import ComparisonSignedCavitySecondLowExteriorIndexedTelescope
public import ComparisonSignedCavityExteriorForestDisorder

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_two_level_incoming_conditional_integral
    (pre mid tail : List PositiveMass) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (q : ℕ→ι→ℝ≥0) (B : ((ι→ℝ)×(ι→ℝ))→ℝ) (hB : BddSmooth 0 B)
    (hBs : ∀xi,BddSmooth 0 (fun xs=>B (xi,xs)))
    (hA : BddSmooth 0 (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
      (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
      (fun xs=>B (xi,xs)) xi))
    {κ : Type} [MeasurableSpace κ] (μ : Measure κ) [IsFiniteMeasure μ]
    (x : κ→ι→ℝ) (hx : Measurable x) :
    (∫p,prefixTest (clockSteps pre q)
      (gaussianHierarchy w φ (clockSteps (mid++tail) (fun j=>q (pre.length+j))))
      (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
        (fun xs=>B (xi,xs)) xi) (x p) ∂μ)=
      ∫r,B (exteriorForestIRoot r,exteriorForestStarRoot r)
        ∂nativeExteriorForestRootLaw w φ pre mid tail q μ x hx := by
  let ps:=clockSteps pre q
  let ms:=clockSteps mid (fun j=>q (pre.length+j))
  let ts:=clockSteps tail (fun j=>q (pre.length+(mid.length+j)))
  have hoG : OrderedSteps a (ps++(ms++ts)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  obtain ⟨C,_,hbound⟩:=hB.bound
  have :=retainedPrefixFieldLaw_finite hw φ ps (ms++ts) hoG μ x hx
  have HB:=integral_retainedPrefixFieldLaw hw φ ms ts (hoG.suffix ps _)
    (retainedPrefixFieldLaw w φ ps (ms++ts) μ x hx) Prod.snd measurable_snd
    (fun z xs=>B (z.2,xs))
    (hB.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    (fun z=>hBs z.2) C (fun z xs=>hbound _)
  obtain ⟨C',_,hbound'⟩:=hA.bound
  have HA:=integral_retainedPrefixFieldLaw hw φ ps (ms++ts) hoG μ x hx
    (fun _ xi=>prefixTest ms (gaussianHierarchy w φ ts) (fun xs=>B (xi,xs)) xi)
    (hA.continuous.measurable.comp measurable_snd) (fun _=>hA) C' (fun _ xi=>hbound' xi)
  unfold nativeExteriorForestRootLaw exteriorForestRootLaw exteriorForestIRoot exteriorForestStarRoot
    departedAnchorRootLaw departedAnchorTargetRoot departedAnchorExteriorRoot
  change _=∫r,B (r.1.2,r.2)
    ∂retainedPrefixFieldLaw w φ ms ts
      (retainedPrefixFieldLaw w φ ps (ms++ts) μ x hx) Prod.snd measurable_snd
  rw [HB,HA]
  rw [clockSteps_append]

theorem native_two_level_disorder_conditional_integral
    (pre mid tail : List PositiveMass) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (B : ((ι→ℝ)×(ι→ℝ))→ℝ) (hB : BddSmooth 0 B)
    (hBs : ∀xi,BddSmooth 0 (fun xs=>B (xi,xs)))
    (hA : BddSmooth 0 (fun xi=>prefixTest
      (clockSteps mid (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)))
      (gaussianHierarchy w φ (clockSteps tail
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))))
      (fun xs=>B (xi,xs)) xi)) :
    (∫y,prefixTest (clockSteps pre (cumulativeIncrements (q 0) (fun k=>q (k+1))))
      (gaussianHierarchy w φ (clockSteps (mid++tail)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))))
      (fun xi=>prefixTest
        (clockSteps mid (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)))
        (gaussianHierarchy w φ (clockSteps tail
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))))
        (fun xs=>B (xi,xs)) xi) (x+y)
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i))))=
      ∫r,B (exteriorForestIRoot r,exteriorForestStarRoot r)
        ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x := by
  exact native_two_level_incoming_conditional_integral pre mid tail hw φ ho
    (cumulativeIncrements (q 0) (fun k=>q (k+1))) B hB hBs hA
    (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
    (fun y=>x+y) (measurable_const.add measurable_id)

end OAI.SKFluctuations.Cavity
