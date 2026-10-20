module

public import ComparisonSignedCavityExteriorForestDisorder
public import ComparisonSignedCavityTwinPrefixRootLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

theorem integral_nativeExteriorForestRootLaw_dynamic
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail))) (q : ℕ→ι→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→ι→ℝ) (hx : Measurable x)
    (B : (ι→ℝ)→(ι→ℝ)→ℝ)
    (hB : BddSmooth 0 (fun z : (ι→ℝ)×(ι→ℝ)=>B z.1 z.2)) :
    (∫z,B (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestRootLaw w φ pre mid tail q μ x hx)=
      ∫p,prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps mid (fun j=>q (pre.length+j))++
          clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
        (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
          (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
          (B xi) xi) (x p) ∂μ := by
  let ps:=clockSteps pre q
  let ms:=clockSteps mid (fun j=>q (pre.length+j))
  let ts:=clockSteps tail (fun j=>q (pre.length+(mid.length+j)))
  have hoG : OrderedSteps a (ps++(ms++ts)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  have hmid:=hoG.suffix ps (ms++ts)
  have htail:=hmid.suffix ms ts
  obtain ⟨C,hC,hbound⟩:=hB.bound
  have hBs (xi) : BddSmooth 0 (B xi) :=
    ⟨hB.continuous.comp (continuous_const.prodMk continuous_id),C,hC,fun y=>hbound (xi,y)⟩
  have hμ:=retainedPrefixFieldLaw_finite hw φ ps (ms++ts) hoG μ x hx
  have HB:=integral_retainedPrefixFieldLaw hw φ ms ts hmid
    (retainedPrefixFieldLaw w φ ps (ms++ts) μ x hx) Prod.snd measurable_snd
    (fun z xs=>B z.2 xs)
    (hB.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    (fun z=>hBs z.2) C (fun z xs=>hbound (z.2,xs))
  have hL:=(gaussianHierarchy_regular hw φ ts htail 0).1.choose_spec
  have hJ:=prefixTest_parameter_smooth0 hL hB ms
    (fun st hst=>hmid.mem_pos st (List.mem_append_left ts hst))
  obtain ⟨C',hC',hbound'⟩:=hJ.bound
  have hA : BddSmooth 0 (fun xi=>prefixTest ms (gaussianHierarchy w φ ts) (B xi) xi) :=
    ⟨hJ.continuous.comp (continuous_id.prodMk continuous_id),C',hC',fun xi=>hbound' (xi,xi)⟩
  have HA:=integral_retainedPrefixFieldLaw hw φ ps (ms++ts) hoG μ x hx
    (fun _ xi=>prefixTest ms (gaussianHierarchy w φ ts) (B xi) xi)
    (hA.continuous.measurable.comp measurable_snd) (fun _=>hA) C' (fun _ xi=>hbound' (xi,xi))
  unfold nativeExteriorForestRootLaw exteriorForestRootLaw exteriorForestIRoot exteriorForestStarRoot
    departedAnchorRootLaw departedAnchorTargetRoot departedAnchorExteriorRoot
  exact HB.trans HA

theorem integral_nativeExteriorForestDisorderRootLaw_dynamic
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (B : (ι→ℝ)→(ι→ℝ)→ℝ)
    (hB : BddSmooth 0 (fun z : (ι→ℝ)×(ι→ℝ)=>B z.1 z.2)) :
    let dq:=cumulativeIncrements (q 0) (fun j=>q (j+1))
    (∫z,B (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x)=
      ∫y,prefixTest (clockSteps pre dq)
        (gaussianHierarchy w φ (clockSteps mid (fun j=>dq (pre.length+j))++
          clockSteps tail (fun j=>dq (pre.length+(mid.length+j)))))
        (fun xi=>prefixTest (clockSteps mid (fun j=>dq (pre.length+j)))
          (gaussianHierarchy w φ (clockSteps tail (fun j=>dq (pre.length+(mid.length+j)))))
          (B xi) xi) (x+y)
        ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i))) := by
  exact integral_nativeExteriorForestRootLaw_dynamic hw φ pre mid tail ho _
    (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
    (fun y=>x+y) (measurable_const.add measurable_id) B hB

end OAI.SKFluctuations.Cavity
