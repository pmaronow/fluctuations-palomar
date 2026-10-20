module

public import ComparisonSignedCavityExteriorForestNative

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype ι] in
theorem nativeExteriorForest_clockSteps_eq (pre mid tail : List PositiveMass)
    (q : ℕ→ι→ℝ≥0) :
    clockSteps (pre++(mid++tail)) q =
      clockSteps pre q++(clockSteps mid (fun j=>q (pre.length+j))++
        clockSteps tail (fun j=>q (pre.length+(mid.length+j)))) := by
  rw [clockSteps_append,clockSteps_append]

theorem nativeExteriorForestConditionalPrefix_smooth (mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (mid++tail))
    (q : ℕ→ι→ℝ≥0) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (r : ℕ) :
    BddSmooth r (fun xi=>prefixTest (clockSteps mid q)
      (gaussianHierarchy w φ (clockSteps tail (fun j=>q (mid.length+j))))
      (nativeExteriorForestConditionalTest Ei Es D w φ q (fun j=>q (mid.length+j)) Q xi) xi) := by
  have he : (Ei.fork (ClockTree.exteriorPrepend mid (Es.fork D))).expect w φ q
      (fun z=>let u:=ClockTree.exteriorPrependAssignmentEquiv mid (Es.fork D) z.2;Q z.1 u.1 u.2) =
      fun xi=>prefixTest (clockSteps mid q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (mid.length+j))))
        (nativeExteriorForestConditionalTest Ei Es D w φ q (fun j=>q (mid.length+j)) Q xi) xi :=
    funext fun xi=>nativeExteriorForestTail_expect_eq_prefix mid hw φ Ei Es D ho q Q xi
  rw [←he]
  exact (Ei.fork (ClockTree.exteriorPrepend mid (Es.fork D))).nativeAnchor_expect_smooth hw φ ho q _ r

variable [MeasurableSpace S] [StandardBorelSpace S]

def nativeExteriorForestRootLaw (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) (q : ℕ→ι→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) (x : P→ι→ℝ) (hx : Measurable x) :
    Measure ((P×(ι→ℝ))×(ι→ℝ)) :=
  exteriorForestRootLaw w φ (clockSteps pre q) (clockSteps mid (fun j=>q (pre.length+j)))
    (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))) μ x hx

theorem nativeExteriorForestRootLaw_probability
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (q : ℕ→ι→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ] (x : P→ι→ℝ) (hx : Measurable x) :
    IsProbabilityMeasure (nativeExteriorForestRootLaw w φ pre mid tail q μ x hx) := by
  have hoG : OrderedSteps a (clockSteps pre q++(clockSteps mid (fun j=>q (pre.length+j))++
      clockSteps tail (fun j=>q (pre.length+(mid.length+j))))) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  exact departedAnchorRootLaw_probability hw φ _ _ _ hoG μ x hx

theorem nativeExteriorForest_original_law_eq_conditional (pre mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (q : ℕ→ι→ℝ≥0) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→ι→ℝ) (hx : Measurable x) :
    (∫ p,(nativeExteriorForestTree pre mid Ei Es D).expect w φ q
      (nativeExteriorForestRead pre mid Ei Es D Q) (x p) ∂μ) =
    ∫ z,nativeExteriorForestConditionalTest Ei Es D w φ (fun j=>q (pre.length+j))
      (fun j=>q (pre.length+(mid.length+j))) Q (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestRootLaw w φ pre mid tail q μ x hx := by
  let ps:=clockSteps pre q
  let ms:=clockSteps mid (fun j=>q (pre.length+j))
  let ts:=clockSteps tail (fun j=>q (pre.length+(mid.length+j)))
  let qi:=fun j=>q (pre.length+j)
  let qs:=fun j=>q (pre.length+(mid.length+j))
  have hoG : OrderedSteps a (ps++(ms++ts)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  let B:=fun z : (ι→ℝ)×(ι→ℝ)=>nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q z.1 z.2
  have hB:=nativeExteriorForestConditionalTest_smooth_joint hw φ Ei Es D
    ho.suffix_end ho.suffix_end.suffix_end qi qs Q 0
  obtain ⟨C,hC,hbound⟩:=hB.bound
  have hμ:=retainedPrefixFieldLaw_finite hw φ ps (ms++ts) hoG μ x hx
  have HB:=integral_retainedPrefixFieldLaw hw φ ms ts (hoG.suffix ps _)
    (retainedPrefixFieldLaw w φ ps (ms++ts) μ x hx) Prod.snd measurable_snd
    (fun z xs=>B (z.2,xs))
    (hB.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    (fun z=>nativeExteriorForestConditionalTest_smooth_star hw φ Ei Es D
      ho.suffix_end.suffix_end qi qs Q z.2 0) C (fun z xs=>hbound _)
  have hA:=nativeExteriorForestConditionalPrefix_smooth mid hw φ Ei Es D ho.suffix_end qi Q 0
  obtain ⟨C',hC',hbound'⟩:=hA.bound
  have HA:=integral_retainedPrefixFieldLaw hw φ ps (ms++ts) hoG μ x hx
    (fun _ xi=>prefixTest ms (gaussianHierarchy w φ ts)
      (nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q xi) xi)
    (hA.continuous.measurable.comp measurable_snd) (fun _=>hA) C' (fun _ xi=>hbound' xi)
  unfold nativeExteriorForestRootLaw exteriorForestRootLaw exteriorForestIRoot exteriorForestStarRoot
    departedAnchorRootLaw departedAnchorTargetRoot departedAnchorExteriorRoot
  change _=∫ z,B (z.1.2,z.2)
    ∂retainedPrefixFieldLaw w φ ms ts
      (retainedPrefixFieldLaw w φ ps (ms++ts) μ x hx) Prod.snd measurable_snd
  rw [HB,HA]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have H:=nativeExteriorForestTree_expect_eq_prefix pre mid hw φ Ei Es D ho q Q (x p)
  have hc : clockSteps (mid++tail) qi=ms++ts := clockSteps_append mid tail qi
  rw [hc] at H
  exact H

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem nativeExteriorForest_four_copy_mean {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (Q : Ei.Assignment→Es.Assignment→ℝ) (xi xs : ι→ℝ) :
    nativeExteriorForestMean (ClockTree.exteriorQuadNative Ei) (ClockTree.exteriorQuadNative Es)
      w φ qi qs (fun η ζ=>Q η.1.1 ζ.1.1*Q η.1.2 ζ.1.2*Q η.2.1 ζ.2.1*Q η.2.2 ζ.2.2) xi xs =
      (nativeExteriorForestMean Ei Es w φ qi qs Q xi xs)^4 := by
  unfold nativeExteriorForestMean
  simp_rw [ClockTree.exteriorQuadNative_expect_product]
  calc
    _ = (Ei.expect w φ qi (fun η=>Es.expect w φ qs (Q η) xs) xi)*
        (Ei.expect w φ qi (fun η=>Es.expect w φ qs (Q η) xs) xi)*
        (Ei.expect w φ qi (fun η=>Es.expect w φ qs (Q η) xs) xi)*
        (Ei.expect w φ qi (fun η=>Es.expect w φ qs (Q η) xs) xi) :=
      ClockTree.exteriorQuadNative_expect_product Ei w φ qi _ _ _ _ xi
    _ = _ := by ring

def nativeExteriorForestAveragedFourth {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi xs : ι→ℝ) : ℝ :=
  D.expect w φ qs (fun σ=>(nativeExteriorForestMean Ei Es w φ qi qs (fun η ζ=>Q η ζ σ) xi xs)^4) xs

theorem nativeExteriorForest_four_tooth_original_law (pre mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (q : ℕ→ι→ℝ≥0) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→ι→ℝ) (hx : Measurable x) :
    (∫ p,(nativeExteriorForestTree pre mid (ClockTree.exteriorQuadNative Ei)
      (ClockTree.exteriorQuadNative Es) D).expect w φ q
      (nativeExteriorForestRead pre mid (ClockTree.exteriorQuadNative Ei)
        (ClockTree.exteriorQuadNative Es) D
        (fun η ζ σ=>Q η.1.1 ζ.1.1 σ*Q η.1.2 ζ.1.2 σ*
          Q η.2.1 ζ.2.1 σ*Q η.2.2 ζ.2.2 σ)) (x p) ∂μ) =
    ∫ z,nativeExteriorForestAveragedFourth Ei Es D w φ (fun j=>q (pre.length+j))
      (fun j=>q (pre.length+(mid.length+j))) Q (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂nativeExteriorForestRootLaw w φ pre mid tail q μ x hx := by
  rw [nativeExteriorForest_original_law_eq_conditional pre mid hw φ
    (ClockTree.exteriorQuadNative Ei) (ClockTree.exteriorQuadNative Es) D ho q _ μ x hx]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only [nativeExteriorForestConditionalTest,nativeExteriorForestAveragedFourth]
  apply congrArg (fun F : D.Assignment→ℝ=>D.expect w φ _ F (exteriorForestStarRoot z))
  funext σ
  exact nativeExteriorForest_four_copy_mean Ei Es w φ _ _ (fun η ζ=>Q η ζ σ) _ _

end OAI.SKFluctuations.Cavity
