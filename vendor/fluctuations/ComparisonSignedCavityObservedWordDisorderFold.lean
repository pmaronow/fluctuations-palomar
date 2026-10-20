module

public import ComparisonSignedCavityObservedWordPairedFold
public import ComparisonSignedCavityStarFieldJointClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory Filter
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] {as : List PositiveMass}

theorem NativeProjectionSpine.observed_word_paired_disorder_fold
    {A V : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest V}
    {star : ℕ} (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (F : S→S→ℝ)
    (J₁ J₂ : (ι→ℝ)→A.cavityLeft.Assignment→List S→ℝ)
    (U₁ U₂ : (ι→ℝ)→A.cavityLeft.Assignment→List S→S) (x : ι→ℝ) :
    nativeStarFieldDisorderMean w φ (h.graftDiagram D).tree.cavityLeft
      ((h.graftDiagram D).tree.cavityLeftSlot ((h.graftDiagram D).embed base.target)) star v q
      (fun y σ=>nativeObservedToothPayload (h.graftDiagram D) D.marks.length F J₁ U₁ y σ-
        nativeObservedToothPayload (h.graftDiagram D) D.marks.length F J₂ U₂ y σ) x=
    nativeStarFieldDisorderMean w φ D.tree.cavityLeft (D.tree.cavityLeftSlot (D.embed base.target)) star v q
      (fun y σ=>J₁ y (D.restRead σ) (D.restMarks σ)*
        (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1))) F y
          (U₁ y (D.restRead σ) (D.restMarks σ)))^h.toothCount-
        J₂ y (D.restRead σ) (D.restMarks σ)*
        (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1))) F y
          (U₂ y (D.restRead σ) (D.restMarks σ)))^h.toothCount) x := by
  unfold nativeStarFieldDisorderMean
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>h.observed_word_paired_tooth_fold D hw φ ho _ F J₁ J₂ U₁ U₂ (x+y))

end OAI.SKFluctuations.Hierarchy.ClockTree
