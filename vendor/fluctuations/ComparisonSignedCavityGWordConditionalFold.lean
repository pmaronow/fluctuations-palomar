module

public import ComparisonSignedCavityGWordFreshConditional
public import ComparisonSignedCavityObservedWordDisorderFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_rest_G_word_fresh_partner_fold_index
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (base : NativeGeneratedTest T) (E : NativeObservedDiagram T)
    (hk : 3 ≤ E.marks.length) (ho : MassOrdered 0 as) (star U : ℕ)
    (hstar : star ≤ as.length) (q : ℕ→RestCoordinate n→ℝ)
    (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ) :
    nativeRestGSpineDiagramValue T base star U q b h K C A R (E.fresh base.target star 0)=
      nativeObservedGScalar E base.target U K*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) E.tree.cavityLeft
        (E.tree.cavityLeftSlot (E.embed base.target)) star 0 q
        (fun y σ=>
          nativeObservedToothPayload E 3 (fun u v=>R u v-C star)
            (nativeGWordOldPayload T base star U (nativeObservedErrorIndex E) q b h K C A R)
            (nativeGWordOldSelector T base) y σ-
          nativeObservedToothPayload E 3 (fun u v=>R u v-C star)
            (nativeGWordNewPayload T base star U (nativeObservedErrorIndex E) q b h K C A R)
            (nativeGWordNewSelector T) y σ) 0 := by
  cases hm : E.marks with
  | nil=>simp only [hm,List.length_nil] at hk;omega
  | cons f tail=>
    cases tail with
    | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
    | cons e tail=>
      cases tail with
      | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
      | cons c tail=>
        simpa only [nativeObservedErrorIndex,hm] using
          native_rest_G_word_fresh_partner_fold T base E f e c tail hm ho star U hstar q b h K C A R

def nativeGWordProjectedPayload {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T)
    (D : NativeObservedDiagram T) (star U power : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ)
    (y : RestCoordinate n→ℝ) (σ : D.tree.cavityLeft.Assignment) : ℝ :=
  nativeGWordOldPayload T base star U (nativeObservedErrorIndex D) q b h K C A R
      y (D.restRead σ) (D.restMarks σ)*
    (nativeStarPairFactor (restWeight n) (restFeature n) as star
      (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun u v=>R u v-C star) y
      (nativeGWordOldSelector T base y (D.restRead σ) (D.restMarks σ)))^power-
  nativeGWordNewPayload T base star U (nativeObservedErrorIndex D) q b h K C A R
      y (D.restRead σ) (D.restMarks σ)*
    (nativeStarPairFactor (restWeight n) (restFeature n) as star
      (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun u v=>R u v-C star) y
      (nativeGWordNewSelector T y (D.restRead σ) (D.restMarks σ)))^power

theorem native_rest_G_spine_word_conditional_fold
    {n : ℕ} {as : List PositiveMass} {B T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (spine : NativeProjectionSpine base star P) (D : NativeObservedDiagram B)
    (hk : D.marks.length=3) (ho : MassOrdered 0 as) (U : ℕ)
    (hstar : star ≤ as.length) (q : ℕ→RestCoordinate n→ℝ)
    (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ) :
    nativeRestGSpineDiagramValue B base star U q b h K C A R
      ((spine.graftDiagram D).fresh base.target star 0)=
    nativeObservedGScalar (spine.graftDiagram D) base.target U K*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
        (D.tree.cavityLeftSlot (D.embed base.target)) star 0 q
        (nativeGWordProjectedPayload B base D star U spine.toothCount q b h K C A R) 0 := by
  rw [native_rest_G_word_fresh_partner_fold_index B base (spine.graftDiagram D)
    (by rw [spine.graft_marks_length_all,hk];omega) ho star U hstar]
  rw [spine.graft_error_index D (by omega)]
  apply congrArg (fun z=>nativeObservedGScalar (spine.graftDiagram D) base.target U K*z)
  have H:=spine.observed_word_paired_disorder_fold D (restWeight_pos n) (restFeature n) ho 0 q
    (fun u v=>R u v-C star)
    (nativeGWordOldPayload B base star U (nativeObservedErrorIndex D) q b h K C A R)
    (nativeGWordNewPayload B base star U (nativeObservedErrorIndex D) q b h K C A R)
    (nativeGWordOldSelector B base) (nativeGWordNewSelector B) 0
  unfold nativeGWordProjectedPayload
  simpa only [hk] using H

end OAI.SKFluctuations.Cavity
