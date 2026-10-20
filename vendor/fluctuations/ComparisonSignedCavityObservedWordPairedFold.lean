module

public import ComparisonSignedCavityObservedWordToothFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open scoped NNReal BigOperators
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S]
variable {as : List PositiveMass}

theorem native_star_fresh_paired_factor
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (star : ℕ) (q : ℕ→ι→ℝ≥0)
    (F : S→S→ℝ) (x : ι→ℝ) (a b : ℝ) (u v : S) :
    nativeStarFreshTestMean w φ as star q (fun t=>a*F u t-b*F v t) x=
      a*nativeStarPairFactor w φ as star q F x u-
        b*nativeStarPairFactor w φ as star q F x v := by
  unfold nativeStarFreshTestMean nativeStarPairFactor expect
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

theorem NativeProjectionSpine.observed_word_paired_tooth_fold
    {A V : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest V}
    {star : ℕ} (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ→ι→ℝ≥0) (F : S→S→ℝ)
    (J₁ J₂ : (ι→ℝ)→A.cavityLeft.Assignment→List S→ℝ)
    (U₁ U₂ : (ι→ℝ)→A.cavityLeft.Assignment→List S→S) (x : ι→ℝ) :
    nativeStarFieldTestMean w φ (h.graftDiagram D).tree.cavityLeft
      ((h.graftDiagram D).tree.cavityLeftSlot ((h.graftDiagram D).embed base.target)) star q
      (fun y σ=>nativeObservedToothPayload (h.graftDiagram D) D.marks.length F J₁ U₁ y σ-
        nativeObservedToothPayload (h.graftDiagram D) D.marks.length F J₂ U₂ y σ) x=
    nativeStarFieldTestMean w φ D.tree.cavityLeft (D.tree.cavityLeftSlot (D.embed base.target)) star q
      (fun y σ=>J₁ y (D.restRead σ) (D.restMarks σ)*
        (nativeStarPairFactor w φ as star q F y (U₁ y (D.restRead σ) (D.restMarks σ)))^h.toothCount-
        J₂ y (D.restRead σ) (D.restMarks σ)*
        (nativeStarPairFactor w φ as star q F y (U₂ y (D.restRead σ) (D.restMarks σ)))^h.toothCount) x := by
  induction h generalizing J₁ J₂ with
  | base=>
    simp only [graftDiagram,id_eq,toothCount,pow_zero,mul_one]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) star q L x)
    funext y σ
    simp only [nativeObservedToothPayload,←D.restMarks_length σ,List.take_length,List.drop_length,
      List.map_nil,List.prod_nil,mul_one]
  | @projection V P h a hl ih=>
    let E:=h.graftDiagram D
    have hk : D.marks.length ≤ E.marks.length := by
      dsimp only [E]
      rw [h.graft_marks_length]
      omega
    change nativeStarFieldTestMean w φ (E.fresh base.target star a).tree.cavityLeft
      ((E.fresh base.target star a).tree.cavityLeftSlot ((E.fresh base.target star a).embed base.target)) star q
      (fun y σ=>nativeObservedToothPayload (E.fresh base.target star a) D.marks.length F J₁ U₁ y σ-
        nativeObservedToothPayload (E.fresh base.target star a) D.marks.length F J₂ U₂ y σ) x=_
    simp_rw [native_observed_tooth_payload_fresh E base.target star a D.marks.length hk]
    refine (native_star_field_fresh_test_factor E.tree (E.embed base.target) star hl a hw φ ho q
      (fun y σ d=>nativeObservedToothPayload E D.marks.length F J₁ U₁ y σ*
        F (U₁ y (E.restRead σ) ((E.restMarks σ).take D.marks.length)) d-
        nativeObservedToothPayload E D.marks.length F J₂ U₂ y σ*
        F (U₂ y (E.restRead σ) ((E.restMarks σ).take D.marks.length)) d) x).trans ?_
    simp_rw [native_star_fresh_paired_factor]
    have HP (J : (ι→ℝ)→A.cavityLeft.Assignment→List S→ℝ)
        (U : (ι→ℝ)→A.cavityLeft.Assignment→List S→S) :
        (fun y σ=>nativeObservedToothPayload E D.marks.length F J U y σ*
          nativeStarPairFactor w φ as star q F y
            (U y (E.restRead σ) ((E.restMarks σ).take D.marks.length)))=
        nativeObservedToothPayload E D.marks.length F
          (fun y τ us=>J y τ us*nativeStarPairFactor w φ as star q F y (U y τ us)) U := by
      funext y σ
      unfold nativeObservedToothPayload
      ring
    conv_lhs =>
      arg 7
      change (fun y σ=>(fun y σ=>nativeObservedToothPayload E D.marks.length F J₁ U₁ y σ*
          nativeStarPairFactor w φ as star q F y (U₁ y (E.restRead σ) ((E.restMarks σ).take D.marks.length))) y σ-
        (fun y σ=>nativeObservedToothPayload E D.marks.length F J₂ U₂ y σ*
          nativeStarPairFactor w φ as star q F y (U₂ y (E.restRead σ) ((E.restMarks σ).take D.marks.length))) y σ)
      rw [HP J₁ U₁,HP J₂ U₂]
    rw [ih]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) star q L x)
    funext y σ
    simp only [toothCount,pow_succ]
    ring

end OAI.SKFluctuations.Hierarchy.ClockTree
