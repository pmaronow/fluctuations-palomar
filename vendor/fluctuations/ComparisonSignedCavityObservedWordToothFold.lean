module

public import ComparisonSignedCavityObservedDiagramRestRead

@[expose] public section

noncomputable section
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
open scoped NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} {as : List PositiveMass} {T : ClockTree (S×B) as}

def nativeObservedToothPayload (D : NativeObservedDiagram T) (k : ℕ) (F : S→S→ℝ)
    (J : (ι→ℝ)→T.cavityLeft.Assignment→List S→ℝ)
    (U : (ι→ℝ)→T.cavityLeft.Assignment→List S→S)
    (y : ι→ℝ) (σ : D.tree.cavityLeft.Assignment) : ℝ :=
  J y (D.restRead σ) ((D.restMarks σ).take k)*
    (((D.restMarks σ).drop k).map (F (U y (D.restRead σ) ((D.restMarks σ).take k)))).prod

theorem native_observed_tooth_payload_fresh
    (D : NativeObservedDiagram T) (s : T.Slot) (star : ℕ) (a : ℝ)
    (k : ℕ) (hk : k ≤ D.marks.length) (F : S→S→ℝ)
    (J : (ι→ℝ)→T.cavityLeft.Assignment→List S→ℝ)
    (U : (ι→ℝ)→T.cavityLeft.Assignment→List S→S)
    (y : ι→ℝ) (σ : (D.fresh s star a).tree.cavityLeft.Assignment) :
    nativeObservedToothPayload (D.fresh s star a) k F J U y σ=
      nativeObservedToothPayload D k F J U y
        ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict σ)*
      F (U y (D.restRead ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict σ))
          ((D.restMarks ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict σ)).take k))
        ((nativeFreshAtSlot D.tree a (D.embed s) star).restSpin σ) := by
  have hk' : k ≤ (D.restMarks ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict σ)).length := by
    simpa only [D.restMarks_length] using hk
  simp only [nativeObservedToothPayload,D.restRead_fresh,D.restMarks_fresh,
    List.take_append_of_le_length hk',List.drop_append_of_le_length hk',
    List.map_append,List.map_singleton,List.prod_append,List.prod_singleton]
  ring

variable [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem NativeProjectionSpine.observed_word_tooth_fold
    {A V : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest V}
    {star : ℕ} (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ→ι→ℝ≥0) (F : S→S→ℝ)
    (J : (ι→ℝ)→A.cavityLeft.Assignment→List S→ℝ)
    (U : (ι→ℝ)→A.cavityLeft.Assignment→List S→S) (x : ι→ℝ) :
    nativeStarFieldTestMean w φ (h.graftDiagram D).tree.cavityLeft
      ((h.graftDiagram D).tree.cavityLeftSlot ((h.graftDiagram D).embed base.target)) star q
      (nativeObservedToothPayload (h.graftDiagram D) D.marks.length F J U) x=
    nativeStarFieldTestMean w φ D.tree.cavityLeft (D.tree.cavityLeftSlot (D.embed base.target)) star q
      (fun y σ=>J y (D.restRead σ) (D.restMarks σ)*
        (nativeStarPairFactor w φ as star q F y (U y (D.restRead σ) (D.restMarks σ)))^h.toothCount) x := by
  induction h generalizing J with
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
      (fun y σ=>nativeObservedToothPayload (E.fresh base.target star a) D.marks.length F J U y σ) x=_
    simp_rw [native_observed_tooth_payload_fresh E base.target star a D.marks.length hk F J U]
    refine (native_star_field_fresh_selector_factor E.tree (E.embed base.target) star hl a hw φ ho q
      (nativeObservedToothPayload E D.marks.length F J U)
      (fun y σ=>U y (E.restRead σ) ((E.restMarks σ).take D.marks.length)) F x).trans ?_
    have HP : (fun y σ=>nativeObservedToothPayload E D.marks.length F J U y σ*
        nativeStarPairFactor w φ as star q F y
          (U y (E.restRead σ) ((E.restMarks σ).take D.marks.length)))=
      nativeObservedToothPayload E D.marks.length F
        (fun y τ us=>J y τ us*nativeStarPairFactor w φ as star q F y (U y τ us)) U := by
      funext y σ
      unfold nativeObservedToothPayload
      ring
    rw [HP,ih]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) star q L x)
    funext y σ
    simp only [toothCount,pow_succ]
    ring

end OAI.SKFluctuations.Hierarchy.ClockTree
