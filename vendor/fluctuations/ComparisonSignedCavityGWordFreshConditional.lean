module

public import ComparisonSignedCavityGWordPayload

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_rest_G_word_fresh_partner_fold
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (base : NativeGeneratedTest T) (E : NativeObservedDiagram T)
    (f e c : E.tree.Slot) (teeth : List E.tree.Slot) (hm : E.marks=f::e::c::teeth)
    (ho : MassOrdered 0 as) (star U : ℕ) (hstar : star ≤ as.length)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ) :
    nativeRestGSpineDiagramValue T base star U q b h K C A R (E.fresh base.target star 0)=
      nativeObservedGScalar E base.target U K*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) E.tree.cavityLeft
        (E.tree.cavityLeftSlot (E.embed base.target)) star 0 q
        (fun y σ=>
          nativeObservedToothPayload E 3 (fun u v=>R u v-C star)
            (nativeGWordOldPayload T base star U (E.tree.splitIndex e f) q b h K C A R)
            (nativeGWordOldSelector T base) y σ-
          nativeObservedToothPayload E 3 (fun u v=>R u v-C star)
            (nativeGWordNewPayload T base star U (E.tree.splitIndex e f) q b h K C A R)
            (nativeGWordNewSelector T) y σ) 0 := by
  let g:=nativeFreshAtSlot E.tree 0 (E.embed base.target) star
  let spinAt:=fun (σ : E.tree.cavityLeft.Assignment) d=>E.tree.cavityLeft.atSlot σ (E.tree.cavityLeftSlot d)
  let oldSpin:=fun σ=>T.cavityLeft.atSlot (E.restRead σ) (T.cavityLeftSlot base.target)
  let Q : E.tree.cavityLeft.Assignment→ℝ:=fun σ=>
    (nativeRestGeneratedTestValue T base R C (E.restRead σ)*
      (teeth.map (fun d=>R (oldSpin σ) (spinAt σ d)-C star)).prod-
    nativeRestGeneratedTestValue T base R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot base.target) (E.restRead σ) (spinAt σ c))*
      (teeth.map (fun d=>R (spinAt σ c) (spinAt σ d)-C star)).prod)*
      restHighKernel n U b h K (E.tree.splitIndex e f) (spinAt σ e) (spinAt σ f)
  have hM : (E.fresh base.target star 0).marks=
      g.embed f::g.embed e::g.embed c::(teeth.map g.embed++[g.mark]) := by
    simp only [NativeObservedDiagram.fresh,hm,List.map_cons,List.cons_append,g]
  have HRaw : nativeRestGSpineDiagramValue T base star U q b h K C A R (E.fresh base.target star 0)=
      nativeObservedGScalar E base.target U K*
      g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>Q (g.restRestrict σ)*
          (A (spinAt (g.restRestrict σ) c) (g.restSpin σ)-A (oldSpin (g.restRestrict σ)) (g.restSpin σ))) 0 := by
    simp only [nativeRestGSpineDiagramValue,hM,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.cons_append,List.map_reverse,List.prod_reverse,
      NativeObservedDiagram.restRead_fresh]
    simp only [nativeObservedGScalar,hm,NativeObservedDiagram.fresh]
    rw [native_full_connected_four_marked_preserves E.tree ho U K (E.embed base.target) c e f
      g (nativeFreshAtSlot_mem E.tree 0 (E.embed base.target) star)]
    apply congrArg (fun x=>(1/2:ℝ)*fullScalarCutConnected4 E.tree U K (E.embed base.target) c e f*x)
    apply congrArg (fun J=>g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q J 0)
    funext σ
    dsimp only [Q,oldSpin,spinAt,g]
    simp only [List.map_map,Function.comp_def,MarkedPlacement.restRestrict_at,MarkedPlacement.restSpin,
      (nativeFreshAtSlot_old_splits E.tree 0 (E.embed base.target) star).2]
    ring
  rw [HRaw]
  apply congrArg (fun x=>nativeObservedGScalar E base.target U K*x)
  rw [←native_star_field_disorder_field_independent g.tree.cavityLeft
    (g.tree.cavityLeftSlot (g.embed (E.embed base.target))) star (restWeight_pos n) (restFeature n) ho 0 q]
  rw [native_star_field_disorder_fresh_displacement_fold E.tree (E.embed base.target) star hstar 0
    (restWeight_pos n) (restFeature n) ho 0 q A (fun _ σ=>Q σ)
    (fun _ σ=>spinAt σ c) (fun _ σ=>oldSpin σ) 0]
  apply congrArg (fun J=>nativeStarFieldDisorderMean (restWeight n) (restFeature n) E.tree.cavityLeft
    (E.tree.cavityLeftSlot (E.embed base.target)) star 0 q J 0)
  funext y σ
  simp only [nativeObservedToothPayload,nativeGWordOldPayload,nativeGWordNewPayload,
    nativeGWordOldSelector,nativeGWordNewSelector,nativeGWordNewSpin,nativeGWordError,
    nativeGWordDisplacement,NativeObservedDiagram.restMarks,hm,List.map_cons,List.take_succ_cons,
    List.take_zero,List.drop_succ_cons,List.drop_zero,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  dsimp only [Q,oldSpin,spinAt]
  simp only [List.map_map,Function.comp_def]
  ring

end OAI.SKFluctuations.Cavity
