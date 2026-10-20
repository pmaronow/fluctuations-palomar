module

public import ComparisonSignedCavitySecondLowCanonicalFreshMiddleSource
public import ComparisonSignedCavitySecondLowInheritedFreshAffineSource
public import ComparisonSignedCavityObservedDiagramRestRead
public import ComparisonSignedCavityHighFreshWordSums
public import ComparisonSignedCavityHighRowsSupportReduction

@[expose] public section

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def nativeSecondLowObservedHighEvalFold (D : NativeObservedDiagram T) (high : ℕ)
    (F : NativeObservedDiagram T→ℝ) : List T.Slot→ℝ
  | []=>F D
  | c::cs=>((nativeHighMarkedRows D.tree (D.embed c) high 0).map
      (fun p=>p.coeff*nativeSecondLowObservedHighEvalFold (D.observe p) high F cs)).sum

theorem native_second_low_observed_high_word_eval_fold (D : NativeObservedDiagram T)
    (high : ℕ) (F : NativeObservedDiagram T→ℝ) (cs : List T.Slot) :
    ((nativeSecondLowObservedHighWord D high cs).map (fun w=>w.1*F w.2)).sum=
      nativeSecondLowObservedHighEvalFold D high F cs := by
  induction cs generalizing D with
  | nil=>simp only [nativeSecondLowObservedHighWord,nativeSecondLowObservedHighEvalFold,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  | cons c cs ih=>
    simp only [nativeSecondLowObservedHighWord,nativeObservedHighRows,List.map_flatMap,
      native_sum_flatMap,List.map_map,Function.comp_def,mul_assoc,List.sum_map_mul_left,
      ih,nativeSecondLowObservedHighEvalFold]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
attribute [local instance] Classical.propDecidable

def nativeSecondLowObservedFreshDiagramResidualValue
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) (D : NativeObservedDiagram T) : ℝ :=
  match D.marks with
  | e::c::f::z::_=>
      fullScalarCutGamma D.tree U K (D.embed a) f*fullScalarCutGamma D.tree U K c e*
        D.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>P (D.restRead τ)*
            restLowKernel n U b h (D.tree.splitIndex f c)
              (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot f))
              (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot c))*
            (restLowKernel n U b h (D.tree.splitIndex e z)
                (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot e))
                (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot z))-
              restLowKernel n U b h (D.tree.splitIndex c z)
                (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot c))
                (D.tree.cavityLeft.atSlot τ (D.tree.cavityLeftSlot z)))) 0
  | _=>0

def nativeSecondLowFreshThreeObservedDiagram {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (z : T.Slot) (star : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 z star).tree)
    (r : MarkedPlacement p.tree) (e : MarkedPlacement r.tree) : NativeObservedDiagram T :=
  ((((NativeObservedDiagram.identity T).fresh z star 0).observe p).observe r).observe e

theorem native_second_low_fresh_three_observe_rest_read {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (z : T.Slot) (star : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 z star).tree)
    (r : MarkedPlacement p.tree) (e : MarkedPlacement r.tree) (τ : e.tree.cavityLeft.Assignment) :
    (nativeSecondLowFreshThreeObservedDiagram T z star p r e).restRead τ=
      (nativeFreshAtSlot T 0 z star).restRestrict (p.restRestrict (r.restRestrict (e.restRestrict τ))) := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [NativeObservedDiagram.restRead_at,(nativeFreshAtSlot T 0 z star).restRestrict_at,
    p.restRestrict_at,r.restRestrict_at,e.restRestrict_at]
  rfl

theorem native_second_low_fresh_three_diagram_residual_value
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 z star).tree)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (e : MarkedPlacement r.tree) (he : e∈r.tree.markedAttach 0)
    (He : U ≤ e.tree.splitIndex (e.embed r.mark) e.mark)
    (Hcz : r.tree.splitIndex r.mark (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark))<U) :
    nativeSecondLowObservedFreshDiagramResidualValue n q U b h K P a
      (nativeSecondLowFreshThreeObservedDiagram T z star p r e)=
      fullScalarCutGamma p.tree U K (p.embed ((nativeFreshAtSlot T 0 z star).embed a)) p.mark*
        fullScalarCutGamma e.tree U K (e.embed r.mark) e.mark*
        e.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>
            nativeSecondLowCanonicalPartnerOldTest
              (fun old=>P ((nativeFreshAtSlot T 0 z star).restRestrict old)) p r (e.restRestrict τ)*
            nativeSecondLowCanonicalPartnerLowFactor n U b h p r (e.restRestrict τ)*
            (restLowKernel n U b h (r.tree.splitIndex r.mark (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark)))
                (e.restSpin τ)
                (r.tree.cavityLeft.atSlot (e.restRestrict τ)
                  (r.tree.cavityLeftSlot (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark))))-
              restLowKernel n U b h (r.tree.splitIndex r.mark (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark)))
                (r.tree.cavityLeft.atSlot (e.restRestrict τ) (r.tree.cavityLeftSlot r.mark))
                (r.tree.cavityLeft.atSlot (e.restRestrict τ)
                  (r.tree.cavityLeftSlot (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark)))))) 0 := by
  have Hez : e.tree.splitIndex e.mark (e.embed (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark)))=
      r.tree.splitIndex r.mark (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark)) := by
    rw [e.tree.splitIndex_symm]
    exact (native_second_low_high_mark_low_split r.tree U
      (r.embed (p.embed (nativeFreshAtSlot T 0 z star).mark)) r.mark e he He
      (by rw [r.tree.splitIndex_symm];exact Hcz)).trans (r.tree.splitIndex_symm _ _)
  have HR : (nativeSecondLowFreshThreeObservedDiagram T z star p r e).restRead=
      fun τ=>(nativeFreshAtSlot T 0 z star).restRestrict (p.restRestrict (r.restRestrict (e.restRestrict τ))):=by
    funext τ
    exact native_second_low_fresh_three_observe_rest_read T z star p r e τ
  simp only [nativeSecondLowFreshThreeObservedDiagram,NativeObservedDiagram.observe,
    NativeObservedDiagram.fresh,NativeObservedDiagram.identity,id_eq] at HR
  unfold nativeSecondLowObservedFreshDiagramResidualValue
  simp only [nativeSecondLowFreshThreeObservedDiagram,NativeObservedDiagram.observe,
    NativeObservedDiagram.fresh,NativeObservedDiagram.identity,List.map_cons,List.map_nil,List.nil_append,id_eq]
  rw [fullScalarCutGamma_double_preserves p.tree ho U K
    (p.embed ((nativeFreshAtSlot T 0 z star).embed a)) p.mark r hr e he]
  congr 2
  funext τ
  rw [←e.restRestrict_at,←e.restRestrict_at]
  rw [(r.tree.markedAttach_embed_preserves 0 e he).2,Hez,(r.tree.markedAttach_embed_preserves 0 e he).2]
  rw [HR]
  simp only [nativeSecondLowCanonicalPartnerOldTest,nativeSecondLowCanonicalPartnerLowFactor,
    MarkedPlacement.restSpin,←e.restRestrict_at,←r.restRestrict_at]

theorem native_second_low_observed_middle_residual_eq_high_rows
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (c z : T.Slot) (P F : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowObservedMiddleResidual n q U b h K T c z P F=
      ((nativeHighMarkedRows T c (U-1) 0).map (fun e=>e.coeff*fullScalarCutGamma e.tree U K (e.embed c) e.mark*
        e.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun τ=>P (e.restRestrict τ)*F (e.restRestrict τ)*
            (restLowKernel n U b h (T.splitIndex c z) (e.restSpin τ)
                (T.cavityLeft.atSlot (e.restRestrict τ) (T.cavityLeftSlot z))-
              restLowKernel n U b h (T.splitIndex c z)
                (T.cavityLeft.atSlot (e.restRestrict τ) (T.cavityLeftSlot c))
                (T.cavityLeft.atSlot (e.restRestrict τ) (T.cavityLeftSlot z)))) 0)).sum := by
  unfold nativeSecondLowObservedMiddleResidual
  symm
  apply native_high_row_sum_eq_full_of_support
  intro e _ he
  rw [fullScalarCutGamma_cross_zero e.tree ho U K (e.embed c) e.mark hU (by omega)]
  ring

theorem native_second_low_actual_fresh_residual_eq_observed_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) :
    let g:=nativeFreshAtSlot T 0 z star
    nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
        (fun old=>P (g.restRestrict old)) (g.embed a) (g.embed v) g.mark=
      ((nativeSecondLowObservedHighWord ((NativeObservedDiagram.identity T).fresh z star 0)
        (U-1) [a,v,v]).map
        (fun w=>w.1*nativeSecondLowObservedFreshDiagramResidualValue n q U b h K P a w.2)).sum := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 z star
  have hU0 : 0<U:=by omega
  rw [native_second_low_observed_high_word_eval_fold]
  change nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
      (fun old=>P (g.restRestrict old)) (g.embed a) (g.embed v) g.mark=
    ((nativeHighMarkedRows g.tree (g.embed a) (U-1) 0).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed (g.embed v)) (U-1) 0).map (fun r=>r.coeff*
        ((nativeHighMarkedRows r.tree (r.embed (p.embed (g.embed v))) (U-1) 0).map (fun e=>e.coeff*
          nativeSecondLowObservedFreshDiagramResidualValue n q U b h K P a
            (nativeSecondLowFreshThreeObservedDiagram T z star p r e))).sum)).sum)).sum
  unfold nativeSecondLowCanonicalObservedResidualSource
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  obtain ⟨hp',_⟩:=(mem_nativeHighMarkedRows g.tree (g.embed a) (U-1) 0 p).mp hp
  rw [mul_assoc,←List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  obtain ⟨hr',Hr⟩:=(mem_nativeHighMarkedRows p.tree (p.embed (g.embed v)) (U-1) 0 r).mp hr
  have HrU : U ≤ r.tree.splitIndex (r.embed (p.embed (g.embed v))) r.mark:=by omega
  have Hsame:=native_second_low_high_rows_eq_of_same_cut r.tree U hU0 hU
    (r.embed (p.embed (g.embed v))) r.mark HrU
  have Hcz : r.tree.splitIndex r.mark (r.embed (p.embed g.mark))<U:=by
    rw [r.tree.splitIndex_symm,native_second_low_high_mark_low_split p.tree U (p.embed g.mark)
      (p.embed (g.embed v)) r hr' HrU]
    · rw [(g.tree.markedAttach_embed_preserves 0 p hp').2,nativeFreshAtSlot_split]
      exact lt_of_le_of_lt (Nat.min_le_left _ _) hstar
    · rw [(g.tree.markedAttach_embed_preserves 0 p hp').2,nativeFreshAtSlot_split]
      exact lt_of_le_of_lt (Nat.min_le_left _ _) hstar
  rw [native_second_low_observed_middle_residual_eq_high_rows n q U b h K r.tree ho hU0 hU,
    ←Hsame,mul_left_comm,←List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have hec : e∈nativeHighMarkedRows r.tree r.mark (U-1) 0:=by rw [←Hsame];exact he
  obtain ⟨he',He⟩:=(mem_nativeHighMarkedRows r.tree r.mark (U-1) 0 e).mp hec
  rw [native_second_low_fresh_three_diagram_residual_value n q U star b h K T ho P a z p r hr' e he'
    (by omega) Hcz]
  ring

theorem native_second_low_actual_fresh_residual_eq_commuted_observed_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) :
    let g:=nativeFreshAtSlot T 0 z star
    nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
        (fun old=>P (g.restRestrict old)) (g.embed a) (g.embed v) g.mark=
      ((nativeSecondLowObservedHighWord (NativeObservedDiagram.identity T) (U-1) [a,v,v]).map
        (fun w=>w.1*nativeSecondLowObservedFreshDiagramResidualValue n q U b h K P a
          (w.2.fresh z star 0))).sum := by
  dsimp only
  rw [native_second_low_actual_fresh_residual_eq_observed_word n q U star b h K T ho hstar hU P a v z,
    native_second_low_actual_fresh_outside_high_word_numeric (NativeObservedDiagram.identity T)
      z star U hstar hU [a,v,v]]

end OAI.SKFluctuations.Cavity
