module

public import ComparisonSignedCavitySecondLowOccupiedLabeledWordJoin
public import ComparisonSignedCavitySecondLowObservedMiddleValueSymmetry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_second_low_high_mark_low_split {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (x c : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (Hhigh : U ≤ p.tree.splitIndex (p.embed c) p.mark) (Hlow : T.splitIndex x c<U) :
    p.tree.splitIndex (p.embed x) p.mark=T.splitIndex x c := by
  rw [p.tree.splitIndex_symm]
  calc
    p.tree.splitIndex p.mark (p.embed x)=p.tree.splitIndex (p.embed c) (p.embed x):=
      p.tree.splitIndex_low_eq_of_high p.mark (p.embed c) (p.embed x)
        (by simpa only [p.tree.splitIndex_symm p.mark (p.embed c)] using Hhigh)
        (by rw [(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm c x];omega)
    _=T.splitIndex c x:=(T.markedAttach_embed_preserves 0 p hp).2 c x
    _=T.splitIndex x c:=T.splitIndex_symm c x

theorem native_second_low_two_high_old_endpoint_splits {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (f d c : T.Slot)
    (Hf : T.splitIndex f c<U) (Hd : T.splitIndex d c<U)
    (s : MarkedPlacement T) (hs : s∈T.markedAttach 0)
    (Hs : U ≤ s.tree.splitIndex (s.embed c) s.mark)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Ht : U ≤ t.tree.splitIndex (t.embed (s.embed c)) t.mark) :
    t.tree.splitIndex (t.embed (s.embed f)) (t.embed s.mark)=T.splitIndex f c ∧
    t.tree.splitIndex (t.embed (s.embed f)) t.mark=T.splitIndex f c ∧
    t.tree.splitIndex (t.embed (s.embed d)) (t.embed s.mark)=T.splitIndex d c ∧
    t.tree.splitIndex (t.embed (s.embed d)) t.mark=T.splitIndex d c := by
  have HSf:=native_second_low_high_mark_low_split T U f c s hs Hs Hf
  have HSd:=native_second_low_high_mark_low_split T U d c s hs Hs Hd
  have HTf:=native_second_low_high_mark_low_split s.tree U (s.embed f) (s.embed c) t ht Ht
    (by rw [(T.markedAttach_embed_preserves 0 s hs).2];exact Hf)
  have HTd:=native_second_low_high_mark_low_split s.tree U (s.embed d) (s.embed c) t ht Ht
    (by rw [(T.markedAttach_embed_preserves 0 s hs).2];exact Hd)
  exact ⟨((s.tree.markedAttach_embed_preserves 0 t ht).2 _ _).trans HSf,
    HTf.trans ((T.markedAttach_embed_preserves 0 s hs).2 _ _),
    ((s.tree.markedAttach_embed_preserves 0 t ht).2 _ _).trans HSd,
    HTd.trans ((T.markedAttach_embed_preserves 0 s hs).2 _ _)⟩

theorem native_second_low_labeled_middle_QQKK_test_adapter
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (U : ℕ) (b h K : ℕ→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (_a v _z : T.Slot) (j : Fin 8) (D : NativeSecondLowLabeledDiagram T)
    (Hf : D.tree.splitIndex (D.marks 0) (D.embed v)<U)
    (Hd : D.tree.splitIndex (D.marks 3) (D.embed v)<U)
    (s : MarkedPlacement D.tree) (hs : s∈D.tree.markedAttach 0)
    (Hs : U ≤ s.tree.splitIndex (s.embed (D.embed v)) s.mark)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Ht : U ≤ t.tree.splitIndex (t.embed (s.embed (D.embed v))) t.mark) :
    nativeSecondLowLabeledQQKKTest U b h K P j ((D.observe 1 s).observe 2 t)=
      fun τ=>
        let old:=s.restRestrict (t.restRestrict τ)
        let i:=D.tree.splitIndex (D.marks 0) (D.embed v)
        let k:=D.tree.splitIndex (D.marks 3) (D.embed v)
        let F:=D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 0))
        let G:=D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 3))
        P (D.restRead old)*
          (if j.val<4 then restLowKernel n U b h i F (s.restSpin (t.restRestrict τ))*
              restLowKernel n U b h k G (t.restSpin τ)-nativeSecondLowScalarValue U K i*nativeSecondLowScalarValue U K k
          else restLowKernel n U b h k G (s.restSpin (t.restRestrict τ))*
              restLowKernel n U b h i F (t.restSpin τ)-nativeSecondLowScalarValue U K k*nativeSecondLowScalarValue U K i) := by
  obtain ⟨Hfc,Hfe,Hdc,Hde⟩:=native_second_low_two_high_old_endpoint_splits D.tree U
    (D.marks 0) (D.marks 3) (D.embed v) Hf Hd s hs Hs t ht Ht
  have Hcd : t.tree.splitIndex (t.embed s.mark) (t.embed (s.embed (D.marks 3)))=
      D.tree.splitIndex (D.marks 3) (D.embed v):=by
    rw [t.tree.splitIndex_symm]
    exact Hdc
  have Hed : t.tree.splitIndex t.mark (t.embed (s.embed (D.marks 3)))=
      D.tree.splitIndex (D.marks 3) (D.embed v):=by
    rw [t.tree.splitIndex_symm]
    exact Hde
  funext τ
  simp only [nativeSecondLowLabeledQQKKTest,NativeSecondLowLabeledDiagram.observe_restRead]
  simp [nativeSecondLowLabeledLowRow,nativeSecondLowLabeledScalarRow,
    NativeSecondLowLabeledDiagram.observe,←t.restRestrict_at,←s.restRestrict_at,
    MarkedPlacement.restSpin,Hfc,Hfe,Hcd,Hed,
    native_second_low_rest_low_kernel_symm]

theorem native_second_low_labeled_middle_gamma_atom_adapter
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) (j : Fin 8) (D : NativeSecondLowLabeledDiagram T)
    (Hf : D.tree.splitIndex (D.marks 0) (D.embed v)<U)
    (Hd : D.tree.splitIndex (D.marks 3) (D.embed v)<U)
    (s : MarkedPlacement D.tree) (hs : s∈D.tree.markedAttach 0)
    (Hs : U ≤ s.tree.splitIndex (s.embed (D.embed v)) s.mark)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Ht : U ≤ t.tree.splitIndex (t.embed (s.embed (D.embed v))) t.mark) :
    nativeSecondLowLabeledGammaValue q U b h K P a z j ((D.observe 1 s).observe 2 t)=
      (fullScalarCutGamma D.tree U K (D.embed a) (D.marks 0)*
        fullScalarCutGamma D.tree U K (D.marks 3) (D.embed z))*
      (t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ=>
          let old:=s.restRestrict (t.restRestrict τ)
          let i:=D.tree.splitIndex (D.marks 0) (D.embed v)
          let k:=D.tree.splitIndex (D.marks 3) (D.embed v)
          let F:=D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 0))
          let G:=D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 3))
          P (D.restRead old)*
            (if j.val<4 then restLowKernel n U b h i F (s.restSpin (t.restRestrict τ))*
                restLowKernel n U b h k G (t.restSpin τ)-nativeSecondLowScalarValue U K i*nativeSecondLowScalarValue U K k
            else restLowKernel n U b h k G (s.restSpin (t.restRestrict τ))*
                restLowKernel n U b h i F (t.restSpin τ)-nativeSecondLowScalarValue U K k*nativeSecondLowScalarValue U K i)) 0*
        fullScalarCutGamma t.tree U K (t.embed s.mark) t.mark) := by
  unfold nativeSecondLowLabeledGammaValue
  rw [native_second_low_labeled_middle_QQKK_test_adapter U b h K P a v z j D Hf Hd s hs Hs t ht Ht]
  simp only [NativeSecondLowLabeledDiagram.observe]
  simp only [Fin.isValue,show (0:Fin 4)≠2 by decide,show (0:Fin 4)≠1 by decide,
    show (1:Fin 4)≠2 by decide,show (3:Fin 4)≠2 by decide,show (3:Fin 4)≠1 by decide,
    ↓reduceIte]
  rw [fullScalarCutGamma_double_preserves D.tree ho U K (D.embed a) (D.marks 0) s hs t ht,
    fullScalarCutGamma_double_preserves D.tree ho U K (D.marks 3) (D.embed z) s hs t ht]
  ring

theorem native_second_low_labeled_inner_middle_source_adapter
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) (j : Fin 8)
    (D : NativeSecondLowLabeledDiagram T)
    (Hf : D.tree.splitIndex (D.marks 0) (D.embed v)<U)
    (Hd : D.tree.splitIndex (D.marks 3) (D.embed v)<U) :
    nativeSecondLowLabeledHighEvalFold D (![a,v,v,z]) (U-1)
      (nativeSecondLowLabeledGammaValue q U b h K P a z j) [1,2]=
      (fullScalarCutGamma D.tree U K (D.embed a) (D.marks 0)*
        fullScalarCutGamma D.tree U K (D.marks 3) (D.embed z))*
      (if j.val<4 then
        nativeSecondLowObservedMiddleQQKKValue n q U b h K D.tree (D.embed v) (U-1)
          (fun old=>P (D.restRead old))
          (fun old=>D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 0)))
          (fun old=>D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 3)))
          (D.tree.splitIndex (D.marks 0) (D.embed v)) (D.tree.splitIndex (D.marks 3) (D.embed v))
      else
        nativeSecondLowObservedMiddleQQKKValue n q U b h K D.tree (D.embed v) (U-1)
          (fun old=>P (D.restRead old))
          (fun old=>D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 3)))
          (fun old=>D.tree.cavityLeft.atSlot old (D.tree.cavityLeftSlot (D.marks 0)))
          (D.tree.splitIndex (D.marks 3) (D.embed v)) (D.tree.splitIndex (D.marks 0) (D.embed v))) := by
  have Hat (s : MarkedPlacement D.tree) (hs : s∈nativeHighMarkedRows D.tree (D.embed v) (U-1) 0)
      (t : MarkedPlacement s.tree) (ht : t∈nativeHighMarkedRows s.tree (s.embed (D.embed v)) (U-1) 0) :=
    native_second_low_labeled_middle_gamma_atom_adapter q U b h K ho P a v z j D Hf Hd
      s ((mem_nativeHighMarkedRows D.tree (D.embed v) (U-1) 0 s).mp hs).1
      (by have H:=((mem_nativeHighMarkedRows D.tree (D.embed v) (U-1) 0 s).mp hs).2;omega)
      t ((mem_nativeHighMarkedRows s.tree (s.embed (D.embed v)) (U-1) 0 t).mp ht).1
      (by have H:=((mem_nativeHighMarkedRows s.tree (s.embed (D.embed v)) (U-1) 0 t).mp ht).2;omega)
  by_cases HB : j.val<4
  all_goals simp only [HB,ite_true,ite_false]
  all_goals unfold nativeSecondLowObservedMiddleQQKKValue
  all_goals simp only [nativeSecondLowLabeledHighEvalFold,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,NativeSecondLowLabeledDiagram.observe]
  all_goals simp only [←List.sum_map_mul_left]
  all_goals apply congrArg List.sum
  all_goals apply List.map_congr_left
  all_goals intro s hs
  all_goals apply congrArg List.sum
  all_goals apply List.map_congr_left
  all_goals intro t ht
  all_goals have H:=Hat s hs t ht
  all_goals simp only [HB,ite_true,ite_false,nativeSecondLowScalarValue,
    NativeSecondLowLabeledDiagram.observe] at H
  all_goals rw [H]
  all_goals ring

theorem native_second_low_labeled_inner_middle_value_orientation_independent
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) (j : Fin 8)
    (D : NativeSecondLowLabeledDiagram T)
    (Hf : D.tree.splitIndex (D.marks 0) (D.embed v)<U)
    (Hd : D.tree.splitIndex (D.marks 3) (D.embed v)<U) :
    nativeSecondLowLabeledHighEvalFold D (![a,v,v,z]) (U-1)
      (nativeSecondLowLabeledGammaValue q U b h K P a z j) [1,2]=
    nativeSecondLowLabeledHighEvalFold D (![a,v,v,z]) (U-1)
      (nativeSecondLowLabeledGammaValue q U b h K P a z 0) [1,2] := by
  rw [native_second_low_labeled_inner_middle_source_adapter q U b h K ho hU0 P a v z j D Hf Hd,
    native_second_low_labeled_inner_middle_source_adapter q U b h K ho hU0 P a v z 0 D Hf Hd]
  simp only [Fin.val_zero,show (0:ℕ)<4 by decide,ite_true]
  by_cases HB : j.val<4
  · rw [ite_eq_left HB]
  · rw [ite_eq_right HB]
    rw [native_second_low_observed_middle_QQKK_value_edge_order_symm n q U b h K D.tree ho]

end OAI.SKFluctuations.Cavity
