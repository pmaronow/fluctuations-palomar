module

public import ComparisonSignedCavityGeneratedProjectionScales
public import ComparisonSignedCavityActualProjectionSpine

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem NativeProjectionSpine.exterior_length {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : P.exterior.length=base.exterior.length := by
  induction h with
  | base=>rfl
  | projection h a hl ih=>simpa only [NativeGeneratedTest.addProjection,List.length_map] using ih

theorem NativeProjectionSpine.edges_length {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : P.edges.length=base.edges.length+h.toothCount := by
  induction h with
  | base=>simp only [NativeProjectionSpine.toothCount,Nat.add_zero]
  | @projection T P h a hl ih=>
    have H:=(P.addProjection_edges_perm a star).length_eq
    simp only [List.length_append,List.length_map,List.length_singleton] at H
    simp only [H,NativeProjectionSpine.toothCount,ih,Nat.add_assoc]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_add_projection_scale {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) (a : ℝ)
    {i star : ℕ} (hi : i < star) (hl : star ≤ as.length) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial (P.addProjection a star) i)=
      sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)*W := by
  simp only [nativeGeneratedCompleteInitial,native_edge_list_source_scale]
  have H:=((P.addProjection_edges_perm a star).map
    (fun e=>if (nativeFreshAtSlot T a P.target star).tree.splitIndex e.1 e.2=i then x else W)).prod_eq
  rw [H]
  simp only [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,List.map_map,Function.comp_def,mul_one]
  have hs:(nativeFreshAtSlot T a P.target star).tree.splitIndex
      ((nativeFreshAtSlot T a P.target star).embed P.target) (nativeFreshAtSlot T a P.target star).mark=star:=by
    rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hl]
  simp only [hs,ite_eq_right (ne_of_gt hi),(nativeFreshAtSlot_old_splits T a P.target star).2]

theorem native_projection_spine_source_scale {n : ℕ} {as : List PositiveMass}
    {A T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {i star : ℕ}
    (h : NativeProjectionSpine base star P) (hi : i < star) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)=
      sourceMonomialScale x W (nativeGeneratedCompleteInitial base i)*W^h.toothCount := by
  induction h with
  | base=>simp only [NativeProjectionSpine.toothCount,pow_zero,mul_one]
  | @projection T P h a hl ih=>
    rw [native_generated_add_projection_scale P a hi hl,ih]
    simp only [NativeProjectionSpine.toothCount,pow_succ,mul_assoc]

end OAI.SKFluctuations.Cavity
