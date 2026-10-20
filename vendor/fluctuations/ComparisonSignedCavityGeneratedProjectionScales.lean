module

public import ComparisonSignedCavityGeneratedCompleteShape
public import ComparisonSignedCavitySavedRowPolynomialDecay

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_edge_list_source_scale {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (es : List (T.Slot×T.Slot)) (i : ℕ) (x W : ℝ) :
    sourceMonomialScale x W (Finset.univ.filter (fun e : Fin es.length=>
      T.splitIndex (es.get e).1 (es.get e).2=i))=
      (es.map (fun e=>if T.splitIndex e.1 e.2=i then x else W)).prod := by
  rw [←source_factor_scale_product,←List.prod_ofFn]
  conv_rhs => rw [←List.ofFn_get es,List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext e
  simp only [sourceFactorScale,Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply]

theorem native_generated_projection_source_scale {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (hi : i<star) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)=
      sourceMonomialScale x W (nativeGeneratedExteriorInitial P i)*W^P.teeth.length*
        (P.incoming.map (fun c=>if T.splitIndex P.target c=i then x else W)).prod := by
  rw [nativeGeneratedCompleteInitial,native_edge_list_source_scale,
    nativeGeneratedExteriorInitial,native_edge_list_source_scale]
  simp only [NativeGeneratedTest.edges,List.map_append,List.prod_append,List.map_map,Function.comp_def]
  have hTeeth : (P.teeth.map (fun c=>if T.splitIndex P.target c=i then x else W)).prod=W^P.teeth.length := by
    have H : P.teeth.map (fun c=>if T.splitIndex P.target c=i then x else W)=P.teeth.map (fun _=>W) := by
      apply List.map_congr_left
      intro c hc
      rw [hP.teeth_star c hc,ite_eq_right (ne_of_gt hi)]
    rw [H,List.map_const',List.prod_replicate]
  rw [hTeeth]

theorem native_generated_reset_incoming_i_source_scale {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (hi : i<star) (ht : P.teeth=[])
    (e : T.Slot) (hIn : P.incoming=[e]) (he : T.splitIndex P.target e=i) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)=
      sourceMonomialScale x W (nativeGeneratedExteriorInitial P i)*x := by
  rw [native_generated_projection_source_scale P hP hi]
  simp only [ht,List.length_nil,pow_zero,mul_one,hIn,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,he,ite_true]

theorem native_generated_reset_incoming_star_source_scale {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (hi : i<star) (ht : P.teeth=[])
    (e : T.Slot) (hIn : P.incoming=[e]) (he : T.splitIndex P.target e=star) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)=
      sourceMonomialScale x W (nativeGeneratedExteriorInitial P i)*W := by
  rw [native_generated_projection_source_scale P hP hi]
  simp only [ht,List.length_nil,pow_zero,mul_one,hIn,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,he,ite_eq_right (ne_of_gt hi)]

theorem native_generated_reset_no_incoming_source_scale {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (hi : i<star) (ht : P.teeth=[])
    (hIn : P.incoming=[]) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)=
      sourceMonomialScale x W (nativeGeneratedExteriorInitial P i) := by
  rw [native_generated_projection_source_scale P hP hi]
  simp only [ht,List.length_nil,pow_zero,mul_one,hIn,List.map_nil,List.prod_nil]

theorem native_saved_incoming_product_normalize (d : ℕ) (x W s v H : ℝ) (hs : s≠0) :
    savedProjectedScale x W v*savedWeightedExteriorScale x W v s*H*W^d=
      nativeSavedIncomingScale x W s v*(H*s*W^d) := by
  unfold nativeSavedIncomingScale
  field_simp

theorem native_saved_power_product_normalize (d : ℕ) (hd : 0<d) (x W v A : ℝ)
    (hW : 0<W) (hv : 0<v) :
    (savedProjectedScale x W v)^2*A*W^(d-1)=
      nativeSavedIncomingScale x W W v*(A*W^d) := by
  rw [native_saved_power_scale_eq hW hv]
  have H : W^d=W^(d-1)*W := by
    rw [←pow_succ,Nat.sub_add_cancel (show 1≤d by omega)]
  rw [H]
  field_simp

end OAI.SKFluctuations.Cavity
