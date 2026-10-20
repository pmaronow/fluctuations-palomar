module

public import ComparisonSignedCavitySecondLowLabeledRestSource
public import ComparisonSignedCavitySecondLowOccupiedGammaHighRows

@[expose] public section

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def nativeSecondLowLabeledHighEvalFold (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) (F : NativeSecondLowLabeledDiagram T→ℝ) : List (Fin 4)→ℝ
  | []=>F D
  | i::is=>((nativeHighMarkedRows D.tree (D.embed (targets i)) high 0).map
      (fun p=>p.coeff*nativeSecondLowLabeledHighEvalFold (D.observe i p) targets high F is)).sum

private theorem labeled_word_sum_flatMap {α : Type} (L : List α) (F : α→List ℝ) :
    (L.flatMap F).sum=(L.map (fun a=>(F a).sum)).sum := by
  induction L with
  | nil=>rfl
  | cons a L ih=>simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem native_second_low_labeled_high_word_eval_fold (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) (F : NativeSecondLowLabeledDiagram T→ℝ) (is : List (Fin 4)) :
    ((nativeSecondLowLabeledHighWord D targets high is).map (fun z=>z.1*F z.2)).sum=
      nativeSecondLowLabeledHighEvalFold D targets high F is := by
  induction is generalizing D with
  | nil=>simp only [nativeSecondLowLabeledHighWord,nativeSecondLowLabeledHighEvalFold,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  | cons i is ih=>
    simp only [nativeSecondLowLabeledHighWord,nativeSecondLowLabeledHighRows,
      List.map_flatMap,labeled_word_sum_flatMap,List.map_map,Function.comp_def,mul_assoc,
      List.sum_map_mul_left,ih,nativeSecondLowLabeledHighEvalFold]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
attribute [local instance] Classical.propDecidable

theorem native_second_low_labeled_high_word_four_base_eval {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (a : T.Slot) (targets : Fin 4→T.Slot) (high : ℕ)
    (I : Fin 4→Fin 4) (F : NativeSecondLowLabeledDiagram T→ℝ) :
    ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a) targets high
      [I 0,I 1,I 2,I 3]).map (fun z=>z.1*F z.2)).sum=
      nativeSecondLowFourHighSum T (fun k=>targets (I k)) high
        (fun p r s t=>F (((((NativeSecondLowLabeledDiagram.base T a).observe (I 0) p).observe (I 1) r).observe (I 2) s).observe (I 3) t)) := by
  rw [native_second_low_labeled_high_word_eval_fold]
  rfl

theorem native_second_low_four_high_gamma_sum_eq_labeled_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (high : ℕ)
    (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) (j : Fin 8) :
    nativeSecondLowFourHighSum T (nativeSecondLowChronologicalTargets j a v z) high
      (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z j p r s t)=
      ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a) (![a,v,v,z]) high
        (nativeSecondLowOriginalLabelOrder j)).map
        (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum := by
  rw [native_second_low_original_label_order_eq_vector,native_second_low_labeled_high_word_four_base_eval]
  rw [←native_second_low_chronological_targets_eq_semantic_targets j a v z]
  apply native_second_low_four_high_sum_congr
  intro p _hp r _hr s hs t ht
  exact native_second_low_gamma_word_eq_labeled_gamma_value n q U b h K T P a z j p r
    s ((mem_nativeHighMarkedRows r.tree (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 2)))
      high 0 s).mp hs).1
    t ((mem_nativeHighMarkedRows s.tree (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z 3))))
      high 0 t).mp ht).1

theorem native_second_low_occupied_gamma_high_ledger_eq_original_labeled_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU) :
    nativeSecondLowOccupiedGammaHighPathLedger n q U b h K T hU P a z j B=
      ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a)
        (![a,nativeSecondLowOccupiedBlockRepresentative T U hU B,nativeSecondLowOccupiedBlockRepresentative T U hU B,z])
        (U-1) (nativeSecondLowOriginalLabelOrder j)).map
        (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum/4 := by
  unfold nativeSecondLowOccupiedGammaHighPathLedger
  rw [native_second_low_four_high_gamma_sum_eq_labeled_word]

theorem native_second_low_occupied_gamma_ledger_eq_original_labeled_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU) :
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B=
      ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a)
        (![a,nativeSecondLowOccupiedBlockRepresentative T U hU B,nativeSecondLowOccupiedBlockRepresentative T U hU B,z])
        (U-1) (nativeSecondLowOriginalLabelOrder j)).map
        (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum/4 := by
  rw [native_second_low_occupied_gamma_path_ledger_eq_high_rows n q U b h K T ho hU0 hU P a z j B,
    native_second_low_occupied_gamma_high_ledger_eq_original_labeled_word]

theorem native_second_low_labeled_gamma_word_value_eq_endpoint_order
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU0 : 0<U) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU v)
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU v)
    (hAz : T.cutBlock U hU a≠T.cutBlock U hU z) (j : Fin 8) :
    ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a) (![a,v,v,z]) (U-1)
      (nativeSecondLowOriginalLabelOrder j)).map
      (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum=
      ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a) (![a,v,v,z]) (U-1)
        [0,3,1,2]).map (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum := by
  have HAv : T.splitIndex a v≤U-1:=by
    have H:=cut_block_ne_split_lt T U hU a v hAv
    omega
  have HZv : T.splitIndex z v≤U-1:=by
    have H:=cut_block_ne_split_lt T U hU z v hZv
    omega
  have HAz : T.splitIndex a z≤U-1:=by
    have H:=cut_block_ne_split_lt T U hU a z hAz
    omega
  have H:=native_second_low_eight_labeled_endpoint_routing (NativeSecondLowLabeledDiagram.base T a)
    (NativeSecondLowLabeledDiagram.base_preserves a) (![a,v,v,z]) (U-1) rfl HAv HZv HAz j
  exact (H.map (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum_eq

theorem native_second_low_occupied_gamma_ledger_eq_endpoint_labeled_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hAz : T.cutBlock U hU a≠T.cutBlock U hU z) :
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B=
      ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a)
        (![a,nativeSecondLowOccupiedBlockRepresentative T U hU B,nativeSecondLowOccupiedBlockRepresentative T U hU B,z])
        (U-1) [0,3,1,2]).map
        (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum/4 := by
  rw [native_second_low_occupied_gamma_ledger_eq_original_labeled_word n q U b h K T ho hU0 hU P a z j B,
    native_second_low_labeled_gamma_word_value_eq_endpoint_order n q U b h K T hU0 hU P a
      (nativeSecondLowOccupiedBlockRepresentative T U hU B) z hAv hZv hAz j]

theorem native_second_low_constant_occupied_gamma_ledger_eq_endpoint_labeled_word
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hAz : T.cutBlock U hU a≠T.cutBlock U hU z) :
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU (fun _=>1) a z j B=
      ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a)
        (![a,nativeSecondLowOccupiedBlockRepresentative T U hU B,nativeSecondLowOccupiedBlockRepresentative T U hU B,z])
        (U-1) [0,3,1,2]).map
        (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K (fun _=>1) a z j w.2)).sum/4 :=
  native_second_low_occupied_gamma_ledger_eq_endpoint_labeled_word n q U b h K T ho hU0 hU
    (fun _=>1) a z j B hAv hZv hAz

end OAI.SKFluctuations.Cavity
