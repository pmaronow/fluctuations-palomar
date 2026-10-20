module

public import ComparisonSignedCavitySecondLowLabeledMiddleSourceAdapter

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_second_low_endpoint_prefix_low_splits
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (a v z : T.Slot) (HAv : T.splitIndex a v<U) (HZv : T.splitIndex z v<U)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (Hp : U ≤ p.tree.splitIndex (p.embed a) p.mark)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (Hr : U ≤ r.tree.splitIndex (r.embed (p.embed z)) r.mark) :
    let D:=((NativeSecondLowLabeledDiagram.base T a).observe 0 p).observe 3 r
    D.tree.splitIndex (D.marks 0) (D.embed v)<U ∧
      D.tree.splitIndex (D.marks 3) (D.embed v)<U := by
  have HF:=native_second_low_high_mark_low_split T U v a p hp Hp
    (by simpa only [T.splitIndex_symm v a] using HAv)
  have HD:=native_second_low_high_mark_low_split p.tree U (p.embed v) (p.embed z) r hr Hr
    (by rw [(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm v z];exact HZv)
  simp only [NativeSecondLowLabeledDiagram.observe,NativeSecondLowLabeledDiagram.base,
    Fin.isValue,show (0:Fin 4)≠3 by decide,↓reduceIte,id_eq]
  constructor
  · rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,p.tree.splitIndex_symm,HF,T.splitIndex_symm v a]
    exact HAv
  · rw [r.tree.splitIndex_symm,HD,(T.markedAttach_embed_preserves 0 p hp).2,T.splitIndex_symm v z]
    exact HZv

theorem native_second_low_endpoint_labeled_value_orientation_independent
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU v)
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU v) (j : Fin 8) :
    ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a) (![a,v,v,z]) (U-1)
      [0,3,1,2]).map (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z j w.2)).sum=
    ((nativeSecondLowLabeledHighWord (NativeSecondLowLabeledDiagram.base T a) (![a,v,v,z]) (U-1)
      [0,3,1,2]).map (fun w=>w.1*nativeSecondLowLabeledGammaValue q U b h K P a z 0 w.2)).sum := by
  rw [native_second_low_labeled_high_word_eval_fold,native_second_low_labeled_high_word_eval_fold]
  change ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*
    ((nativeHighMarkedRows p.tree (p.embed z) (U-1) 0).map (fun r=>r.coeff*
      nativeSecondLowLabeledHighEvalFold (((NativeSecondLowLabeledDiagram.base T a).observe 0 p).observe 3 r)
        (![a,v,v,z]) (U-1) (nativeSecondLowLabeledGammaValue q U b h K P a z j) [1,2])).sum)).sum=
    ((nativeHighMarkedRows T a (U-1) 0).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed z) (U-1) 0).map (fun r=>r.coeff*
        nativeSecondLowLabeledHighEvalFold (((NativeSecondLowLabeledDiagram.base T a).observe 0 p).observe 3 r)
          (![a,v,v,z]) (U-1) (nativeSecondLowLabeledGammaValue q U b h K P a z 0) [1,2])).sum)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  obtain ⟨hp',Hp⟩:=(mem_nativeHighMarkedRows T a (U-1) 0 p).mp hp
  obtain ⟨hr',Hr⟩:=(mem_nativeHighMarkedRows p.tree (p.embed z) (U-1) 0 r).mp hr
  have Hlow:=native_second_low_endpoint_prefix_low_splits T U a v z
    (cut_block_ne_split_lt T U hU a v hAv) (cut_block_ne_split_lt T U hU z v hZv)
    p hp' (by omega) r hr' (by omega)
  exact native_second_low_labeled_inner_middle_value_orientation_independent q U b h K ho hU0 P a v z j
    (((NativeSecondLowLabeledDiagram.base T a).observe 0 p).observe 3 r) Hlow.1 Hlow.2

theorem native_second_low_occupied_gamma_ledger_eq_canonical_value
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (j : Fin 8) (B : T.CutBlock U hU)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hAz : T.cutBlock U hU a≠T.cutBlock U hU z) :
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B=
      nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z 0 B := by
  rw [native_second_low_occupied_gamma_ledger_eq_endpoint_labeled_word n q U b h K T ho hU0 hU P a z j B hAv hZv hAz,
    native_second_low_occupied_gamma_ledger_eq_endpoint_labeled_word n q U b h K T ho hU0 hU P a z 0 B hAv hZv hAz]
  exact congrArg (fun x : ℝ=>x/4) (native_second_low_endpoint_labeled_value_orientation_independent
    n q U b h K T ho hU0 hU P a (nativeSecondLowOccupiedBlockRepresentative T U hU B) z hAv hZv j)

theorem native_second_low_eight_occupied_gamma_half_eq_canonical_raw_source
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (B : T.CutBlock U hU)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hAz : T.cutBlock U hU a≠T.cutBlock U hU z) :
    (∑j : Fin 8,nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B/2)=
      nativeSecondLowFourHighSum T
        (nativeSecondLowChronologicalTargets 0 a (nativeSecondLowOccupiedBlockRepresentative T U hU B) z) (U-1)
        (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z 0 p r s t) := by
  calc
    _=∑_j : Fin 8,nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z 0 B/2:=by
      apply Finset.sum_congr rfl
      intro j _
      rw [native_second_low_occupied_gamma_ledger_eq_canonical_value n q U b h K T ho hU0 hU P a z j B hAv hZv hAz]
    _=4*nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z 0 B:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _=nativeSecondLowFourHighSum T
        (nativeSecondLowChronologicalTargets 0 a (nativeSecondLowOccupiedBlockRepresentative T U hU B) z) (U-1)
        (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K P a z 0 p r s t):=by
      rw [native_second_low_occupied_gamma_path_ledger_eq_high_rows n q U b h K T ho hU0 hU P a z 0 B]
      unfold nativeSecondLowOccupiedGammaHighPathLedger
      ring

theorem native_second_low_constant_eight_occupied_gamma_half_eq_canonical_raw_source
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (a z : T.Slot) (B : T.CutBlock U hU)
    (hAv : T.cutBlock U hU a≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hZv : T.cutBlock U hU z≠T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B))
    (hAz : T.cutBlock U hU a≠T.cutBlock U hU z) :
    (∑j : Fin 8,nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU (fun _=>1) a z j B/2)=
      nativeSecondLowFourHighSum T
        (nativeSecondLowChronologicalTargets 0 a (nativeSecondLowOccupiedBlockRepresentative T U hU B) z) (U-1)
        (fun p r s t=>nativeSecondLowGammaWordValue n q U b h K (fun _=>1) a z 0 p r s t) :=
  native_second_low_eight_occupied_gamma_half_eq_canonical_raw_source n q U b h K T ho hU0 hU
    (fun _=>1) a z B hAv hZv hAz

end OAI.SKFluctuations.Cavity
