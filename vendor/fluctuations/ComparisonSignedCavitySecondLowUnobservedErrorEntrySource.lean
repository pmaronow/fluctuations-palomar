module

public import ComparisonSignedCavitySecondLowOriginalErrorWordAllocation
public import ComparisonSignedCavitySecondLowInitialEntrySource

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
attribute [local instance] Classical.propDecidable

 theorem native_second_low_first_error_word_zero_first_high
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (H : U≤r.tree.splitIndex (r.embed p.mark) r.mark) :
    nativeSecondLowFirstErrorWord n q U b h K P a z p r s t=0 := by
  have Hfc : t.tree.splitIndex (t.embed (s.embed (r.embed p.mark)))
      (t.embed (s.embed r.mark))=r.tree.splitIndex (r.embed p.mark) r.mark:=by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  unfold nativeSecondLowFirstErrorWord ClockTree.disorderExpect
  simp only [nativeOldInitialRowProduct,nativeRestRowKernel,Hfc,nativeSmallCutOldErrorRestKernel,
    not_lt.mpr H,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]

 theorem native_second_low_second_error_word_zero_first_high
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (H : U≤r.tree.splitIndex (r.embed p.mark) r.mark) :
    nativeSecondLowSecondErrorWord n q U b h K P a z p r s t=0 := by
  have Hfc : t.tree.splitIndex (t.embed (s.embed (r.embed p.mark)))
      (t.embed (s.embed r.mark))=r.tree.splitIndex (r.embed p.mark) r.mark:=by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  unfold nativeSecondLowSecondErrorWord ClockTree.disorderExpect
  simp only [nativeOldInitialRowProduct,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    nativeRestRowKernel]
  simp only [nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false,ite_true]
  simp only [nativeSmallCutMovingRestKernel,Hfc,not_lt.mpr H,ite_false,zero_mul,mul_zero,
    Finset.sum_const_zero]

 theorem native_second_low_first_error_word_zero_second_high
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (H : U≤t.tree.splitIndex (t.embed s.mark) t.mark) :
    nativeSecondLowFirstErrorWord n q U b h K P a z p r s t=0 := by
  unfold nativeSecondLowFirstErrorWord ClockTree.disorderExpect
  simp only [nativeOldInitialRowProduct,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    nativeRestRowKernel]
  simp only [nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false,ite_true]
  simp only [nativeSmallCutMovingRestKernel,not_lt.mpr H,ite_false,zero_mul,mul_zero,
    Finset.sum_const_zero]

 theorem native_second_low_second_error_word_zero_second_high
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (H : U≤t.tree.splitIndex (t.embed s.mark) t.mark) :
    nativeSecondLowSecondErrorWord n q U b h K P a z p r s t=0 := by
  unfold nativeSecondLowSecondErrorWord ClockTree.disorderExpect
  simp only [nativeOldInitialRowProduct,nativeRestRowKernel,nativeSmallCutOldErrorRestKernel,
    not_lt.mpr H,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]

 def nativeSecondLowErrorWord (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (firstError : Bool)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  if firstError then nativeSecondLowFirstErrorWord n q U b h K P a z p r s t
    else nativeSecondLowSecondErrorWord n q U b h K P a z p r s t

 theorem native_second_low_word_path_second_entry_first_mark_HIGH
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (hU : U≤as.length) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (j : Fin 8) (Hpath : nativeSecondLowWordPath U hU a z p r s t j)
    (Hsecond : nativeSecondLowFirstMiddleIsFirst j=false) :
    U≤p.tree.splitIndex (p.embed (if j.val<4 then a else z)) p.mark := by
  have HB : t.tree.cutBlock U hU (t.embed (s.embed (r.embed (p.embed
      (if j.val<4 then a else z)))))=
      t.tree.cutBlock U hU (t.embed (s.embed (r.embed p.mark))) := by
    fin_cases j
    all_goals simp_all [nativeSecondLowFirstMiddleIsFirst,nativeSecondLowWordPath,
      nativeSecondLowBlockPath]
  have HI:=(t.tree.cutBlock_eq_iff U hU _ _).mp HB
  rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
    (r.tree.markedAttach_embed_preserves 0 s hs).2,
    (p.tree.markedAttach_embed_preserves 0 r hr).2] at HI
  exact HI

 theorem native_second_low_word_path_second_entry_first_mark_HIGH_row
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (a z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (j : Fin 8) (Hpath : nativeSecondLowWordPath U hU a z p r s t j)
    (Hsecond : nativeSecondLowFirstMiddleIsFirst j=false) :
    p∈nativeHighMarkedRows T (if j.val<4 then a else z) (U-1) 0 := by
  rw [mem_nativeHighMarkedRows]
  refine ⟨hp,?_⟩
  have HI:=native_second_low_word_path_second_entry_first_mark_HIGH T U hU a z
    p r hr s hs t ht j Hpath Hsecond
  omega

 def nativeSecondLowErrorCut {S : Type} {as : List PositiveMass} {T : ClockTree S as}
    (firstError : Bool) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℕ :=
  if firstError then r.tree.splitIndex (r.embed p.mark) r.mark else t.tree.splitIndex (t.embed s.mark) t.mark

 theorem native_second_low_error_word_zero_first_high
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (firstError : Bool)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (H : U≤r.tree.splitIndex (r.embed p.mark) r.mark) :
    nativeSecondLowErrorWord n q U b h K P a z firstError p r s t=0 := by
  cases firstError
  · exact native_second_low_second_error_word_zero_first_high n q U b h K P a z p r s hs t ht H
  · exact native_second_low_first_error_word_zero_first_high n q U b h K P a z p r s hs t ht H

 theorem native_second_low_error_word_zero_second_high
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (firstError : Bool)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (H : U≤t.tree.splitIndex (t.embed s.mark) t.mark) :
    nativeSecondLowErrorWord n q U b h K P a z firstError p r s t=0 := by
  cases firstError
  · exact native_second_low_second_error_word_zero_second_high n q U b h K P a z p r s t H
  · exact native_second_low_first_error_word_zero_second_high n q U b h K P a z p r s t H

 def nativeSecondLowUnobservedErrorWord (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (j : Fin 8) (firstError : Bool) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  if nativeSecondLowWordPath U hU a z p r s t j ∧ ¬nativeSecondLowWordObserved U p r s t j
    then nativeSecondLowErrorWord n q U b h K P a z firstError p r s t else 0

 theorem native_second_low_unobserved_error_word_zero_outside_entry
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Hentry : ¬(if nativeSecondLowFirstMiddleIsFirst j then p∈nativeSecondLowUnobservedEntryRows T U 0
      else r∈nativeSecondLowUnobservedEntryRows p.tree U 0)) :
    nativeSecondLowUnobservedErrorWord n q U b h K hU P a z j firstError p r s t=0 := by
  unfold nativeSecondLowUnobservedErrorWord
  split_ifs with H
  · rcases H with ⟨Hpath,Hunobs⟩
    by_contra HV
    have Hlow : r.tree.splitIndex (r.embed p.mark) r.mark<U:=by
      by_contra HH
      exact HV (native_second_low_error_word_zero_first_high n q U b h K P a z firstError p r s hs t ht (not_lt.mp HH))
    exact Hentry (native_second_low_unobserved_source_entry T U hU a z p hp r hr s hs t ht j Hpath Hunobs Hlow)
  · rfl

 def nativeSecondLowUnobservedErrorClassLedger (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (j : Fin 8) (firstError : Bool) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree
    (nativeSecondLowUnobservedErrorWord n q U b h K hU P a z j firstError p r))

 theorem native_second_low_original_unobserved_class_eq_error_classes
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j false=
      nativeSecondLowUnobservedErrorClassLedger n q U b h K T hU P a z j true+
      nativeSecondLowUnobservedErrorClassLedger n q U b h K T hU P a z j false := by
  unfold nativeSecondLowClassLedger nativeSecondLowUnobservedErrorClassLedger
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro p hp r hr
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro s hs t ht
  simp only [nativeSecondLowUnobservedErrorWord,nativeSecondLowErrorWord,
    Bool.false_eq_true,iff_false,ite_true,ite_false]
  by_cases HH : nativeSecondLowWordPath U hU a z p r s t j ∧
      ¬nativeSecondLowWordObserved U p r s t j
  · simp only [HH]
    exact native_second_low_original_word_eq_error_allocations n q U b h K T ho P a z
      p r s hs t ht
  · simp only [HH,ite_false,add_zero]

 theorem native_second_low_unobserved_error_class_eq_entry
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool) :
    nativeSecondLowUnobservedErrorClassLedger n q U b h K T hU P a z j firstError=
      nativeSecondLowEntryFourAverage T U (nativeSecondLowFirstMiddleIsFirst j)
        (nativeSecondLowUnobservedErrorWord n q U b h K hU P a z j firstError) := by
  unfold nativeSecondLowUnobservedErrorClassLedger
  apply native_second_low_four_average_eq_entry_four_average
  intro p hp r hr s hs t ht Hentry
  exact native_second_low_unobserved_error_word_zero_outside_entry n q U b h K T hU P a z
    j firstError p hp r hr s hs t ht Hentry

 def nativeSecondLowFixedErrorUnobservedWord (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (fixed U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (j : Fin 8) (firstError : Bool) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  if nativeSecondLowErrorCut firstError p r s t=fixed then
    nativeSecondLowUnobservedErrorWord n q U b h K hU P a z j firstError p r s t else 0

 def nativeSecondLowFixedErrorUnobservedClassLedger (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (fixed U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (j : Fin 8) (firstError : Bool) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree
    (nativeSecondLowFixedErrorUnobservedWord n q fixed U b h K hU P a z j firstError p r))

 theorem native_second_low_fixed_error_unobserved_class_eq_entry
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (fixed U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool) :
    nativeSecondLowFixedErrorUnobservedClassLedger n q fixed U b h K T hU P a z j firstError=
      nativeSecondLowEntryFourAverage T U (nativeSecondLowFirstMiddleIsFirst j)
        (nativeSecondLowFixedErrorUnobservedWord n q fixed U b h K hU P a z j firstError) := by
  unfold nativeSecondLowFixedErrorUnobservedClassLedger
  apply native_second_low_four_average_eq_entry_four_average
  intro p hp r hr s hs t ht Hentry
  unfold nativeSecondLowFixedErrorUnobservedWord
  split_ifs
  · exact native_second_low_unobserved_error_word_zero_outside_entry n q U b h K T hU P a z j firstError
      p hp r hr s hs t ht Hentry
  · rfl

end OAI.SKFluctuations.Cavity
