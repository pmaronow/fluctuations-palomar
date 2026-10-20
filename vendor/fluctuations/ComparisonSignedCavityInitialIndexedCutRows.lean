module

public import ComparisonSignedCavityOutsideMarkedRows
public import ComparisonSignedCavityActualGroupedClosure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Hierarchy
open scoped BigOperators
variable {S : Type}
set_option maxHeartbeats 18000000

def nativeInitialIndexedCutRows : {as : List PositiveMass}→(T : ClockTree S as)→ℕ→ℝ→List (MarkedPlacement T)
  | _,.leaf,_,a=>[MarkedPlacement.fresh .leaf a]
  | _,.step b T,0,a=>[MarkedPlacement.fresh (T.step b) a]
  | _,.step b T,i+1,a=>MarkedPlacement.fresh (T.step b) (a-b.val)::
      (nativeInitialIndexedCutRows T i b.val).map (fun p=>p.step b)
  | _,.fork T V,i,a=>MarkedPlacement.fresh (T.fork V) (-a)::
      ((nativeInitialIndexedCutRows T i a).map (fun p=>p.left V)++
       (nativeInitialIndexedCutRows V i a).map (fun p=>p.right T))

def nativeInitialRetainedPastCutRows : {as : List PositiveMass}→(T : ClockTree S as)→ℕ→ℝ→List (MarkedPlacement T)
  | _,.leaf,_,_=>[MarkedPlacement.coincide,MarkedPlacement.fresh .leaf (-1)]
  | _,.step b T,0,_=>MarkedPlacement.fresh (T.step b) (-b.val)::
      (T.markedAttach b.val).map (fun p=>p.step b)
  | _,.step b T,i+1,_=>(nativeInitialRetainedPastCutRows T i b.val).map (fun p=>p.step b)
  | _,.fork T V,i,a=>(nativeInitialRetainedPastCutRows T i a).map (fun p=>p.left V)++
      (nativeInitialRetainedPastCutRows V i a).map (fun p=>p.right T)

def nativeInitialOutsideCutResidualRows : {as : List PositiveMass}→(T : ClockTree S as)→T.Slot→ℕ→ℝ→List (MarkedPlacement T)
  | _,.leaf,_,i,a=>nativeInitialRetainedPastCutRows .leaf i a
  | _,.step b T,_,0,_=>[MarkedPlacement.fresh (T.step b) (-b.val)]
  | _,.step b T,s,i+1,_=>(nativeInitialOutsideCutResidualRows T s i b.val).map (fun p=>p.step b)
  | _,.fork T V,s,i,a=>match (s:T.Slot⊕V.Slot) with
    | Sum.inl s=>(nativeInitialOutsideCutResidualRows T s i a).map (fun p=>p.left V)++
        (nativeInitialRetainedPastCutRows V i a).map (fun p=>p.right T)
    | Sum.inr s=>(nativeInitialRetainedPastCutRows T i a).map (fun p=>p.left V)++
        (nativeInitialOutsideCutResidualRows V s i a).map (fun p=>p.right T)

def nativeInitialMarkedRowsValue {as : List PositiveMass} {T : ClockTree S as}
    (ps : List (MarkedPlacement T))
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) : ℝ :=
  (ps.map (fun p=>p.coeff*F p.tree p.restrict p.spin)).sum

theorem native_initial_retained_past_cut_exact {as : List PositiveMass}
    (T : ClockTree S as) (i : ℕ) (a : ℝ)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) :
    nativeInitialMarkedRowsValue (T.markedAttach a) F=
      nativeInitialMarkedRowsValue (nativeInitialIndexedCutRows T i a) F+
        nativeInitialMarkedRowsValue (nativeInitialRetainedPastCutRows T i a) F := by
  induction T generalizing i a with
  | leaf=>simp only [nativeInitialMarkedRowsValue,markedAttach,nativeInitialIndexedCutRows,
      nativeInitialRetainedPastCutRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      MarkedPlacement.fresh,MarkedPlacement.coincide];ring
  | step b T ih=>
    cases i with
    | zero=>simp only [nativeInitialMarkedRowsValue,markedAttach,nativeInitialIndexedCutRows,
        nativeInitialRetainedPastCutRows,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
        MarkedPlacement.fresh,List.map_nil,List.sum_nil];ring
    | succ i=>
      have H:=ih i b.val (fun V R B=>F (V.step b) R B)
      simp only [nativeInitialMarkedRowsValue,markedAttach,nativeInitialIndexedCutRows,
        nativeInitialRetainedPastCutRows,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
        MarkedPlacement.step,MarkedPlacement.fresh] at H ⊢
      linarith only [H]
  | fork T V ihT ihV=>
    have HT:=ihT i a (fun A R B=>F (A.fork V) (fun σ=>(R σ.1,σ.2)) (fun σ=>B σ.1))
    have HV:=ihV i a (fun A R B=>F (T.fork A) (fun σ=>(σ.1,R σ.2)) (fun σ=>B σ.2))
    simp only [nativeInitialMarkedRowsValue,markedAttach,nativeInitialIndexedCutRows,
      nativeInitialRetainedPastCutRows,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,MarkedPlacement.left,MarkedPlacement.right,MarkedPlacement.fresh] at HT HV ⊢
    linarith only [HT,HV]

theorem native_initial_outside_to_indexed_cut_exact {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (i : ℕ) (a : ℝ)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) :
    nativeInitialMarkedRowsValue (nativeOutsideMarkedRows T s i a) F=
      nativeInitialMarkedRowsValue (nativeInitialIndexedCutRows T i a) F+
        nativeInitialMarkedRowsValue (nativeInitialOutsideCutResidualRows T s i a) F := by
  induction T generalizing i a with
  | leaf=>exact native_initial_retained_past_cut_exact .leaf i a F
  | step b T ih=>
    cases i with
    | zero=>simp only [nativeInitialMarkedRowsValue,nativeOutsideMarkedRows,nativeInitialIndexedCutRows,
        nativeInitialOutsideCutResidualRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        MarkedPlacement.fresh];ring
    | succ i=>
      have H:=ih s i b.val (fun V R B=>F (V.step b) R B)
      simp only [nativeInitialMarkedRowsValue,nativeOutsideMarkedRows,nativeInitialIndexedCutRows,
        nativeInitialOutsideCutResidualRows,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
        MarkedPlacement.step,MarkedPlacement.fresh] at H ⊢
      linarith only [H]
  | fork T V ihT ihV=>
    cases s with
    | inl s=>
      have HT:=ihT s i a (fun A R B=>F (A.fork V) (fun σ=>(R σ.1,σ.2)) (fun σ=>B σ.1))
      have HV:=native_initial_retained_past_cut_exact V i a
        (fun A R B=>F (T.fork A) (fun σ=>(σ.1,R σ.2)) (fun σ=>B σ.2))
      simp only [nativeInitialMarkedRowsValue,nativeOutsideMarkedRows,nativeInitialIndexedCutRows,
        nativeInitialOutsideCutResidualRows,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,MarkedPlacement.left,MarkedPlacement.right,MarkedPlacement.fresh] at HT HV ⊢
      linarith only [HT,HV]
    | inr s=>
      have HT:=native_initial_retained_past_cut_exact T i a
        (fun A R B=>F (A.fork V) (fun σ=>(R σ.1,σ.2)) (fun σ=>B σ.1))
      have HV:=ihV s i a (fun A R B=>F (T.fork A) (fun σ=>(σ.1,R σ.2)) (fun σ=>B σ.2))
      simp only [nativeInitialMarkedRowsValue,nativeOutsideMarkedRows,nativeInitialIndexedCutRows,
        nativeInitialOutsideCutResidualRows,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,MarkedPlacement.left,MarkedPlacement.right,MarkedPlacement.fresh] at HT HV ⊢
      linarith only [HT,HV]

theorem native_initial_indexed_cut_variation {as : List PositiveMass}
    (T : ClockTree S as) (i : ℕ) {a : ℝ} (ho : MassOrdered a as) :
    ((nativeInitialIndexedCutRows T i a).map (fun p=>|p.coeff|)).sum≤
      2*(T.leaves:ℝ)*partitionPoint a as i-a := by
  induction T generalizing i a with
  | leaf=>simp only [nativeInitialIndexedCutRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      MarkedPlacement.fresh,leaves,partitionPoint,partitionValues,id_eq]
          rw [abs_of_nonneg ho.1]
          norm_num only [Nat.cast_one,add_zero]
          linarith
  | step b T ih=>
    cases i with
    | zero=>
      simp only [nativeInitialIndexedCutRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        MarkedPlacement.fresh,leaves,partitionPoint,partitionValues,id_eq]
      rw [abs_of_nonneg ho.1]
      have Hleaf : 1≤(T.leaves:ℝ):=by exact_mod_cast T.leaves_pos
      have H:=mul_le_mul_of_nonneg_right Hleaf ho.1
      nlinarith only [H]
    | succ i=>
      simp only [nativeInitialIndexedCutRows,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
        MarkedPlacement.fresh,MarkedPlacement.step,leaves,partitionPoint,partitionValues]
      rw [abs_of_nonpos (sub_nonpos.mpr ho.2.1)]
      have H:=ih i ho.2.2
      dsimp only [partitionPoint] at H
      linarith only [H]
  | fork T V ihT ihV=>
    simp only [nativeInitialIndexedCutRows,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,leaves,Nat.cast_add]
    rw [abs_neg,abs_of_nonneg (massOrdered_bounds ho).1]
    have HT:=ihT i ho
    have HV:=ihV i ho
    linarith only [HT,HV]

theorem native_initial_indexed_cut_eq_mass_cut {as : List PositiveMass}
    (T : ClockTree S as) (i : ℕ) (a v : ℝ) (hi : i≤as.length) (hv : v<1)
    (hpre : ∀b∈as.take i,b.val≤v) (hsuffix : ∀b∈as.drop i,v<b.val) :
    nativeInitialIndexedCutRows T i a=T.nativeCutMarkedAttach a v := by
  induction T generalizing i a with
  | leaf=>simp only [nativeInitialIndexedCutRows,nativeCutMarkedAttach,ite_eq_left hv]
  | @step b bs T ih=>
    cases i with
    | zero=>
      have hb : v<b.val:=hsuffix b (by simp)
      simp only [nativeInitialIndexedCutRows,nativeCutMarkedAttach,ite_eq_left hb]
    | succ i=>
      have hb : b.val≤v:=hpre b (by simp)
      have hp : ∀d∈bs.take i,d.val≤v:=by
        intro d hd
        exact hpre d (by simpa only [List.take_succ_cons,List.mem_cons] using Or.inr hd)
      have hs : ∀d∈bs.drop i,v<d.val:=by simpa only [List.drop_succ_cons] using hsuffix
      simp only [nativeInitialIndexedCutRows,nativeCutMarkedAttach,ite_eq_right (not_lt.mpr hb)]
      rw [ih i b.val (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hi) hp hs]
  | fork T V ihT ihV=>
    simp only [nativeInitialIndexedCutRows,nativeCutMarkedAttach]
    rw [ihT i a hi hpre hsuffix,ihV i a hi hpre hsuffix]

end OAI.SKFluctuations.Hierarchy.ClockTree
