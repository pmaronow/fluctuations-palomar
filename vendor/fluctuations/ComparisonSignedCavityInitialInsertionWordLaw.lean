module

public import ComparisonSignedCavityInitialInsertionWords

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators
variable {S ι : Type} [Fintype S] [Fintype ι]
set_option maxHeartbeats 28000000

private theorem initial_word_sum_attach {α : Type} (L : List α) (F : α→ℝ) :
    ((L.attach).map (fun a=>F a.val)).sum=(L.map F).sum := by
  conv_rhs=>rw [←List.attach_map_val]

private theorem initial_word_sum_map_div {α : Type} (L : List α) (F : α→ℝ) (c : ℝ) :
    ((L.map (fun a=>F a/c)).sum)=(L.map F).sum/c := by
  induction L with
  | nil=>simp only [List.map_nil,List.sum_nil,zero_div]
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih,add_div]

private theorem initial_word_sum_flatMap {α : Type} (L : List α) (F : α→List ℝ) :
    (L.flatMap F).sum=(L.map (fun a=>(F a).sum)).sum := by
  induction L with
  | nil=>rfl
  | cons a L ih=>simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

 theorem native_initial_insertion_word_exact
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (Ds : List (ℕ→S→S→ℝ)) (T : ClockTree S as) (P : T.Assignment→ℝ) :
    disorderOffDiagonalJets w φ v q x Ds T P=
      ((nativeInitialInsertionWords T Ds.length).map fun g=>g.coefficient*
        g.tree.disorderExpect w φ v q (g.test (fun e=>Ds[e.val]) P) x).sum := by
  induction Ds generalizing T with
  | nil=>simp only [disorderOffDiagonalJets,List.length_nil,nativeInitialInsertionWords,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NativeInitialInsertionWord.coefficient,
      NativeInitialInsertionWord.tree,NativeInitialInsertionWord.test,one_mul,add_zero]
  | cons D Ds ih=>
    have Hrow (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
        (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
        ((nativeInitialInsertionWords r.tree Ds.length).map fun g=>
          (NativeInitialInsertionWord.pair p hp r hr g).coefficient*
          (NativeInitialInsertionWord.pair p hp r hr g).tree.disorderExpect w φ v q
            ((NativeInitialInsertionWord.pair p hp r hr g).test (fun e=>(D::Ds)[e.val]) P) x).sum=
        p.coeff*r.coeff*(1-r.hit p.mark)*
          disorderOffDiagonalJets w φ v q x Ds r.tree (profilePairTest P D p r)/2 := by
      dsimp only [NativeInitialInsertionWord.coefficient,NativeInitialInsertionWord.tree,
        NativeInitialInsertionWord.test,List.getElem_cons_zero,List.getElem_cons_succ,Fin.val_zero,Fin.val_succ]
      rw [ih]
      calc
        _=((nativeInitialInsertionWords r.tree Ds.length).map fun g=>
          (p.coeff*r.coeff*(1-r.hit p.mark)*(g.coefficient*
            g.tree.disorderExpect w φ v q (g.test (fun e=>Ds[e.val]) (profilePairTest P D p r)) x))/2).sum:=by
          apply congrArg List.sum
          apply List.map_congr_left
          intro g _
          change (p.coeff*r.coeff*(1-r.hit p.mark)*g.coefficient/2)*
            g.tree.disorderExpect w φ v q (g.test (fun e=>Ds[e.val]) (profilePairTest P D p r)) x=_
          ring
        _= _ := by rw [initial_word_sum_map_div,List.sum_map_mul_left]
    rw [disorderOffDiagonalJets]
    simp only [List.length_cons,nativeInitialInsertionWords,List.map_flatMap,initial_word_sum_flatMap,
      List.map_map,Function.comp_def]
    simp_rw [Hrow]
    have Hinner (p : MarkedPlacement T) :
      ((p.tree.markedAttach 0).attach.map fun r=>p.coeff*r.val.coeff*(1-r.val.hit p.mark)*
        disorderOffDiagonalJets w φ v q x Ds r.val.tree (profilePairTest P D p r.val)/2).sum=
      p.coeff*((p.tree.markedAttach 0).map fun r=>r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x Ds r.tree (profilePairTest P D p r)).sum/2 := by
      rw [initial_word_sum_attach (p.tree.markedAttach 0)
        (fun r=>p.coeff*r.coeff*(1-r.hit p.mark)*
          disorderOffDiagonalJets w φ v q x Ds r.tree (profilePairTest P D p r)/2),
        initial_word_sum_map_div]
      rw [←List.sum_map_mul_left]
      apply congrArg (fun a : ℝ=>a/2)
      apply congrArg List.sum
      apply List.map_congr_left
      intro r _
      ring
    simp_rw [Hinner]
    rw [initial_word_sum_attach (T.markedAttach 0) (fun p=>
      p.coeff*((p.tree.markedAttach 0).map fun r=>r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x Ds r.tree (profilePairTest P D p r)).sum/2),
      initial_word_sum_map_div]

 theorem native_initial_insertion_word_exact_ofFn
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (k : ℕ) (D : Fin k→ℕ→S→S→ℝ) (T : ClockTree S as) (P : T.Assignment→ℝ) :
    disorderOffDiagonalJets w φ v q x (List.ofFn D) T P=
      ((nativeInitialInsertionWords T k).map fun g=>g.coefficient*
        g.tree.disorderExpect w φ v q (g.test D P) x).sum := by
  induction k generalizing T with
  | zero=>simp only [List.ofFn_zero,disorderOffDiagonalJets,nativeInitialInsertionWords,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NativeInitialInsertionWord.coefficient,
      NativeInitialInsertionWord.tree,NativeInitialInsertionWord.test,one_mul,add_zero]
  | succ k ih=>
    let Dt : Fin k→ℕ→S→S→ℝ:=fun e=>D e.succ
    have Hrow (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
        (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
        ((nativeInitialInsertionWords r.tree k).map fun g=>
          (NativeInitialInsertionWord.pair p hp r hr g).coefficient*
          (NativeInitialInsertionWord.pair p hp r hr g).tree.disorderExpect w φ v q
            ((NativeInitialInsertionWord.pair p hp r hr g).test D P) x).sum=
        p.coeff*r.coeff*(1-r.hit p.mark)*
          disorderOffDiagonalJets w φ v q x (List.ofFn Dt) r.tree (profilePairTest P (D 0) p r)/2 := by
      dsimp only [NativeInitialInsertionWord.coefficient,NativeInitialInsertionWord.tree,
        NativeInitialInsertionWord.test]
      rw [ih]
      calc
        _=((nativeInitialInsertionWords r.tree k).map fun g=>
          (p.coeff*r.coeff*(1-r.hit p.mark)*(g.coefficient*
            g.tree.disorderExpect w φ v q (g.test Dt (profilePairTest P (D 0) p r)) x))/2).sum:=by
          apply congrArg List.sum
          apply List.map_congr_left
          intro g _
          change (p.coeff*r.coeff*(1-r.hit p.mark)*g.coefficient/2)*
            g.tree.disorderExpect w φ v q (g.test Dt (profilePairTest P (D 0) p r)) x=_
          ring
        _= _ := by rw [initial_word_sum_map_div,List.sum_map_mul_left]
    rw [List.ofFn_succ,disorderOffDiagonalJets]
    simp only [nativeInitialInsertionWords,List.map_flatMap,initial_word_sum_flatMap,
      List.map_map,Function.comp_def]
    simp_rw [Hrow]
    have Hinner (p : MarkedPlacement T) :
      ((p.tree.markedAttach 0).attach.map fun r=>p.coeff*r.val.coeff*(1-r.val.hit p.mark)*
        disorderOffDiagonalJets w φ v q x (List.ofFn Dt) r.val.tree (profilePairTest P (D 0) p r.val)/2).sum=
      p.coeff*((p.tree.markedAttach 0).map fun r=>r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x (List.ofFn Dt) r.tree (profilePairTest P (D 0) p r)).sum/2 := by
      rw [initial_word_sum_attach (p.tree.markedAttach 0)
        (fun r=>p.coeff*r.coeff*(1-r.hit p.mark)*
          disorderOffDiagonalJets w φ v q x (List.ofFn Dt) r.tree (profilePairTest P (D 0) p r)/2),
        initial_word_sum_map_div]
      rw [←List.sum_map_mul_left]
      apply congrArg (fun a : ℝ=>a/2)
      apply congrArg List.sum
      apply List.map_congr_left
      intro r _
      ring
    simp_rw [Hinner]
    rw [initial_word_sum_attach (T.markedAttach 0) (fun p=>
      p.coeff*((p.tree.markedAttach 0).map fun r=>r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x (List.ofFn Dt) r.tree (profilePairTest P (D 0) p r)).sum/2),
      initial_word_sum_map_div]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}
set_option maxHeartbeats 28000000

 theorem native_initial_insertion_word_variation
    (T : ClockTree S as) (ho : MassOrdered 0 as) (k rBound : ℕ) (hT : T.leaves≤rBound) :
    ((nativeInitialInsertionWords T k).map (fun g=>|g.coefficient|)).sum≤absJetVariation rBound k := by
  induction k generalizing T rBound with
  | zero=>simp only [nativeInitialInsertionWords,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      NativeInitialInsertionWord.coefficient,abs_one,add_zero,absJetVariation,le_refl]
  | succ k ih=>
    let B:=absJetVariation (rBound+2) k
    have hB : 0≤B:=absJetVariation_nonneg _ _
    have Hrow (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
        (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
        ((nativeInitialInsertionWords r.tree k).map fun g=>
          |(NativeInitialInsertionWord.pair p hp r hr g).coefficient|).sum≤|p.coeff| *|r.coeff| *B := by
      have Hleaves : r.tree.leaves≤rBound+2:=by
        have Hp:=T.markedAttach_leaves 0 p hp
        have Hr:=p.tree.markedAttach_leaves 0 r hr
        omega
      have Htail:=ih r.tree (rBound+2) Hleaves
      have Hhit : |1-r.hit p.mark|≤1:=by
        unfold MarkedPlacement.hit
        split_ifs <;> norm_num
      have Hpoint (g : NativeInitialInsertionWord r.tree k) :
          |(NativeInitialInsertionWord.pair p hp r hr g).coefficient|≤|p.coeff| *|r.coeff| *|g.coefficient| := by
        simp only [NativeInitialInsertionWord.coefficient,abs_div,abs_mul,show |(2:ℝ)|=2 by norm_num]
        have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hhit
          (mul_nonneg (abs_nonneg p.coeff) (abs_nonneg r.coeff))) (abs_nonneg g.coefficient)
        have Hpos : 0≤|p.coeff| *|r.coeff| *|g.coefficient|:=by positivity
        nlinarith only [H,Hpos]
      apply (List.sum_le_sum (fun g _=>Hpoint g)).trans
      rw [List.sum_map_mul_left]
      exact mul_le_mul_of_nonneg_left Htail (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    simp only [nativeInitialInsertionWords,List.map_flatMap,initial_word_sum_flatMap,List.map_map,Function.comp_def]
    have Hnorm : (((T.markedAttach 0).attach.map fun p=>
        ((p.val.tree.markedAttach 0).attach.map fun r=>|p.val.coeff| *|r.val.coeff| *B).sum).sum)=
        T.pairAbsSum (fun _ _=>B):=by
      have Hin (p : MarkedPlacement T) :
          ((p.tree.markedAttach 0).attach.map fun r=>|p.coeff| *|r.val.coeff| *B).sum=
          |p.coeff| *((p.tree.markedAttach 0).map fun r=>|r.coeff| *B).sum:=by
        rw [initial_word_sum_attach (p.tree.markedAttach 0) (fun r=>|p.coeff| *|r.coeff| *B)]
        simp only [mul_assoc,List.sum_map_mul_left]
      simp_rw [Hin]
      rw [initial_word_sum_attach (T.markedAttach 0)
        (fun p=>|p.coeff| *((p.tree.markedAttach 0).map fun r=>|r.coeff| *B).sum)]
      rfl
    calc
      _≤((T.markedAttach 0).attach.map fun p=>
          ((p.val.tree.markedAttach 0).attach.map fun r=>|p.val.coeff| *|r.val.coeff| *B).sum).sum:=by
        apply List.sum_le_sum
        intro p _
        apply List.sum_le_sum
        intro r _
        exact Hrow p.val p.property r.val r.property
      _=T.pairAbsSum (fun _ _=>B):=Hnorm
      _≤absJetVariation rBound (k+1):=by
        simpa only [absJetVariation,B] using T.pairAbsSum_constant_le ho hT hB

end OAI.SKFluctuations.Hierarchy.ClockTree
