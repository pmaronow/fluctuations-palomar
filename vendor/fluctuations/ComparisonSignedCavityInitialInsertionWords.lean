module

public import ComparisonSignedCavityInitialAtomicPairJetLaw
public import ComparisonSignedCavityCanonicalMarkedTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open OAI.SKFluctuations.Cavity
open scoped BigOperators
variable {S : Type} {as : List PositiveMass}
set_option maxHeartbeats 28000000

inductive NativeInitialInsertionWord : (T : ClockTree S as)→ℕ→Type where
  | done (T : ClockTree S as) : NativeInitialInsertionWord T 0
  | pair {T : ClockTree S as} {k : ℕ}
      (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
      (tail : NativeInitialInsertionWord r.tree k) : NativeInitialInsertionWord T (k+1)

namespace NativeInitialInsertionWord

 def tree : {T : ClockTree S as}→{k : ℕ}→NativeInitialInsertionWord T k→ClockTree S as
  | _,_,.done T=>T
  | _,_,.pair _ _ _ _ tail=>tail.tree

 def coefficient : {T : ClockTree S as}→{k : ℕ}→NativeInitialInsertionWord T k→ℝ
  | _,_,.done _=>1
  | _,_,.pair p _ r _ tail=>p.coeff*r.coeff*(1-r.hit p.mark)*tail.coefficient/2

 def restrict : {T : ClockTree S as}→{k : ℕ}→(g : NativeInitialInsertionWord T k)→ g.tree.Assignment→T.Assignment
  | _,_,.done _,σ=>σ
  | _,_,.pair p _ r _ tail,σ=>p.restrict (r.restrict (tail.restrict σ))

 def embed : {T : ClockTree S as}→{k : ℕ}→(g : NativeInitialInsertionWord T k)→T.Slot→ g.tree.Slot
  | _,_,.done _,s=>s
  | _,_,.pair p _ r _ tail,s=>tail.embed (r.embed (p.embed s))

 def pairSlots : {T : ClockTree S as}→{k : ℕ}→(g : NativeInitialInsertionWord T k)→Fin k→ g.tree.Slot×g.tree.Slot
  | _,_,.done _,e=>Fin.elim0 e
  | _,_,.pair p _ r _ tail,e=>Fin.cases (tail.embed (r.embed p.mark),tail.embed r.mark) tail.pairSlots e

 theorem embed_preserves {T : ClockTree S as} {k : ℕ} (g : NativeInitialInsertionWord T k) :
    Function.Injective g.embed ∧ ∀s t,g.tree.splitIndex (g.embed s) (g.embed t)=T.splitIndex s t := by
  induction g with
  | done T=>exact ⟨Function.injective_id,fun _ _=>rfl⟩
  | @pair T k p hp r hr tail ih=>
    have Hp:=T.markedAttach_embed_preserves 0 p hp
    have Hr:=p.tree.markedAttach_embed_preserves 0 r hr
    refine ⟨?_,fun s t=>(ih.2 _ _).trans ((Hr.2 _ _).trans (Hp.2 _ _))⟩
    intro s t H
    exact Hp.1 (Hr.1 (ih.1 H))

 theorem restrict_at {T : ClockTree S as} {k : ℕ} (g : NativeInitialInsertionWord T k)
    (σ : g.tree.Assignment) (s : T.Slot) : T.atSlot (g.restrict σ) s=g.tree.atSlot σ (g.embed s) := by
  induction g with
  | done T=>rfl
  | @pair T k p hp r hr tail ih=>
    exact (p.restrict_at _ s).trans ((r.restrict_at _ (p.embed s)).trans (ih _ _))

 theorem leaves_le {T : ClockTree S as} {k : ℕ} (g : NativeInitialInsertionWord T k) :
    g.tree.leaves≤T.leaves+2*k := by
  induction g with
  | done T=>simp only [tree,Nat.mul_zero,Nat.add_zero,le_refl]
  | @pair T k p hp r hr tail ih=>
    have Hp:=T.markedAttach_leaves 0 p hp
    have Hr:=p.tree.markedAttach_leaves 0 r hr
    dsimp only [tree]
    omega

 theorem pair_distinct_of_coefficient_ne_zero {T : ClockTree S as} {k : ℕ}
    (g : NativeInitialInsertionWord T k) (hg : g.coefficient≠0) :
    ∀e,(g.pairSlots e).1≠(g.pairSlots e).2 := by
  induction g with
  | done T=>intro e;exact Fin.elim0 e
  | @pair T k p hp r hr tail ih=>
    have Htail : tail.coefficient≠0:=by
      intro H
      apply hg
      simp only [coefficient,H,mul_zero,zero_div]
    have Hmark : r.mark≠r.embed p.mark:=by
      intro H
      apply hg
      simp only [coefficient,MarkedPlacement.hit,H,ite_true,sub_self,mul_zero,zero_mul,zero_div]
    intro e
    refine Fin.cases ?_ (ih Htail) e
    exact fun H=>Hmark ((tail.embed_preserves.1 H).symm)

 def test :
    {T : ClockTree S as}→{k : ℕ}→(g : NativeInitialInsertionWord T k)→
    (Fin k→ℕ→S→S→ℝ)→(T.Assignment→ℝ)→ g.tree.Assignment→ℝ
  | _,_,.done _,_,P=>P
  | _,_,.pair p _ r _ tail,D,P=>tail.test (fun e=>D e.succ) (profilePairTest P (D 0) p r)

 theorem test_eq_joint_product
    {T : ClockTree S as} {k : ℕ} (g : NativeInitialInsertionWord T k)
    (D : Fin k→ℕ→S→S→ℝ) (P : T.Assignment→ℝ) (σ : g.tree.Assignment) :
    g.test D P σ=P (g.restrict σ)*
      (∏e,D e (g.tree.splitIndex (g.pairSlots e).1 (g.pairSlots e).2)
        (g.tree.atSlot σ (g.pairSlots e).1) (g.tree.atSlot σ (g.pairSlots e).2)) := by
  induction g with
  | done T=>simp only [test,restrict,Fin.prod_univ_zero,mul_one]
  | @pair T k p hp r hr tail ih=>
    dsimp only [tree] at σ ⊢
    rw [test,ih]
    simp only [Fin.prod_univ_succ]
    have Hzero : ((NativeInitialInsertionWord.pair p hp r hr tail).pairSlots 0)=
        (tail.embed (r.embed p.mark),tail.embed r.mark):=rfl
    have Hsucc (e : Fin k) : ((NativeInitialInsertionWord.pair p hp r hr tail).pairSlots e.succ)=tail.pairSlots e:=rfl
    simp only [Hzero,Hsucc]
    simp only [profilePairTest,restrict,tail.embed_preserves.2,←tail.restrict_at,p.spin_at,r.spin_at,r.restrict_at]
    ring

end NativeInitialInsertionWord

 def nativeInitialInsertionWords : (T : ClockTree S as)→(k : ℕ)→List (NativeInitialInsertionWord T k)
  | T,0=>[.done T]
  | T,k+1=>(T.markedAttach 0).attach.flatMap fun p=>
      (p.val.tree.markedAttach 0).attach.flatMap fun r=>
        (nativeInitialInsertionWords r.val.tree k).map (NativeInitialInsertionWord.pair p.val p.property r.val r.property)

end OAI.SKFluctuations.Hierarchy.ClockTree
