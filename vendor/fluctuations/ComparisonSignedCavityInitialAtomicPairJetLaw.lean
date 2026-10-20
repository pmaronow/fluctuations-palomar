module

public import ComparisonSignedCavityInitialAtomicCutLaw
public import ComparisonSignedCavityTransientLowWordLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open OAI.SKFluctuations.Cavity
open scoped BigOperators
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
set_option maxHeartbeats 26000000

 omit [Nonempty S] [Nonempty ι] in
 theorem native_initial_offDiagonalJets_zero_test
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (Ks : List (ℕ→S→S→ℝ)) (T : ClockTree S as) :
    disorderOffDiagonalJets w φ v q x Ks T (fun _=>0)=0 := by
  induction Ks generalizing T with
  | nil=>simp only [disorderOffDiagonalJets,disorderExpect,mul_zero,Finset.sum_const_zero]
  | cons K Ks ih=>
    have Htest (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
        profilePairTest (fun _=>0) K p r=(fun _=>0):=by
      funext σ
      simp only [profilePairTest,zero_mul]
    simp only [disorderOffDiagonalJets,Htest,ih,mul_zero]
    simp

 def nativeInitialAtomicPairJetPayload
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (i : ℕ) (A : ℕ→S→S→ℝ) (Ks : List (ℕ→S→S→ℝ))
    {T : ClockTree S as} (P : T.Assignment→ℝ) (p : MarkedPlacement T)
    (V : ClockTree S as) (R : V.Assignment→p.tree.Assignment) (B : V.Assignment→S) : ℝ :=
  disorderOffDiagonalJets w φ v q x Ks V
    (fun σ=>P (p.restrict (R σ))*A i (p.spin (R σ)) (B σ))

 def nativeInitialAtomicPairJetClone
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (i : ℕ) (A : ℕ→S→S→ℝ) (Ks : List (ℕ→S→S→ℝ))
    (T : ClockTree S as) (P : T.Assignment→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*nativeInitialAtomicCloneValue p.tree i 0
    (nativeInitialAtomicPairJetPayload w φ v q x i A Ks P p)).sum/2

 def nativeInitialAtomicPairJetRetained
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (i : ℕ) (A : ℕ→S→S→ℝ) (Ks : List (ℕ→S→S→ℝ))
    (T : ClockTree S as) (P : T.Assignment→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*nativeInitialAtomicRetainedResamplingValue p.tree p.mark i 0
    (nativeInitialAtomicPairJetPayload w φ v q x i A Ks P p)).sum/2

private theorem initial_sum_filter_zero {α : Type} (L : List α) (pred : α→Bool) (F : α→ℝ)
    (hF : ∀a∈L,pred a=false→F a=0) :
    (L.map F).sum=((L.filter pred).map F).sum := by
  induction L with
  | nil=>rfl
  | cons a L ih=>
    have H:=ih (fun b hb=>hF b (List.mem_cons_of_mem a hb))
    cases hp : pred a
    · simp only [List.map_cons,List.sum_cons,List.filter_cons,hp,Bool.false_eq_true,ite_false,
        hF a List.mem_cons_self hp,zero_add,H]
    · simp only [List.map_cons,List.sum_cons,List.filter_cons,hp,ite_true,H]

 omit [Nonempty S] [Nonempty ι] in
 theorem native_initial_atomic_pair_jet_eq_clone_add_retained
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass}
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (i : ℕ) (hi : i<as.length) (A : ℕ→S→S→ℝ) (Ks : List (ℕ→S→S→ℝ))
    (T : ClockTree S as) (P : T.Assignment→ℝ) :
    disorderOffDiagonalJets w φ v q x ((fun j σ τ=>if j=i then A j σ τ else 0)::Ks) T P=
      nativeInitialAtomicPairJetClone w φ v q x i A Ks T P+
        nativeInitialAtomicPairJetRetained w φ v q x i A Ks T P := by
  let Am : ℕ→S→S→ℝ:=fun j σ τ=>if j=i then A j σ τ else 0
  have Hinner (p : MarkedPlacement T) :
      ((p.tree.markedAttach 0).map fun r=>r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x Ks r.tree (profilePairTest P Am p r)).sum=
      nativeInitialAtomicCloneValue p.tree i 0 (nativeInitialAtomicPairJetPayload w φ v q x i A Ks P p)+
        nativeInitialAtomicRetainedResamplingValue p.tree p.mark i 0
          (nativeInitialAtomicPairJetPayload w φ v q x i A Ks P p) := by
    have Hfilter:=initial_sum_filter_zero (p.tree.markedAttach 0)
      (fun r=>decide (r.tree.splitIndex (r.embed p.mark) r.mark=i))
      (fun r=>r.coeff*(1-r.hit p.mark)*
        disorderOffDiagonalJets w φ v q x Ks r.tree (profilePairTest P Am p r)) (by
      intro r hr hnot
      have hn : r.tree.splitIndex (r.embed p.mark) r.mark≠i:=of_decide_eq_false hnot
      have Hz : profilePairTest P Am p r=(fun _=>0):=by
        funext σ
        simp only [profilePairTest,Am,hn,ite_false,mul_zero]
      rw [Hz,native_initial_offDiagonalJets_zero_test,mul_zero])
    rw [Hfilter]
    rw [←native_initial_atomic_original_eq_clone_add_retained_resampling p.tree p.mark i 0
      (nativeInitialAtomicPairJetPayload w φ v q x i A Ks P p)]
    unfold nativeInitialMarkedRowsValue
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    have hs : r.tree.splitIndex (r.embed p.mark) r.mark=i:=of_decide_eq_true (List.mem_filter.mp hr).2
    have hn:=native_initial_atomic_original_row_off_diagonal p.tree p.mark i hi 0 r hr
    have Htest : profilePairTest P Am p r=
        (fun σ=>P (p.restrict (r.restrict σ))*A i (p.spin (r.restrict σ)) (r.spin σ)):=by
      funext σ
      simp only [profilePairTest,Am,hs,ite_true]
    simp only [MarkedPlacement.hit,hn,ite_false,sub_zero,mul_one,Htest,nativeInitialAtomicPairJetPayload]
  change ((T.markedAttach 0).map fun p=>p.coeff*
    ((p.tree.markedAttach 0).map fun r=>r.coeff*(1-r.hit p.mark)*
      disorderOffDiagonalJets w φ v q x Ks r.tree (profilePairTest P Am p r)).sum).sum/2=_
  simp_rw [Hinner]
  simp only [nativeInitialAtomicPairJetClone,nativeInitialAtomicPairJetRetained,mul_add,
    List.sum_map_add,add_div]

end OAI.SKFluctuations.Hierarchy.ClockTree
