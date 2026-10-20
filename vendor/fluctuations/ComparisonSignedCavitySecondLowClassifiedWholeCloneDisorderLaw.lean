module

public import ComparisonSignedCavitySecondLowClassifiedWholeRetainedSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_classified_forest_retained_clone_eq_whole_D_clone
    (pre mid tail : List PositiveMass) (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (d : D.Slot) (cut : ℕ) (hc : pre.length+mid.length < cut)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    {X : Type} (R : Ei.Assignment→Es.Assignment→D.Assignment→X)
    (q : ℕ→ι→ℝ≥0) (Q : X→X→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ (nativeExteriorForestTree pre mid Ei Es D)
      (nativeClassifiedForestOccupiedSlot pre mid Ei Es D d) cut q
      (fun σ σ'=>Q (nativeClassifiedSourceRead pre mid Ei Es D R σ)
        (nativeClassifiedSourceRead pre mid Ei Es D R σ')) x=
      let C:=nativeCloneBlockAtSlot D d (cut-(pre.length+mid.length))
      (nativeExteriorForestTree pre mid Ei Es C.tree).expect w φ q
        (nativeExteriorForestRead pre mid Ei Es C.tree
          (fun η ζ δ=>Q (R η ζ (C.oldRestrict δ)) (R η ζ (C.newRestrict δ)))) x := by
  let C:=nativeCloneBlockAtSlot D d (cut-(pre.length+mid.length))
  let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
  let VC:=Ei.fork (exteriorPrepend mid (Es.fork C.tree))
  let qi:=fun j=>q (pre.length+j)
  let qs:=fun j=>q (pre.length+(mid.length+j))
  have hcutI : mid.length < cut-pre.length:=by omega
  have hcutS : 0 < cut-(pre.length+mid.length):=by omega
  have HC:=native_retained_clone_prepend_general_prefix_law pre V
    (.inr ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d))) (cut-pre.length) w φ q
    (fun σ σ'=>Q (nativeClassifiedSourceRead pre mid Ei Es D R σ)
      (nativeClassifiedSourceRead pre mid Ei Es D R σ')) x
  rw [show pre.length+(cut-pre.length)=cut by omega] at HC
  dsimp only [nativeExteriorForestTree,nativeClassifiedForestOccupiedSlot,V] at HC ⊢
  rw [HC]
  have HE:=exteriorPrepend_expect pre hw φ VC ho q
    (fun σ=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork C.tree) σ.2;
      Q (R σ.1 u.1 (C.oldRestrict u.2)) (R σ.1 u.1 (C.newRestrict u.2))) x
  change _=(exteriorPrepend pre VC).expect w φ q
    (fun σ=>let u:=exteriorPrependAssignmentEquiv pre VC σ;
      let z:=exteriorPrependAssignmentEquiv mid (Es.fork C.tree) u.2;
      Q (R u.1 z.1 (C.oldRestrict z.2)) (R u.1 z.1 (C.newRestrict z.2))) x
  rw [HE]
  apply congrArg (fun F=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps (mid++tail) qi)) F x)
  funext xi
  obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : cut-pre.length≠0)
  conv_lhs=>rw [hj]
  rw [expect_fork]
  dsimp only [nativeClassifiedSourceRead]
  simp only [Equiv.apply_symm_apply]
  change Ei.expect w φ qi (fun η=>nativeRetainedCloneCutMean w φ (exteriorPrepend mid (Es.fork D))
    ((exteriorPrependSlotEquiv mid (Es.fork D)).symm (.inr d)) (j+1) qi
    (fun δ δ'=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) δ;
      let u':=exteriorPrependAssignmentEquiv mid (Es.fork D) δ';
      Q (R η u.1 u.2) (R η u'.1 u'.2)) xi) xi=
    Ei.expect w φ qi (fun η=>(exteriorPrepend mid (Es.fork C.tree)).expect w φ qi
      (fun δ=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork C.tree) δ;
        Q (R η u.1 (C.oldRestrict u.2)) (R η u.1 (C.newRestrict u.2))) xi) xi
  apply congrArg (fun F=>Ei.expect w φ qi F xi)
  funext η
  have HS:=native_retained_clone_prepend_general_prefix_law mid (Es.fork D) (.inr d)
    (cut-(pre.length+mid.length)) w φ qi
    (fun δ δ'=>let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) δ;
      let u':=exteriorPrependAssignmentEquiv mid (Es.fork D) δ';
      Q (R η u.1 u.2) (R η u'.1 u'.2)) xi
  rw [show mid.length+(cut-(pre.length+mid.length))=j+1 by omega] at HS
  rw [HS,exteriorPrepend_expect mid hw φ (Es.fork C.tree) ho.suffix_end qi
    (fun u=>Q (R η u.1 (C.oldRestrict u.2)) (R η u.1 (C.newRestrict u.2)))]
  apply congrArg (fun F=>prefixTest (clockSteps mid qi)
    (gaussianHierarchy w φ (clockSteps tail (fun j=>qi (mid.length+j)))) F xi)
  funext xs
  obtain ⟨l,hl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcutS)
  conv_lhs=>rw [hl]
  rw [expect_fork]
  simp only [Equiv.apply_symm_apply]
  change Es.expect w φ qs (fun ζ=>nativeRetainedCloneCutMean w φ D d (l+1) qs
    (fun δ δ'=>Q (R η ζ δ) (R η ζ δ')) xs) xs=
    Es.expect w φ qs (fun ζ=>C.tree.expect w φ qs
      (fun δ=>Q (R η ζ (C.oldRestrict δ)) (R η ζ (C.newRestrict δ))) xs) xs
  apply congrArg (fun F=>Es.expect w φ qs F xs)
  funext ζ
  have HH:=nativeRetainedCloneCutMean_eq_clone hw φ D ho.suffix_end.suffix_end d
    (cut-(pre.length+mid.length)) qs (fun δ δ'=>Q (R η ζ δ) (R η ζ δ')) xs
  rw [hl] at HH
  dsimp only [C]
  rw [hl]
  exact HH

namespace NativeClassifiedWholeRetainedSource
variable {pre mid tail : List PositiveMass} {T : ClockTree S (pre++(mid++tail))} {s : T.Slot}
variable {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ}
variable [MeasurableSpace S] [StandardBorelSpace S]

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem leaves_le (E : NativeClassifiedWholeRetainedSource pre mid tail T s w φ) :
    E.D.leaves ≤ T.leaves := by
  let :=nativeSecondLowSlotFintype E.D
  let :=nativeSecondLowSlotFintype T
  have H:=Fintype.card_le_of_injective E.embedD E.embed_injective
  rw [native_second_low_slot_fintype_card_eq_leaves E.D,native_second_low_slot_fintype_card_eq_leaves T] at H
  exact H

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem occupied_high (E : NativeClassifiedWholeRetainedSource pre mid tail T s w φ)
    {U : ℕ} (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T) (d : E.D.Slot) :
    U ≤ T.splitIndex s (E.embedD d) := by
  have htail : tail≠[]:=by
    intro H
    simp only [H,List.append_nil,List.length_append] at hU
    omega
  have HD:=E.occupied_root_free.split_pos htail E.target d
  have HS:=E.embed_splits E.target d
  rw [E.embed_target] at HS
  rcases hT s (E.embedD d) with H|H|H <;> omega

theorem whole_law (E : NativeClassifiedWholeRetainedSource pre mid tail T s w φ)
    (hw : ∀σ,0 < w σ) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.Assignment→ℝ) (x : ι→ℝ) :
    T.disorderExpect w φ v q Q x=
      ∫r,nativeExteriorForestConditionalTest E.Ei E.Es E.D w φ
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>Q (E.read η ζ δ)) (exteriorForestIRoot r) (exteriorForestStarRoot r)
        ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x := by
  rw [native_whole_expect_map_disorder T (nativeExteriorForestTree pre mid E.Ei E.Es E.D)
    (nativeClassifiedSourceRead pre mid E.Ei E.Es E.D E.read) hw φ ho E.whole_expect]
  have HR : (fun σ=>Q (nativeClassifiedSourceRead pre mid E.Ei E.Es E.D E.read σ))=
      nativeExteriorForestRead pre mid E.Ei E.Es E.D (fun η ζ δ=>Q (E.read η ζ δ)):=by
    funext σ
    rfl
  rw [HR]
  exact nativeExteriorForest_disorder_law_eq_conditional pre mid hw φ E.Ei E.Es E.D ho v q
    (fun η ζ δ=>Q (E.read η ζ δ)) x

def retainedCloneConditional (E : NativeClassifiedWholeRetainedSource pre mid tail T s w φ)
    (d : E.D.Slot) (cut : ℕ) (qi qs : ℕ→ι→ℝ≥0) (Q : T.Assignment→T.Assignment→ℝ)
    (xi xs : ι→ℝ) : ℝ:=
  E.Ei.expect w φ qi (fun η=>E.Es.expect w φ qs (fun ζ=>
    nativeRetainedCloneCutMean w φ E.D d (cut-(pre.length+mid.length)) qs
      (fun δ δ'=>Q (E.read η ζ δ) (E.read η ζ δ')) xs) xs) xi

theorem retained_clone_whole_law (E : NativeClassifiedWholeRetainedSource pre mid tail T s w φ)
    (hw : ∀σ,0 < w σ) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (d : E.D.Slot) (cut : ℕ) (hc : pre.length+mid.length < cut)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.Assignment→T.Assignment→ℝ) (x : ι→ℝ) :
    zeroContinuation (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
      (nativeRetainedCloneCutMean w φ T (E.embedD d) cut
        (cumulativeIncrements (q 0) (fun k=>q (k+1))) Q) x=
      ∫r,E.retainedCloneConditional d cut
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        Q (exteriorForestIRoot r) (exteriorForestStarRoot r)
        ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x := by
  let C:=nativeCloneBlockAtSlot E.D d (cut-(pre.length+mid.length))
  have HE : nativeRetainedCloneCutMean w φ T (E.embedD d) cut
      (cumulativeIncrements (q 0) (fun k=>q (k+1))) Q=
      (nativeExteriorForestTree pre mid E.Ei E.Es C.tree).expect w φ
        (cumulativeIncrements (q 0) (fun k=>q (k+1)))
        (nativeExteriorForestRead pre mid E.Ei E.Es C.tree
          (fun η ζ δ=>Q (E.read η ζ (C.oldRestrict δ)) (E.read η ζ (C.newRestrict δ)))) := by
    funext y
    rw [E.retained_clone_expect d cut hc]
    exact native_classified_forest_retained_clone_eq_whole_D_clone pre mid tail E.Ei E.Es E.D
      d cut hc hw φ ho E.read _ Q y
  rw [HE]
  rw [←(nativeExteriorForestTree pre mid E.Ei E.Es C.tree).disorderExpect_integral hw φ ho]
  rw [nativeExteriorForest_disorder_law_eq_conditional pre mid hw φ E.Ei E.Es C.tree ho]
  apply integral_congr_ae
  refine Eventually.of_forall fun r=>?_
  dsimp only [retainedCloneConditional]
  rw [nativeExteriorForestConditionalTest_eq_joint]
  apply congrArg (fun F=>E.Ei.expect w φ _ F (exteriorForestIRoot r))
  funext η
  rw [expect_fork]
  apply congrArg (fun F=>E.Es.expect w φ _ F (exteriorForestStarRoot r))
  funext ζ
  exact (nativeRetainedCloneCutMean_eq_clone hw φ E.D ho.suffix_end.suffix_end d
    (cut-(pre.length+mid.length)) _ (fun δ δ'=>Q (E.read η ζ δ) (E.read η ζ δ')) _).symm

end NativeClassifiedWholeRetainedSource
end OAI.SKFluctuations.Cavity
