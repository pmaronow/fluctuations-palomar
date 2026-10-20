module

public import ComparisonSignedCavitySecondLowClassifiedWholeCSource
public import ComparisonSignedCavityRetainedSubtreeClone

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Cavity
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_group_root_forest_retained_clone
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (cut : ℕ) (hcut : 0 < cut)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→T.Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ T s cut q Q x=
      (nativeGroupRootForest T s).exterior.expect w φ q (fun η=>
        nativeRetainedCloneCutMean w φ (nativeGroupRootForest T s).occupied
          (nativeGroupRootForest T s).target cut q
          (fun δ δ'=>Q ((nativeGroupRootForest T s).read η δ)
            ((nativeGroupRootForest T s).read η δ')) x) x := by
  induction T generalizing a with
  | leaf=>
    change _=(single []).expect w φ q (fun _=>nativeRetainedCloneCutMean w φ .leaf s cut q Q x) x
    exact (expect_const hw φ (single []) ho q _ x).symm
  | @step b tail T ih=>
    change _=(single (b::tail)).expect w φ q (fun _=>nativeRetainedCloneCutMean w φ (T.step b) s cut q Q x) x
    exact (expect_const hw φ (single (b::tail)) ho q _ x).symm
  | @fork tail T V ihT ihV=>
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcut)
    cases s with
    | inl s=>
      change (∑η,V.weight w φ q η x*nativeRetainedCloneCutMean w φ T s (j+1) q
        (fun δ δ'=>Q (δ,η) (δ',η)) x)=
        (V.fork (nativeGroupRootForest T s).exterior).expect w φ q (fun η=>
          nativeRetainedCloneCutMean w φ (nativeGroupRootForest T s).occupied
            (nativeGroupRootForest T s).target (j+1) q
            (fun δ δ'=>Q ((nativeGroupRootForest T s).read η.2 δ,η.1)
              ((nativeGroupRootForest T s).read η.2 δ',η.1)) x) x
      rw [expect_fork]
      change V.expect w φ q _ x=V.expect w φ q _ x
      apply congrArg (fun F=>V.expect w φ q F x)
      funext η
      exact ihT s ho _
    | inr s=>
      change (∑η,T.weight w φ q η x*nativeRetainedCloneCutMean w φ V s (j+1) q
        (fun δ δ'=>Q (η,δ) (η,δ')) x)=
        (T.fork (nativeGroupRootForest V s).exterior).expect w φ q (fun η=>
          nativeRetainedCloneCutMean w φ (nativeGroupRootForest V s).occupied
            (nativeGroupRootForest V s).target (j+1) q
            (fun δ δ'=>Q (η.1,(nativeGroupRootForest V s).read η.2 δ)
              (η.1,(nativeGroupRootForest V s).read η.2 δ')) x) x
      rw [expect_fork]
      change T.expect w φ q _ x=T.expect w φ q _ x
      apply congrArg (fun F=>T.expect w φ q F x)
      funext η
      exact ihV s ho _

theorem native_group_root_forest_retained_clone_all_occupied
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (d : (nativeGroupRootForest T s).occupied.Slot) (cut : ℕ) (hcut : 0 < cut)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→T.Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ T ((nativeGroupRootForest T s).occupiedEmbed d) cut q Q x=
      (nativeGroupRootForest T s).exterior.expect w φ q (fun η=>
        nativeRetainedCloneCutMean w φ (nativeGroupRootForest T s).occupied
          d cut q
          (fun δ δ'=>Q ((nativeGroupRootForest T s).read η δ)
            ((nativeGroupRootForest T s).read η δ')) x) x := by
  induction T generalizing a with
  | leaf=>
    change _=(single []).expect w φ q (fun _=>nativeRetainedCloneCutMean w φ .leaf d cut q Q x) x
    exact (expect_const hw φ (single []) ho q _ x).symm
  | @step b tail T ih=>
    change _=(single (b::tail)).expect w φ q (fun _=>nativeRetainedCloneCutMean w φ (T.step b) d cut q Q x) x
    exact (expect_const hw φ (single (b::tail)) ho q _ x).symm
  | @fork tail T V ihT ihV=>
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcut)
    cases s with
    | inl s=>
      change (∑η,V.weight w φ q η x*nativeRetainedCloneCutMean w φ T ((nativeGroupRootForest T s).occupiedEmbed d) (j+1) q
        (fun δ δ'=>Q (δ,η) (δ',η)) x)=
        (V.fork (nativeGroupRootForest T s).exterior).expect w φ q (fun η=>
          nativeRetainedCloneCutMean w φ (nativeGroupRootForest T s).occupied
            d (j+1) q
            (fun δ δ'=>Q ((nativeGroupRootForest T s).read η.2 δ,η.1)
              ((nativeGroupRootForest T s).read η.2 δ',η.1)) x) x
      rw [expect_fork]
      change V.expect w φ q _ x=V.expect w φ q _ x
      apply congrArg (fun F=>V.expect w φ q F x)
      funext η
      exact ihT s d ho _
    | inr s=>
      change (∑η,T.weight w φ q η x*nativeRetainedCloneCutMean w φ V ((nativeGroupRootForest V s).occupiedEmbed d) (j+1) q
        (fun δ δ'=>Q (η,δ) (η,δ')) x)=
        (T.fork (nativeGroupRootForest V s).exterior).expect w φ q (fun η=>
          nativeRetainedCloneCutMean w φ (nativeGroupRootForest V s).occupied
            d (j+1) q
            (fun δ δ'=>Q (η.1,(nativeGroupRootForest V s).read η.2 δ)
              (η.1,(nativeGroupRootForest V s).read η.2 δ')) x) x
      rw [expect_fork]
      change T.expect w φ q _ x=T.expect w φ q _ x
      apply congrArg (fun F=>T.expect w φ q F x)
      funext η
      exact ihV s d ho _

omit [Nonempty S] in
theorem native_retained_clone_prepend_general_prefix_law
    (pre : List PositiveMass) {tail : List PositiveMass} (A : ClockTree S tail) (s : A.Slot)
    (cut : ℕ) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (Q : (exteriorPrepend pre A).Assignment→(exteriorPrepend pre A).Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
      ((exteriorPrependSlotEquiv pre A).symm s) (pre.length+cut) q Q x=
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
        (nativeRetainedCloneCutMean w φ A s cut (fun j=>q (pre.length+j))
          (fun δ δ'=>Q ((exteriorPrependAssignmentEquiv pre A).symm δ)
            ((exteriorPrependAssignmentEquiv pre A).symm δ'))) x := by
  induction pre generalizing q x with
  | nil=>
    simp only [exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,
      List.length_nil,Nat.zero_add,Equiv.refl_symm,Equiv.refl_apply,clockSteps,prefixTest]
  | cons b pre ih=>
    change (exteriorPrepend pre A).Assignment→(exteriorPrepend pre A).Assignment→ℝ at Q
    simp only [List.length_cons]
    rw [show pre.length+1+cut=pre.length+cut+1 by omega]
    change shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps (pre++tail) (fun j=>q (j+1))))
      (nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
        ((exteriorPrependSlotEquiv pre A).symm s) (pre.length+cut) (fun j=>q (j+1)) Q) x=_
    change _=prefixTest (clockSteps (b::pre) q)
      (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+1+j))))
      (nativeRetainedCloneCutMean w φ A s cut (fun j=>q (pre.length+1+j))
        (fun δ δ'=>Q ((exteriorPrependAssignmentEquiv pre A).symm δ)
          ((exteriorPrependAssignmentEquiv pre A).symm δ'))) x
    have HI : nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
        ((exteriorPrependSlotEquiv pre A).symm s) (pre.length+cut) (fun j=>q (j+1)) Q=
      prefixTest (clockSteps pre (fun j=>q (j+1)))
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j+1))))
        (nativeRetainedCloneCutMean w φ A s cut (fun j=>q (pre.length+j+1))
          (fun δ δ'=>Q ((exteriorPrependAssignmentEquiv pre A).symm δ)
            ((exteriorPrependAssignmentEquiv pre A).symm δ'))) :=
      funext fun y=>ih (fun j=>q (j+1)) Q y
    rw [HI]
    simp only [clockSteps,prefixTest]
    rw [prefixContinuation_hierarchy]
    have Hq:(fun j=>q (pre.length+j+1))=(fun j=>q (pre.length+1+j)):=by
      funext j;congr 1;omega
    rw [Hq]
    rw [clockSteps_append,Hq]

omit [Nonempty S] in
theorem exteriorPrepend_retained_clone_map_congr
    (pre : List PositiveMass) {tail : List PositiveMass} (A B : ClockTree S tail)
    (s : A.Slot) (t : B.Slot) (R : B.Assignment→A.Assignment) (cut : ℕ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (hLaw : ∀(q : ℕ→ι→ℝ≥0) (Q : A.Assignment→A.Assignment→ℝ) (x : ι→ℝ),
      nativeRetainedCloneCutMean w φ A s cut q Q x=
        nativeRetainedCloneCutMean w φ B t cut q (fun δ δ'=>Q (R δ) (R δ')) x)
    (q : ℕ→ι→ℝ≥0)
    (Q : (exteriorPrepend pre A).Assignment→(exteriorPrepend pre A).Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
      ((exteriorPrependSlotEquiv pre A).symm s) (pre.length+cut) q Q x=
      nativeRetainedCloneCutMean w φ (exteriorPrepend pre B)
        ((exteriorPrependSlotEquiv pre B).symm t) (pre.length+cut) q
        (fun δ δ'=>Q (exteriorPrependRead pre A B R δ) (exteriorPrependRead pre A B R δ')) x := by
  rw [native_retained_clone_prepend_general_prefix_law,native_retained_clone_prepend_general_prefix_law]
  apply congrArg (fun F=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j)))) F x)
  funext y
  simpa only [exteriorPrependRead,Equiv.apply_symm_apply] using hLaw (fun j=>q (pre.length+j))
    (fun δ δ'=>Q ((exteriorPrependAssignmentEquiv pre A).symm δ)
      ((exteriorPrependAssignmentEquiv pre A).symm δ')) y

end OAI.SKFluctuations.Hierarchy.ClockTree
