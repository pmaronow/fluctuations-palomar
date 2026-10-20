module

public import ComparisonSignedCavitySecondLowInheritedCloneProductRate
public import ComparisonSignedCavityForestPrefixGeometry
public import ComparisonSignedCavityActualGroupedClosure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Cavity
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_retained_clone_prepend_prefix_law
    (pre : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S tail) (s : A.Slot) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (Q : (exteriorPrepend pre A).Assignment→
      (exteriorPrepend pre A).Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
      ((exteriorPrependSlotEquiv pre A).symm s) pre.length q Q x=
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
        ((A.fork A).expect w φ (fun j=>q (pre.length+j)) (fun σ=>
          Q ((exteriorPrependAssignmentEquiv pre A).symm σ.1)
            ((exteriorPrependAssignmentEquiv pre A).symm σ.2))) x := by
  induction pre generalizing q x with
  | nil=>
    simp only [exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,
      List.length_nil,Nat.zero_add,Equiv.refl_symm,Equiv.refl_apply,clockSteps,prefixTest]
    cases A <;> exact nativeRetainedCloneRootMean_eq_clone w φ _ q Q x
  | cons b pre ih=>
    change (exteriorPrepend pre A).Assignment→(exteriorPrepend pre A).Assignment→ℝ at Q
    change shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps (pre++tail) (fun j=>q (j+1))))
      (nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
        ((exteriorPrependSlotEquiv pre A).symm s) pre.length (fun j=>q (j+1)) Q) x=_
    have HI:nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
        ((exteriorPrependSlotEquiv pre A).symm s) pre.length (fun j=>q (j+1)) Q=
      prefixTest (clockSteps pre (fun j=>q (j+1)))
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j+1))))
        ((A.fork A).expect w φ (fun j=>q (pre.length+j+1)) (fun σ=>
          Q ((exteriorPrependAssignmentEquiv pre A).symm σ.1)
            ((exteriorPrependAssignmentEquiv pre A).symm σ.2))) :=
      funext fun y=>ih (fun j=>q (j+1)) Q y
    rw [HI]
    simp only [clockSteps,prefixTest,List.length_cons]
    rw [prefixContinuation_hierarchy]
    have Hq:(fun j=>q (pre.length+j+1))=(fun j=>q (pre.length+1+j)):=by
      funext j;congr 1;omega
    rw [Hq]
    rw [clockSteps_append,Hq]
    rfl

omit [Nonempty S] in
theorem native_retained_clone_shared_exterior_prefix_law
    (pre : List PositiveMass) (hpre : pre≠[]) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (Q : ((exteriorPrepend pre A).fork E).Assignment→
      ((exteriorPrepend pre A).fork E).Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedCloneCutMean w φ ((exteriorPrepend pre A).fork E)
      (.inl ((exteriorPrependSlotEquiv pre A).symm s)) pre.length q Q x=
      E.expect w φ q (fun e=>prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
        ((A.fork A).expect w φ (fun j=>q (pre.length+j)) (fun σ=>
          Q (((exteriorPrependAssignmentEquiv pre A).symm σ.1),e)
            (((exteriorPrependAssignmentEquiv pre A).symm σ.2),e))) x) x := by
  have hlen:0 < pre.length:=List.length_pos_iff.mpr hpre
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  simp only [Nat.succ_eq_add_one] at hk
  conv_lhs=>rw [hk]
  change (∑e,E.weight w φ q e x*nativeRetainedCloneCutMean w φ (exteriorPrepend pre A)
    ((exteriorPrependSlotEquiv pre A).symm s) (k+1) q (fun σ τ=>Q (σ,e) (τ,e)) x)=_
  rw [←hk]
  simp_rw [native_retained_clone_prepend_prefix_law]
  rfl

theorem native_two_complete_c_copies_eq_two_single
    {tail : List PositiveMass} (A : ClockTree S tail) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a tail) (q : ℕ→ι→ℝ≥0)
    (H : S→S→ℝ) (x : ι→ℝ) :
    (A.fork A).expect w φ q (fun σ=>H (A.atSlot σ.1 s) (A.atSlot σ.2 s)) x=
      ((single (S:=S) tail).fork (single (S:=S) tail)).expect w φ q
        (fun σ=>H ((singleEquiv (S:=S) tail) σ.1) ((singleEquiv (S:=S) tail) σ.2)) x := by
  rw [ClockTree.expect_fork,ClockTree.expect_fork]
  have H1:∀σ,A.expect w φ q (fun τ=>H (A.atSlot σ s) (A.atSlot τ s)) x=
      singleMean w φ tail q (H (A.atSlot σ s)) x:=by
    intro σ
    exact A.expect_atSlot hw φ ho q s _ x
  simp_rw [H1]
  rw [A.expect_atSlot hw φ ho q s (fun u=>singleMean w φ tail q (H u) x)]
  rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
