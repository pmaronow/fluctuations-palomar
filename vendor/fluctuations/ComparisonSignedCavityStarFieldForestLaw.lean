module

public import ComparisonSignedCavityStarFieldTestFold
public import ComparisonSignedCavityTwoLevelExteriorRead

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem nativeGroupRootForest_star_field_test {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (J : (ι → ℝ) → T.Assignment → ℝ) (x : ι → ℝ) :
    nativeStarFieldTestMean w φ T s (star+1) q J x=
      (nativeGroupRootForest T s).exterior.expect w φ q
        (fun η=>nativeStarFieldTestMean w φ (nativeGroupRootForest T s).occupied
          (nativeGroupRootForest T s).target (star+1) q
          (fun y σ=>J y ((nativeGroupRootForest T s).read η σ)) x) x := by
  induction T generalizing a with
  | leaf=>
    change _=(single []).expect w φ q (fun _=>nativeStarFieldTestMean w φ leaf s (star+1) q J x) x
    exact ((single []).expect_const hw φ ho q _ x).symm
  | @step b tail T ih=>
    change _=(single (b::tail)).expect w φ q
      (fun _=>nativeStarFieldTestMean w φ (T.step b) s (star+1) q J x) x
    exact ((single (b::tail)).expect_const hw φ ho q _ x).symm
  | @fork tail T V ihT ihV=>
    cases s with
    | inl s=>
      change (∑τ,V.weight w φ q τ x*nativeStarFieldTestMean w φ T s (star+1) q
        (fun y σ=>J y (σ,τ)) x)=
        (V.fork (nativeGroupRootForest T s).exterior).expect w φ q
          (fun η=>nativeStarFieldTestMean w φ (nativeGroupRootForest T s).occupied
            (nativeGroupRootForest T s).target (star+1) q
            (fun y σ=>J y ((nativeGroupRootForest T s).read η.2 σ,η.1)) x) x
      rw [expect_fork]
      change V.expect w φ q
        (fun τ=>nativeStarFieldTestMean w φ T s (star+1) q (fun y σ=>J y (σ,τ)) x) x=_
      apply congrArg (fun F=>V.expect w φ q F x)
      funext τ
      exact ihT s ho (fun y σ=>J y (σ,τ))
    | inr s=>
      change (∑τ,T.weight w φ q τ x*nativeStarFieldTestMean w φ V s (star+1) q
        (fun y σ=>J y (τ,σ)) x)=
        (T.fork (nativeGroupRootForest V s).exterior).expect w φ q
          (fun η=>nativeStarFieldTestMean w φ (nativeGroupRootForest V s).occupied
            (nativeGroupRootForest V s).target (star+1) q
            (fun y σ=>J y (η.1,(nativeGroupRootForest V s).read η.2 σ)) x) x
      rw [expect_fork]
      change T.expect w φ q
        (fun τ=>nativeStarFieldTestMean w φ V s (star+1) q (fun y σ=>J y (τ,σ)) x) x=_
      apply congrArg (fun F=>T.expect w φ q F x)
      funext τ
      exact ihV s ho (fun y σ=>J y (τ,σ))

theorem exteriorPrepend_star_field_test (pre : List PositiveMass) {tail : List PositiveMass}
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ClockTree S tail) (s : T.Slot) (star : ℕ)
    {a : ℝ} (ho : MassOrdered a (pre++tail)) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→T.Assignment→ℝ) (x : ι→ℝ) :
    nativeStarFieldTestMean w φ (exteriorPrepend pre T)
      ((exteriorPrependSlotEquiv pre T).symm s) (pre.length+star) q
      (fun y σ=>J y (exteriorPrependAssignmentEquiv pre T σ)) x=
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
        (fun y=>nativeStarFieldTestMean w φ T s star (fun j=>q (pre.length+j)) J y) x := by
  induction pre generalizing a q x with
  | nil=>
    simp only [exteriorPrepend,exteriorPrependSlotEquiv,exteriorPrependAssignmentEquiv,
      clockSteps,prefixTest,List.length_nil,Nat.zero_add,Equiv.refl_symm,Equiv.refl_apply]
    rfl
  | cons b pre ih=>
    rw [show (b::pre).length+star=(pre.length+star)+1 by simp only [List.length_cons];omega]
    change shiftedMean _ _ _
      (nativeStarFieldTestMean w φ (exteriorPrepend pre T)
        ((exteriorPrependSlotEquiv pre T).symm s) (pre.length+star) (fun j=>q (j+1))
        (fun y σ=>J y (exteriorPrependAssignmentEquiv pre T σ))) x=_
    have he : (nativeStarFieldTestMean w φ (exteriorPrepend pre T)
        ((exteriorPrependSlotEquiv pre T).symm s) (pre.length+star) (fun j=>q (j+1))
        (fun y σ=>J y (exteriorPrependAssignmentEquiv pre T σ)))=
        prefixTest (clockSteps pre (fun j=>q (j+1)))
          (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j+1))))
          (fun y=>nativeStarFieldTestMean w φ T s star (fun j=>q (pre.length+j+1)) J y) :=
      funext fun y=>ih ho.2.2 (fun j=>q (j+1)) y
    rw [he]
    simp only [clockSteps,prefixTest,List.length_cons]
    have hq : (fun j=>q (pre.length+j+1))=(fun j=>q (pre.length+1+j)) := by
      funext j;congr 1;omega
    rw [hq,prefixContinuation_hierarchy]
    have hc : clockSteps (pre++tail) (fun j=>q (j+1))=
        clockSteps pre (fun j=>q (j+1))++clockSteps tail (fun j=>q (pre.length+1+j)) := by
      rw [clockSteps_append,hq]
    exact congrArg (fun ls=>shiftedMean (MeasureTheory.Measure.pi fun i=>ProbabilityTheory.gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ ls)
      (prefixTest (clockSteps pre (fun j=>q (j+1)))
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+1+j))))
        (fun y=>nativeStarFieldTestMean w φ T s star (fun j=>q (pre.length+1+j)) J y)) x) hc

end OAI.SKFluctuations.Hierarchy.ClockTree
