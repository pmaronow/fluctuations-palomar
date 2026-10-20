module

public import CavityProjectionErrorPrefixTransport
public import CavityRetainedPrefix
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalTerminalPairLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

theorem conditionalPathAverage_root_parameter (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (j : ℕ)
    {P : Type} (x : P → ι → ℝ)
    (A : P → ForwardPath (ι → ℝ) S steps.length → ℝ)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    conditionalPathAverage w φ steps x j (fun q => A q.1 q.2) p =
      conditionalPathAverage w φ steps x j (fun q => A p.1 q.2) p := by
  induction steps generalizing P j with
  | nil => cases j <;> rfl
  | cons st tail ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hL := ih j (fun q : P × (ι → ℝ) => x q.1+q.2)
        (fun q c => A q.1 (q.2,c)) ((p.1,p.2.1),p.2.2)
      have hR := ih j (fun q : P × (ι → ℝ) => x q.1+q.2)
        (fun q c => A p.1 (q.2,c)) ((p.1,p.2.1),p.2.2)
      exact hL.trans hR.symm

theorem conditional_terminal_fork_root_irrel (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (j : ℕ)
    {P R : Type} (x : P → ι → ℝ) (y : R → ι → ℝ)
    (p : P) (r : R) (he : x p=y r) (Q : S → S → ℝ)
    (c : ForwardPath (ι → ℝ) S steps.length) :
    conditionalForkTest w φ steps x j (terminalPairTest steps Q) (p,c) =
      conditionalForkTest w φ steps y j (terminalPairTest steps Q) (r,c) := by
  induction steps generalizing P R j with
  | nil =>
    cases j with
    | zero => simp only [conditionalForkTest,conditionalPathAverage,terminalPairTest,he]
    | succ j => rfl
  | cons st tail ih =>
    cases j with
    | zero => simp only [conditionalForkTest,conditionalPathAverage,terminalPairTest,he]
    | succ j =>
      exact ih j (fun q : P × (ι → ℝ) => x q.1+q.2)
        (fun q : R × (ι → ℝ) => y q.1+q.2) (p,c.1) (r,c.1)
        (by simp only [he]) c.2

theorem integral_terminal_fork_fixed_root {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a steps) {P : Type}
    (x : P → ι → ℝ) (p : P) (j : ℕ) (hj : j ≤ steps.length) (Q : S → S → ℝ) :
    (∫ c, conditionalForkTest w φ steps x j (terminalPairTest steps Q) (p,c)
      ∂hierarchyPathKernel w φ steps (x p)) = levelPairMean w φ Q steps j (x p) := by
  have h := integral_terminalFork_eq_levelPairMean hw φ steps hs
    (Measure.dirac ()) (fun _ : Unit => x p) measurable_const j hj Q
  have hI := conditionalForkTest_integrable hw φ steps hs (Measure.dirac ())
    (fun _ : Unit => x p) measurable_const j (terminalPairTest_measurable steps Q)
    (terminalPairTest_abs_le steps Q)
  have := hierarchyPathKernel_markov hw φ steps hs
  rw [Measure.integral_compProd hI] at h
  simp only [Kernel.comap_apply,integral_dirac] at h
  convert h using 1
  congr 1
  funext c
  exact conditional_terminal_fork_root_irrel w φ steps j x (fun _ : Unit => x p) p () rfl Q c

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem actual_prepend_expect {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} (T : ReplicaTree ι S tail)
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) (Q : T.Assignment → ℝ) (x : ι → ℝ) :
    (prependReplicaTree pre T).expect w φ
      (fun σ => Q (prependAssignmentEquiv pre T σ)) x =
      prefixTest pre (gaussianHierarchy w φ tail) (T.expect w φ Q) x := by
  induction pre generalizing a x with
  | nil => rfl
  | cons st pre ih =>
    change ((prependReplicaTree pre T).step st).expect w φ
      (fun σ => Q (prependAssignmentEquiv pre T σ)) x = _
    rw [ReplicaTree.expect_step hw φ _ st.1 st.2 hs.2.2.2]
    have he := funext (ih hs.2.2.2)
    rw [he]
    simp only [prefixTest]
    rw [prefixContinuation_hierarchy]
    rfl

def actualBoundaryResamplingTree (mid tail : List (GaussianStep ι)) :
    ReplicaTree ι S (mid++tail) :=
  (ReplicaTree.single (S := S) (mid++tail)).fork
    (prependReplicaTree mid ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail)))

def actualBoundaryResamplingTest (mid tail : List (GaussianStep ι)) (Q : S → S → S → ℝ)
    (σ : (actualBoundaryResamplingTree (S := S) mid tail).Assignment) : ℝ :=
  let cs := prependAssignmentEquiv mid ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail)) σ.2
  Q (ReplicaTree.singleEquiv (S := S) (mid++tail) σ.1)
    (ReplicaTree.singleEquiv (S := S) tail cs.1)
    (ReplicaTree.singleEquiv (S := S) tail cs.2)

theorem actual_boundary_resampling_tree_expect {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (mid++tail)) (Q : S → S → S → ℝ) (x : ι → ℝ) :
    (actualBoundaryResamplingTree (S := S) mid tail).expect w φ
      (actualBoundaryResamplingTest mid tail Q) x =
      gaussianHierarchyMean w φ (fun d => levelPairMean w φ (Q d) (mid++tail) mid.length x)
        (mid++tail) x := by
  change ((ReplicaTree.single (S := S) (mid++tail)).fork
    (prependReplicaTree mid ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail)))).expect
    w φ (fun σ => let cs := (prependAssignmentEquiv mid
      ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail))) σ.2;
      Q (ReplicaTree.singleEquiv (S := S) (mid++tail) σ.1)
        (ReplicaTree.singleEquiv (S := S) tail cs.1)
        (ReplicaTree.singleEquiv (S := S) tail cs.2)) x = _
  rw [ReplicaTree.expect_fork]
  have hp (d : S) : (prependReplicaTree mid ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail))).expect
      w φ (fun σ => let cs := (prependAssignmentEquiv mid
        ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail))) σ;
        Q d (ReplicaTree.singleEquiv (S := S) tail cs.1)
          (ReplicaTree.singleEquiv (S := S) tail cs.2)) x =
      levelPairMean w φ (Q d) (mid++tail) mid.length x := by
    change (prependReplicaTree mid ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail))).expect
      w φ (fun σ => (fun cs => Q d (ReplicaTree.singleEquiv (S := S) tail cs.1)
        (ReplicaTree.singleEquiv (S := S) tail cs.2))
          (prependAssignmentEquiv mid ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail)) σ)) x = _
    rw [actual_prepend_expect hw φ mid
      ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail)) hs
      (fun cs => Q d (ReplicaTree.singleEquiv (S := S) tail cs.1)
        (ReplicaTree.singleEquiv (S := S) tail cs.2)) x]
    have hpair : (((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail)).expect w φ
        (fun cs => Q d (ReplicaTree.singleEquiv (S := S) tail cs.1)
          (ReplicaTree.singleEquiv (S := S) tail cs.2))) = hierarchyPairMean w φ (Q d) tail := by
      funext y
      rw [ReplicaTree.expect_fork]
      have hinner := funext fun c => ReplicaTree.single_expect hw φ tail (hs.suffix mid tail)
        (Q d (ReplicaTree.singleEquiv (S := S) tail c)) y
      change (ReplicaTree.single (S := S) tail).expect w φ
        (fun c => (ReplicaTree.single (S := S) tail).expect w φ
          (fun e => Q d (ReplicaTree.singleEquiv (S := S) tail c)
            (ReplicaTree.singleEquiv (S := S) tail e)) y) y = _
      rw [hinner]
      exact (ReplicaTree.single_expect hw φ tail (hs.suffix mid tail)
        (fun c => gaussianHierarchyMean w φ (Q d c) tail y) y).trans
          (hierarchyPairMean_eq_nested hw φ (Q d) tail (hs.suffix mid tail) y).symm
    rw [hpair]
    exact (congrFun (levelPairMean_prefix w φ (Q d) mid tail) x).symm
  have hfun : (fun σ => (prependReplicaTree mid
      ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail))).expect w φ
        (fun τ => let cs := (prependAssignmentEquiv mid
          ((ReplicaTree.single (S := S) tail).fork (ReplicaTree.single (S := S) tail))) τ;
          Q (ReplicaTree.singleEquiv (S := S) (mid++tail) σ)
            (ReplicaTree.singleEquiv (S := S) tail cs.1)
            (ReplicaTree.singleEquiv (S := S) tail cs.2)) x) =
      fun σ => levelPairMean w φ
        (Q (ReplicaTree.singleEquiv (S := S) (mid++tail) σ)) (mid++tail) mid.length x :=
    funext (fun σ => hp _)
  change (ReplicaTree.single (S := S) (mid++tail)).expect w φ _ x = _
  rw [hfun]
  exact ReplicaTree.single_expect hw φ (mid++tail) hs
    (fun d => levelPairMean w φ (Q d) (mid++tail) mid.length x) x

end OAI.SKFluctuations.Cavity
