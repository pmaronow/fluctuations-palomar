module

public import ComparisonSignedCavitySecondLowNativeSharedLayerLaw

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

private theorem native_two_copies_slot_square_eq_single
    {steps : List (GaussianStep ι)} (A : ReplicaTree ι S steps) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : OrderedSteps a steps) (F : S→ℝ) (x : ι→ℝ) :
    actualForkResamplingSquare A w φ (fun σ=>F (A.atSlot σ s)) x=
      actualSingleResamplingSquare steps w φ F x := by
  unfold actualSingleResamplingSquare actualForkResamplingSquare
  rw [ReplicaTree.expect_fork,ReplicaTree.expect_fork]
  have H1:∀σ,A.expect w φ (fun τ=>(F (A.atSlot σ s)-F (A.atSlot τ s))^2) x=
      gaussianHierarchyMean w φ (fun z=>(F (A.atSlot σ s)-F z)^2) steps x:=by
    intro σ
    exact A.expect_atSlot hw φ ho s (fun z=>(F (A.atSlot σ s)-F z)^2) x
  simp_rw [H1]
  rw [A.expect_atSlot hw φ ho s (fun u=>gaussianHierarchyMean w φ (fun z=>(F u-F z)^2) steps x) x]
  have HS:∀σ:(ReplicaTree.single (S:=S) steps).Assignment,
      (ReplicaTree.single (S:=S) steps).expect w φ
        (fun τ=>(F (ReplicaTree.singleEquiv (S:=S) steps σ)-F (ReplicaTree.singleEquiv (S:=S) steps τ))^2) x=
      gaussianHierarchyMean w φ (fun z=>(F (ReplicaTree.singleEquiv (S:=S) steps σ)-F z)^2) steps x:=by
    intro σ
    exact ReplicaTree.single_expect hw φ steps ho
      (fun z=>(F (ReplicaTree.singleEquiv (S:=S) steps σ)-F z)^2) x
  simp_rw [HS]
  exact (ReplicaTree.single_expect hw φ steps ho
    (fun u=>gaussianHierarchyMean w φ (fun z=>(F u-F z)^2) steps x) x).symm

omit [Fintype ι] [Fintype S] [Nonempty S] in
private theorem native_realized_slot_inverse {tail : List PositiveMass}
    (A : ClockTree S tail) (q : ℕ→ι→ℝ≥0) (s : A.Slot) (σ : (A.realize q).Assignment) :
    A.atSlot ((A.assignmentEquiv q).symm σ) s=(A.realize q).atSlot σ (A.slotEquiv q s) := by
  have HH:=A.realize_atSlot q ((A.assignmentEquiv q).symm σ) s
  simpa only [Equiv.apply_symm_apply] using HH.symm

def nativeSharedPrefixLayer (pre : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (a v z : ℝ) (q : ℕ→ι→ℝ≥0)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  let qt:=fun j=>q (pre.length+j)
  let cs:=clockSteps pre q
  let ts:=clockSteps tail qt
  E.expect w φ q (fun e=>prefixTest cs (gaussianHierarchy w φ ts)
    (fun y=>actualCutRow (A.realize qt) w φ (prefixEndMass a cs) z
      (fun σ=>P ((A.assignmentEquiv qt).symm σ) e) (F e) y-
      actualCutRow (A.realize qt) w φ (prefixEndMass a cs) v
        (fun σ=>P ((A.assignmentEquiv qt).symm σ) e) (F e) y) x) x

def nativeSharedPrefixOldMoment (pre : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : A.Assignment→E.Assignment→ℝ) (x : ι→ℝ) : ℝ :=
  E.expect w φ q (fun e=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
    ((A.fork A).expect w φ (fun j=>q (pre.length+j))
      (fun σ=>(P σ.1 e-P σ.2 e)^2)) x) x

def nativeSharedPrefixNewMoment (pre : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (F : E.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  E.expect w φ q (fun e=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
    ((A.fork A).expect w φ (fun j=>q (pre.length+j))
      (fun σ=>(F e (A.atSlot σ.1 s)-F e (A.atSlot σ.2 s))^2)) x) x

omit [Fintype ι] in
private theorem native_shared_prefix_positive (pre : List PositiveMass) (q : ℕ→ι→ℝ≥0) :
    ∀st∈clockSteps pre q,0 < st.1 := by
  induction pre generalizing q with
  | nil=>simp [clockSteps]
  | cons b pre ih=>
    intro st hst
    rcases List.mem_cons.mp hst with rfl|hst
    · exact b.property
    · exact ih (fun j=>q (j+1)) st hst

private theorem native_expect_gram_sq_le {as : List PositiveMass}
    (E : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (A B C : E.Assignment→ℝ) (k : ℝ) (hA : ∀e,0 ≤ A e) (hB : ∀e,0 ≤ B e)
    (hC : ∀e,(C e)^2 ≤ k^2*A e*B e) (x : ι→ℝ) :
    (E.expect w φ q C x)^2 ≤ k^2*E.expect w φ q A x*E.expect w φ q B x := by
  classical
  simp_rw [E.expect_realize w φ q]
  exact actualExterior_expect_gram_sq_le hw φ (E.realize q) (clockSteps_ordered ho q)
    (fun e=>A ((E.assignmentEquiv q).symm e)) (fun e=>B ((E.assignmentEquiv q).symm e))
    (fun e=>C ((E.assignmentEquiv q).symm e)) k
    (fun e=>hA _) (fun e=>hB _) (fun e=>hC _) x

omit [Nonempty S] in
private theorem native_shared_prefix_moment_realize {tail : List PositiveMass}
    (A : ClockTree S tail) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (P : A.Assignment→ℝ) (x : ι→ℝ) :
    (A.fork A).expect w φ q (fun σ=>(P σ.1-P σ.2)^2) x=
      actualForkResamplingSquare (A.realize q) w φ
        (fun σ=>P ((A.assignmentEquiv q).symm σ)) x := by
  rw [(A.fork A).expect_realize w φ q]
  rfl

theorem native_shared_prefix_layer_sq_le
    (pre : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a v z : ℝ} (ho : MassOrdered a (pre++tail)) (hav : a ≤ v)
    (q_placeholder : ℕ→ι→ℝ≥0)
    (hp : ∀st∈clockSteps pre q_placeholder,st.1 ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : A.Assignment→E.Assignment→ℝ) (F : E.Assignment→S→ℝ) (x : ι→ℝ) :
    (nativeSharedPrefixLayer pre A E w φ a v z q_placeholder P F x)^2 ≤
      (3*(A.leaves:ℝ)*v)^2*nativeSharedPrefixOldMoment pre A E w φ q_placeholder P x*
        nativeSharedPrefixNewMoment pre A E s w φ q_placeholder F x := by
  let q:=q_placeholder
  let qt:=fun j=>q (pre.length+j)
  let cs:=clockSteps pre q
  let ts:=clockSteps tail qt
  have Hfull:OrderedSteps a (cs++ts):=by
    have HH:=clockSteps_ordered ho q
    rw [clockSteps_append] at HH
    exact HH
  have Htail:=prefixEndMass_ordered cs ts Hfull
  have hend:=prefixEndMass_le cs hav hp
  obtain ⟨L,hL⟩:=gaussianHierarchy_lipschitz hw φ ts Htail
  have hpos:=native_shared_prefix_positive pre q
  unfold nativeSharedPrefixLayer nativeSharedPrefixOldMoment nativeSharedPrefixNewMoment
  apply native_expect_gram_sq_le E hw φ ho q _ _ _ (3*(A.leaves:ℝ)*v)
  · intro e
    apply prefixTest_nonneg hL _ cs hpos x
    intro y
    rw [native_shared_prefix_moment_realize A w φ qt (fun σ=>P σ e) y]
    exact ((A.realize qt).fork (A.realize qt)).expect_nonneg hw φ Htail (fun _=>sq_nonneg _) y
  · intro e
    apply prefixTest_nonneg hL _ cs hpos x
    intro y
    rw [native_shared_prefix_moment_realize A w φ qt (fun σ=>F e (A.atSlot σ s)) y]
    exact ((A.realize qt).fork (A.realize qt)).expect_nonneg hw φ Htail (fun _=>sq_nonneg _) y
  · intro e
    have H:=actual_prefix_cut_layer_resampling_sq_le hw φ (A.realize qt) Htail hend hvz hz
      cs hpos (fun σ=>P ((A.assignmentEquiv qt).symm σ) e) (F e) x
    have HOld:(A.fork A).expect w φ qt (fun σ=>(P σ.1 e-P σ.2 e)^2)=
      actualForkResamplingSquare (A.realize qt) w φ
        (fun σ=>P ((A.assignmentEquiv qt).symm σ) e):=
      funext fun y=>native_shared_prefix_moment_realize A w φ qt (fun σ=>P σ e) y
    have HNew:(A.fork A).expect w φ qt (fun σ=>(F e (A.atSlot σ.1 s)-F e (A.atSlot σ.2 s))^2)=
        actualSingleResamplingSquare ts w φ (F e):=by
      funext y
      rw [native_shared_prefix_moment_realize A w φ qt (fun σ=>F e (A.atSlot σ s)) y]
      simp_rw [native_realized_slot_inverse]
      exact native_two_copies_slot_square_eq_single (A.realize qt) (A.slotEquiv qt s) hw φ Htail (F e) y
    rw [HOld,HNew]
    simpa only [ClockTree.realize_leaves] using H

end OAI.SKFluctuations.Cavity
