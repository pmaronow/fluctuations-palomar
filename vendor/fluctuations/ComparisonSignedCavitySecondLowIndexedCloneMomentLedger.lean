module

public import ComparisonSignedCavitySecondLowNativeSharedLayerIntegral
public import ComparisonSignedCavitySecondLowOccupiedBlockPartition

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
attribute [local instance] nativeSecondLowSlotFintype

def nativeRetainedOldCloneSquareSum {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (x : ι→ℝ) : ℝ :=
  ∑s:T.Slot,nativeRetainedCloneCutMean w φ T s cut q (fun σ τ=>(P σ-P τ)^2) x

def nativeRetainedNewCloneSquareSum {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (F : S→ℝ) (x : ι→ℝ) : ℝ :=
  ∑s:T.Slot,nativeRetainedCloneCutMean w φ T s cut q
    (fun σ τ=>(F (T.atSlot σ s)-F (T.atSlot τ s))^2) x

private theorem indexed_clock_expect_smooth {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) :
    BddSmooth 0 (T.expect w φ q P) := by
  have H:T.expect w φ q P=(T.realize q).expect w φ
      (fun σ=>P ((T.assignmentEquiv q).symm σ)):=funext (T.expect_realize w φ q P)
  rw [H]
  exact (T.realize q).expect_smooth hw φ (clockSteps_ordered ho q) _ 0

theorem nativeRetainedCloneCutMean_smooth0 {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (s : T.Slot) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→T.Assignment→ℝ) :
    BddSmooth 0 (nativeRetainedCloneCutMean w φ T s cut q Q) := by
  have H:nativeRetainedCloneCutMean w φ T s cut q Q=
      (nativeCloneBlockAtSlot T s cut).tree.expect w φ q
        (fun σ=>Q ((nativeCloneBlockAtSlot T s cut).oldRestrict σ)
          ((nativeCloneBlockAtSlot T s cut).newRestrict σ)):=
    funext fun x=>nativeRetainedCloneCutMean_eq_clone hw φ T ho s cut q Q x
  rw [H]
  exact indexed_clock_expect_smooth _ hw φ ho q _

theorem nativeRetainedOldCloneSquareSum_smooth0 {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (cut : ℕ) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) :
    BddSmooth 0 (nativeRetainedOldCloneSquareSum T w φ cut q P) :=
  BddSmooth.sum Finset.univ fun s _=>nativeRetainedCloneCutMean_smooth0 T hw φ ho s cut q (fun σ τ=>(P σ-P τ)^2)

theorem nativeRetainedNewCloneSquareSum_smooth0 {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (cut : ℕ) (q : ℕ→ι→ℝ≥0) (F : S→ℝ) :
    BddSmooth 0 (nativeRetainedNewCloneSquareSum T w φ cut q F) :=
  BddSmooth.sum Finset.univ fun s _=>nativeRetainedCloneCutMean_smooth0 T hw φ ho s cut q (fun σ τ=>(F (T.atSlot σ s)-F (T.atSlot τ s))^2)

theorem nativeRetainedOldCloneSquareSum_nonneg {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (cut : ℕ) (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (x : ι→ℝ) :
    0 ≤ nativeRetainedOldCloneSquareSum T w φ cut q P x := by
  unfold nativeRetainedOldCloneSquareSum
  apply Finset.sum_nonneg
  intro s _
  rw [nativeRetainedCloneCutMean_eq_clone hw φ T ho,ClockTree.expect_realize]
  exact ReplicaTree.expect_nonneg hw φ _ (clockSteps_ordered ho q) (fun _=>sq_nonneg _) x

theorem nativeRetainedNewCloneSquareSum_nonneg {as : List PositiveMass} (T : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (cut : ℕ) (q : ℕ→ι→ℝ≥0) (F : S→ℝ) (x : ι→ℝ) :
    0 ≤ nativeRetainedNewCloneSquareSum T w φ cut q F x := by
  unfold nativeRetainedNewCloneSquareSum
  apply Finset.sum_nonneg
  intro s _
  rw [nativeRetainedCloneCutMean_eq_clone hw φ T ho,ClockTree.expect_realize]
  exact ReplicaTree.expect_nonneg hw φ _ (clockSteps_ordered ho q) (fun _=>sq_nonneg _) x

theorem native_retained_old_clone_sum_step {as : List PositiveMass} (T : ClockTree S as)
    (b : PositiveMass) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (b::as)) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (P : (T.step b).Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedOldCloneSquareSum (T.step b) w φ (cut+1) q P x=
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j=>q (j+1))))
        (nativeRetainedOldCloneSquareSum T w φ cut (fun j=>q (j+1)) P) x := by
  change T.Assignment→ℝ at P
  unfold nativeRetainedOldCloneSquareSum
  simp only [nativeRetainedCloneCutMean]
  rw [shiftedMean_sum]
  · intro s
    exact nativeRetainedCloneCutMean_smooth0 T hw φ ho.2.2 s cut (fun j=>q (j+1)) _
  · exact gaussianHierarchy_integrable hw φ _ (clockSteps_ordered ho.2.2 _) b.val (q 0) x

theorem native_retained_new_clone_sum_step {as : List PositiveMass} (T : ClockTree S as)
    (b : PositiveMass) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (b::as)) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (F : S→ℝ) (x : ι→ℝ) :
    nativeRetainedNewCloneSquareSum (T.step b) w φ (cut+1) q F x=
      shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j=>q (j+1))))
        (nativeRetainedNewCloneSquareSum T w φ cut (fun j=>q (j+1)) F) x := by
  unfold nativeRetainedNewCloneSquareSum
  simp only [nativeRetainedCloneCutMean,ClockTree.atSlot]
  rw [shiftedMean_sum]
  · intro s
    exact nativeRetainedCloneCutMean_smooth0 T hw φ ho.2.2 s cut (fun j=>q (j+1)) _
  · exact gaussianHierarchy_integrable hw φ _ (clockSteps_ordered ho.2.2 _) b.val (q 0) x

omit [Nonempty S] in
theorem native_retained_old_clone_sum_fork {as : List PositiveMass} (T E : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (P : (T.fork E).Assignment→ℝ) (x : ι→ℝ) :
    nativeRetainedOldCloneSquareSum (T.fork E) w φ (cut+1) q P x=
      E.expect w φ q (fun e=>nativeRetainedOldCloneSquareSum T w φ (cut+1) q (fun σ=>P (σ,e)) x) x+
      T.expect w φ q (fun σ=>nativeRetainedOldCloneSquareSum E w φ (cut+1) q (fun e=>P (σ,e)) x) x := by
  classical
  change T.Assignment×E.Assignment→ℝ at P
  unfold nativeRetainedOldCloneSquareSum
  simp only [Fintype.sum_sum_type,nativeRetainedCloneCutMean]
  unfold ClockTree.expect
  simp only [Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm]

omit [Nonempty S] in
theorem native_retained_new_clone_sum_fork {as : List PositiveMass} (T E : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (q : ℕ→ι→ℝ≥0)
    (F : S→ℝ) (x : ι→ℝ) :
    nativeRetainedNewCloneSquareSum (T.fork E) w φ (cut+1) q F x=
      E.expect w φ q (fun _=>nativeRetainedNewCloneSquareSum T w φ (cut+1) q F x) x+
      T.expect w φ q (fun _=>nativeRetainedNewCloneSquareSum E w φ (cut+1) q F x) x := by
  classical
  unfold nativeRetainedNewCloneSquareSum
  simp only [Fintype.sum_sum_type,nativeRetainedCloneCutMean,ClockTree.atSlot,Sum.elim_inl,Sum.elim_inr]
  unfold ClockTree.expect
  simp only [Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm]

end OAI.SKFluctuations.Cavity
