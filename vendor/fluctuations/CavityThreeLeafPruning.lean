module

public import CavityPhysicalResamplingTreeLaw
public import CavityAttachedTree

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def boundaryTripleMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (as : List PositiveMass) → (ℕ → ι → ℝ≥0) → ℕ → ℕ →
      (S → S → S → ℝ) → (ι → ℝ) → ℝ
  | as, q, 0, high, Q, x =>
    singleMean w φ as q (fun d => pairMean w φ as q high (Q d) x) x
  | [], q, _+1, high, Q, x =>
    singleMean w φ [] q (fun d => pairMean w φ [] q high (Q d) x) x
  | b::as, q, low+1, high, Q, x =>
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
      (boundaryTripleMean w φ as (fun j => q (j+1)) low (high-1) Q) x

private theorem expect_singleMean_swap (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (Q : T.Assignment → S → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ => singleMean w φ as q (Q σ) x) x =
      singleMean w φ as q (fun d => T.expect w φ q (fun σ => Q σ d) x) x := by
  simp only [singleMean,expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem expect_boundary_threeAtSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k)
    (Q : S → S → S → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ => Q (T.atSlot σ i) (T.atSlot σ j) (T.atSlot σ k)) x =
      boundaryTripleMean w φ as q (T.splitIndex i j) (T.splitIndex j k) Q x := by
  induction T generalizing a q Q x with
  | leaf => exact (hjk (Subsingleton.elim _ _)).elim
  | @step b bs T ih =>
    rw [expect_step hw φ b T ho.2.2]
    change _ = boundaryTripleMean w φ (b::bs) q
      (1+T.splitIndex i j) (1+T.splitIndex j k) Q x
    rw [Nat.add_comm 1]
    simp only [boundaryTripleMean,Nat.add_sub_cancel_left]
    congr 1
    funext y
    apply ih ho.2.2 _ i j k hjk
    · have h : 1+T.splitIndex i j=1+T.splitIndex i k := hlow
      omega
    · have h : 1+T.splitIndex i j < 1+T.splitIndex j k := hgap
      omega
  | @fork as T U ihT ihU =>
    cases i with
    | inl i => cases j with
      | inl j => cases k with
        | inl k =>
          rw [expect_fork]
          change T.expect w φ q (fun σ => U.expect w φ q
            (fun _ => Q (T.atSlot σ i) (T.atSlot σ j) (T.atSlot σ k)) x) x = _
          simp only [U.expect_const hw φ ho q]
          exact ihT ho q i j k (fun h => hjk (congrArg Sum.inl h)) hlow hgap Q x
        | inr k =>
          simp only [splitIndex,Sum.elim_inl,Sum.elim_inr] at hlow hgap
          omega
      | inr j => cases k with
        | inl k =>
          simp only [splitIndex,Sum.elim_inl,Sum.elim_inr] at hgap
          omega
        | inr k =>
          rw [expect_fork]
          change T.expect w φ q (fun σ => U.expect w φ q
            (fun τ => Q (T.atSlot σ i) (U.atSlot τ j) (U.atSlot τ k)) x) x = _
          have hin := funext fun σ => U.expect_pairAtSlot hw φ ho q j k
            (fun h => hjk (congrArg Sum.inr h)) (Q (T.atSlot σ i)) x
          rw [hin]
          have he := T.expect_atSlot hw φ ho q i
            (fun d => pairMean w φ as q (U.splitIndex j k) (Q d) x) x
          apply he.trans
          cases as <;> rfl
    | inr i => cases j with
      | inl j => cases k with
        | inl k =>
          rw [expect_fork]
          change T.expect w φ q (fun σ => U.expect w φ q
            (fun τ => Q (U.atSlot τ i) (T.atSlot σ j) (T.atSlot σ k)) x) x = _
          have hin := funext fun σ => U.expect_atSlot hw φ ho q i
            (fun d => Q d (T.atSlot σ j) (T.atSlot σ k)) x
          rw [hin,expect_singleMean_swap]
          change singleMean w φ as q
            (fun d => T.expect w φ q (fun σ => Q d (T.atSlot σ j) (T.atSlot σ k)) x) x = _
          have hp := funext fun d => T.expect_pairAtSlot hw φ ho q j k
            (fun h => hjk (congrArg Sum.inl h)) (Q d) x
          rw [hp]
          cases as <;> rfl
        | inr k =>
          simp only [splitIndex,Sum.elim_inl,Sum.elim_inr] at hgap
          omega
      | inr j => cases k with
        | inl k =>
          simp only [splitIndex,Sum.elim_inl,Sum.elim_inr] at hlow hgap
          omega
        | inr k =>
          rw [expect_fork]
          change T.expect w φ q (fun _ => U.expect w φ q
            (fun σ => Q (U.atSlot σ i) (U.atSlot σ j) (U.atSlot σ k)) x) x = _
          rw [T.expect_const hw φ ho q]
          exact ihU ho q i j k (fun h => hjk (congrArg Sum.inr h)) hlow hgap Q x

def boundaryTripleClock : (as : List PositiveMass) → ℕ → ℕ → ClockTree S as
  | [], _, _ => leaf.fork (leaf.fork leaf)
  | b::as, 0, high => (single (b::as)).fork (pairClock (b::as) high)
  | b::as, low+1, high => (boundaryTripleClock as low (high-1)).step b

def boundaryTripleSpin : (as : List PositiveMass) → (low high : ℕ) →
    (boundaryTripleClock (S := S) as low high).Assignment → S × S × S
  | [], _, _, σ => (σ.1,σ.2.1,σ.2.2)
  | b::as, 0, high, σ =>
    (singleEquiv (S := S) (b::as) σ.1,
      (pairSpin (b::as) high σ.2).1,(pairSpin (b::as) high σ.2).2)
  | _::as, low+1, high, σ => boundaryTripleSpin as low (high-1) σ

theorem boundaryTripleClock_expect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (low high : ℕ) (Q : S → S → S → ℝ) (x : ι → ℝ) :
    (boundaryTripleClock (S := S) as low high).expect w φ q
      (fun σ => let z := boundaryTripleSpin as low high σ; Q z.1 z.2.1 z.2.2) x =
    boundaryTripleMean w φ as q low high Q x := by
  induction as generalizing a q low high x with
  | nil =>
    change (leaf.fork (leaf.fork leaf)).expect w φ q (fun σ => Q σ.1 σ.2.1 σ.2.2) x = _
    rw [expect_fork]
    have he : (fun d : S => (leaf.fork leaf).expect w φ q
        (fun σ => Q d σ.1 σ.2) x) =
        fun d => pairMean w φ [] q high (Q d) x :=
      funext fun d => pairClock_expect hw φ [] ho q high (Q d) x
    rw [he]
    cases low <;> rfl
  | cons b as ih =>
    cases low with
    | zero =>
      change ((single (S := S) (b::as)).fork (pairClock (S := S) (b::as) high)).expect w φ q
        (fun σ => Q (singleEquiv (S := S) (b::as) σ.1)
          (pairSpin (b::as) high σ.2).1 (pairSpin (b::as) high σ.2).2) x = _
      rw [expect_fork]
      have he := funext fun σ => pairClock_expect hw φ (b::as) ho q high
        (Q (singleEquiv (S := S) (b::as) σ)) x
      rw [he]
      rfl
    | succ low =>
      change ((boundaryTripleClock (S := S) as low (high-1)).step b).expect w φ q
        (fun σ => let z := boundaryTripleSpin as low (high-1) σ; Q z.1 z.2.1 z.2.2) x = _
      rw [expect_step hw φ b _ ho.2.2]
      change shiftedMean _ _ _ _ x = shiftedMean _ _ _ _ x
      congr 1
      funext y
      exact ih ho.2.2 _ low (high-1) y

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
open GaussianCalculus
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem rootExpect_boundary_threeAtSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    {n : ℕ} (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k)
    (Q : S → S → S → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ (fun σ => Q (T.atSlot σ i) (T.atSlot σ j) (T.atSlot σ k)) q₀ q x =
      (boundaryTripleClock (S := S) as (T.splitIndex i j) (T.splitIndex j k)).rootExpect w φ
        (fun σ => let z := boundaryTripleSpin as (T.splitIndex i j) (T.splitIndex j k) σ;
          Q z.1 z.2.1 z.2.2) q₀ q x := by
  simp only [rootExpect_eq_integral,expect_boundary_threeAtSlot hw φ T ho _ i j k hjk hlow hgap,
    boundaryTripleClock_expect hw φ as ho]

theorem disorderExpect_boundary_threeAtSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    [Nonempty ι] (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k) (Q : S → S → S → ℝ) :
    T.disorderExpect w φ v q (fun σ => Q (T.atSlot σ i) (T.atSlot σ j) (T.atSlot σ k)) x =
      (boundaryTripleClock (S := S) as (T.splitIndex i j) (T.splitIndex j k)).disorderExpect w φ v q
        (fun σ => let z := boundaryTripleSpin as (T.splitIndex i j) (T.splitIndex j k) σ;
          Q z.1 z.2.1 z.2.2) x := by
  let e := finiteJetEquiv ι
  let z := (coordinateEquiv e).symm x
  have H := T.rootExpect_boundary_threeAtSlot hw (reindexFeature e φ) ho
    (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i))
    i j k hjk hlow hgap Q z
  rw [T.rootExpect_eq_disorderExpect hw (reindexFeature e φ) ho _
      (fun i => v (e i)) (fun j i => q j (e i)),
    (boundaryTripleClock (S := S) as (T.splitIndex i j) (T.splitIndex j k)).rootExpect_eq_disorderExpect
      hw (reindexFeature e φ) ho _ (fun i => v (e i)) (fun j i => q j (e i)),
    T.disorderExpect_reindex e w φ v q,
    (boundaryTripleClock (S := S) as (T.splitIndex i j) (T.splitIndex j k)).disorderExpect_reindex
      e w φ v q,
    ContinuousLinearEquiv.apply_symm_apply] at H
  exact H

end OAI.SKFluctuations.Hierarchy.ClockTree
