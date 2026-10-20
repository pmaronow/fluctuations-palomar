module

public import CavityCutErrorMoments
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalPinnedWindow
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockMassIntegral

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem actualBoundarySteps_length {ι : Type*} (as : List PositiveMass)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    (diagonalBoundarySteps as l q).length=as.length := by
  induction as generalizing l q with
  | nil => rfl
  | cons a as ih => simp only [diagonalBoundarySteps,List.length_cons,ih]

 def finitePhysicalMean (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
  let q := physicalCompletedClock n b h
  physicalPathSecondMoment n (diagonalBoundarySteps as (q 0) (fun k=>q (k+1)))
    (fun i=>Real.toNNReal (q 0 i)) (min j as.length)

 def finitePhysicalMixedClock (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
   h j+b j*finitePhysicalMean n as b h j

 theorem finitePhysicalMean_nonneg (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) :
    0≤finitePhysicalMean n as b h j := by
  unfold finitePhysicalMean physicalPathSecondMoment
  exact integral_nonneg fun _ => sq_nonneg _

 theorem finitePhysicalMean_monotone (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) : Monotone (finitePhysicalMean n as b h) := by
  let q := physicalCompletedClock n b h
  let steps := diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
  have hs : OrderedSteps 0 steps := diagonalBoundarySteps_ordered as (by norm_num) (by norm_num)
    ho.pairwise ho.members_le_one (fun a _=>a.property.le) _ _
  have hl : steps.length=as.length := actualBoundarySteps_length _ _ _
  intro i j hij
  exact physicalPathSecondMoment_mono n steps hs (fun k=>Real.toNNReal (q 0 k))
    (min_le_min_right _ hij) (by rw [hl]; exact Nat.min_le_right _ _)

 theorem finitePhysicalMean_eq_actual_pair (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (j : ℕ) (hj : j≤as.length) :
    finitePhysicalMean n as b h j =
      (ClockTree.pairClock as j).disorderExpect (uniformWeight n) (finiteFeature n) 0
        (physicalCompletedClock n b h)
        (fun σ=>orderedOverlap n (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) 0 := by
  unfold finitePhysicalMean
  rw [Nat.min_eq_left hj]
  have hs : OrderedSteps 0 (diagonalBoundarySteps as (physicalCompletedClock n b h 0)
      (fun k=>physicalCompletedClock n b h (k+1))) :=
    diagonalBoundarySteps_ordered as (by norm_num) (by norm_num)
      ho.pairwise ho.members_le_one (fun a _=>a.property.le) _ _
  rw [physicalSecondMoment_eq_rootLevelPairMean n _ hs _ j (by
    rw [actualBoundarySteps_length]; exact hj)]
  exact (ClockTree.pairDisorder_eq_rootLevelPairMean (uniformWeight_pos n) (finiteFeature n)
    as ho (physicalCompletedClock n b h) j (orderedOverlap n)).symm

 theorem finitePhysicalMixedClock_nonneg (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ)
    (hb : ∀ j, 0≤b j) (hh : ∀ j, 0≤h j) (j : ℕ) :
    0≤finitePhysicalMixedClock n as b h j :=
  add_nonneg (hh j) (mul_nonneg (hb j) (finitePhysicalMean_nonneg n as b h j))

 theorem finitePhysicalMean_le_one (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (j : ℕ) : finitePhysicalMean n as b h j≤1 := by
  have he : finitePhysicalMean n as b h j=finitePhysicalMean n as b h (min j as.length) := by
    simp only [finitePhysicalMean,Nat.min_assoc,Nat.min_self]
  rw [he,finitePhysicalMean_eq_actual_pair n ho b h _ (Nat.min_le_right _ _)]
  have hw := (ClockTree.pairClock as (min j as.length)).disorderWeight_probability
    (uniformWeight_pos n) (finiteFeature n) ho 0 (physicalCompletedClock n b h) 0
  unfold ClockTree.disorderExpect
  calc
    _ ≤ ∑ σ, (ClockTree.pairClock as (min j as.length)).disorderWeight (uniformWeight n)
        (finiteFeature n) 0 (physicalCompletedClock n b h) σ 0*1 := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (hw.1 σ)
      exact (le_abs_self _).trans (orderedOverlap_abs_le_one n _ _)
    _ = 1 := by simpa only [mul_one] using hw.2

 theorem finitePhysicalMixedClock_le_add (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : ∀ j, 0≤b j) (j : ℕ) :
    finitePhysicalMixedClock n as b h j≤h j+b j := by
  have H := mul_le_mul_of_nonneg_left (finitePhysicalMean_le_one n ho b h j) (hb j)
  simpa only [finitePhysicalMixedClock,mul_one] using add_le_add (le_refl (h j)) H

 theorem finitePhysicalMixedClock_monotone (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h) (hb0 : ∀ j, 0≤b j) :
    Monotone (finitePhysicalMixedClock n as b h) := by
  intro i j hij
  exact add_le_add (hh hij) (mul_le_mul (hb hij) (finitePhysicalMean_monotone n ho b h hij)
    (finitePhysicalMean_nonneg n as b h i) (hb0 j))

end OAI.SKFluctuations.Cavity
