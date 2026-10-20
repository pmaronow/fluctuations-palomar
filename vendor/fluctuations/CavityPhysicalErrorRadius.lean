module

public import CavityPhysicalMixedClock

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 def finitePhysicalCavityVariance (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (t : ℝ) :=
   cutFullVariance n (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) U 0 t b h
     (finitePhysicalMixedClock (n+1) as b h)

 def finitePhysicalHighKernel (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) :=
   ReplicaTree.coordinateProfile (fullFeature n)
     (cutTSlope n U 0 b h (finitePhysicalMixedClock (n+1) as b h))

 def finitePhysicalHighSecond (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
   (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
     (finitePhysicalCavityVariance n U as b h t)
     (fun σ => (finitePhysicalHighKernel n U as b h j
       (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) 0

 def finitePhysicalHighRadius (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
   Real.sqrt (finitePhysicalHighSecond n U as b h t j)

 theorem finitePhysicalHighSecond_nonneg (n U : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (t : ℝ) (j : ℕ) : 0≤finitePhysicalHighSecond n U as b h t j := by
  unfold finitePhysicalHighSecond ClockTree.disorderExpect
  exact Finset.sum_nonneg fun σ _ => mul_nonneg
    (((ClockTree.pairClock as j).disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 _ 0).1 σ)
    (sq_nonneg _)

 theorem finitePhysicalHighRadius_nonneg (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ → ℝ) (t : ℝ) (j : ℕ) : 0≤finitePhysicalHighRadius n U as b h t j :=
   Real.sqrt_nonneg _

 theorem finitePhysicalHighSecond_eq_radius_sq (n U : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (t : ℝ) (j : ℕ) :
    finitePhysicalHighSecond n U as b h t j=(finitePhysicalHighRadius n U as b h t j)^2 :=
   (Real.sq_sqrt (finitePhysicalHighSecond_nonneg n U ho b h t j)).symm

 theorem finitePhysicalHighSecond_le_physicalStar (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j) (j : ℕ) (hj : j≤as.length) :
    let K := finitePhysicalMixedClock (n+1) as b h
    let q := physicalCompletedClock (n+1) b h
    let steps := diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
    let μ := Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
    finitePhysicalHighSecond n U as b h t j ≤
      (b j)^2*Real.exp (220*(K as.length+b as.length+h as.length))*2*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) 1 steps μ id measurable_id j
          (finitePhysicalMean (n+1) as b h j)+(1/(n+1:ℕ):ℝ)^2) := by
  exact cutHighError_pair_second_le_physicalStar n U ho ht b h (finitePhysicalMean (n+1) as b h)
    hb hh (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0)
    hb0 hh0 (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) j hj

end OAI.SKFluctuations.Cavity
