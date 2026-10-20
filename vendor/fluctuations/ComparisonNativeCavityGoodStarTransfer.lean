module

public import ComparisonNativeCavityRadiusGoodPoint
public import ComparisonSignedCavityActualNaturalBoundaryBudget
public import CavityPhysicalRawCentering
public import PhysicalBPathLimit
public import RetainedWindowGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

def nativeRetainedPairValue (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (u : ℝ) (P : Spin (n+1)→Spin (n+1)→ℝ) : ℝ :=
  let b := fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h := fun j=>(hf (partitionPoint 0 as j):ℝ)
  let cut := retainedMassPrefixIndex u as
  (ClockTree.pairClock as cut).disorderExpect (uniformWeight (n+1))
    (finiteFeature (n+1)) 0 (physicalCompletedClock (n+1) b h)
    (fun σ=>P (ClockTree.pairSpin as cut σ).1 (ClockTree.pairSpin as cut σ).2) 0

def nativeRetainedCenteredMoment (n l : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (u center : ℝ) : ℝ :=
  nativeRetainedPairValue n bf hf as u
    (fun σ τ=>|orderedOverlap (n+1) σ τ-center|^(2*l))

theorem nativeRetainedPairValue_eq_stepPairMoment (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u : ℝ)
    (P : Spin (n+1)→Spin (n+1)→ℝ) :
    nativeRetainedPairValue n bf hf as u P=
      stepPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) bf hf 0)
        (sampleClockSteps (completedPathClock (n+1) bf hf) 0 as)
        (sampleClockSteps_ordered _ as ho).mem_pos P u := by
  unfold stepPairMoment
  rw [massStepFunction_split_index,sampleClockSteps_masses,
    retainedMass_splitClockSteps_length,actual_sampled_completed_clock_eq (n+1) bf hf hb hh as ho]
  rfl

theorem nativeRetainedPairValue_tendsto (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1)
    (u : PositiveMass) (hu : u∈us) (P : Spin (n+1)→Spin (n+1)→ℝ) :
    Tendsto (fun j=>nativeRetainedPairValue n bf hf (finiteCutMasses us j) u.val P)
      atTop (𝓝 (orderedPathPair (n+1) bf hf P u.val)) := by
  have H:=retainedMoment_tendsto_all (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) bf hf) (completedPathClock_monotone (n+1) hb hh)
    (finiteCutMasses us) (fun j=>(((j+1:ℕ):ℝ))⁻¹)
    (finiteCutMasses_ordered us hus) (finiteCutMasses_mesh us hus)
    (finiteCutMasses_end us hus) uniformMasses_mesh_tendsto u (hus u hu)
    (fun j=>finiteCutMasses_nodes us j hu) P
  simp_rw [←nativeRetainedPairValue_eq_stepPairMoment n bf hf hb hh
    _ (finiteCutMasses_ordered us hus _)] at H
  rw [←orderedPathPair_eq_completed (n+1) (by omega) bf hf hb hh P ⟨u.property,hus u hu⟩] at H
  exact H

theorem nativeRetainedCenteredMoment_one_eq (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u center : ℝ) :
    nativeRetainedCenteredMoment n 1 bf hf as u center=
      nativeRetainedPairValue n bf hf as u (fun σ τ=>(orderedOverlap (n+1) σ τ)^2)-
      2*center*nativeRetainedPairValue n bf hf as u (orderedOverlap (n+1))+center^2 := by
  let b := fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h := fun j=>(hf (partitionPoint 0 as j):ℝ)
  let cut := retainedMassPrefixIndex u as
  let T := ClockTree.pairClock (S:=Spin (n+1)) as cut
  let q := physicalCompletedClock (n+1) b h
  have hw := T.disorderWeight_probability (uniformWeight_pos (n+1))
    (finiteFeature (n+1)) ho 0 q 0
  unfold nativeRetainedCenteredMoment nativeRetainedPairValue ClockTree.disorderExpect
  simp only [Nat.mul_one,sq_abs]
  have he (σ : T.Assignment) :
      T.disorderWeight (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q σ 0*
        (orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
          (ClockTree.pairSpin as cut σ).2-center)^2=
      T.disorderWeight (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q σ 0*
        (orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
          (ClockTree.pairSpin as cut σ).2)^2-
      (2*center)*(T.disorderWeight (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q σ 0*
        orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
          (ClockTree.pairSpin as cut σ).2)+
      center^2*T.disorderWeight (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q σ 0 := by ring
  change (∑σ : T.Assignment,
    T.disorderWeight (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q σ 0*
      (orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
        (ClockTree.pairSpin as cut σ).2-center)^2)=_
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,hw.2]
  ring

theorem nativeRetainedCenteredMoment_one_tendsto (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>nativeRetainedCenteredMoment n 1 bf hf (finiteCutMasses us j)
      u.val (orderedPathS (n+1) bf hf u.val)) atTop
      (𝓝 (orderedPathB (n+1) bf hf u.val-(orderedPathS (n+1) bf hf u.val)^2)) := by
  have HB:=nativeRetainedPairValue_tendsto n bf hf hb hh us hus u hu
    (fun σ τ=>(orderedOverlap (n+1) σ τ)^2)
  have HS:=nativeRetainedPairValue_tendsto n bf hf hb hh us hus u hu (orderedOverlap (n+1))
  have H:=(HB.sub (HS.const_mul (2*orderedPathS (n+1) bf hf u.val))).add_const
    ((orderedPathS (n+1) bf hf u.val)^2)
  simp_rw [←nativeRetainedCenteredMoment_one_eq n bf hf _
    (finiteCutMasses_ordered us hus _) u.val (orderedPathS (n+1) bf hf u.val)] at H
  have he : orderedPathB (n+1) bf hf u.val-2*orderedPathS (n+1) bf hf u.val*
      orderedPathS (n+1) bf hf u.val+(orderedPathS (n+1) bf hf u.val)^2=
      orderedPathB (n+1) bf hf u.val-(orderedPathS (n+1) bf hf u.val)^2 := by ring
  change Tendsto _ _ (𝓝 (orderedPathB (n+1) bf hf u.val-2*orderedPathS (n+1) bf hf u.val*orderedPathS (n+1) bf hf u.val+
    (orderedPathS (n+1) bf hf u.val)^2)) at H
  rw [he] at H
  exact H

theorem nativeRetainedPairValue_overlap_eq_finitePhysicalMean (n : ℕ)
    (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as) (u : ℝ) :
    nativeRetainedPairValue n bf hf as u (orderedOverlap (n+1))=
      finitePhysicalMean (n+1) as (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (fun j=>(hf (partitionPoint 0 as j):ℝ)) (retainedMassPrefixIndex u as) := by
  rw [finitePhysicalMean_eq_actual_pair (n+1) ho _ _ _
    (retainedMassPrefixIndex_le_length u as)]
  rfl

theorem nativeRetainedFinitePhysicalMean_tendsto (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>
      let as:=finiteCutMasses us j
      finitePhysicalMean (n+1) as (fun k=>(bf (partitionPoint 0 as k):ℝ))
        (fun k=>(hf (partitionPoint 0 as k):ℝ)) (retainedMassPrefixIndex u.val as))
      atTop (𝓝 (orderedPathS (n+1) bf hf u.val)) := by
  have H:=nativeRetainedPairValue_tendsto n bf hf hb hh us hus u hu (orderedOverlap (n+1))
  simp_rw [nativeRetainedPairValue_overlap_eq_finitePhysicalMean n bf hf _
    (finiteCutMasses_ordered us hus _) u.val] at H
  exact H

theorem nativeRetainedCut_partitionPoint (as : List PositiveMass)
    (ho : MassOrdered 0 as) (u : PositiveMass) (hu : u∈as) :
    partitionPoint 0 as (retainedMassPrefixIndex u.val as)=u.val := by
  have H:=physicalCutMass_retained_prefix (fun _ _ : ℝ=> (0:ℝ≥0)) as ho u hu
  rw [physicalCutMass_sampleClockSteps _ 0 as _ (retainedMassPrefixIndex_le_length u.val as)] at H
  exact H

theorem nativeRetainedFinitePhysicalMixedClock_tendsto (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>
      let as:=finiteCutMasses us j
      finitePhysicalMixedClock (n+1) as (fun k=>(bf (partitionPoint 0 as k):ℝ))
        (fun k=>(hf (partitionPoint 0 as k):ℝ)) (retainedMassPrefixIndex u.val as))
      atTop (𝓝 ((hf u.val:ℝ)+(bf u.val:ℝ)*orderedPathS (n+1) bf hf u.val)) := by
  have H:=(nativeRetainedFinitePhysicalMean_tendsto n bf hf hb hh us hus u hu).const_mul (bf u.val:ℝ)
  have H':=H.const_add (hf u.val:ℝ)
  convert H' using 1
  funext j
  dsimp only [finitePhysicalMixedClock]
  rw [nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus j) u
    (finiteCutMasses_nodes us j hu)]

theorem nativeRetainedCenteredMoment_interpolation_sq (n l : ℕ) (hl : 0<l)
    (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as) (u center : ℝ) :
    (nativeRetainedCenteredMoment n l bf hf as u center)^2≤
      nativeRetainedCenteredMoment n 1 bf hf as u center*
        nativeRetainedCenteredMoment n (2*l-1) bf hf as u center := by
  let cut:=retainedMassPrefixIndex u as
  let T:=ClockTree.pairClock (S:=Spin (n+1)) as cut
  let q:=physicalCompletedClock (n+1) (fun j=>(bf (partitionPoint 0 as j):ℝ))
    (fun j=>(hf (partitionPoint 0 as j):ℝ))
  let Z:=fun σ:T.Assignment=>|orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
    (ClockTree.pairSpin as cut σ).2-center|
  have H:=T.disorderExpect_mul_sq_le (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    ho 0 q Z (fun σ=>(Z σ)^(2*l-1)) 0
  have he1 : (fun σ:T.Assignment=>Z σ*(Z σ)^(2*l-1))=(fun σ=>(Z σ)^(2*l)) := by
    funext σ
    rw [←pow_succ']
    congr 1
    omega
  have he2 : (fun σ:T.Assignment=>((Z σ)^(2*l-1))^2)=(fun σ=>(Z σ)^(2*(2*l-1))) := by
    funext σ
    rw [←pow_mul]
    congr 1
    omega
  rw [he1,he2] at H
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
