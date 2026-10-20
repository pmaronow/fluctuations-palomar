module

public import ComparisonSignedCavityActualResourceTerminalMoments
public import ComparisonSignedCavityLowAllocation
public import ComparisonNativeCavityGoodStarTransfer

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeOriginalRestCenteredMoment (n l : ℕ) (as : List PositiveMass)
    (b h : ℕ → ℝ) (j : ℕ) (center : ℝ) : ℝ :=
  (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
    (fun k=>Sum.elim (fun _=>b k) (fun _=>h k))
    (fun σ=>|deletedOverlap n (joinSpin ((ClockTree.pairSpin as j σ).1,false))
      (joinSpin ((ClockTree.pairSpin as j σ).2,false))-center|^(2*l)) 0

theorem native_original_rest_centered_le_physical_star (n l : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (hb : Monotone b) (hh : Monotone h) (hb0 : ∀j,0≤b j) (hh0 : ∀j,0≤h j)
    (j : ℕ) (hj : j≤as.length) (S : ℝ) :
    let K:=finitePhysicalMixedClock (n+1) as b h
    let q:=physicalCompletedClock (n+1) b h
    nativeOriginalRestCenteredMoment n l as b h j S≤
      Real.exp (220*(K as.length+b as.length+h as.length))*(2:ℝ)^(2*l-1)*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) l
          (diagonalBoundarySteps as (q 0) (fun k=>q (k+1)))
          (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))) id measurable_id j S+
          (1/(n+1:ℕ):ℝ)^(2*l)) := by
  let : Nonempty (RestCoordinate n):=⟨Sum.inr ⟨0,hn⟩⟩
  let T:=ClockTree.pairClock (S:=Spin n×Bool) as j
  let s:=ClockTree.pairLeftSlot (S:=Spin n×Bool) as j
  let t:=ClockTree.pairRightSlot (S:=Spin n×Bool) as j
  let Q:=fun σ τ : Spin n=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-S|^(2*l)
  let P:=fun σ : T.cavityLeft.Assignment=>
    Q (T.cavityLeft.atSlot σ (T.cavityLeftSlot s)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot t))
  have hst : T.cavityLeftSlot s≠T.cavityLeftSlot t :=
    fun H=>ClockTree.pairSlots_distinct as j (T.cavityLeftSlot.injective H)
  have hsplit : T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot t)=j := by
    rw [ClockTree.cavityLeft_splitIndex]
    exact (ClockTree.pairSlots_splitIndex as j).trans (Nat.min_eq_left hj)
  have HD:=native_decoupled_rest_expect n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k))
    0 b h (finitePhysicalMixedClock (n+1) as b h) T ho P
  dsimp only [P] at HD
  rw [T.cavityLeft.disorderExpect_pairAtSlot_actual (restWeight_pos n) (restFeature n)
    ho 0 _ 0 _ _ hst Q,hsplit] at HD
  have H:=cavityPath_pairDeleted_moment_le_physicalStar n l 0 ho
    (show (0:ℝ)∈Icc 0 1 by norm_num) (show (0:ℝ)∈Icc 0 1 by norm_num) hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0) hb0 hh0
    (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) j hj S
  dsimp only [nativeOriginalRestCenteredMoment]
  rw [←HD]
  convert H using 1
  congr 1
  funext σ
  dsimp only [P,Q]
  rw [ClockTree.atSlot_cavityLeft,ClockTree.atSlot_cavityLeft]
  simp only [T,s,t,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot]
  simp [deletedOverlap,joinSpin]

theorem native_original_rest_centered_le_native_retained (n l : ℕ) (hn : 0 < n)
    (bf hf : ℝ → ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as) (u S : ℝ)
    (hb : Monotone (fun j=>(bf (partitionPoint 0 as j):ℝ)))
    (hh : Monotone (fun j=>(hf (partitionPoint 0 as j):ℝ))) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let j:=retainedMassPrefixIndex u as
    let K:=finitePhysicalMixedClock (n+1) as b h
    nativeOriginalRestCenteredMoment n l as b h j S≤
      Real.exp (220*(K as.length+b as.length+h as.length))*(2:ℝ)^(2*l-1)*
        (Real.exp (110*b as.length)*nativeRetainedCenteredMoment n l bf hf as u S+
          (1/(n+1:ℕ):ℝ)^(2*l)) := by
  dsimp only
  have H:=native_original_rest_centered_le_physical_star n l hn ho
    (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ)) hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (retainedMassPrefixIndex u as) (retainedMassPrefixIndex_le_length u as) S
  dsimp only at H
  rw [physicalStarPairMoment_eq_pairDisorder (n+1) l as ho _
    (retainedMassPrefixIndex u as) (retainedMassPrefixIndex_le_length u as) S] at H
  exact H

end OAI.SKFluctuations.Cavity
