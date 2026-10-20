module

public import ComparisonSignedCavityActualRestStarFinalNet
public import ComparisonSignedCavityFullSquareRawBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_full_decoupled_centered_pair_eq_rest (n l : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (U : ℕ) (j : ℕ) (hj : j≤as.length) (S : ℝ) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h 0 0)
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-S|^(2*l)) 0=
      nativeOriginalRestCenteredMoment n l as b h j S := by
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
    U b h (finitePhysicalMixedClock (n+1) as b h) T ho P
  dsimp only [P] at HD
  rw [T.cavityLeft.disorderExpect_pairAtSlot_actual (restWeight_pos n) (restFeature n)
    ho 0 _ 0 _ _ hst Q,hsplit] at HD
  dsimp only [nativeOriginalRestCenteredMoment]
  rw [←HD]
  congr 1
  funext σ
  dsimp only [Q]
  rw [ClockTree.atSlot_cavityLeft,ClockTree.atSlot_cavityLeft]
  simp only [T,s,t,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot]
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
