module

public import ComparisonSignedCavityActualCenteredPairMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_rest_centered_pair_eq_decoupled (n l : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h K : ℕ→ℝ)
    (U j : ℕ) (hj : j ≤ as.length) (center : ℝ) :
    (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
      (fun l=>Sum.elim (fun _=>b l) (fun _=>h l))
      (fun σ=>|deletedOverlap n (joinSpin ((ClockTree.pairSpin as j σ).1,false))
        (joinSpin ((ClockTree.pairSpin as j σ).2,false))-center|^(2*l)) 0=
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun l=>Sum.elim (fun _=>b l) (fun _=>h l)) U 0 0 b h K)
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-center|^(2*l)) 0 := by
  let : Nonempty (RestCoordinate n) := ⟨Sum.inr ⟨0,hn⟩⟩
  let T := ClockTree.pairClock (S:=Spin n × Bool) as j
  let s := ClockTree.pairLeftSlot (S:=Spin n × Bool) as j
  let t := ClockTree.pairRightSlot (S:=Spin n × Bool) as j
  let Q := fun σ τ : Spin n => |deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-center|^(2*l)
  let P := fun σ : T.cavityLeft.Assignment =>
    Q (T.cavityLeft.atSlot σ (T.cavityLeftSlot s)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot t))
  have hst : T.cavityLeftSlot s ≠ T.cavityLeftSlot t :=
    fun H => ClockTree.pairSlots_distinct as j (T.cavityLeftSlot.injective H)
  have hsplit : T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot t)=j := by
    rw [ClockTree.cavityLeft_splitIndex]
    exact (ClockTree.pairSlots_splitIndex as j).trans (Nat.min_eq_left hj)
  have HD := native_decoupled_rest_expect n
    (fun l => Sum.elim (fun _ => b l) (fun _ => h l)) U b h K T ho P
  dsimp only [P] at HD
  rw [T.cavityLeft.disorderExpect_pairAtSlot_actual (restWeight_pos n) (restFeature n)
    ho 0 _ 0 _ _ hst Q,hsplit] at HD
  rw [←HD]
  congr 1
  funext σ
  dsimp only [P,Q]
  rw [ClockTree.atSlot_cavityLeft,ClockTree.atSlot_cavityLeft]
  simp only [T,s,t,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot]
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
