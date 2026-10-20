module

public import CavityScalarObservedBound
public import CavitySignedWeightedIncomingMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {S : Type*} [Fintype S] [Nonempty S]

def singlePrefixAttachments : (pre tail : List PositiveMass) → ℝ →
    List (MarkedPlacement (single (S := S) (pre++tail)))
  | [],_,_ => []
  | m::pre,tail,a => MarkedPlacement.fresh (single ((m::pre)++tail)) (a-m.val)::
      (singlePrefixAttachments pre tail m.val).map (MarkedPlacement.step m)

def MarkedPlacement.prependSingle : (pre tail : List PositiveMass) →
    MarkedPlacement (single (S := S) tail) →
    MarkedPlacement (single (S := S) (pre++tail))
  | [],_,p => p
  | m::pre,tail,p => (MarkedPlacement.prependSingle pre tail p).step m

theorem single_markedAttach_append (pre tail : List PositiveMass) (a : ℝ) :
    (single (S := S) (pre++tail)).markedAttach a=
      singlePrefixAttachments pre tail a++
        ((single tail).markedAttach (partitionEnd a pre)).map
          (MarkedPlacement.prependSingle pre tail) := by
  induction pre generalizing a with
  | nil => simp [singlePrefixAttachments,MarkedPlacement.prependSingle,partitionEnd]
  | cons m pre ih =>
    simp only [List.cons_append,single,markedAttach,partitionEnd,
      singlePrefixAttachments,MarkedPlacement.prependSingle]
    rw [ih,List.map_append,List.map_map]
    rfl

theorem single_prefix_attachment_variation (pre tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++tail)) :
    ((singlePrefixAttachments (S := S) pre tail a).map fun p=>|p.coeff|).sum=
      partitionEnd a pre-a := by
  induction pre generalizing a with
  | nil => simp [singlePrefixAttachments,partitionEnd]
  | cons m pre ih =>
    simp only [List.cons_append] at ho
    simp only [singlePrefixAttachments,List.cons_append,single,List.map_cons,List.sum_cons,List.map_map,
      MarkedPlacement.fresh,MarkedPlacement.step,Function.comp_def]
    rw [abs_of_nonpos (sub_nonpos.mpr ho.2.1)]
    change -(a-m.val)+((singlePrefixAttachments (S := S) pre tail m.val).map fun p=>|p.coeff|).sum=_
    rw [ih ho.2.2]
    simp only [partitionEnd]
    ring

theorem single_prefix_attachment_noncoincident (pre tail : List PositiveMass) (a : ℝ)
    (p : MarkedPlacement (single (S := S) (pre++tail)))
    (hp : p∈singlePrefixAttachments pre tail a) :
    p.embed (singleSlot (pre++tail))≠p.mark := by
  induction pre generalizing a with
  | nil => simp [singlePrefixAttachments] at hp
  | cons m pre ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · simp [MarkedPlacement.fresh,singleSlot]
    · obtain ⟨z,hz,hpz⟩ := List.mem_map.mp hp
      subst p
      exact ih m.val z hz

theorem single_prefix_attachment_split (pre tail : List PositiveMass) (a : ℝ)
    (p : MarkedPlacement (single (S := S) (pre++tail)))
    (hp : p∈singlePrefixAttachments pre tail a) :
    p.tree.splitIndex (p.embed (singleSlot (pre++tail))) p.mark<pre.length := by
  induction pre generalizing a with
  | nil => simp [singlePrefixAttachments] at hp
  | cons m pre ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · simp [MarkedPlacement.fresh,splitIndex]
    · obtain ⟨z,hz,hpz⟩ := List.mem_map.mp hp
      subst p
      have hs:=ih m.val z hz
      change 1+z.tree.splitIndex (z.embed (singleSlot (pre++tail))) z.mark<pre.length+1
      omega

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations
open Hierarchy Cavity LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem scalar_single_prefix_gamma_weight_le (pre tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++tail)) (hroot : MassOrdered 0 (pre++tail))
    (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0=0) {C v : ℝ}
    (hC : 0 ≤ C) (hv : 0 ≤ v) (hclock : q pre.length≤C*v) :
    ((ClockTree.singlePrefixAttachments (S := Bool) pre tail a).map fun p=>|p.coeff| *
      |scalarPlacementGamma ((ClockTree.single (S := Bool) (pre++tail)).realize (scalarClockIncrements q))
        ((ClockTree.single (S := Bool) (pre++tail)).slotEquiv (scalarClockIncrements q)
          (ClockTree.singleSlot (S := Bool) (pre++tail))) (p.realize (scalarClockIncrements q)) 0|).sum ≤
      C*v*(partitionEnd a pre-a) := by
  have hb : ∀ p∈ClockTree.singlePrefixAttachments (S := Bool) pre tail a,
      |scalarPlacementGamma ((ClockTree.single (S := Bool) (pre++tail)).realize (scalarClockIncrements q))
        ((ClockTree.single (S := Bool) (pre++tail)).slotEquiv (scalarClockIncrements q)
          (ClockTree.singleSlot (S := Bool) (pre++tail))) (p.realize (scalarClockIncrements q)) 0|≤C*v := by
    intro p hp
    apply scalarPlacementGamma_realized_abs_le (ClockTree.single (S := Bool) (pre++tail)) hroot q hq hq0
      (ClockTree.singleSlot (S := Bool) (pre++tail)) p
      (ClockTree.single_prefix_attachment_noncoincident pre tail a p hp)
    exact (hq (ClockTree.single_prefix_attachment_split pre tail a p hp).le).trans hclock
  have ht : ((ClockTree.singlePrefixAttachments (S := Bool) pre tail a).map fun p=>|p.coeff| *
      |scalarPlacementGamma ((ClockTree.single (S := Bool) (pre++tail)).realize (scalarClockIncrements q))
        ((ClockTree.single (S := Bool) (pre++tail)).slotEquiv (scalarClockIncrements q)
          (ClockTree.singleSlot (S := Bool) (pre++tail))) (p.realize (scalarClockIncrements q)) 0|).sum ≤
    ((ClockTree.singlePrefixAttachments (S := Bool) pre tail a).map fun p=>|p.coeff| *(C*v)).sum := by
    apply (le_abs_self _).trans
    simpa only [abs_abs] using ReplicaTree.list_weighted_absolute_bound
      (ClockTree.singlePrefixAttachments (S := Bool) pre tail a)
      (fun p=>|p.coeff|)
      (fun p=>|scalarPlacementGamma
        ((ClockTree.single (S := Bool) (pre++tail)).realize (scalarClockIncrements q))
        ((ClockTree.single (S := Bool) (pre++tail)).slotEquiv (scalarClockIncrements q)
          (ClockTree.singleSlot (S := Bool) (pre++tail))) (p.realize (scalarClockIncrements q)) 0|)
      (fun _=>C*v) (fun p hp=>by simpa only [abs_abs] using hb p hp)
  apply ht.trans_eq
  rw [List.sum_map_mul_right,ClockTree.single_prefix_attachment_variation pre tail ho]
  ring

theorem scalar_single_prefix_gamma_weight_le_square (pre tail : List PositiveMass)
    (ho : MassOrdered 0 (pre++tail)) (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0=0)
    {C v : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) (hclock : q pre.length≤C*v)
    (hmass : partitionEnd 0 pre≤v) :
    ((ClockTree.singlePrefixAttachments (S := Bool) pre tail 0).map fun p=>|p.coeff| *
      |scalarPlacementGamma ((ClockTree.single (S := Bool) (pre++tail)).realize (scalarClockIncrements q))
        ((ClockTree.single (S := Bool) (pre++tail)).slotEquiv (scalarClockIncrements q)
          (ClockTree.singleSlot (S := Bool) (pre++tail))) (p.realize (scalarClockIncrements q)) 0|).sum ≤ C*v^2 := by
  apply (scalar_single_prefix_gamma_weight_le pre tail ho ho q hq hq0 hC hv hclock).trans
  simpa only [sub_zero,pow_two,mul_assoc] using mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hv)

end OAI.SKFluctuations
