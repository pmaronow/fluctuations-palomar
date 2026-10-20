module

public import CavityScalarRowBridge
public import CavityDiagonalCancellation

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators Topology NNReal
variable {S : Type*} [Fintype S] [Nonempty S]
attribute [local instance] Classical.propDecidable

def scalarTopology : {as : List PositiveMass} → ClockTree S as → ClockTree Bool as
  | _,.leaf => .leaf
  | _,.step b T => (scalarTopology T).step b
  | _,.fork T V => (scalarTopology T).fork (scalarTopology V)

def scalarTopologySlot : {as : List PositiveMass} → (T : ClockTree S as) →
    T.Slot ≃ (scalarTopology T).Slot
  | _,.leaf => Equiv.refl _
  | _,.step _ T => scalarTopologySlot T
  | _,.fork T V => (scalarTopologySlot T).sumCongr (scalarTopologySlot V)

def firstSlot : {as : List PositiveMass} → (T : ClockTree S as) → T.Slot
  | _,.leaf => ()
  | _,.step _ T => firstSlot T
  | _,.fork T _ => Sum.inl (firstSlot T)

theorem scalarTopology_single (as : List PositiveMass) :
    scalarTopology (single (S:=S) as)=single (S:=Bool) as := by
  induction as with
  | nil => rfl
  | cons b bs ih => simp only [single,scalarTopology,ih]

theorem scalarTopology_splitIndex {as : List PositiveMass} (T : ClockTree S as)
    (s t : T.Slot) :
    (scalarTopology T).splitIndex (scalarTopologySlot T s) (scalarTopologySlot T t)=
      T.splitIndex s t := by
  induction T with
  | leaf => rfl
  | step b T ih => exact congrArg (1+·) (ih s t)
  | fork T V ihT ihV => cases s <;> cases t <;>
      first | rfl | exact ihT _ _ | exact ihV _ _

theorem scalarTopologySlot_fork_inl {as : List PositiveMass} (T V : ClockTree S as)
    (s : T.Slot) : scalarTopologySlot (T.fork V) (.inl s)=.inl (scalarTopologySlot T s) := rfl

theorem scalarTopologySlot_fork_inr {as : List PositiveMass} (T V : ClockTree S as)
    (s : V.Slot) : scalarTopologySlot (T.fork V) (.inr s)=.inr (scalarTopologySlot V s) := rfl

theorem MarkedPlacement.hit_step {as : List PositiveMass} {T : ClockTree S as}
    (b : PositiveMass) (p : MarkedPlacement T) (s : T.Slot) :
    (MarkedPlacement.step b p).hit s=p.hit s := rfl

theorem MarkedPlacement.hit_left_inl {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (s : T.Slot) :
    (MarkedPlacement.left V p).hit (.inl s)=p.hit s := by
  simp [MarkedPlacement.hit,MarkedPlacement.left]

theorem MarkedPlacement.hit_left_inr {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (s : V.Slot) :
    (MarkedPlacement.left V p).hit (.inr s)=0 := by
  simp [MarkedPlacement.hit,MarkedPlacement.left]

theorem MarkedPlacement.hit_right_inl {as : List PositiveMass} (T : ClockTree S as)
    {V : ClockTree S as} (p : MarkedPlacement V) (s : T.Slot) :
    (MarkedPlacement.right T p).hit (.inl s)=0 := by
  simp [MarkedPlacement.hit,MarkedPlacement.right]

theorem MarkedPlacement.hit_right_inr {as : List PositiveMass} (T : ClockTree S as)
    {V : ClockTree S as} (p : MarkedPlacement V) (s : V.Slot) :
    (MarkedPlacement.right T p).hit (.inr s)=p.hit s := by
  simp [MarkedPlacement.hit,MarkedPlacement.right]

theorem markedAttach_scalar_topology_fold {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (F : ℕ→ℝ→ℝ) :
    ((T.markedAttach a).map (fun (p : MarkedPlacement T)=>p.coeff*
      F (p.tree.splitIndex (p.embed s) p.mark) (p.hit s))).sum =
    (((scalarTopology T).markedAttach a).map (fun (p : MarkedPlacement (scalarTopology T))=>
      p.coeff*F (p.tree.splitIndex (p.embed (scalarTopologySlot T s)) p.mark)
        (p.hit (scalarTopologySlot T s)))).sum := by
  induction T generalizing a F with
  | leaf => cases s; simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.coincide,
      scalarTopology,scalarTopologySlot,splitIndex,MarkedPlacement.hit]
  | @step b bs T ih =>
    simp only [markedAttach,scalarTopology,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_def,MarkedPlacement.hit_fresh,MarkedPlacement.hit_step]
    change (a-b.val)*F 0 0+_=(a-b.val)*F 0 0+_
    exact congrArg ((a-b.val)*F 0 0+·) (ih b.val s (fun j d=>F (1+j) d))
  | @fork bs T V ihT ihV =>
    cases s with
    | inl s =>
      change _ = ((((scalarTopology T).fork (scalarTopology V)).markedAttach a).map
        (fun p=>p.coeff*F (p.tree.splitIndex (p.embed (.inl (scalarTopologySlot T s))) p.mark)
          (p.hit (.inl (scalarTopologySlot T s))))).sum
      have hR : ((V.markedAttach a).map (fun p=>p.coeff*F 0 0)).sum=a*F 0 0 := by
        rw [List.sum_map_mul_right,V.markedAttach_mass]
      have hsR : (((scalarTopology V).markedAttach a).map
          (fun p=>p.coeff*F 0 0)).sum=a*F 0 0 := by
        rw [List.sum_map_mul_right,(scalarTopology V).markedAttach_mass]
      simp only [markedAttach,scalarTopology,List.map_cons,List.sum_cons,List.map_append,
        List.sum_append,List.map_map,Function.comp_def,scalarTopologySlot_fork_inl,
        MarkedPlacement.hit_fresh,MarkedPlacement.hit_left_inl,MarkedPlacement.hit_right_inl]
      simp only [MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        splitIndex,Sum.map_inl,id_eq,Sum.elim_inl,Sum.elim_inr,hR,hsR]
      rw [ihT a s F]
    | inr s =>
      change _ = ((((scalarTopology T).fork (scalarTopology V)).markedAttach a).map
        (fun p=>p.coeff*F (p.tree.splitIndex (p.embed (.inr (scalarTopologySlot V s))) p.mark)
          (p.hit (.inr (scalarTopologySlot V s))))).sum
      have hL : ((T.markedAttach a).map (fun p=>p.coeff*F 0 0)).sum=a*F 0 0 := by
        rw [List.sum_map_mul_right,T.markedAttach_mass]
      have hsL : (((scalarTopology T).markedAttach a).map
          (fun p=>p.coeff*F 0 0)).sum=a*F 0 0 := by
        rw [List.sum_map_mul_right,(scalarTopology T).markedAttach_mass]
      simp only [markedAttach,scalarTopology,List.map_cons,List.sum_cons,List.map_append,
        List.sum_append,List.map_map,Function.comp_def,scalarTopologySlot_fork_inr,
        MarkedPlacement.hit_fresh,MarkedPlacement.hit_left_inr,MarkedPlacement.hit_right_inr]
      simp only [MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        splitIndex,Sum.map_inr,id_eq,Sum.elim_inl,Sum.elim_inr,hL,hsL]
      rw [ihV a s F]

end OAI.SKFluctuations.Hierarchy.ClockTree
