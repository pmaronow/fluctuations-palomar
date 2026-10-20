module

public import ComparisonSignedCavityActualDyadicRetainedChain
public import ComparisonSignedCavitySampledMeanUniform

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity Set
open scoped NNReal
set_option maxHeartbeats 1000000

theorem native_partitionPoint_append_shift (start : ℝ) (pre tail : List PositiveMass) (j : ℕ) :
    partitionPoint start (pre++tail) (pre.length+j)=partitionPoint (partitionEnd start pre) tail j := by
  induction pre generalizing start with
  | nil=>simp only [List.nil_append,List.length_nil,Nat.zero_add,partitionEnd]
  | cons a pre ih=>
    simpa only [List.cons_append,List.length_cons,Nat.succ_add,partitionPoint,partitionValues,
      partitionEnd] using ih a.val

theorem native_partitionPoint_suffix_readout
    (as pre tail : List PositiveMass) (hcut : pre++tail=as)
    (k : ℕ) (hk : pre.length≤k) :
    partitionPoint (partitionPoint 0 as pre.length) tail (k-pre.length)=partitionPoint 0 as k := by
  have H0:=native_partitionPoint_append_shift 0 pre tail 0
  simp only [Nat.add_zero,partitionPoint,partitionValues_zero,id_eq] at H0
  rw [hcut] at H0
  change partitionPoint 0 as pre.length=partitionEnd 0 pre at H0
  rw [H0,←native_partitionPoint_append_shift,hcut,Nat.add_sub_of_le hk]

theorem native_clockSteps_suffix_readout {ι : Type*}
    (as pre tail : List PositiveMass) (hcut : pre++tail=as) (q : ℕ→ι→ℝ≥0) :
    clockSteps tail (fun j=>q (pre.length+j))=(clockSteps as q).drop pre.length := by
  rw [←hcut,clockSteps_append,List.drop_append,length_clockSteps,Nat.sub_self,List.drop_zero,
    List.drop_eq_nil_of_le (by rw [length_clockSteps]),List.nil_append]

theorem native_clockSteps_take_mass_le_of_nodes {ι : Type*}
    (as : List PositiveMass) (q : ℕ→ι→ℝ≥0) (k : ℕ) (u : ℝ)
    (hnodes : ∀v∈as.take k,v.val≤u) :
    ∀s∈(clockSteps as q).take k,s.1≤u := by
  induction as generalizing q k with
  | nil=>simp only [clockSteps,List.take_nil,List.not_mem_nil,forall_false,implies_true]
  | cons a as ih=>
    cases k with
    | zero=>simp only [List.take_zero,List.not_mem_nil,forall_false,implies_true]
    | succ k=>
      intro s hs
      simp only [clockSteps,List.take_succ_cons,List.mem_cons] at hs
      rcases hs with rfl|hs
      · exact hnodes a (by simp only [List.take_succ_cons,List.mem_cons,true_or])
      · exact ih (fun j=>q (j+1)) k (fun v hv=>hnodes v
          (by simp only [List.take_succ_cons,List.mem_cons];exact Or.inr hv)) s hs

theorem native_suffix_clock_prefix_mass_le {ι : Type*}
    (as pre tail : List PositiveMass) (ho : MassOrdered 0 as) (hcut : pre++tail=as)
    (q : ℕ→ι→ℝ≥0) (k : ℕ) (hk : pre.length≤k) (u : ℝ)
    (hmass : partitionPoint 0 as k≤u) :
    ∀s∈(clockSteps tail (fun j=>q (pre.length+j))).take (k-pre.length),s.1≤u := by
  have Hd : as.drop pre.length=tail:=by
    rw [←hcut,List.drop_append,List.drop_eq_nil_of_le le_rfl,Nat.sub_self,List.drop_zero,List.nil_append]
  have Hordered:=(MassOrdered.take_drop_geometry as ho pre.length).2.1
  rw [Hd] at Hordered
  have Hprefix:=(MassOrdered.take_drop_geometry tail Hordered (k-pre.length)).2.2.2
  apply native_clockSteps_take_mass_le_of_nodes
  intro v hv
  have HV:=Hprefix v hv
  rw [native_partitionPoint_suffix_readout as pre tail hcut k hk] at HV
  exact HV.trans hmass

end OAI.SKFluctuations.LaplaceWindowFormalization
