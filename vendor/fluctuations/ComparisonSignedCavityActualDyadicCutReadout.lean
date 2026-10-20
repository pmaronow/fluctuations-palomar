module

public import ComparisonSignedCavityActualDyadicCutChain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum Set Filter
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_index_le_retained_prefix_of_mass_le {start u : ℝ}
    (as : List PositiveMass) (ho : MassOrdered start as) (k : ℕ) (hk : k ≤ as.length)
    (hmass : partitionPoint start as k ≤ u) : k ≤ retainedMassPrefixIndex u as := by
  induction as generalizing start k with
  | nil=>simp only [List.length_nil] at hk;omega
  | cons b bs ih=>
    cases k with
    | zero=>exact Nat.zero_le _
    | succ k=>
      have Hmass : partitionPoint b.val bs k ≤ u:=hmass
      have Hb : b.val ≤ u:=((partitionPoint_mem bs ho.2.2 k).1).trans Hmass
      have HI:=ih ho.2.2 k (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hk) Hmass
      simpa only [retainedMassPrefixIndex,retainedMassBefore_cons_le b bs Hb,List.length_cons]
        using Nat.succ_le_succ HI

theorem native_retained_prefix_take_eq (as : List PositiveMass) (u : ℝ) :
    as.take (retainedMassPrefixIndex u as)=retainedMassBefore u as := by
  have H:=congrArg (List.take (retainedMassBefore u as).length) (retainedMass_append u as)
  simpa only [List.take_left,retainedMassPrefixIndex] using H.symm

theorem native_retained_prefix_take_mass_le (as : List PositiveMass) (ho : MassOrdered 0 as)
    (u : PositiveMass) (hu1 : u.val ≤ 1) :
    ∀v∈as.take (retainedMassPrefixIndex u.val as),v.val ≤ u.val := by
  rw [native_retained_prefix_take_eq]
  exact (retainedMass_ordered as ho ⟨u.property.le,hu1⟩ u.property.le).2.2.1

theorem native_retained_prefix_one_eq_length (as : List PositiveMass) (ho : MassOrdered 0 as) :
    retainedMassPrefixIndex 1 as=as.length :=
  le_antisymm (retainedMassPrefixIndex_le_length 1 as)
    (native_index_le_retained_prefix_of_mass_le as ho as.length le_rfl
      (partitionPoint_mem as ho as.length).2)

theorem native_sampleClockSteps_take {ι : Type*} (q : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (start : ℝ) (k : ℕ) :
    (sampleClockSteps q start as).take k=sampleClockSteps q start (as.take k) := by
  induction as generalizing start k with
  | nil=>simp only [sampleClockSteps,List.take_nil]
  | cons b bs ih=>
    cases k with
    | zero=>rfl
    | succ k=>simpa only [sampleClockSteps,List.take_succ_cons] using congrArg (List.cons _) (ih b.val k)

theorem native_sampleClockSteps_mass_le_of_nodes {ι : Type*} (q : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) {u : ℝ} (hnodes : ∀v∈as,v.val ≤ u) (start : ℝ) :
    ∀s∈sampleClockSteps q start as,s.1 ≤ u := by
  induction as generalizing start with
  | nil=>simp only [sampleClockSteps,List.not_mem_nil,forall_false,implies_true]
  | cons b bs ih=>
    intro s hs
    rcases List.mem_cons.mp hs with rfl|hs
    · exact hnodes b List.mem_cons_self
    · exact ih (fun v hv=>hnodes v (List.mem_cons_of_mem _ hv)) b.val s hs

theorem native_retained_prefix_sampled_take_mass_le {ι : Type*} (q : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u : PositiveMass) (hu1 : u.val ≤ 1) :
    ∀s∈(sampleClockSteps q 0 as).take (retainedMassPrefixIndex u.val as),s.1 ≤ u.val := by
  rw [native_sampleClockSteps_take]
  exact native_sampleClockSteps_mass_le_of_nodes q _ (native_retained_prefix_take_mass_le as ho u hu1) 0

def nativeDyadicRetainedIndex (a : ℝ) (ha : 0 < a) (as : List PositiveMass) (j : ℕ) : ℕ :=
  retainedMassPrefixIndex (nativeDyadicMassCut a ha j).val as

theorem nativeDyadicRetainedIndex_readout {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (q : ℕ) (_hq : 1 ≤ q) (hreach : 1 ≤ (2:ℝ)^q*(a/2))
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hret : ∀j ≤ q,nativeDyadicMassCut a ha j∈as)
    (U : ℕ) (hU : U ≤ as.length) (hUa : partitionPoint 0 as U=a) :
    (∀j ≤ q,partitionPoint 0 as (nativeDyadicRetainedIndex a ha as j)=
      (nativeDyadicMassCut a ha j).val) ∧
    (∀j,1 ≤ j → j ≤ q → U ≤ nativeDyadicRetainedIndex a ha as j ∧
      nativeDyadicRetainedIndex a ha as j ≤ as.length) ∧
    (∀j ≤ q,∀v∈as.take (nativeDyadicRetainedIndex a ha as j),v.val ≤ (nativeDyadicMassCut a ha j).val) ∧
    (∀j k,j ≤ k → k ≤ q → nativeDyadicRetainedIndex a ha as j ≤ nativeDyadicRetainedIndex a ha as k) ∧
    nativeDyadicRetainedIndex a ha as q=as.length := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j hj
    exact nativeRetainedCut_partitionPoint as ho _ (hret j hj)
  · intro j hj1 _hjq
    refine ⟨native_index_le_retained_prefix_of_mass_le as ho U hU ?_,retainedMassPrefixIndex_le_length _ _⟩
    rw [hUa]
    simpa only [nativeDyadicMassCut_one ha ha1] using nativeDyadicMassCut_monotone ha hj1
  · intro j _
    exact native_retained_prefix_take_mass_le as ho _ (nativeDyadicMassCut_le_one ha j)
  · intro j k hjk hk
    exact retainedMassPrefixIndex_monotone as ho _ _ (hret j (hjk.trans hk)) (hret k hk)
      (nativeDyadicMassCut_monotone ha hjk)
  · unfold nativeDyadicRetainedIndex
    rw [nativeDyadicMassCut_terminal ha q hreach,native_retained_prefix_one_eq_length as ho]

theorem nativeDyadicRetainedIndex_old_index_lt {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i U j : ℕ} (hi : i < U) (hU : U ≤ as.length) (hUa : partitionPoint 0 as U=a) (hj : 1 ≤ j) :
    i < nativeDyadicRetainedIndex a ha as j := by
  apply hi.trans_le (native_index_le_retained_prefix_of_mass_le as ho U hU _)
  rw [hUa]
  simpa only [nativeDyadicMassCut_one ha ha1] using nativeDyadicMassCut_monotone ha hj

end OAI.SKFluctuations.LaplaceWindowFormalization
