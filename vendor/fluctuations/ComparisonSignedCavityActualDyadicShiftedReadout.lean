module

public import ComparisonSignedCavityDyadicSuffixGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity Set
open scoped NNReal
set_option maxHeartbeats 1000000

def nativeDyadicSourceRetainedIndex (a : ℝ) (ha : 0<a)
    (as : List PositiveMass) (U j : ℕ) : ℕ :=
  if j=0 then U else nativeDyadicRetainedIndex a ha as j

def nativeDyadicShiftedRetainedIndex (a : ℝ) (ha : 0<a)
    (as : List PositiveMass) (U star j : ℕ) : ℕ :=
  nativeDyadicSourceRetainedIndex a ha as U j-star

structure NativeDyadicShiftedRetainedReadout {ι : Type*}
    (a : ℝ) (ha : 0<a) (as pre mid tail : List PositiveMass) (U : ℕ)
    (q : ℕ→ι→ℝ≥0) : Prop where
  source_mass : partitionPoint (partitionPoint 0 as (pre.length+mid.length)) tail
    (U-(pre.length+mid.length))=a
  first_virtual : (nativeDyadicMassCut a ha 0).val=
    partitionPoint (partitionPoint 0 as (pre.length+mid.length)) tail (U-(pre.length+mid.length))/2
  first_physical : (nativeDyadicMassCut a ha 1).val=a
  last_mass : (nativeDyadicMassCut a ha (nativeDyadicCutDepth a)).val=1
  first_index : nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) 0=
    U-(pre.length+mid.length)
  source_index_le : U-(pre.length+mid.length)≤tail.length
  index_le : ∀j≤nativeDyadicCutDepth a,
    nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) j≤tail.length
  source_le_index : ∀j≤nativeDyadicCutDepth a,
    U-(pre.length+mid.length)≤nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) j
  original_source_le : ∀j≤nativeDyadicCutDepth a,U≤nativeDyadicSourceRetainedIndex a ha as U j
  original_index_le : ∀j≤nativeDyadicCutDepth a,nativeDyadicSourceRetainedIndex a ha as U j≤as.length
  add_shift : ∀j≤nativeDyadicCutDepth a,
    pre.length+mid.length+nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) j=
      nativeDyadicSourceRetainedIndex a ha as U j
  exact_mass : ∀j,1≤j→j≤nativeDyadicCutDepth a→
    partitionPoint (partitionPoint 0 as (pre.length+mid.length)) tail
      (nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) j)=
        (nativeDyadicMassCut a ha j).val
  lower_mass : ∀j≤nativeDyadicCutDepth a,
    (nativeDyadicMassCut a ha j).val≤
      partitionPoint 0 as (nativeDyadicSourceRetainedIndex a ha as U j)
  prefix_mass : ∀j,1≤j→j≤nativeDyadicCutDepth a→
    ∀s∈(clockSteps tail (fun k=>q (pre.length+mid.length+k))).take
      (nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) j),
      s.1≤(nativeDyadicMassCut a ha j).val
  source_prefix_mass : ∀j,1≤j→j≤nativeDyadicCutDepth a→
    ∀s∈(clockSteps tail (fun k=>q (pre.length+mid.length+k))).take (U-(pre.length+mid.length)),
      s.1≤(nativeDyadicMassCut a ha j).val
  index_monotone : ∀j k,j≤k→k≤nativeDyadicCutDepth a→
    nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) j≤
      nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length) k
  terminal_index : nativeDyadicShiftedRetainedIndex a ha as U (pre.length+mid.length)
    (nativeDyadicCutDepth a)=tail.length
  clock_suffix : clockSteps tail (fun k=>q (pre.length+mid.length+k))=
    (clockSteps as q).drop (pre.length+mid.length)
  comparable : ∀j<nativeDyadicCutDepth a,
    (nativeDyadicMassCut a ha (j+1)).val≤2*(nativeDyadicMassCut a ha j).val
  cut_monotone : Monotone (fun j=>(nativeDyadicMassCut a ha j).val)

theorem NativeDyadicRetainedReadout.shifted_two_level {ι : Type*}
    {a : ℝ} {ha : 0<a} {as : List PositiveMass} {U : ℕ}
    (H : NativeDyadicRetainedReadout a ha as U) (ho : MassOrdered 0 as)
    (pre mid tail : List PositiveMass) (hcut : pre++(mid++tail)=as)
    (hstar : pre.length+mid.length<U) (hU : U≤as.length) (q : ℕ→ι→ℝ≥0) :
    NativeDyadicShiftedRetainedReadout a ha as pre mid tail U q := by
  let star:=pre.length+mid.length
  have hcut' : (pre++mid)++tail=as:=by simpa only [List.append_assoc] using hcut
  have hlength : as.length=star+tail.length:=by
    rw [←hcut,List.length_append,List.length_append]
    dsimp only [star]
    omega
  have hshift (k : ℕ) (hk : star≤k) :
      partitionPoint (partitionPoint 0 as star) tail (k-star)=partitionPoint 0 as k:=by
    simpa only [List.length_append] using native_partitionPoint_suffix_readout as (pre++mid) tail hcut' k
      (by simpa only [List.length_append] using hk)
  have hsource : partitionPoint (partitionPoint 0 as star) tail (U-star)=a:=by
    rw [hshift U hstar.le,H.literal_source_mass]
  have hindex (j : ℕ) (hj : j≤nativeDyadicCutDepth a) :
      U≤nativeDyadicSourceRetainedIndex a ha as U j ∧
      nativeDyadicSourceRetainedIndex a ha as U j≤as.length:=by
    by_cases hz : j=0
    · simp only [nativeDyadicSourceRetainedIndex,hz,ite_true]
      exact ⟨le_rfl,hU⟩
    · simp only [nativeDyadicSourceRetainedIndex,hz,ite_false]
      exact ⟨H.source_index j (by omega) hj,H.index_le_length j⟩
  have hposindex (j : ℕ) (hj : 1≤j) :
      nativeDyadicSourceRetainedIndex a ha as U j=nativeDyadicRetainedIndex a ha as j:=by
    simp only [nativeDyadicSourceRetainedIndex,show j≠0 by omega,ite_false]
  refine ⟨hsource,?_,H.first_physical,H.terminal_mass,?_,?_,?_,?_,
    fun j hj=>(hindex j hj).1,fun j hj=>(hindex j hj).2,?_,?_,?_,?_,?_,?_,?_,?_,
    H.comparable,H.cut_monotone⟩
  · rw [hsource,H.first_virtual]
  · rfl
  · change U-star≤tail.length
    omega
  · intro j hj
    have HH:=(hindex j hj).2
    dsimp only [nativeDyadicShiftedRetainedIndex]
    change nativeDyadicSourceRetainedIndex a ha as U j-star≤tail.length
    omega
  · intro j hj
    exact Nat.sub_le_sub_right (hindex j hj).1 star
  · intro j hj
    exact Nat.add_sub_of_le (hstar.le.trans (hindex j hj).1)
  · intro j hj hjq
    change partitionPoint (partitionPoint 0 as star) tail
      (nativeDyadicSourceRetainedIndex a ha as U j-star)=_
    rw [hshift _ (hstar.le.trans (hindex j hjq).1),hposindex j hj,H.exact_mass j hjq]
  · intro j hj
    by_cases hz : j=0
    · subst j
      exact H.literal_source_lower
    · rw [hposindex j (by omega),H.exact_mass j hj]
  · intro j hj hjq
    have HH:=native_suffix_clock_prefix_mass_le as (pre++mid) tail ho hcut' q
      (nativeDyadicSourceRetainedIndex a ha as U j)
      (by simpa only [List.length_append] using hstar.le.trans (hindex j hjq).1)
      (nativeDyadicMassCut a ha j).val
      (by rw [hposindex j hj,H.exact_mass j hjq])
    simpa only [List.length_append,nativeDyadicShiftedRetainedIndex] using HH
  · intro j hj _hjq
    have HM : partitionPoint 0 as U≤(nativeDyadicMassCut a ha j).val:=by
      calc
        _=a:=H.literal_source_mass
        _=(nativeDyadicMassCut a ha 1).val:=H.first_physical.symm
        _≤_:=H.cut_monotone hj
    have HH:=native_suffix_clock_prefix_mass_le as (pre++mid) tail ho hcut' q U
      (by simpa only [List.length_append] using hstar.le) (nativeDyadicMassCut a ha j).val HM
    simpa only [List.length_append] using HH
  · intro j k hjk hk
    apply Nat.sub_le_sub_right
    by_cases hz : j=0
    · subst j
      exact (hindex k hk).1
    · rw [hposindex j (by omega),hposindex k (by omega)]
      exact H.index_monotone j k hjk hk
  · change nativeDyadicSourceRetainedIndex a ha as U (nativeDyadicCutDepth a)-star=tail.length
    rw [hposindex _ (nativeDyadicCutDepth_pos a),H.terminal_index,hlength,Nat.add_sub_cancel_left]
  · simpa only [List.length_append] using native_clockSteps_suffix_readout as (pre++mid) tail hcut' q

end OAI.SKFluctuations.LaplaceWindowFormalization
