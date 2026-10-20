module

public import ComparisonSignedCavityActualSharpSourceCuts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

theorem actual_retained_mass_strict_index
    (as : List PositiveMass) (ho : MassOrdered 0 as) (a b : PositiveMass)
    (ha : a∈as) (hb : b∈as) (hab : a.val < b.val) :
    retainedMassPrefixIndex a.val as < retainedMassPrefixIndex b.val as := by
  by_contra H
  have Hmass:=partitionPoint_mono as ho (Nat.le_of_not_gt H)
  rw [nativeRetainedCut_partitionPoint as ho a ha,
    nativeRetainedCut_partitionPoint as ho b hb] at Hmass
  linarith

theorem actual_retained_mass_split_before_endpoint
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u : PositiveMass) (hu : u∈as) :
    ∃before after : List PositiveMass,as=before++u::after ∧
      before.length+1=retainedMassPrefixIndex u.val as := by
  have Hend:=retainedMass_endpoint as ho u hu
  rcases List.eq_nil_or_concat (retainedMassBefore u.val as) with Hnil|⟨before,a,Ha⟩
  · rw [Hnil] at Hend
    simp only [partitionEnd] at Hend
    exact False.elim ((ne_of_gt u.property) Hend.symm)
  · have Hau : a=u:=by
      apply Subtype.ext
      simpa only [Ha,List.concat_eq_append,partitionEnd_append,partitionEnd] using Hend
    subst a
    refine ⟨before,retainedMassAfter u.val as,?_,?_⟩
    · have H:=retainedMass_append u.val as
      rw [Ha] at H
      simpa only [List.concat_append] using H.symm
    · simp only [retainedMassPrefixIndex,Ha,List.length_concat]

theorem ActualSharpSourceCutGeometry.retained_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius cFirst cK A)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hs : w.star∈as) (hh : high∈as) (hv : outer∈as) :
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star < U ∧ U < V ∧ V ≤ as.length ∧
      2*cFirst*W ≤ partitionPoint 0 as U ∧
      partitionPoint 0 as star ≤ A*W ∧ partitionPoint 0 as V ≤ A*W ∧
      W ≤ radius ∧ radius ≤ 1 ∧ radius ≤ M.R (partitionPoint 0 as U) ∧
      M.R (partitionPoint 0 as star) ≤ radius/2 ∧ M.z ≤ radius/2 ∧
      cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star ∧
      ∃before after : List PositiveMass,as=before++high::after ∧before.length+1=U := by
  dsimp only
  have Hstar:=nativeRetainedCut_partitionPoint as ho w.star hs
  have Hhigh:=nativeRetainedCut_partitionPoint as ho high hh
  have Houter:=nativeRetainedCut_partitionPoint as ho outer hv
  refine ⟨actual_retained_mass_strict_index as ho w.star high hs hh H.star_lt,
    actual_retained_mass_strict_index as ho high outer hh hv H.high_lt,
    retainedMassPrefixIndex_le_length outer.val as,?_,?_,?_,H.radius_lower,H.radius_upper,
    ?_,?_,H.regular_radius,?_,actual_retained_mass_split_before_endpoint as ho high hh⟩
  · simpa only [Hhigh] using H.first_high
  · rw [Hstar]
    exact H.star_lt.le.trans (H.high_lt.le.trans H.outer_scale)
  · simpa only [Houter] using H.outer_scale
  · simpa only [Hhigh] using H.radius_high
  · simpa only [Hstar] using H.star_radius
  · rw [native_continuum_mixed_clock_retained_eq n M.bf M.hf as ho w.star hs]
    exact H.clock_star

theorem ActualSharpSourceCutGeometry.finite_net_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius cFirst cK A)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (hs : w.star∈us) (hh : high∈us) (hv : outer∈us) (k : ℕ) :
    let as:=finiteCutMasses us k
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star < U ∧ U < V ∧ V ≤ as.length ∧
      2*cFirst*W ≤ partitionPoint 0 as U ∧
      partitionPoint 0 as star ≤ A*W ∧ partitionPoint 0 as V ≤ A*W ∧
      W ≤ radius ∧ radius ≤ 1 ∧ radius ≤ M.R (partitionPoint 0 as U) ∧
      M.R (partitionPoint 0 as star) ≤ radius/2 ∧ M.z ≤ radius/2 ∧
      cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star ∧
      ∃before after : List PositiveMass,as=before++high::after ∧before.length+1=U :=
  H.retained_readout (finiteCutMasses us k) (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_nodes us k hs) (finiteCutMasses_nodes us k hh) (finiteCutMasses_nodes us k hv)

theorem ActualSharpSourceCutGeometry.exists_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius cFirst cK A)
    (L : ℕ) (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ w.star∈us ∧ high∈us ∧ outer∈us ∧
      (∀u∈uniformMasses L,u∈us) ∧ (∀u∈extra,u∈us) := by
  let us:=w.star::high::outer::(uniformMasses L++extra)
  have hstar1 : w.star.val ≤ 1:=H.star_lt.le.trans (H.high_lt.le.trans H.outer_le_one)
  have hhigh1 : high.val ≤ 1:=H.high_lt.le.trans H.outer_le_one
  refine ⟨us,?_,by simp [us],by simp [us],by simp [us],?_,?_⟩
  · intro u hu
    simp only [us,List.mem_cons,List.mem_append] at hu
    rcases hu with rfl|rfl|rfl|hunet|huextra
    · exact hstar1
    · exact hhigh1
    · exact H.outer_le_one
    · exact (uniformMasses_ordered L).members_le_one u hunet
    · exact hextra u huextra
  · intro u hu
    simp only [us,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl hu)))
  · intro u hu
    simp only [us,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr hu)))

end OAI.SKFluctuations.LaplaceWindowFormalization
