module

public import ComparisonSignedCavityActualStrongSharpSourceCuts
public import ComparisonSignedCavityActualSharpSourceCutReadout
public import ComparisonSignedCavityActualDyadicRetainedChain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem ActualStrongSharpSourceCutGeometry.retained_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hs : w.star∈as) (hh : high∈as) (hv : outer∈as) :
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star<U ∧ U<V ∧ V ≤ as.length ∧
      partitionPoint 0 as star=w.star.val ∧ partitionPoint 0 as U=high.val ∧ partitionPoint 0 as V=outer.val ∧
      4*W ≤ M.R (partitionPoint 0 as U) ∧
      M.R (partitionPoint 0 as star) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      Cx*M.xs ≤ partitionPoint 0 as U ∧ W ≤ Rmacro/2 := by
  dsimp only
  have Hstar:=nativeRetainedCut_partitionPoint as ho w.star hs
  have Hhigh:=nativeRetainedCut_partitionPoint as ho high hh
  have Houter:=nativeRetainedCut_partitionPoint as ho outer hv
  refine ⟨actual_retained_mass_strict_index as ho w.star high hs hh H.star_lt,
    actual_retained_mass_strict_index as ho high outer hh hv H.high_lt,
    retainedMassPrefixIndex_le_length outer.val as,Hstar,Hhigh,Houter,?_,?_,?_,?_,H.macro_band⟩
  · simpa only [Hhigh] using H.four_band
  · simpa only [Hstar,Hhigh] using H.star_gap
  · simpa only [Hhigh] using H.regular_gap
  · simpa only [Hhigh] using H.source_lower

theorem ActualStrongSharpSourceCutGeometry.finite_net_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (hs : w.star∈us) (hh : high∈us) (hv : outer∈us) (k : ℕ) :
    let as:=finiteCutMasses us k
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star<U ∧ U<V ∧ V ≤ as.length ∧
      partitionPoint 0 as star=w.star.val ∧ partitionPoint 0 as U=high.val ∧ partitionPoint 0 as V=outer.val ∧
      4*W ≤ M.R (partitionPoint 0 as U) ∧
      M.R (partitionPoint 0 as star) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      Cx*M.xs ≤ partitionPoint 0 as U ∧ W ≤ Rmacro/2 :=
  H.retained_readout _ (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_nodes us k hs) (finiteCutMasses_nodes us k hh) (finiteCutMasses_nodes us k hv)

theorem ActualStrongSharpSourceCutGeometry.lower_radius_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    {u : ℝ} (hu : u ≤ w.star.val) :
    M.R u ≤ min (M.R high.val/8) (Rmacro/4) :=
  (comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu).trans H.star_gap

theorem ActualStrongSharpSourceCutGeometry.retained_initial_radius_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hs : w.star∈as) (hh : high∈as)
    (i : ℕ) (hi : i ≤ retainedMassPrefixIndex w.star.val as) :
    M.R (partitionPoint 0 as i) ≤ min
      (M.R (partitionPoint 0 as (retainedMassPrefixIndex high.val as))/8) (Rmacro/4) := by
  have Hmass:partitionPoint 0 as i ≤ w.star.val:=
    (partitionPoint_mono as ho hi).trans_eq (nativeRetainedCut_partitionPoint as ho w.star hs)
  simpa only [nativeRetainedCut_partitionPoint as ho high hh] using H.lower_radius_gap Hmass

theorem ActualStrongSharpSourceCutGeometry.finite_net_initial_radius_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (hs : w.star∈us) (hh : high∈us)
    (k i : ℕ) (hi : i ≤ retainedMassPrefixIndex w.star.val (finiteCutMasses us k)) :
    M.R (partitionPoint 0 (finiteCutMasses us k) i) ≤ min
      (M.R (partitionPoint 0 (finiteCutMasses us k) (retainedMassPrefixIndex high.val (finiteCutMasses us k)))/8) (Rmacro/4) :=
  H.retained_initial_radius_gap _ (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_nodes us k hs) (finiteCutMasses_nodes us k hh) i hi

theorem ActualStrongSharpSourceCutGeometry.exists_dyadic_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (L : ℕ) (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ w.star∈us ∧ high∈us ∧ outer∈us ∧
      (∀j ≤ nativeDyadicCutDepth high.val,nativeDyadicMassCut high.val high.property j∈us) ∧
      (∀u∈uniformMasses L,u∈us) ∧ (∀u∈extra,u∈us) ∧
      ∀k,NativeDyadicRetainedReadout high.val high.property (finiteCutMasses us k)
        (retainedMassPrefixIndex high.val (finiteCutMasses us k)) := by
  have hstar1:w.star.val ≤ 1:=H.star_lt.le.trans (H.high_lt.le.trans H.outer_le_one)
  have hhigh1:high.val ≤ 1:=H.high_lt.le.trans H.outer_le_one
  let more:=w.star::high::outer::extra
  have hmore:∀u∈more,u.val ≤ 1:=by
    intro u hu
    simp only [more,List.mem_cons] at hu
    rcases hu with rfl|rfl|rfl|hu
    · exact hstar1
    · exact hhigh1
    · exact H.outer_le_one
    · exact hextra u hu
  obtain ⟨us,hus,hnodes,hmore',hmesh,Hread⟩:=native_dyadic_chain_exists_common_net high.property hhigh1 L more hmore
  have hs:w.star∈us:=hmore' _ (by simp only [more,List.mem_cons_self])
  have hh:high∈us:=hmore' _ (by simp only [more,List.mem_cons];exact Or.inr (Or.inl trivial))
  have hv:outer∈us:=hmore' _ (by simp only [more,List.mem_cons];exact Or.inr (Or.inr (Or.inl trivial)))
  refine ⟨us,hus,hs,hh,hv,hnodes,hmesh,?_,?_⟩
  · intro u hu
    exact hmore' _ (by simp only [more,List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))
  · intro k
    exact Hread k _ (retainedMassPrefixIndex_le_length high.val _) (nativeRetainedCut_partitionPoint
      _ (finiteCutMasses_ordered us hus k) high (finiteCutMasses_nodes us k hh))

end OAI.SKFluctuations.LaplaceWindowFormalization
