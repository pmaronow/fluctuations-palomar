module

public import ComparisonSignedCavityActualSharpSourceCutReadout
public import ComparisonSignedCavityActualStrongSharpSourceCutReadout
public import ComparisonSignedCavityActualRetainedTargetCutGeometry
public import ComparisonSignedCavityActualSourceCutOuterScaleMonotonicity
public import ComparisonSignedCavityActualOriginalTargetCommonNet
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics

@[expose] public section
noncomputable section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualThetaZeroOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

theorem ActualSharpSourceCutGeometry_original_q.retained_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hs : w.star∈as) (hh : high∈as) (hv : outer∈as) :
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star < U ∧ U < V ∧ V ≤ as.length ∧
      2*cFirst*W ≤ partitionPoint 0 as U ∧
      partitionPoint 0 as star ≤ A*W ∧ partitionPoint 0 as V ≤ A*W ∧
      W ≤ radius ∧ radius ≤ 1 ∧ radius ≤ M.sweepRadius (partitionPoint 0 as U) ∧
      M.sweepRadius (partitionPoint 0 as star) ≤ radius/2 ∧ M.z ≤ radius/2 ∧
      cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star ∧
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
  · rw [native_continuum_mixed_clock_retained_eq n M.sweepBf M.sweepHf as ho w.star hs]
    exact H.clock_star

theorem ActualSharpSourceCutGeometry_original_q.finite_net_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (hs : w.star∈us) (hh : high∈us) (hv : outer∈us) (k : ℕ) :
    let as:=finiteCutMasses us k
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star < U ∧ U < V ∧ V ≤ as.length ∧
      2*cFirst*W ≤ partitionPoint 0 as U ∧
      partitionPoint 0 as star ≤ A*W ∧ partitionPoint 0 as V ≤ A*W ∧
      W ≤ radius ∧ radius ≤ 1 ∧ radius ≤ M.sweepRadius (partitionPoint 0 as U) ∧
      M.sweepRadius (partitionPoint 0 as star) ≤ radius/2 ∧ M.z ≤ radius/2 ∧
      cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star ∧
      ∃before after : List PositiveMass,as=before++high::after ∧before.length+1=U :=
  H.retained_readout (finiteCutMasses us k) (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_nodes us k hs) (finiteCutMasses_nodes us k hh) (finiteCutMasses_nodes us k hv)

theorem ActualSharpSourceCutGeometry_original_q.exists_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A)
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
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualThetaZeroOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem ActualStrongSharpSourceCutGeometry_original_q.retained_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hs : w.star∈as) (hh : high∈as) (hv : outer∈as) :
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star<U ∧ U<V ∧ V ≤ as.length ∧
      partitionPoint 0 as star=w.star.val ∧ partitionPoint 0 as U=high.val ∧ partitionPoint 0 as V=outer.val ∧
      4*W ≤ M.sweepRadius (partitionPoint 0 as U) ∧
      M.sweepRadius (partitionPoint 0 as star) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      M.z ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) ∧
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

theorem ActualStrongSharpSourceCutGeometry_original_q.finite_net_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (hs : w.star∈us) (hh : high∈us) (hv : outer∈us) (k : ℕ) :
    let as:=finiteCutMasses us k
    let star:=retainedMassPrefixIndex w.star.val as
    let U:=retainedMassPrefixIndex high.val as
    let V:=retainedMassPrefixIndex outer.val as
    star<U ∧ U<V ∧ V ≤ as.length ∧
      partitionPoint 0 as star=w.star.val ∧ partitionPoint 0 as U=high.val ∧ partitionPoint 0 as V=outer.val ∧
      4*W ≤ M.sweepRadius (partitionPoint 0 as U) ∧
      M.sweepRadius (partitionPoint 0 as star) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      M.z ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      Cx*M.xs ≤ partitionPoint 0 as U ∧ W ≤ Rmacro/2 :=
  H.retained_readout _ (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_nodes us k hs) (finiteCutMasses_nodes us k hh) (finiteCutMasses_nodes us k hv)

theorem ActualStrongSharpSourceCutGeometry_original_q.lower_radius_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    {u : ℝ} (hu : u ≤ w.star.val) :
    M.sweepRadius u ≤ min (M.sweepRadius high.val/8) (Rmacro/4) :=
  ((show Monotone M.sweepRadius from M.shiftedNativeModel.R_monotone) hu).trans H.star_gap

theorem ActualStrongSharpSourceCutGeometry_original_q.retained_initial_radius_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hs : w.star∈as) (hh : high∈as)
    (i : ℕ) (hi : i ≤ retainedMassPrefixIndex w.star.val as) :
    M.sweepRadius (partitionPoint 0 as i) ≤ min
      (M.sweepRadius (partitionPoint 0 as (retainedMassPrefixIndex high.val as))/8) (Rmacro/4) := by
  have Hmass:partitionPoint 0 as i ≤ w.star.val:=
    (partitionPoint_mono as ho hi).trans_eq (nativeRetainedCut_partitionPoint as ho w.star hs)
  simpa only [nativeRetainedCut_partitionPoint as ho high hh] using H.lower_radius_gap Hmass

theorem ActualStrongSharpSourceCutGeometry_original_q.finite_net_initial_radius_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (hs : w.star∈us) (hh : high∈us)
    (k i : ℕ) (hi : i ≤ retainedMassPrefixIndex w.star.val (finiteCutMasses us k)) :
    M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) i) ≤ min
      (M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) (retainedMassPrefixIndex high.val (finiteCutMasses us k)))/8) (Rmacro/4) :=
  H.retained_initial_radius_gap _ (finiteCutMasses_ordered us hus k)
    (finiteCutMasses_nodes us k hs) (finiteCutMasses_nodes us k hh) i hi

theorem ActualStrongSharpSourceCutGeometry_original_q.exists_dyadic_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
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
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualThetaZeroOverlapMinimum Set Filter
open scoped Topology NNReal
set_option maxHeartbeats 2000000

theorem ActualSharpSourceCutGeometry_original_q.target_cut_le_one
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius c cK A)
    (hc : 0 < c) (hx : 0 < x) (hxW : x ≤ W) :
    (nativeActualTargetMassCut c x hc hx).val ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left hxW (by positivity : 0≤2*c)).trans
    (H.first_high.trans (H.high_lt.le.trans H.outer_le_one))

theorem ActualSharpSourceCutGeometry_original_q.target_cut_retained_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius c cK A)
    (hc : 0 < c) (hx : 0 < x) (hxW : x ≤ W)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (ht : nativeActualTargetMassCut c x hc hx∈as) (hs : w.star∈as) (hh : high∈as) :
    ActualTargetCutRetainedReadout as w high c x W A := by
  let target:=nativeActualTargetMassCut c x hc hx
  have Htarget : target.val ≤ high.val :=
    (mul_le_mul_of_nonneg_left hxW (by positivity : 0≤2*c)).trans H.first_high
  have Hhigh:=nativeRetainedCut_partitionPoint as ho high hh
  refine ⟨nativeRetainedCut_partitionPoint as ho target ht,Hhigh,
    actual_retained_mass_nonstrict_index as ho target high ht hh Htarget,
    retainedMassPrefixIndex_le_length high.val as,
    actual_retained_mass_strict_index as ho w.star high hs hh H.star_lt,?_,?_⟩
  · rw [Hhigh]
    exact H.high_lt.le.trans H.outer_scale
  · intro u hu hut hus
    exact ⟨actual_retained_mass_strict_index as ho u target hu ht hut,
      actual_retained_mass_nonstrict_index as ho u w.star hu hs hus⟩

theorem ActualSharpSourceCutGeometry_original_q.target_cut_finite_net_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius c cK A)
    (hc : 0 < c) (hx : 0 < x) (hxW : x ≤ W)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (ht : nativeActualTargetMassCut c x hc hx∈us) (hs : w.star∈us) (hh : high∈us)
    (jGrid : ℕ) :
    ActualTargetCutRetainedReadout (finiteCutMasses us jGrid) w high c x W A :=
  H.target_cut_retained_readout hc hx hxW _ (finiteCutMasses_ordered us hus jGrid)
    (finiteCutMasses_nodes us jGrid ht) (finiteCutMasses_nodes us jGrid hs)
    (finiteCutMasses_nodes us jGrid hh)

theorem ActualSharpSourceCutGeometry_original_q.exists_target_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius c cK A)
    (hc : 0 < c) (hx : 0 < x) (hxW : x ≤ W)
    (L : ℕ) (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧
      nativeActualTargetMassCut c x hc hx∈us ∧ w.star∈us ∧ high∈us ∧ outer∈us ∧
      (∀u∈uniformMasses L,u∈us) ∧ (∀u∈extra,u∈us) ∧
      ∀jGrid : ℕ,ActualTargetCutRetainedReadout (finiteCutMasses us jGrid) w high c x W A := by
  obtain ⟨us,hus,hs,hh,ho,hnet,he⟩:=H.exists_common_net L
    (nativeActualTargetMassCut c x hc hx::extra) (by
      intro u hu
      rcases List.mem_cons.mp hu with rfl|hu
      · exact H.target_cut_le_one hc hx hxW
      · exact hextra u hu)
  have ht:=he _ (List.mem_cons_self)
  refine ⟨us,hus,ht,hs,hh,ho,hnet,?_,?_⟩
  · intro u hu
    exact he u (List.mem_cons_of_mem _ hu)
  · exact H.target_cut_finite_net_readout hc hx hxW us hus ht hs hh

theorem exists_actual_retained_target_cut_geometry_along_original_q
    {m delta cl cu Az C0 Ct D Bclock c cK A : ℝ} (hc : 0 < c)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W x radius : ℕ→ℝ) (hxsx : ∀n,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃target : ℕ→PositiveMass,(∀n,(target n).val=2*c*x n) ∧
      ∀ᶠn in atTop,(target n).val ≤ 1 ∧
        ∀(us : List PositiveMass), (∀u∈us,u.val ≤ 1) →
          target n∈us → (w n).star∈us → high n∈us →
          ∀jGrid : ℕ,ActualTargetCutRetainedReadout (finiteCutMasses us jGrid)
            (w n) (high n) c (x n) (W n) A := by
  have hx n : 0 < x n:=(M n).hxs.trans_le (hxsx n)
  let target n:=nativeActualTargetMassCut c (x n) hc (hx n)
  refine ⟨target,fun _=>rfl,?_⟩
  filter_upwards [Hcuts,hxW] with n hn hxw
  exact ⟨hn.target_cut_le_one hc (hx n) hxw,
    fun us hus ht hs hh=>hn.target_cut_finite_net_readout hc (hx n) hxw us hus ht hs hh⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualThetaZeroOverlapMinimum

theorem ActualSharpSourceCutGeometry_original_q.mono_outer_scale
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius cFirst cK A A' : ℝ} {w : ActualSlowWindowChoice}
    {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A)
    (hW : 0 ≤ W) (hA : A ≤ A') :
    ActualSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A' :=
  { H with outer_scale := H.outer_scale.trans (mul_le_mul_of_nonneg_right hA hW) }

theorem ActualStrongSharpSourceCutGeometry_original_q.mono_outer_scale
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius cFirst cK A A' Rmacro Cx : ℝ} {w : ActualSlowWindowChoice}
    {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (hW : 0 ≤ W) (hA : A ≤ A') :
    ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A' Rmacro Cx :=
  { H with toActualSharpSourceCutGeometry_original_q := H.toActualSharpSourceCutGeometry_original_q.mono_outer_scale hW hA }

end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualThetaZeroOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

structure ActualOriginalTargetCommonReadout_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (w : ActualSlowWindowChoice) (u high : PositiveMass) (c A W : ℝ) : Prop where
  target_mass : partitionPoint 0 as (retainedMassPrefixIndex u.val as)=u.val
  inner_mass : partitionPoint 0 as (retainedMassPrefixIndex (2*c*M.xs) as)=2*c*M.xs
  coarse_mass : partitionPoint 0 as (retainedMassPrefixIndex high.val as)=high.val
  target_lt_star : retainedMassPrefixIndex u.val as < retainedMassPrefixIndex w.star.val as
  target_lt_inner : retainedMassPrefixIndex u.val as < retainedMassPrefixIndex (2*c*M.xs) as
  inner_le_coarse : retainedMassPrefixIndex (2*c*M.xs) as ≤ retainedMassPrefixIndex high.val as
  star_lt_coarse : retainedMassPrefixIndex w.star.val as < retainedMassPrefixIndex high.val as
  coarse_le_length : retainedMassPrefixIndex high.val as ≤ as.length
  coarse_scale : partitionPoint 0 as (retainedMassPrefixIndex high.val as) ≤ A*W

theorem ActualStrongSharpSourceCutGeometry_original_q.target_inner_le_high
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx c : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (hCx : 2*c ≤ Cx) : 2*c*M.xs ≤ high.val :=
  (mul_le_mul_of_nonneg_right hCx M.hxs.le).trans H.source_lower

theorem ActualStrongSharpSourceCutGeometry_original_q.target_common_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx c Atarget : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer u : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (hc : 0 < c) (hCx : 2*c ≤ Cx) (hAtarget : Atarget < 2*c)
    (hu : u.val ≤ Atarget*M.xs) (hustar : u.val < w.star.val)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hretain : u∈as) (hinner : nativeActualTargetMassCut c M.xs hc M.hxs∈as)
    (hstar : w.star∈as) (hhigh : high∈as) :
    ActualOriginalTargetCommonReadout_original_q M as w u high c A W := by
  let inner:=nativeActualTargetMassCut c M.xs hc M.hxs
  have hsmall : u.val < inner.val:=hu.trans_lt (mul_lt_mul_of_pos_right hAtarget M.hxs)
  have hlarge : inner.val ≤ high.val:=H.target_inner_le_high hCx
  have HH:=nativeRetainedCut_partitionPoint as ho high hhigh
  refine ⟨nativeRetainedCut_partitionPoint as ho u hretain,
    nativeRetainedCut_partitionPoint as ho inner hinner,HH,
    actual_retained_mass_strict_index as ho u w.star hretain hstar hustar,
    actual_retained_mass_strict_index as ho u inner hretain hinner hsmall,
    actual_retained_mass_nonstrict_index as ho inner high hinner hhigh hlarge,
    actual_retained_mass_strict_index as ho w.star high hstar hhigh H.star_lt,
    retainedMassPrefixIndex_le_length high.val as,?_⟩
  rw [HH]
  exact H.high_lt.le.trans H.outer_scale

theorem ActualStrongSharpSourceCutGeometry_original_q.exists_original_target_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx c Atarget : ℝ}
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer u : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry_original_q M W w high outer radius cFirst cK A Rmacro Cx)
    (hc : 0 < c) (hCx : 2*c ≤ Cx) (hAtarget : Atarget < 2*c)
    (hu : u.val ≤ Atarget*M.xs) (hustar : u.val < w.star.val)
    (L : ℕ) (extra : List PositiveMass) (hextra : ∀v∈extra,v.val ≤ 1) :
    ∃us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧
      nativeActualTargetMassCut c M.xs hc M.hxs∈us ∧ w.star∈us ∧ high∈us ∧ outer∈us ∧
      (∀j ≤ nativeDyadicCutDepth high.val,nativeDyadicMassCut high.val high.property j∈us) ∧
      (∀v∈uniformMasses L,v∈us) ∧ (∀v∈extra,v∈us) ∧
      ∀jGrid : ℕ,ActualOriginalTargetCommonReadout_original_q M (finiteCutMasses us jGrid) w u high c A W := by
  let inner:=nativeActualTargetMassCut c M.xs hc M.hxs
  have hhigh : high.val ≤ 1:=H.high_lt.le.trans H.outer_le_one
  have hinner : inner.val ≤ 1:=(H.target_inner_le_high hCx).trans hhigh
  have hu1 : u.val ≤ 1:=hustar.le.trans (H.star_lt.le.trans hhigh)
  obtain ⟨us,hus,hstar,hh,houter,hnodes,hnet,he,Hdyadic⟩:=H.exists_dyadic_common_net L
    (u::inner::extra) (by
      intro v hv
      rcases List.mem_cons.mp hv with rfl|hv
      · exact hu1
      rcases List.mem_cons.mp hv with rfl|hv
      · exact hinner
      · exact hextra v hv)
  have hut:=he u (by simp only [List.mem_cons_self])
  have hit:=he inner (by simp only [List.mem_cons];exact Or.inr (Or.inl trivial))
  refine ⟨us,hus,hut,hit,hstar,hh,houter,hnodes,hnet,?_,?_⟩
  · intro v hv
    exact he v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
  · intro jGrid
    exact H.target_common_readout hc hCx hAtarget hu hustar _ (finiteCutMasses_ordered us hus jGrid)
      (finiteCutMasses_nodes us jGrid hut) (finiteCutMasses_nodes us jGrid hit)
      (finiteCutMasses_nodes us jGrid hstar) (finiteCutMasses_nodes us jGrid hh)

end OAI.SKFluctuations.LaplaceWindowFormalization
