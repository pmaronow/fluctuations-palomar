module

public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum Set Filter
open scoped Topology NNReal
set_option maxHeartbeats 2000000

def nativeActualTargetMassCut (c x : ℝ) (hc : 0 < c) (hx : 0 < x) : PositiveMass :=
  ⟨2*c*x, mul_pos (mul_pos (by norm_num) hc) hx⟩

theorem nativeActualTargetMassCut_val (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    (nativeActualTargetMassCut c x hc hx).val=2*c*x := rfl

theorem actual_retained_mass_nonstrict_index
    (as : List PositiveMass) (ho : MassOrdered 0 as) (a b : PositiveMass)
    (ha : a∈as) (hb : b∈as) (hab : a.val ≤ b.val) :
    retainedMassPrefixIndex a.val as ≤ retainedMassPrefixIndex b.val as := by
  rcases lt_or_eq_of_le hab with hlt|heq
  · exact (actual_retained_mass_strict_index as ho a b ha hb hlt).le
  · rw [heq]

structure ActualTargetCutRetainedReadout
    (as : List PositiveMass) (w : ActualSlowWindowChoice) (high : PositiveMass)
    (c x W A : ℝ) : Prop where
  target_mass : partitionPoint 0 as (retainedMassPrefixIndex (2*c*x) as)=2*c*x
  high_mass : partitionPoint 0 as (retainedMassPrefixIndex high.val as)=high.val
  target_le_high : retainedMassPrefixIndex (2*c*x) as ≤ retainedMassPrefixIndex high.val as
  high_le_length : retainedMassPrefixIndex high.val as ≤ as.length
  star_lt_high : retainedMassPrefixIndex w.star.val as < retainedMassPrefixIndex high.val as
  high_scale : partitionPoint 0 as (retainedMassPrefixIndex high.val as) ≤ A*W
  old_indices : ∀u∈as,u.val < 2*c*x → u.val ≤ w.star.val →
    retainedMassPrefixIndex u.val as < retainedMassPrefixIndex (2*c*x) as ∧
      retainedMassPrefixIndex u.val as ≤ retainedMassPrefixIndex w.star.val as

theorem ActualSharpSourceCutGeometry.target_cut_le_one
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius c cK A)
    (hc : 0 < c) (hx : 0 < x) (hxW : x ≤ W) :
    (nativeActualTargetMassCut c x hc hx).val ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left hxW (by positivity : 0≤2*c)).trans
    (H.first_high.trans (H.high_lt.le.trans H.outer_le_one))

theorem ActualSharpSourceCutGeometry.target_cut_retained_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius c cK A)
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

theorem ActualSharpSourceCutGeometry.target_cut_finite_net_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius c cK A)
    (hc : 0 < c) (hx : 0 < x) (hxW : x ≤ W)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (ht : nativeActualTargetMassCut c x hc hx∈us) (hs : w.star∈us) (hh : high∈us)
    (jGrid : ℕ) :
    ActualTargetCutRetainedReadout (finiteCutMasses us jGrid) w high c x W A :=
  H.target_cut_retained_readout hc hx hxW _ (finiteCutMasses_ordered us hus jGrid)
    (finiteCutMasses_nodes us jGrid ht) (finiteCutMasses_nodes us jGrid hs)
    (finiteCutMasses_nodes us jGrid hh)

theorem ActualSharpSourceCutGeometry.exists_target_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius c cK A x : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualSharpSourceCutGeometry M W w high outer radius c cK A)
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

theorem exists_actual_retained_target_cut_geometry_along
    {m delta cl cu Az C0 Ct D Bclock c cK A : ℝ} (hc : 0 < c)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W x radius : ℕ→ℝ) (hxsx : ∀n,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
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
