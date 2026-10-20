module

public import ComparisonSignedCavityActualStrongSharpSourceCutReadout
public import ComparisonSignedCavityActualRetainedTargetCutGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

structure ActualOriginalTargetCommonReadout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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

theorem ActualStrongSharpSourceCutGeometry.target_inner_le_high
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx c : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (hCx : 2*c ≤ Cx) : 2*c*M.xs ≤ high.val :=
  (mul_le_mul_of_nonneg_right hCx M.hxs.le).trans H.source_lower

theorem ActualStrongSharpSourceCutGeometry.target_common_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx c Atarget : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer u : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (hc : 0 < c) (hCx : 2*c ≤ Cx) (hAtarget : Atarget < 2*c)
    (hu : u.val ≤ Atarget*M.xs) (hustar : u.val < w.star.val)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hretain : u∈as) (hinner : nativeActualTargetMassCut c M.xs hc M.hxs∈as)
    (hstar : w.star∈as) (hhigh : high∈as) :
    ActualOriginalTargetCommonReadout M as w u high c A W := by
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

theorem ActualStrongSharpSourceCutGeometry.exists_original_target_common_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W radius cFirst cK A Rmacro Cx c Atarget : ℝ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice} {high outer u : PositiveMass}
    (H : ActualStrongSharpSourceCutGeometry M W w high outer radius cFirst cK A Rmacro Cx)
    (hc : 0 < c) (hCx : 2*c ≤ Cx) (hAtarget : Atarget < 2*c)
    (hu : u.val ≤ Atarget*M.xs) (hustar : u.val < w.star.val)
    (L : ℕ) (extra : List PositiveMass) (hextra : ∀v∈extra,v.val ≤ 1) :
    ∃us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧
      nativeActualTargetMassCut c M.xs hc M.hxs∈us ∧ w.star∈us ∧ high∈us ∧ outer∈us ∧
      (∀j ≤ nativeDyadicCutDepth high.val,nativeDyadicMassCut high.val high.property j∈us) ∧
      (∀v∈uniformMasses L,v∈us) ∧ (∀v∈extra,v∈us) ∧
      ∀jGrid : ℕ,ActualOriginalTargetCommonReadout M (finiteCutMasses us jGrid) w u high c A W := by
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
