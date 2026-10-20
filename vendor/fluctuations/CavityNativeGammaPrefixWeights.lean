module

public import CavityNativeSignedProjectedReplacement
public import CavityScalarGammaTopology

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_attachment_gamma_abs_le {n : ℕ} {as : List PositiveMass}
    (ho : MassOrdered 0 as)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (U : ℕ) (hU : 0 < U) (K : ℕ → ℝ) (hK : Monotone K) (hK0 : ∀ j, 0 ≤ K j)
    (hnon : p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)≠p.mark) :
    |nativeAttachmentGamma p U K|≤
      relocatedClock U 0 K (p.tree.splitIndex
        (p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)) p.mark) := by
  let u := p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)
  have hm := relocatedClock_monotone U (show (0:ℝ)∈Icc 0 1 by norm_num) hK hK0
  have hq0 : relocatedClock U 0 K 0=0 := by simp [relocatedClock,hU]
  have hn : p.tree.cavityRightSlot u≠p.tree.cavityRightSlot p.mark :=
    fun h=>hnon ((p.tree.cavityRightSlot).injective h)
  have hg:=actual_scalar_distinct_pair_bounds p.tree.cavityRight ho
    (relocatedClock U 0 K) hm hq0 (p.tree.cavityRightSlot u) (p.tree.cavityRightSlot p.mark) hn
  have he : scalarCutGamma p.tree.cavityRight U K
      (p.tree.cavityRightSlot u) (p.tree.cavityRightSlot p.mark)=nativeAttachmentGamma p U K := rfl
  simp only [scalarFeature_apply_spin,mul_one] at hg
  have hg' : 0 ≤ scalarCutGamma p.tree.cavityRight U K
    (p.tree.cavityRightSlot u) (p.tree.cavityRightSlot p.mark) ∧
    scalarCutGamma p.tree.cavityRight U K
      (p.tree.cavityRightSlot u) (p.tree.cavityRightSlot p.mark)≤
      relocatedClock U 0 K (p.tree.cavityRight.splitIndex
        (p.tree.cavityRightSlot u) (p.tree.cavityRightSlot p.mark)) := by
    simpa only [scalarCutGamma,scalarCutMoment,ClockTree.slotProduct,mul_one,Pi.zero_def] using hg
  rw [he,p.tree.splitIndex_cavityRight] at hg'
  rw [abs_of_nonneg hg'.1]
  exact hg'.2

theorem native_single_prefix_gamma_weight_le_square (n : ℕ) (pre tail : List PositiveMass)
    (ho : MassOrdered 0 (pre++tail)) (U : ℕ) (hU : 0 < U)
    (K : ℕ → ℝ) (hK : Monotone K) (hK0 : ∀ j, 0 ≤ K j)
    {C v : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hclock : relocatedClock U 0 K pre.length≤C*v) (hmass : partitionEnd 0 pre≤v) :
    ((ClockTree.singlePrefixAttachments (S := Spin n×Bool) pre tail 0).map fun p=>
      |p.coeff| * |nativeAttachmentGamma p U K|).sum ≤ C*v^2 := by
  have hm:=relocatedClock_monotone U (show (0:ℝ)∈Icc 0 1 by norm_num) hK hK0
  have hb : ∀ p∈ClockTree.singlePrefixAttachments (S := Spin n×Bool) pre tail 0,
      |nativeAttachmentGamma p U K|≤C*v := by
    intro p hp
    apply (native_attachment_gamma_abs_le ho p U hU K hK hK0
      (ClockTree.single_prefix_attachment_noncoincident pre tail 0 p hp)).trans
    exact (hm (ClockTree.single_prefix_attachment_split pre tail 0 p hp).le).trans hclock
  have ht : ((ClockTree.singlePrefixAttachments (S := Spin n×Bool) pre tail 0).map fun p=>
      |p.coeff| * |nativeAttachmentGamma p U K|).sum ≤
    ((ClockTree.singlePrefixAttachments (S := Spin n×Bool) pre tail 0).map fun p=>|p.coeff| *(C*v)).sum := by
    apply (le_abs_self _).trans
    simpa only [abs_abs] using ReplicaTree.list_weighted_absolute_bound
      (ClockTree.singlePrefixAttachments (S := Spin n×Bool) pre tail 0)
      (fun p=>|p.coeff|) (fun p=>|nativeAttachmentGamma p U K|) (fun _=>C*v)
      (fun p hp=>by simpa only [abs_abs] using hb p hp)
  apply ht.trans
  rw [List.sum_map_mul_right,ClockTree.single_prefix_attachment_variation pre tail ho,sub_zero]
  calc
    _ ≤ v*(C*v) := mul_le_mul_of_nonneg_right hmass (mul_nonneg hC hv)
    _=C*v^2 := by ring

end OAI.SKFluctuations.Cavity
