module

public import ComparisonSignedCavityOriginalLongitudinalMean
public import ComparisonSignedCavityPhysicalBareRootZero

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
attribute [local instance] Classical.propDecidable

theorem MassOrdered.take_drop_geometry {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (j : ℕ) :
    MassOrdered a (as.take j) ∧
      MassOrdered (partitionPoint a as j) (as.drop j) ∧
      partitionEnd a (as.take j)=partitionPoint a as j ∧
      ∀u∈as.take j,u.val ≤ partitionPoint a as j := by
  induction as generalizing a j with
  | nil => simpa only [List.take_nil,List.drop_nil,partitionPoint,partitionValues,partitionEnd,id_eq] using
      (show MassOrdered a [] ∧ MassOrdered a [] ∧ a=a ∧ ∀u∈([]:List PositiveMass),u.val ≤ a from
        ⟨ho,ho,rfl,by simp⟩)
  | cons b bs ih =>
    cases j with
    | zero =>
      exact ⟨massOrdered_bounds ho,ho,rfl,by simp⟩
    | succ j =>
      obtain ⟨Hpre,Htail,Hend,Hupper⟩ := ih ho.2.2 j
      refine ⟨⟨ho.1,ho.2.1,Hpre⟩,Htail,Hend,?_⟩
      intro u hu
      simp only [List.take_succ_cons,List.mem_cons] at hu
      rcases hu with rfl|hu
      · exact (partitionPoint_mem bs ho.2.2 j).1
      · exact Hupper u hu

theorem partitionPoint_eq_end_take (a : ℝ) (as : List PositiveMass) (j : ℕ) :
    partitionPoint a as j=partitionEnd a (as.take j) := by
  induction as generalizing a j with
  | nil => simp only [List.take_nil,partitionPoint,partitionValues,partitionEnd,id_eq]
  | cons b bs ih => cases j with
    | zero => rfl
    | succ j => exact ih b.val j

theorem sampled_pair_disorder_uniform_path_bound
    {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
    {w : S → ℝ} (hw : ∀σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (D : ι → ℝ) (hD : ∀i,0 ≤ D i) (hφ : ∀σ i,|φ σ (Pi.single i 1)| ≤ D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀i,MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val ≤ 1) (pre tail : List PositiveMass)
    (hpre : MassOrdered 0 pre) (htail : MassOrdered u.val tail)
    (hupper : ∀v∈pre,v.val ≤ u.val) (hend : partitionEnd 0 pre=u.val)
    (hterminal : partitionEnd u.val tail=1) {mesh : ℝ}
    (hmesh : PartitionMesh mesh 0 (pre++tail))
    (P : S → S → ℝ) {K : ℝ} (hK : 0 ≤ K) (hP : ∀σ τ,|P σ τ| ≤ K) :
    |sampledPairDisorder w φ q u.val pre tail P 0-pathPairMoment w φ q P u.val| ≤
      ClockTree.errorJetVariation 2 0 0*K*(2*mesh*clockVariationBound D q) := by
  have HA (k : ℕ) := retainedMasses_ordered u hu (uniformMasses k) (uniformMasses_ordered k)
  have H (k : ℕ) := sampledPairDisorder_mesh_comparison hw φ D hD hφ q hq u.property.le
    pre tail (retainedBefore u (uniformMasses k)) (retainedAfter u (uniformMasses k))
    hpre htail (HA k).1 (HA k).2 hupper (retainedBefore_bounds u _)
    hend (retainedBefore_end u _) hterminal (retainedAfter_end u _) hmesh
    (retainedMasses_mesh u hu _ (uniformMasses_ordered k) (by positivity) (uniformMasses_mesh k))
    P hK hP 0
  have Hleft := ((tendsto_const_nhds (x:=sampledPairDisorder w φ q u.val pre tail P 0)).sub
    (retainedPairSample_tendsto hw φ D hD hφ q hq u hu P hK hP 0)).abs
  have Hright := ((tendsto_const_nhds (x:=mesh)).add uniformMasses_mesh_tendsto).const_mul 2
  have Hright' := (Hright.mul_const (clockVariationBound D q)).const_mul
    (ClockTree.errorJetVariation 2 0 0*K)
  simp only [add_zero] at Hright'
  have HB := le_of_tendsto_of_tendsto Hleft Hright' (Eventually.of_forall H)
  simpa only [pathPairMoment,dite_eq_left u.property] using HB

end OAI.SKFluctuations.Hierarchy
