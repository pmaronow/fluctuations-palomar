module

public import ComparisonNativeRadiusCellAverages

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

namespace MassCellAveraging

theorem average_mem_Icc (f : ℝ→ℝ) {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hf : IntervalIntegrable f volume a b) (hbound : ∀u∈Icc a b,f u∈Icc (0:ℝ) B) :
    average f a b∈Icc (0:ℝ) B := by
  by_cases he : a=b
  · subst b;simp [average,hB]
  have hp : 0<b-a := sub_pos.mpr (lt_of_le_of_ne hab he)
  have hnonneg : 0 ≤ ∫u in a..b,f u :=
    intervalIntegral.integral_nonneg hab (fun u hu=>(hbound u hu).1)
  have hupper : (∫u in a..b,f u) ≤ (b-a)*B := by
    have hi := intervalIntegral.integral_mono_on hab hf
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>B) volume a b)
      (fun u hu=>(hbound u hu).2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hi
  exact ⟨div_nonneg hnonneg hp.le,(div_le_iff₀ hp).mpr (by linarith)⟩

theorem originalCoefficient_mem_Icc (f : ℝ→ℝ) {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) {B : ℝ} (hB : 0 ≤ B)
    (hf : IntervalIntegrable f volume a 1) (hbound : ∀u∈Icc a 1,f u∈Icc (0:ℝ) B)
    (i : ℕ) : originalCoefficient f a as i∈Icc (0:ℝ) B := by
  have hi := partitionPoint_mem as ho i
  have hj := partitionPoint_mem as ho (i+1)
  have hij := partitionPoint_mono as ho (Nat.le_succ i)
  have hs : Icc (partitionPoint a as i) (partitionPoint a as (i+1))⊆Icc a 1 :=
    Icc_subset_Icc hi.1 hj.2
  apply average_mem_Icc f hij hB
  · exact hf.mono_set (by rw [uIcc_of_le hij,uIcc_of_le (massOrdered_bounds ho).2];exact hs)
  · exact fun u hu=>hbound u (hs hu)

theorem partitionPoint_eq_end_of_ge (a : ℝ) (as : List PositiveMass)
    {i : ℕ} (hi : as.length ≤ i) : partitionPoint a as i=partitionEnd a as := by
  induction as generalizing a i with
  | nil=>rfl
  | cons b bs ih=>
    cases i with
    | zero=>simp at hi
    | succ i=>exact ih b.val (by simpa using hi)

theorem originalCoefficient_eq_zero_of_end (f : ℝ→ℝ) (a : ℝ) (as : List PositiveMass)
    {i : ℕ} (hi : as.length ≤ i) : originalCoefficient f a as i=0 := by
  unfold originalCoefficient
  rw [partitionPoint_eq_end_of_ge a as hi,
    partitionPoint_eq_end_of_ge a as (hi.trans (Nat.le_succ i))]
  simp [average]

theorem originalCoefficient_support_floor (f : ℝ→ℝ) {a t mesh : ℝ}
    (as : List PositiveMass) (ho : MassOrdered a as) (hmesh : PartitionMesh mesh a as)
    (hzero : ∀u ≤ t,f u=0) {i : ℕ} (hnz : originalCoefficient f a as i ≠ 0) :
    t-mesh ≤ partitionPoint a as i := by
  have hi : i<as.length := lt_of_not_ge (fun hi=>hnz (originalCoefficient_eq_zero_of_end f a as hi))
  have hnext : t<partitionPoint a as (i+1) := by
    by_contra hn
    have he : originalCoefficient f a as i=0 := by
      unfold originalCoefficient average
      rw [intervalIntegral.integral_congr_Ioo_of_le (partitionPoint_mono as ho (Nat.le_succ i))
        (fun u hu=>hzero u (hu.2.le.trans (le_of_not_gt hn)))]
      simp
    exact hnz he
  have hm := massPartition_point_next_mesh as hmesh hi
  linarith

end MassCellAveraging
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonRadiusMassWeight_zero_before_lower_radius
    (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hAD : A⊆Ioo a z)
    (x kmin : ℝ) {u : ℝ} (hu : u ≤ α.val.val a) :
    comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
      α.val.val A x kmin u=0 := by
  have hr := comparisonSweepQuantile_monotone hc hk hkc hm hM α hu
  rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α ha] at hr
  unfold comparisonRadiusMassWeight
  exact if_neg (fun h=>not_lt_of_ge hr (hAD h).1)

theorem comparisonOriginalRadiusWeights_native_cut_floor {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} {a z : ℝ} (ha : a∈Icc (0:ℝ) 1) (hAD : A⊆Ioo a z)
    (x kmin : ℝ) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (i : Fin ((sampleClockSteps q 0 as).length+1))
    (hnz : comparisonOriginalRadiusWeights q as
      (comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
        α.val.val A x kmin) i ≠ 0) :
    α.val.val a-mesh ≤ physicalCutMass 0 (sampleClockSteps q 0 as) i.val := by
  have hi : i.val ≤ as.length := by
    have hit := i.isLt
    simp only [sampleClockSteps_length] at hit
    omega
  rw [physicalCutMass_sampleClockSteps q 0 as i.val hi]
  exact MassCellAveraging.originalCoefficient_support_floor _ as ho hmesh
    (fun u hu=>comparisonRadiusMassWeight_zero_before_lower_radius hc hk hkc hm hM α ha hAD x kmin hu) hnz

end
end OAI.SKFluctuations.LaplaceWindowFormalization
