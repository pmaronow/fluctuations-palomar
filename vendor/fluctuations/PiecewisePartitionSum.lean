module

public import ContinuousPartitionSum
public import SKFluctuationsOAI.Probability.SKFluctuations.RealSKPressureL1

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology

theorem bounded_ae_continuous_partitionSum_tendsto {q : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖q u‖ ≤ C)
    (hc : ∀ᵐ u ∂volume, u ∈ Icc (0 : ℝ) 1 → ContinuousWithinAt q (Icc (0 : ℝ) 1) u) :
    Tendsto (fun k => massStepSum (uniformMasses k) 0
      (fun j => q (partitionPoint 0 (uniformMasses k) j))) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, q u)) := by
  have hlim : Tendsto (fun k => ∫ u in (0 : ℝ)..1, partitionSample q 0 (uniformMasses k) u)
      atTop (𝓝 (∫ u in (0 : ℝ)..1, q u)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun k u => partitionSample q 0 (uniformMasses k) u) (f := q)
      (μ := volume) (a := (0 : ℝ)) (b := 1) (fun _ => C)
    · exact Eventually.of_forall fun k =>
        (partitionSample_intervalIntegrable q 0 (uniformMasses k) 0 1).def'.aestronglyMeasurable
    · apply Eventually.of_forall
      intro k
      apply Eventually.of_forall
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at hu
        exact ⟨hu.1.le, hu.2⟩
      have hb := partitionSample_id_bounds (uniformMasses k) (uniformMasses_ordered k)
        (uniformMasses_mesh k) hu'
      rw [partitionSample_comp]
      exact hbound _ ⟨hb.1, hb.2.1.trans hu'.2⟩
    · exact intervalIntegrable_const
    · filter_upwards [hc] with u hcu
      intro hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at hu
        exact ⟨hu.1.le, hu.2⟩
      exact uniformSample_tendsto hu' (hcu hu')
  have he (k : ℕ) : (∫ u in (0 : ℝ)..1, partitionSample q 0 (uniformMasses k) u) =
      massStepSum (uniformMasses k) 0 (fun j => q (partitionPoint 0 (uniformMasses k) j)) := by
    unfold partitionSample
    rw [massStepFunction_integral _ _ _ (uniformMasses_ordered k)]
    congr 1
    funext j
    exact partitionValues_point q 0 (uniformMasses k) j
  simpa only [he] using hlim

theorem cutoff_continuousWithinAt {u0 : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc u0 1)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hne : u ≠ u0) :
    ContinuousWithinAt (fun v => if u0 ≤ v then f v else 0) (Icc (0 : ℝ) 1) u := by
  rcases lt_or_gt_of_ne hne with hlo | hhi
  · have he : ∀ᶠ v in 𝓝[Icc (0 : ℝ) 1] u, v < u0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hlo)
    apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
    · exact he.mono fun v hv => by simp [not_le.mpr hv]
    · simp [not_le.mpr hlo]
  · have he : ∀ᶠ v in 𝓝[Icc (0 : ℝ) 1] u, u0 < v :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hhi)
    have hm : Icc u0 1 ∈ 𝓝[Icc (0 : ℝ) 1] u := by
      filter_upwards [he, self_mem_nhdsWithin] with v hv hvm
      exact ⟨hv.le, hvm.2⟩
    apply (hf u ⟨hhi.le, hu.2⟩).mono_of_mem_nhdsWithin hm |>.congr_of_eventuallyEq
    · exact he.mono fun v hv => by simp [hv.le]
    · simp [hhi.le]

theorem cutoff_partitionSum_tendsto {u0 : ℝ} (hu0 : u0 ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc u0 1)) :
    Tendsto (fun k => massStepSum (uniformMasses k) 0
      (fun j => if u0 ≤ partitionPoint 0 (uniformMasses k) j then
        f (partitionPoint 0 (uniformMasses k) j) else 0)) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, if u0 ≤ u then f u else 0)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply bounded_ae_continuous_partitionSum_tendsto (C := max C 0)
  · intro u hu
    by_cases he : u0 ≤ u
    · simpa only [ite_eq_left he] using (hC u ⟨he, hu.2⟩).trans (le_max_left C 0)
    · simpa [he] using (le_max_right C 0)
  · have hne : ∀ᵐ u : ℝ ∂volume, u ≠ u0 := by simp [ae_iff]
    filter_upwards [hne] with u hneu
    intro hu
    exact cutoff_continuousWithinAt hf hu hneu

theorem cutoff_intervalIntegrable {u0 : ℝ} (hu0 : u0 ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc u0 1)) :
    IntervalIntegrable (fun u => if u0 ≤ u then f u else 0) volume 0 1 := by
  have hu1 : u0 ≤ 1 := hu0.2
  let F : C(Icc u0 1, ℝ) :=
    ⟨fun u => f u, continuousOn_iff_continuous_restrict.mp hf⟩
  have hi := omittedExtension_intervalIntegrable hu1 F 0 1
  apply IntervalIntegrable.congr (f := omittedExtension hu1 F) (g := fun u => if u0 ≤ u then f u else 0) ?_ hi
  intro u hu
  rw [uIoc_of_le zero_le_one] at hu
  change omittedExtension hu1 F u = if u0 ≤ u then f u else 0
  by_cases he : u0 ≤ u
  · rw [ite_eq_left he, omittedExtension_on hu1 F ⟨u, ⟨he, hu.2⟩⟩]
    rfl
  · rw [ite_eq_right he, omittedExtension_before hu1 F (lt_of_not_ge he)]

theorem cutoff_eq_intervalIntegrable {u0 : ℝ} (hu0 : u0 ∈ Icc (0 : ℝ) 1)
    {q f : ℝ → ℝ} (hf : ContinuousOn f (Icc u0 1))
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, q u = if u0 ≤ u then f u else 0) :
    IntervalIntegrable q volume 0 1 := by
  apply IntervalIntegrable.congr (f := fun u => if u0 ≤ u then f u else 0) (g := q) ?_
    (cutoff_intervalIntegrable hu0 hf)
  intro u hu
  rw [uIoc_of_le zero_le_one] at hu
  exact (heq u ⟨hu.1.le, hu.2⟩).symm

theorem cutoff_eq_partitionSum_tendsto {u0 : ℝ} (hu0 : u0 ∈ Icc (0 : ℝ) 1)
    {q f : ℝ → ℝ} (hf : ContinuousOn f (Icc u0 1))
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, q u = if u0 ≤ u then f u else 0) :
    Tendsto (fun k => massStepSum (uniformMasses k) 0
      (fun j => q (partitionPoint 0 (uniformMasses k) j))) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, q u)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply bounded_ae_continuous_partitionSum_tendsto (C := max C 0)
  · intro u hu
    rw [heq u hu]
    by_cases he : u0 ≤ u
    · simpa only [ite_eq_left he] using (hC u ⟨he, hu.2⟩).trans (le_max_left C 0)
    · simpa [he] using (le_max_right C 0)
  · have hne : ∀ᵐ u : ℝ ∂volume, u ≠ u0 := by simp [ae_iff]
    filter_upwards [hne] with u hneu
    intro hu
    exact (cutoff_continuousWithinAt hf hu hneu).congr
      (fun v hv => heq v hv) (heq u hu)

end OAI.SKFluctuations.LaplaceWindowFormalization
