module

public import ComparisonMacroThermalClosure
public import ComparisonDefectThermalBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal Topology

theorem intervalIntegrable_bounded_measurable_mul {w F : ℝ → ℝ} {M : ℝ}
    (hw : Measurable w) (hM : 0 ≤ M) (hbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) M)
    (hF : IntervalIntegrable F volume 0 1) :
    IntervalIntegrable (fun u=>w u*F u) volume 0 1 := by
  apply IntervalIntegrable.mono_fun' (hF.norm.const_mul M)
    (hw.aestronglyMeasurable.mul hF.aestronglyMeasurable_restrict_uIoc)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
  change ‖w u*F u‖ ≤ M*‖F u‖
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hbound u hu).1]
  exact mul_le_mul_of_nonneg_right (hbound u hu).2 (norm_nonneg _)

theorem physicalSampledThermal_weighted_integral_error (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh M : ℝ} (hm : PartitionMesh mesh 0 as) (w : ℝ → ℝ)
    (hw : Measurable w) (hM : 0 ≤ M) (hbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) M) :
    |(∫u in 0..1,w u*physicalSampledThermal n b h as ha u)-
      (∫u in 0..1,w u*(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))| ≤
      M*(3*mesh*physicalBApproximationConstant n b h) := by
  let F := physicalSampledThermal n b h as ha
  let G := fun u=>orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2
  have hF := physicalSampledThermal_intervalIntegrable n b h as ha
  have hG := physicalOrderedThermal_intervalIntegrable n b h hb hh
  have hwF := intervalIntegrable_bounded_measurable_mul hw hM hbound hF
  have hwG := intervalIntegrable_bounded_measurable_mul hw hM hbound hG
  have hsubI := intervalIntegrable_bounded_measurable_mul hw hM hbound (hF.sub hG)
  have hdiff : (∫u in 0..1,w u*F u)-(∫u in 0..1,w u*G u)=
      ∫u in 0..1,w u*(F u-G u) := by
    rw [← intervalIntegral.integral_sub hwF hwG]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  change |(∫u in 0..1,w u*F u)-(∫u in 0..1,w u*G u)| ≤ _
  rw [hdiff]
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ) ≤ 1)
    hsubI.abs ((hF.sub hG).abs.const_mul M) (fun u hu=>by
      rw [abs_mul,abs_of_nonneg (hbound u ⟨hu.1,hu.2.le⟩).1]
      exact mul_le_mul_of_nonneg_right (hbound u ⟨hu.1,hu.2.le⟩).2 (abs_nonneg _))
  have hl1 := physicalSampledThermal_l1_bound n b h hb hh as ha he hm
  calc
    _ ≤ ∫u in 0..1,|w u*(F u-G u)| := intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫u in 0..1,M*|F u-G u| := hmono
    _ = M*(∫u in 0..1,|F u-G u|) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hl1 hM

theorem physicalSampledThermal_weighted_integral_tendsto (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    (w : ℝ → ℝ) {M : ℝ} (hw : Measurable w) (hM : 0 ≤ M)
    (hbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) M) :
    Tendsto (fun j=>∫u in 0..1,w u*physicalSampledThermal n b h (as j) (ho j) u)
      atTop (𝓝 (∫u in 0..1,w u*(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _=>abs_nonneg _)
    (fun j=>physicalSampledThermal_weighted_integral_error n b h hb hh (as j) (ho j) (he j) (hm j) w hw hM hbound)
    (by simpa only [mul_zero,zero_mul] using (hmesh.const_mul 3 |>.mul_const (physicalBApproximationConstant n b h) |>.const_mul M))

theorem physicalOrderedThermal_weighted_le_of_sampled (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    (w : ℝ → ℝ) {M A : ℝ} (hw : Measurable w) (hM : 0 ≤ M)
    (hbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) M)
    (hfinite : ∀ᶠj in atTop,(∫u in 0..1,w u*physicalSampledThermal n b h (as j) (ho j) u) ≤ A) :
    (∫u in 0..1,w u*(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)) ≤ A := by
  exact le_of_tendsto
    (physicalSampledThermal_weighted_integral_tendsto n b h hb hh as mesh ho he hm hmesh w hw hM hbound)
    hfinite

end OAI.SKFluctuations.LaplaceWindowFormalization
