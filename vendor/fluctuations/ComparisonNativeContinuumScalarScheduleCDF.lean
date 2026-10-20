module

public import ComparisonNativeGeneralScalarScheduleCDF
public import ComparisonSignedCavityContinuumMixedClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
variable {T : ℝ}

theorem native_continuum_mixed_clock_zero_of_zero_root_field
    (n : ℕ) (bf hf : ℝ→ℝ≥0) (hroot : hf 0=0) (as : List PositiveMass) :
    nativeContinuumMixedClock n bf hf as 0=0 := by
  have hp : partitionPoint 0 as 0=0 := by cases as <;> rfl
  simp only [nativeContinuumMixedClock,hp,hroot,NNReal.coe_zero,
    orderedPathS,orderedPathPair_zero,mul_zero,add_zero]

def continuumRetainedScalarScheduleProfile
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (as : List PositiveMass) (ho : MassOrdered 0 as) : boundedMassProfiles :=
  actualScalarScheduleMass hT (scalarBoundaryClocks as (nativeContinuumMixedClock n bf hf as))
    (by
      rw [scalarBoundaryClocks_duration _ _ (native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho),
        native_continuum_mixed_clock_zero_of_zero_root_field n bf hf hroot as,sub_zero]
      exact (native_continuum_mixed_clock_terminal_le n bf hf hbf hhf as ho).trans
        (htotal 1 (by norm_num)))

theorem continuum_retained_scalar_schedule_cdf_l1_error
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh : PartitionMesh mesh 0 as) :
    (∫ t in (0:ℝ)..1,
      |(continuumRetainedScalarScheduleProfile n bf hf hbf hhf hroot hT htotal as ho).val t-
        (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal).val t|) ≤ mesh := by
  let q:=nativeContinuumMixedClock n bf hf as
  let f:=actualScalarClockQuantile T (n+1) bf hf
  have hq : Monotone q:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  have hq0 : q 0=0:=native_continuum_mixed_clock_zero_of_zero_root_field n bf hf hroot as
  have hfmono : MonotoneOn f (Icc (0:ℝ) 1):=
    actualScalarClockQuantile_monotone hT (n+1) (by omega) bf hf hbf hhf
  have hfb:=actualScalarClockQuantile_bounds hT (n+1) (by omega) bf hf hbf hhf htotal
  have hnodes (j : ℕ) (_hj : j ≤ as.length) :
      |q j-T*partitionValues f 0 as j| ≤ T*0 := by
    have hv : partitionValues f 0 as j=f (partitionPoint 0 as j) := by
      have H (a : ℝ) (bs : List PositiveMass) (k : ℕ) :
          partitionValues f a bs k=f (partitionValues id a bs k) := by
        induction bs generalizing a k with
        | nil=>rfl
        | cons b bs ih=>cases k with
          | zero=>rfl
          | succ k=>exact ih b.val k
      exact H 0 as j
    rw [hv]
    by_cases hp : 0 < partitionPoint 0 as j
    · have he : q j=T*f (partitionPoint 0 as j) := by
        dsimp only [q,f]
        rw [actualScalarClockQuantile_on (n+1) bf hf hp]
        unfold nativeContinuumMixedClock actualMixedClock
        field_simp
      rw [he]
      simp
    · have hz : partitionPoint 0 as j=0:=le_antisymm (le_of_not_gt hp) (partitionPoint_mem as ho j).1
      simp only [q,nativeContinuumMixedClock,hz,hroot,NNReal.coe_zero,
        orderedPathS,orderedPathPair_zero,mul_zero,add_zero,f,actualScalarClockQuantile,
        le_refl,ite_eq_left,sub_zero,abs_zero,le_refl]
  have Hq:=normalizedScalarScheduleQuantile_l1_sample_error hT as ho q hq hq0 f hfmono hmesh hnodes
  have Hcdf:=quantileMassProfile_l1_le
    (normalizedScheduleQuantile T 0 (scalarBoundaryClocks as q)) f
    ((normalizedScheduleQuantile_monotone hT.le _).monotoneOn _) hfmono
    (normalizedScheduleQuantile_bounds hT le_rfl _ (by
      rw [zero_add,scalarBoundaryClocks_duration _ q hq,hq0,sub_zero]
      exact (native_continuum_mixed_clock_terminal_le n bf hf hbf hhf as ho).trans
        (htotal 1 (by norm_num)))) hfb
  have Hvar : f 1-f 0 ≤ 1:=by linarith [(hfb 1 (by norm_num)).2,(hfb 0 (by norm_num)).1]
  apply (Hcdf.trans Hq).trans
  simpa only [zero_add,mul_one] using mul_le_mul_of_nonneg_left Hvar hmesh0

theorem continuum_retained_scalar_schedule_cdf_l1_tendsto
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    Tendsto (fun k=>∫ t in (0:ℝ)..1,
      |(continuumRetainedScalarScheduleProfile n bf hf hbf hhf hroot hT htotal (finiteCutMasses us k)
        (finiteCutMasses_ordered us hus k)).val t-
        (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal).val t|) atTop (𝓝 0) := by
  apply squeeze_zero (fun k=>intervalIntegral.integral_nonneg zero_le_one (fun _ _=>abs_nonneg _))
    (fun k=>continuum_retained_scalar_schedule_cdf_l1_error n bf hf hbf hhf hroot hT htotal _
      (finiteCutMasses_ordered us hus k) (by positivity) (finiteCutMasses_mesh us hus k))
  exact uniformMasses_mesh_tendsto

end OAI.SKFluctuations.LaplaceWindowFormalization
