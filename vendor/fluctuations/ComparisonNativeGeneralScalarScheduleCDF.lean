module

public import ComparisonSignedCavityScalarScheduleSample
public import ComparisonSignedCavityPhysicalMeanUniform
public import ActualMixedClockCDF
public import ComparisonSignedCavityPhysicalBareRootZero

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
variable {T : ℝ}

def generalRetainedScalarScheduleProfile
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    boundedMassProfiles :=
  actualScalarScheduleMass hT (scalarBoundaryClocks as (retainedStarMixedClock n bf hf as))
    (by
      rw [scalarBoundaryClocks_duration _ _ (retainedStarMixedClock_monotone n bf hf
          hbf hhf as ho),
        retainedStarMixedClock_zero_of_zero_root_field n bf hf ho hroot, sub_zero]
      exact (retainedStarMixedClock_terminal_le n bf hf as ho he).trans
        (htotal 1 (by norm_num)))

theorem general_retained_scalar_schedule_cdf_l1_error
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh : PartitionMesh mesh 0 as) :
    (∫ t in (0:ℝ)..1,
      |(generalRetainedScalarScheduleProfile n bf hf hbf hhf hroot hT htotal as ho he).val t-
        (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal).val t|) ≤
      mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n)
          (completedPathClock (n+1) bf hf)+1) := by
  let q := retainedStarMixedClock n bf hf as
  let f := actualScalarClockQuantile T (n+1) bf hf
  let E := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) bf hf)
  have hq : Monotone q := retainedStarMixedClock_monotone n bf hf hbf hhf as ho
  have hq0 : q 0=0 := retainedStarMixedClock_zero_of_zero_root_field n bf hf ho hroot
  have hfmono : MonotoneOn f (Icc (0:ℝ) 1) :=
    actualScalarClockQuantile_monotone hT (n+1) (by omega) bf hf hbf hhf
  have hfb := actualScalarClockQuantile_bounds hT (n+1) (by omega) bf hf hbf hhf htotal
  have hnodes (j : ℕ) (hj : j ≤ as.length) :
      |q j-T*partitionValues f 0 as j| ≤ T*(mesh*E) := by
    have hv : partitionValues f 0 as j=f (partitionPoint 0 as j) := by
      have H (a : ℝ) (bs : List PositiveMass) (k : ℕ) :
          partitionValues f a bs k=f (partitionValues id a bs k) := by
        induction bs generalizing a k with
        | nil => rfl
        | cons b bs ih => cases k with
          | zero => rfl
          | succ k => exact ih b.val k
      exact H 0 as j
    rw [hv]
    by_cases hpos : 0 < partitionPoint 0 as j
    · have HS := finite_physical_mean_uniform_continuum_error n bf hf hbf hhf
        hroot as ho he hmesh0 hmesh j hj
      rw [native_physical_resource_center_at_positive_cut n bf hf hbf hhf as ho j hpos] at HS
      have HB : (bf (partitionPoint 0 as j):ℝ) ≤ T := by
        have H := htotal _ (partitionPoint_mem as ho j)
        linarith [(hf (partitionPoint 0 as j)).coe_nonneg]
      have hcancel : T*f (partitionPoint 0 as j)=actualMixedClock (n+1) bf hf
          (partitionPoint 0 as j) := by
        dsimp only [f]
        rw [actualScalarClockQuantile_on (n+1) bf hf hpos]
        field_simp
      rw [hcancel]
      change |(hf (partitionPoint 0 as j):ℝ)+
        (bf (partitionPoint 0 as j):ℝ)*finitePhysicalMean (n+1) as
          (retainedStarMatrix bf as) (retainedStarField hf as) j-
        ((hf (partitionPoint 0 as j):ℝ)+(bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (n+1) bf hf (partitionPoint 0 as j))| ≤ T*(mesh*E)
      rw [show ∀a b c : ℝ,a+b*c-(a+b*orderedPathS (n+1) bf hf
        (partitionPoint 0 as j))=b*(c-orderedPathS (n+1) bf hf
        (partitionPoint 0 as j)) by intros;ring]
      rw [abs_mul,abs_of_nonneg (bf _).coe_nonneg]
      exact mul_le_mul HB HS (abs_nonneg _) hT.le
    · have hj0 : j=0 := by
        cases as with
        | nil => simpa using hj
        | cons b bs => cases j with
          | zero => rfl
          | succ j =>
            exact False.elim (hpos (b.property.trans_le (partitionPoint_mem bs ho.2.2 j).1))
      subst j
      rw [hq0]
      have hp0 : partitionPoint 0 as 0=0 := by cases as <;> rfl
      simp only [hp0,f,actualScalarClockQuantile,le_refl,ite_eq_left,mul_zero,
        sub_zero,abs_zero]
      dsimp only [E]
      exact mul_nonneg hT.le (mul_nonneg hmesh0 (mul_nonneg
        (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg 2 0 0))
        (clockVariationBound_nonneg _ _ (completedPathClock_monotone (n+1) hbf hhf))))
  have Hq := normalizedScalarScheduleQuantile_l1_sample_error hT as ho q hq hq0
    f hfmono hmesh hnodes
  have Hcdf := quantileMassProfile_l1_le
    (normalizedScheduleQuantile T 0 (scalarBoundaryClocks as q)) f
    ((normalizedScheduleQuantile_monotone hT.le _).monotoneOn _) hfmono
    (normalizedScheduleQuantile_bounds hT le_rfl _ (by
      rw [zero_add,scalarBoundaryClocks_duration _ q hq,hq0,sub_zero]
      exact (retainedStarMixedClock_terminal_le n bf hf as ho he).trans
        (htotal 1 (by norm_num)))) hfb
  have H := Hcdf.trans Hq
  have Hvar : f 1-f 0 ≤ 1 := by linarith [(hfb 1 (by norm_num)).2,(hfb 0 (by norm_num)).1]
  apply H.trans
  have Hm := mul_le_mul_of_nonneg_left Hvar hmesh0
  dsimp only [E]
  nlinarith only [Hm]

theorem general_retained_scalar_schedule_cdf_l1_tendsto
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    Tendsto (fun k => ∫ t in (0:ℝ)..1,
      |(generalRetainedScalarScheduleProfile n bf hf hbf hhf hroot hT htotal (finiteCutMasses us k)
          (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)).val t-
        (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal).val t|) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => intervalIntegral.integral_nonneg zero_le_one
    (fun _ _ => abs_nonneg _))
    (fun k => general_retained_scalar_schedule_cdf_l1_error n bf hf hbf hhf hroot hT htotal _
      (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)
      (by positivity) (finiteCutMasses_mesh us hus k))
  simpa only [zero_mul] using uniformMasses_mesh_tendsto.mul_const
    (2*ClockTree.errorJetVariation 2 0 0*clockVariationBound
      (physicalFeatureCoordinateBound n) (completedPathClock (n+1) bf hf)+1)

end OAI.SKFluctuations.LaplaceWindowFormalization
