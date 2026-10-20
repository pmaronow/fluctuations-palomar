module

public import ComparisonSignedCavityScalarScheduleSample
public import ComparisonSignedCavityPhysicalMeanUniform
public import ComparisonNativeActualScalarProfile
public import ComparisonSignedCavityPhysicalBareRootZero

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

def bareRetainedScalarScheduleProfile
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀ u,M.b u=T) (hh : ∀ u,M.h u=0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    boundedMassProfiles :=
  actualScalarScheduleMass hT (scalarBoundaryClocks as (retainedStarMixedClock n M.bf M.hf as))
    (by
      have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
        M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
        M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
      rw [scalarBoundaryClocks_duration _ _ (retainedStarMixedClock_monotone n M.bf M.hf
          (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as ho),
        M.bare_retainedStarMixedClock_zero (hh 0) ho, sub_zero]
      exact (retainedStarMixedClock_terminal_le n M.bf M.hf as ho he).trans
        (M.bare_total_clock_le hb hh (by norm_num)))

theorem bare_retained_scalar_schedule_cdf_l1_error
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀ u,M.b u=T) (hh : ∀ u,M.h u=0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh : PartitionMesh mesh 0 as) :
    (∫ t in (0:ℝ)..1,
      |(M.bareRetainedScalarScheduleProfile hT hb hh as ho he).val t-
        (M.bareScalarMassProfile hT hb hh).val t|) ≤
      mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n)
          (completedPathClock (n+1) M.bf M.hf)+1) := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
  let q := retainedStarMixedClock n M.bf M.hf as
  let f := actualScalarClockQuantile T (n+1) M.bf M.hf
  let E := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) M.bf M.hf)
  have hq : Monotone q := retainedStarMixedClock_monotone n M.bf M.hf hbf hhf as ho
  have hq0 : q 0=0 := M.bare_retainedStarMixedClock_zero (hh 0) ho
  have hf : MonotoneOn f (Icc (0:ℝ) 1) :=
    actualScalarClockQuantile_monotone hT (n+1) (by omega) M.bf M.hf hbf hhf
  have hfb := M.bare_scalar_clock_unit_bounds hT hb hh
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
    · have HS := finite_physical_mean_uniform_continuum_error n M.bf M.hf hbf hhf
        (M.bare_root_field_zero (hh 0)) as ho he hmesh0 hmesh j hj
      rw [native_physical_resource_center_at_positive_cut n M.bf M.hf hbf hhf as ho j hpos] at HS
      have HB : (M.bf (partitionPoint 0 as j):ℝ) ≤ T := by
        have H := M.bare_total_clock_le hb hh (partitionPoint_mem as ho j)
        linarith [(M.hf (partitionPoint 0 as j)).coe_nonneg]
      have hcancel : T*f (partitionPoint 0 as j)=actualMixedClock (n+1) M.bf M.hf
          (partitionPoint 0 as j) := by
        dsimp only [f]
        rw [actualScalarClockQuantile_on (n+1) M.bf M.hf hpos]
        field_simp
      rw [hcancel]
      change |(M.hf (partitionPoint 0 as j):ℝ)+
        (M.bf (partitionPoint 0 as j):ℝ)*finitePhysicalMean (n+1) as
          (retainedStarMatrix M.bf as) (retainedStarField M.hf as) j-
        ((M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))| ≤ T*(mesh*E)
      rw [show ∀a b c : ℝ,a+b*c-(a+b*orderedPathS (n+1) M.bf M.hf
        (partitionPoint 0 as j))=b*(c-orderedPathS (n+1) M.bf M.hf
        (partitionPoint 0 as j)) by intros;ring]
      rw [abs_mul,abs_of_nonneg (M.bf _).coe_nonneg]
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
    f hf hmesh hnodes
  have Hcdf := quantileMassProfile_l1_le
    (normalizedScheduleQuantile T 0 (scalarBoundaryClocks as q)) f
    ((normalizedScheduleQuantile_monotone hT.le _).monotoneOn _) hf
    (normalizedScheduleQuantile_bounds hT le_rfl _ (by
      rw [zero_add,scalarBoundaryClocks_duration _ q hq,hq0,sub_zero]
      exact (retainedStarMixedClock_terminal_le n M.bf M.hf as ho he).trans
        (M.bare_total_clock_le hb hh (by norm_num)))) hfb
  have H := Hcdf.trans Hq
  have Hvar : f 1-f 0 ≤ 1 := by linarith [(hfb 1 (by norm_num)).2,(hfb 0 (by norm_num)).1]
  apply H.trans
  have Hm := mul_le_mul_of_nonneg_left Hvar hmesh0
  dsimp only [E]
  nlinarith only [Hm]

theorem bare_retained_scalar_schedule_cdf_l1_tendsto
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀ u,M.b u=T) (hh : ∀ u,M.h u=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    Tendsto (fun k => ∫ t in (0:ℝ)..1,
      |(M.bareRetainedScalarScheduleProfile hT hb hh (finiteCutMasses us k)
          (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)).val t-
        (M.bareScalarMassProfile hT hb hh).val t|) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => intervalIntegral.integral_nonneg zero_le_one
    (fun _ _ => abs_nonneg _))
    (fun k => M.bare_retained_scalar_schedule_cdf_l1_error hT hb hh _
      (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)
      (by positivity) (finiteCutMasses_mesh us hus k))
  simpa only [zero_mul] using uniformMasses_mesh_tendsto.mul_const
    (2*ClockTree.errorJetVariation 2 0 0*clockVariationBound
      (physicalFeatureCoordinateBound n) (completedPathClock (n+1) M.bf M.hf)+1)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
