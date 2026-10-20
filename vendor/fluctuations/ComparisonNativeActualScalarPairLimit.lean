module

public import ComparisonNativeActualScalarScheduleCDF
public import ComparisonSignedCavityScalarResponseL1

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem bare_retained_scalar_pair_tendsto
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k => nativeOriginalScalarPairMean (finiteCutMasses us k)
      (retainedStarMixedClock n M.bf M.hf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (scalarCovarianceResponse hT (M.bareScalarMassProfile hT hb hh)
        (actualMixedClock (n+1) M.bf M.hf u.val))) := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
  let a := fun k => M.bareRetainedScalarScheduleProfile hT hb hh (finiteCutMasses us k)
    (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)
  let q := fun k => retainedStarMixedClock n M.bf M.hf (finiteCutMasses us k)
    (retainedMassPrefixIndex u.val (finiteCutMasses us k))/T
  let r := actualMixedClock (n+1) M.bf M.hf u.val/T
  have hL1 := M.bare_retained_scalar_schedule_cdf_l1_tendsto hT hb hh us hus
  have hqa : Tendsto q atTop (𝓝 r) :=
    (retainedStarMixedClock_tendsto n M.bf M.hf hbf hhf us hus u hu).div_const T
  have hqbound (k : ℕ) : q k∈Icc (0:ℝ) 1 := by
    have ho := finiteCutMasses_ordered us hus k
    have hm := retainedStarMixedClock_monotone n M.bf M.hf hbf hhf _ ho
    have ht := (retainedStarMixedClock_terminal_le n M.bf M.hf _ ho
      (finiteCutMasses_end us hus k)).trans (M.bare_total_clock_le hb hh (by norm_num))
    exact ⟨div_nonneg (retainedStarMixedClock_nonneg n M.bf M.hf _ _) hT.le,
      (div_le_one₀ hT).mpr ((hm (retainedMassPrefixIndex_le_length u.val _)).trans ht)⟩
  have hrbound : r∈Icc (0:ℝ) 1 := by
    have H := M.bare_scalar_clock_unit_bounds hT hb hh u.val ⟨u.property.le,hus u hu⟩
    simpa only [actualScalarClockQuantile_on (n+1) M.bf M.hf u.property,r] using H
  have H := scalarPlantedEnergy_L1_varying_clock_tendsto hT hL1
    (fun k x => quantileMassProfile_right_continuous _ _ x) hqbound hrbound hqa
  have he (k : ℕ) : nativeOriginalScalarPairMean (finiteCutMasses us k)
      (retainedStarMixedClock n M.bf M.hf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k)) = scalarPlantedEnergy hT (a k) (q k) := by
    have ho := finiteCutMasses_ordered us hus k
    have ht := (retainedStarMixedClock_terminal_le n M.bf M.hf _ ho
      (finiteCutMasses_end us hus k)).trans (M.bare_total_clock_le hb hh (by norm_num))
    exact native_scalar_pairClock_eq_fixed_schedule_response hT _ ho _
      (retainedStarMixedClock_monotone n M.bf M.hf hbf hhf _ ho)
      (M.bare_retainedStarMixedClock_zero (hh 0) ho) ht _
      (retainedMassPrefixIndex_le_length u.val _)
  simp_rw [he]
  exact H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
