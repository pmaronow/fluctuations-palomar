module

public import ComparisonNativeContinuumScalarScheduleCDF
public import ComparisonSignedCavityScalarResponseL1

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
variable {T : ℝ}

theorem continuum_retained_scalar_pair_tendsto
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k => nativeOriginalScalarPairMean (finiteCutMasses us k)
      (nativeContinuumMixedClock n bf hf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (scalarCovarianceResponse hT (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal)
        (actualMixedClock (n+1) bf hf u.val))) := by
  let a := fun k => continuumRetainedScalarScheduleProfile n bf hf hbf hhf hroot hT htotal (finiteCutMasses us k)
    (finiteCutMasses_ordered us hus k)
  let q := fun k => nativeContinuumMixedClock n bf hf (finiteCutMasses us k)
    (retainedMassPrefixIndex u.val (finiteCutMasses us k))/T
  let r := actualMixedClock (n+1) bf hf u.val/T
  have hL1 := continuum_retained_scalar_schedule_cdf_l1_tendsto n bf hf hbf hhf hroot hT htotal us hus
  have hqe (k : ℕ) : q k=r := by
    dsimp only [q,r]
    rw [native_continuum_mixed_clock_retained_eq n bf hf (finiteCutMasses us k)
      (finiteCutMasses_ordered us hus k) u (finiteCutMasses_nodes us k hu)]
  have hqa : Tendsto q atTop (𝓝 r) := by
    rw [show q=(fun _=>r) from funext hqe]
    exact tendsto_const_nhds
  have hqbound (k : ℕ) : q k∈Icc (0:ℝ) 1 := by
    have ho := finiteCutMasses_ordered us hus k
    have hm := native_continuum_mixed_clock_monotone n bf hf hbf hhf _ ho
    have ht := (native_continuum_mixed_clock_terminal_le n bf hf hbf hhf _ ho).trans (htotal 1 (by norm_num))
    exact ⟨div_nonneg (native_continuum_mixed_clock_nonneg n bf hf hbf hhf _ ho _) hT.le,
      (div_le_one₀ hT).mpr ((hm (retainedMassPrefixIndex_le_length u.val _)).trans ht)⟩
  have hrbound : r∈Icc (0:ℝ) 1 := by
    have H := actualScalarClockQuantile_bounds hT (n+1) (by omega) bf hf hbf hhf htotal u.val ⟨u.property.le,hus u hu⟩
    simpa only [actualScalarClockQuantile_on (n+1) bf hf u.property,r] using H
  have H := scalarPlantedEnergy_L1_varying_clock_tendsto hT hL1
    (fun k x => quantileMassProfile_right_continuous _ _ x) hqbound hrbound hqa
  have he (k : ℕ) : nativeOriginalScalarPairMean (finiteCutMasses us k)
      (nativeContinuumMixedClock n bf hf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k)) = scalarPlantedEnergy hT (a k) (q k) := by
    have ho := finiteCutMasses_ordered us hus k
    have ht := (native_continuum_mixed_clock_terminal_le n bf hf hbf hhf _ ho).trans (htotal 1 (by norm_num))
    exact native_scalar_pairClock_eq_fixed_schedule_response hT _ ho _
      (native_continuum_mixed_clock_monotone n bf hf hbf hhf _ ho)
      (native_continuum_mixed_clock_zero_of_zero_root_field n bf hf hroot _) ht _
      (retainedMassPrefixIndex_le_length u.val _)
  simp_rw [he]
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
