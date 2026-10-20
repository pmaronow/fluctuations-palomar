module

public import ComparisonActualHighOnlyOmittedClippedTrials
public import DownwardRampSupport

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem reciprocalFloorTime_strictMonoOn {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    StrictMonoOn (reciprocalFloorTime A B) (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hsB : 0 < s+B := add_pos_of_nonneg_of_pos hs hB
  have htB : 0 < t+B := add_pos_of_nonneg_of_pos ht hB
  have hd : A/(t+B) < A/(s+B) :=
    (div_lt_div_iff_of_pos_left hA htB hsB).mpr (by linarith)
  unfold reciprocalFloorTime
  linarith

theorem downwardRampBarrier_ge_height {A B H b : ℝ} {M : ℝ → ℝ}
    (hA : 0 < A) (hB : 0 < B) (hMc : Continuous M)
    (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hMp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < M u)
    (hH : 0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : H ≤ downwardRampBarrier A B M H b u := by
  have hbmem := downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu
  have hUmem := downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu
  have hpU := (reciprocalFloorTime_monotoneOn hA.le hB) hbmem hUmem
    (downwardBarrierBase_le_envelope hA hB hMc hm hMp hH hHroom u)
  have hclock : reciprocalFloorTime A B (downwardBarrierBase M H u) ≤ downwardBarrierClock A B M H b u :=
    le_min hpU (le_max_left _ _)
  have hwm := downwardRampBarrier_mem (b := b) hA hB hMc hm hMp hH hHroom hu
  have hid := reciprocalFloorInverse_right hA hB
    (downwardBarrierClock_mem (b := b) hA hB hMc hm hMp hH hHroom u hu)
  have hbase : downwardBarrierBase M H u ≤ downwardRampBarrier A B M H b u := by
    by_contra hn
    have hs := reciprocalFloorTime_strictMonoOn hA hB hwm.1 hbmem.1 (lt_of_not_ge hn)
    change reciprocalFloorTime A B (reciprocalFloorInverse A B (downwardBarrierClock A B M H b u)) < _ at hs
    rw [hid] at hs
    exact hs.not_ge hclock
  have hp := inverseCapPrimitive_nonneg hMc hm hMp hu
  unfold downwardBarrierBase at hbase
  linarith

def omittedUpwardRampBarrier (M : ℝ → ℝ) (r0 u0 a b speed u : ℝ) : ℝ :=
  r0-inverseCapPrimitive M u0+upwardRampBarrier M a b speed u

theorem explicit_downward_omitted_ramp_trial
    {r0 u0 A B c t H b : ℝ} {M : ℝ → ℝ}
    (hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
    (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (ht : t ∈ Icc (0 : ℝ) 1)
    (hkc : ∀ r ∈ Icc r0 1, c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0 : ℝ) 1))
    (hMp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < M u)
    (hH : r0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (htail : b+reciprocalFloorTime A B 1 ≤ 1)
    (hspeed : (M 0)⁻¹ ≤ B^2/A)
    (α : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M) :
    let hk := (reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)
    ∃ γ : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M,
      ∀ u ∈ Icc u0 1, γ.val.val (harmonicBarrierRadius B t
        (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 (by norm_num)).le α u)
        (min (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 (by norm_num)).le α u)
          (downwardRampBarrier A B M H b u))) = u := by
  dsimp only
  have hk := (reciprocalSquareFloor_continuousOn (A := A) hB).mono (Icc_subset_Icc hr0 le_rfl)
  have hH0 : 0 ≤ H := hr0.trans hH
  obtain ⟨D, hw⟩ := downwardRampBarrier_lipschitz (b := b) hA hB hMc hm hMp hH0 hHroom
  apply downward_clipped_omitted_comparison_trial hr0 hr1 hu hA hB hc ht hk hkc hMc hm
    (fun u hum => hMp u ⟨hu.1.trans hum.1, hum.2⟩) α
    (downwardRampBarrier A B M H b) (hw.mono (Icc_subset_Icc hu.1 le_rfl))
  · intro u hum
    exact hH.trans (downwardRampBarrier_ge_height hA hB hMc hm hMp hH0 hHroom
      ⟨hu.1.trans hum.1, hum.2⟩)
  · rw [downwardRampBarrier_one hA hB hMc hm hMp hH0 hHroom hb htail]
  · filter_upwards [downwardRampBarrier_ae_slope (b := b) hA hB hMc hm hMp hH0 hHroom hspeed]
      with u hd hum _
    exact hd ⟨hu.1.trans hum.1, hum.2⟩

theorem explicit_upward_omitted_ramp_trial
    {r0 u0 A B c t a b speed : ℝ} {M : ℝ → ℝ}
    (hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
    (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (ht : t ∈ Icc (0 : ℝ) 1)
    (hkc : ∀ r ∈ Icc r0 1, c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0 : ℝ) 1))
    (hMp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < M u)
    (ha : u0 ≤ a) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hrise : r0+inverseCapPrimitive M 1+speed*(b-a) ≤ 1)
    (hspeedroom : (M 0)⁻¹+speed ≤ B^2/A)
    (α : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M) :
    let hk := (reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)
    ∃ γ : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M,
      ∀ u ∈ Icc u0 1, γ.val.val ((1-t)*
        (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 (by norm_num)).le α u)+
        t*max (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 (by norm_num)).le α u)
          (omittedUpwardRampBarrier M r0 u0 a b speed u)) = u := by
  dsimp only
  have hk := (reciprocalSquareFloor_continuousOn (A := A) hB).mono (Icc_subset_Icc hr0 le_rfl)
  obtain ⟨D, hw⟩ := upwardRampBarrier_lipschitz hMc hm hMp a b speed
  have hw' : LipschitzOnWith D (omittedUpwardRampBarrier M r0 u0 a b speed) (Icc u0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hh := hw.dist_le_mul x ⟨hu.1.trans hx.1, hx.2⟩ y ⟨hu.1.trans hy.1, hy.2⟩
    simpa only [omittedUpwardRampBarrier, Real.dist_eq, add_sub_add_left_eq_sub] using hh
  apply upward_clipped_omitted_comparison_trial hr0 hr1 hu hA hB hc ht hk hkc hMc hm
    (fun u hum => hMp u ⟨hu.1.trans hum.1, hum.2⟩) α
    (omittedUpwardRampBarrier M r0 u0 a b speed) hw'
  · intro u hum
    have hh := (upwardRampBarrier_bounds hMc hm hMp hab hspeed ⟨hu.1.trans hum.1, hum.2⟩).2
    have hp := inverseCapPrimitive_nonneg hMc hm hMp hu
    unfold omittedUpwardRampBarrier
    linarith
  · simp [omittedUpwardRampBarrier, upwardRampBarrier, truncatedBarrierRamp_before ha]
  · filter_upwards [upwardRampBarrier_ae_slope hMc hm hMp hspeed] with u hd hum _
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans hum.1, hum.2⟩
    have he : deriv (omittedUpwardRampBarrier M r0 u0 a b speed) u =
        deriv (upwardRampBarrier M a b speed) u := by
      exact deriv_const_add (r0-inverseCapPrimitive M u0)
    rw [he]
    refine ⟨(hd hu').1, (hd hu').2.trans (hspeedroom.trans ?_)⟩
    have hr := omittedSweepQuantile_bounds hr1 hu hc hk hkc hm (hMp 1 (by norm_num)).le α u
    exact reciprocalSquareFloor_inverse_baseline hA hB (hr0.trans hr.1)

end OAI.SKFluctuations.LaplaceWindowFormalization
