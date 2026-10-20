module

public import OmittedConstrainedForwardGeometry
public import HarmonicQuantileFeasibility

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem harmonicBarrierRadius_mem_wall {r0 B t r v : ℝ}
    (hr0 : 0 ≤ r0) (hB : 0 < B) (ht : t ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc r0 1) (hv : v ∈ Icc r0 1) :
    harmonicBarrierRadius B t r v ∈ Icc r0 1 := by
  have hh := harmonicBarrierRadius_mem hB ht ⟨hr0.trans hr.1, hr.2⟩ ⟨hr0.trans hv.1, hv.2⟩
  have hs := harmonicBarrierRadius_mem (r := r-r0) (v := v-r0) (by linarith : 0 < B+r0) ht
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hid : harmonicBarrierRadius (B+r0) t (r-r0) (v-r0) = harmonicBarrierRadius B t r v-r0 := by
    unfold harmonicBarrierRadius
    rw [show r-r0+(B+r0) = r+B by ring, show v-r0+(B+r0) = v+B by ring]
    ring
  rw [hid] at hs
  exact ⟨by linarith [hs.1], hh.2⟩

theorem harmonic_omitted_comparison_trial_feasible
    {r0 u0 A B c t : ℝ} {M : ℝ → ℝ}
    (hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
    (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (ht : t ∈ Icc (0 : ℝ) 1)
    (hkc : ∀ r ∈ Icc r0 1, c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0 : ℝ) 1))
    (hMp : ∀ u ∈ Icc u0 1, 0 < M u)
    (α β : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M) :
    let hk := (reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)
    let hM := (hMp 1 ⟨hu.2, le_rfl⟩).le
    ∃ γ : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M,
      ∀ u ∈ Icc u0 1, γ.val.val (harmonicBarrierRadius B t
        (omittedSweepQuantile hr1 hu hc hk hkc hm hM α u)
        (omittedSweepQuantile hr1 hu hc hk hkc hm hM β u)) = u := by
  dsimp only
  let k := reciprocalSquareFloor A B
  have hk : ContinuousOn k (Icc r0 1) :=
    (reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)
  have hM1 : 0 < M 1 := hMp 1 ⟨hu.2, le_rfl⟩
  let r := omittedSweepQuantile hr1 hu hc hk hkc hm hM1.le α
  let v := omittedSweepQuantile hr1 hu hc hk hkc hm hM1.le β
  let q := fun u => harmonicBarrierRadius B t (r u) (v u)
  have hrb (u : ℝ) : r u ∈ Icc r0 1 := omittedSweepQuantile_bounds hr1 hu hc hk hkc hm hM1.le α u
  have hvb (u : ℝ) : v u ∈ Icc r0 1 := omittedSweepQuantile_bounds hr1 hu hc hk hkc hm hM1.le β u
  have hrl := omittedSweepQuantile_lipschitz hr1 hu hc hk hkc hm hM1.le α
  have hvl := omittedSweepQuantile_lipschitz hr1 hu hc hk hkc hm hM1.le β
  obtain ⟨C, hqall⟩ := harmonicBarrierRadius_lipschitz hB ht
    hrl.lipschitzOnWith hvl.lipschitzOnWith
    (fun u _ => ⟨hr0.trans (hrb u).1, (hrb u).2⟩)
    (fun u _ => ⟨hr0.trans (hvb u).1, (hvb u).2⟩)
  have hql : LipschitzOnWith C q (Icc u0 1) :=
    hqall.mono (Icc_subset_Icc hu.1 le_rfl)
  have hqb : MapsTo q (Icc u0 1) (Icc r0 1) :=
    fun u _ => harmonicBarrierRadius_mem_wall hr0 hB ht (hrb u) (hvb u)
  have hq0 : q u0 = r0 := by
    dsimp [q, r, v]
    rw [omittedSweepQuantile_left hr1 hu hc hk hkc hm hM1.le α,
      omittedSweepQuantile_left hr1 hu hc hk hkc hm hM1.le β]
    exact harmonicBarrierRadius_diagonal hB hr0
  have hq1 : q 1 = 1 := by
    dsimp [q, r, v]
    rw [omittedSweepQuantile_one hr1 hu hc hk hkc hm hM1.le α,
      omittedSweepQuantile_one hr1 hu hc hk hkc hm hM1.le β]
    exact harmonicBarrierRadius_diagonal hB zero_le_one
  have hacr : AbsolutelyContinuousOnInterval r u0 1 := by
    exact hrl.lipschitzOnWith.absolutelyContinuousOnInterval
  have hacv : AbsolutelyContinuousOnInterval v u0 1 := by
    exact hvl.lipschitzOnWith.absolutelyContinuousOnInterval
  have hder : ∀ᵐ u ∂volume, u ∈ Icc u0 1 →
      (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹ := by
    filter_upwards [omittedSweepQuantile_ae_slope hr1 hu hc hk hkc hm hM1.le α hMc hMp,
      omittedSweepQuantile_ae_slope hr1 hu hc hk hkc hm hM1.le β hMc hMp,
      hacr.ae_differentiableAt, hacv.ae_differentiableAt] with u hr hv hdr hdv hum
    have hum' : u ∈ uIcc u0 1 := by simpa only [uIcc_of_le hu.2] using hum
    have hD := harmonicBarrierRadius_derivative (hdr hum').hasDerivAt (hdv hum').hasDerivAt
      (by linarith [(hrb u).1] : r u+B ≠ 0) (by linarith [(hvb u).1] : v u+B ≠ 0)
      (harmonicBarrierDenominator_pos hB ht (hr0.trans (hrb u).1) (hr0.trans (hvb u).1)).ne'
    have hb := harmonicBarrierDerivative_slope_bounds hA hB ht
      (hr0.trans (hrb u).1) (hr0.trans (hvb u).1)
      (inv_nonneg.mpr (hMp u hum).le) (hr hum) (hv hum)
    change (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹
    rw [hD.deriv]
    exact hb
  exact exists_omitted_inverse_profile_of_forward_slope hr1 hu hql hqb hq0 hq1 hk hMc hm
    (fun y hym => hc.trans_le (hkc y hym)) hMp hder

end OAI.SKFluctuations.LaplaceWindowFormalization
