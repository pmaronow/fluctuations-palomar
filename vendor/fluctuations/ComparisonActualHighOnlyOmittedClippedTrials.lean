module

public import ComparisonActualHighOnlyOmittedHarmonicTrial
public import ComparisonActualHighOnlyIntervalClippingSlopes

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

private theorem omitted_const_mul_lipschitzOn {C : ℝ≥0} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : LipschitzOnWith C f s) (t : ℝ) :
    LipschitzOnWith (‖t‖₊*C) (fun u => t*f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg t)
  simpa only [Real.dist_eq, ← mul_sub, abs_mul, Real.norm_eq_abs, NNReal.coe_mul, coe_nnnorm, mul_assoc] using hh

section
variable {r0 u0 A B c t : ℝ} {M : ℝ → ℝ}
variable (hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
variable (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (ht : t ∈ Icc (0 : ℝ) 1)
variable (hk : ContinuousOn (reciprocalSquareFloor A B) (Icc r0 1))
variable (hkc : ∀ r ∈ Icc r0 1, c ≤ reciprocalSquareFloor A B r)
variable (hMc : Continuous M) (hm : MonotoneOn M (Icc (0 : ℝ) 1))
variable (hMp : ∀ u ∈ Icc u0 1, 0 < M u)
include hA hB hMc ht hr0

theorem downward_clipped_omitted_comparison_trial
    (α : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M)
    (w : ℝ → ℝ) {D : ℝ≥0} (hw : LipschitzOnWith D w (Icc u0 1))
    (hwb : ∀ u ∈ Icc u0 1, r0 ≤ w u) (hw1 : 1 ≤ w 1)
    (hdw : ∀ᵐ u ∂volume, u ∈ Icc u0 1 →
      w u ≤ omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u →
      (M u)⁻¹ ≤ deriv w u ∧ deriv w u ≤ (reciprocalSquareFloor A B (w u))⁻¹) :
    ∃ γ : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M,
      ∀ u ∈ Icc u0 1, γ.val.val (harmonicBarrierRadius B t
        (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u)
        (min (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u) (w u))) = u := by
  let k := reciprocalSquareFloor A B
  have hM1 : 0 < M 1 := hMp 1 ⟨hu.2, le_rfl⟩
  let r := omittedSweepQuantile hr1 hu hc hk hkc hm hM1.le α
  let v := fun u => min (r u) (w u)
  have hrl : LipschitzOnWith _ r (Icc u0 1) :=
    (omittedSweepQuantile_lipschitz hr1 hu hc hk hkc hm hM1.le α).lipschitzOnWith
  have hrb (u : ℝ) : r u ∈ Icc r0 1 := omittedSweepQuantile_bounds hr1 hu hc hk hkc hm hM1.le α u
  have hvl : LipschitzOnWith _ v (Icc u0 1) := real_min_lipschitzOn hrl hw
  have hvb : MapsTo v (Icc u0 1) (Icc r0 1) := by
    intro u hum
    exact ⟨le_min (hrb u).1 (hwb u hum), (min_le_left _ _).trans (hrb u).2⟩
  have hv0 : v u0 = r0 := by
    dsimp [v, r]
    rw [omittedSweepQuantile_left hr1 hu hc hk hkc hm hM1.le α]
    exact min_eq_left (hwb u0 ⟨le_rfl, hu.2⟩)
  have hv1 : v 1 = 1 := by
    dsimp [v, r]
    rw [omittedSweepQuantile_one hr1 hu hc hk hkc hm hM1.le α]
    exact min_eq_left hw1
  have hvr := interval_clipped_min_ae_slope hu.2 (lower := fun u => (M u)⁻¹)
    (upper := fun q => (k q)⁻¹) hrl hw
    (omittedSweepQuantile_ae_slope hr1 hu hc hk hkc hm hM1.le α hMc hMp) hdw
  obtain ⟨β, hβ⟩ := exists_omitted_inverse_profile_of_forward_slope hr1 hu hvl hvb hv0 hv1 hk hMc hm
    (fun y hym => hc.trans_le (hkc y hym)) hMp hvr
  have hqβ (u : ℝ) (hum : u ∈ Icc u0 1) :
      omittedSweepQuantile hr1 hu hc hk hkc hm hM1.le β u = v u := by
    have he := omittedSweepQuantile_inverse hr1 hu hc hk hkc hm hM1.le β (hvb hum)
    rw [hβ u hum] at he
    exact he
  obtain ⟨γ, hγ⟩ := harmonic_omitted_comparison_trial_feasible hr0 hr1 hu hA hB hc ht hkc hMc hm hMp α β
  refine ⟨γ, ?_⟩
  intro u hum
  have he := hγ u hum
  rw [hqβ u hum] at he
  exact he

theorem upward_clipped_omitted_comparison_trial
    (α : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M)
    (w : ℝ → ℝ) {D : ℝ≥0} (hw : LipschitzOnWith D w (Icc u0 1))
    (hwb : ∀ u ∈ Icc u0 1, w u ≤ 1) (hw0 : w u0 ≤ r0)
    (hdw : ∀ᵐ u ∂volume, u ∈ Icc u0 1 →
      omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u ≤ w u →
      (M u)⁻¹ ≤ deriv w u ∧ deriv w u ≤
        (reciprocalSquareFloor A B
          (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u))⁻¹) :
    ∃ γ : inverseIntegralConstraints r0 u0 (reciprocalSquareFloor A B) M,
      ∀ u ∈ Icc u0 1, γ.val.val ((1-t)*
        (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u)+
        t*max (omittedSweepQuantile hr1 hu hc hk hkc hm (hMp 1 ⟨hu.2, le_rfl⟩).le α u) (w u)) = u := by
  let k := reciprocalSquareFloor A B
  have hM1 : 0 < M 1 := hMp 1 ⟨hu.2, le_rfl⟩
  let r := omittedSweepQuantile hr1 hu hc hk hkc hm hM1.le α
  let v := fun u => max (r u) (w u)
  let q := fun u => (1-t)*r u+t*v u
  have hrl : LipschitzOnWith _ r (Icc u0 1) :=
    (omittedSweepQuantile_lipschitz hr1 hu hc hk hkc hm hM1.le α).lipschitzOnWith
  have hrb (u : ℝ) : r u ∈ Icc r0 1 := omittedSweepQuantile_bounds hr1 hu hc hk hkc hm hM1.le α u
  have hvl : LipschitzOnWith _ v (Icc u0 1) := real_max_lipschitzOn hrl hw
  have hvb : MapsTo v (Icc u0 1) (Icc r0 1) := by
    intro u hum
    exact ⟨(hrb u).1.trans (le_max_left _ _), max_le (hrb u).2 (hwb u hum)⟩
  have hvr := interval_clipped_max_ae_slope_at_parent hu.2 (lower := fun u => (M u)⁻¹)
    (upper := fun u => (k (r u))⁻¹) hrl hw
    (omittedSweepQuantile_ae_slope hr1 hu hc hk hkc hm hM1.le α hMc hMp) hdw
  have hql : LipschitzOnWith _ q (Icc u0 1) :=
    (omitted_const_mul_lipschitzOn hrl (1-t)).add (omitted_const_mul_lipschitzOn hvl t)
  have hqb : MapsTo q (Icc u0 1) (Icc r0 1) := by
    intro u hum
    have hl := add_le_add (mul_le_mul_of_nonneg_left (hrb u).1 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hvb hum).1 ht.1)
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hrb u).2 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hvb hum).2 ht.1)
    dsimp [q]
    constructor <;> nlinarith
  have hv0 : v u0 = r0 := by
    dsimp [v, r]
    rw [omittedSweepQuantile_left hr1 hu hc hk hkc hm hM1.le α]
    exact max_eq_left hw0
  have hv1 : v 1 = 1 := by
    dsimp [v, r]
    rw [omittedSweepQuantile_one hr1 hu hc hk hkc hm hM1.le α]
    exact max_eq_left (hwb 1 ⟨hu.2, le_rfl⟩)
  have hq0 : q u0 = r0 := by
    dsimp [q, r]
    rw [omittedSweepQuantile_left hr1 hu hc hk hkc hm hM1.le α, hv0]
    ring
  have hq1 : q 1 = 1 := by
    dsimp [q, r]
    rw [omittedSweepQuantile_one hr1 hu hc hk hkc hm hM1.le α, hv1]
    ring
  have hacr : AbsolutelyContinuousOnInterval r u0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hu.2] using hrl
  have hacv : AbsolutelyContinuousOnInterval v u0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hu.2] using hvl
  have hder : ∀ᵐ u ∂volume, u ∈ Icc u0 1 → (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹ := by
    filter_upwards [omittedSweepQuantile_ae_slope hr1 hu hc hk hkc hm hM1.le α hMc hMp,
      hvr, hacr.ae_differentiableAt, hacv.ae_differentiableAt] with u hr hv hdr hdv hum
    have hum' : u ∈ uIcc u0 1 := by simpa only [uIcc_of_le hu.2] using hum
    have hd := (((hdr hum').hasDerivAt.const_mul (1-t)).add ((hdv hum').hasDerivAt.const_mul t)).deriv
    change deriv q u = (1-t)*deriv r u+t*deriv v u at hd
    have hlo := add_le_add (mul_le_mul_of_nonneg_left (hr hum).1 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hv hum).1 ht.1)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left (hr hum).2 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hv hum).2 ht.1)
    have hrq : r u ≤ q u := by
      have hh := mul_nonneg ht.1 (sub_nonneg.mpr (show r u ≤ v u from le_max_left _ _))
      dsimp [q]
      nlinarith
    have hkq : k (q u) ≤ k (r u) := by
      have hR : 0 < r u+B := by linarith [(hrb u).1]
      have hQ : 0 < q u+B := by linarith [(hqb hum).1]
      have hs : (r u+B)^2 ≤ (q u+B)^2 := by nlinarith [hrq]
      dsimp [k, reciprocalSquareFloor]
      exact div_le_div_of_nonneg_left hA.le (sq_pos_of_pos hR) hs
    have hkr : 0 < k (r u) := hc.trans_le (hkc (r u) (hrb u))
    have hkq' : 0 < k (q u) := hc.trans_le (hkc (q u) (hqb hum))
    have hinv := (inv_le_inv₀ hkr hkq').mpr hkq
    rw [hd]
    constructor
    · nlinarith
    · exact (by nlinarith : (1-t)*deriv r u+t*deriv v u ≤ (k (r u))⁻¹).trans hinv
  exact exists_omitted_inverse_profile_of_forward_slope hr1 hu hql hqb hq0 hq1 hk hMc hm
    (fun u hum => hc.trans_le (hkc u hum)) hMp hder
end
end OAI.SKFluctuations.LaplaceWindowFormalization
