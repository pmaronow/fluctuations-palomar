module

public import HarmonicQuantileFeasibility
public import ClippedBarrierGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

private theorem barrier_const_mul_lipschitzOn {C : ℝ≥0} {s : Set ℝ} {f : ℝ→ℝ}
    (hf : LipschitzOnWith C f s) (t : ℝ) :
    LipschitzOnWith (‖t‖₊*C) (fun u=>t*f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg t)
  simpa only [Real.dist_eq,←mul_sub,abs_mul,Real.norm_eq_abs,NNReal.coe_mul,coe_nnnorm,mul_assoc] using hh

section
variable {A B c t : ℝ} {M : ℝ→ℝ}
variable (hA : 0<A) (hB : 0<B) (hc : 0<c) (ht : t∈Icc (0:ℝ) 1)
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤reciprocalSquareFloor A B r)
variable (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
variable (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
include hA hMc ht

theorem downward_clipped_comparison_trial
    (α : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M)
    (w : ℝ→ℝ) {D : ℝ≥0} (hw : LipschitzOnWith D w (Icc (0:ℝ) 1))
    (hwb : ∀u∈Icc (0:ℝ) 1,0≤w u) (hw1 : 1≤w 1)
    (hdw : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 →
      w u≤comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
        (hMp 1 (by norm_num)).le α u →
      (M u)⁻¹≤deriv w u ∧ deriv w u≤(reciprocalSquareFloor A B (w u))⁻¹) :
    ∃γ : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      ∀u∈Icc (0:ℝ) 1,γ.val.val (harmonicBarrierRadius B t
        (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u)
        (min (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u) (w u)))=u := by
  let k := reciprocalSquareFloor A B
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := reciprocalSquareFloor_continuousOn hB
  have hM1 : 0<M 1 := hMp 1 (by norm_num)
  let r := comparisonSweepQuantile hc hk hkc hm hM1.le α
  let v := fun u=>min (r u) (w u)
  have hrl := comparisonSweepQuantile_lipschitzOn hc hk hkc hm hM1.le α
  have hrb (u : ℝ) : r u∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds hc hk hkc hm hM1.le α u
  have hvl : LipschitzOnWith _ v (Icc (0:ℝ) 1) := real_min_lipschitzOn hrl hw
  have hvb : MapsTo v (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
    intro u hu
    exact ⟨le_min (hrb u).1 (hwb u hu),(min_le_left _ _).trans (hrb u).2⟩
  have hv0 : v 0=0 := by
    dsimp [v,r]
    rw [comparisonSweepQuantile_zero hc hk hkc hm hM1.le α]
    exact min_eq_left (hwb 0 (by norm_num))
  have hv1 : v 1=1 := by
    dsimp [v,r]
    rw [comparisonSweepQuantile_one hc hk hkc hm hM1.le α]
    exact min_eq_left hw1
  have hvr := clipped_min_ae_slope (lower := fun u=>(M u)⁻¹) (upper := fun q=>(k q)⁻¹) hrl hw
    (comparisonSweepQuantile_ae_slope hc hk hkc hm hM1.le α hMc hMp) hdw
  obtain ⟨β,hβ⟩ := exists_inverse_profile_of_forward_slope hvl hvb hv0 hv1 hk hMc hm
    (fun q hq=>hc.trans_le (hkc q hq)) hMp hvr
  have hqβ (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      comparisonSweepQuantile hc hk hkc hm hM1.le β u=v u := by
    have he := comparisonSweepQuantile_inverse hc hk hkc hm hM1.le β (hvb hu)
    rw [hβ u hu] at he
    exact he
  obtain ⟨γ,hγ⟩ := harmonic_comparison_trial_feasible hA hB hc ht hkc hMc hm hMp α β
  refine ⟨γ,?_⟩
  intro u hu
  have he := hγ u hu
  rw [hqβ u hu] at he
  exact he

theorem upward_clipped_comparison_trial
    (α : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M)
    (w : ℝ→ℝ) {D : ℝ≥0} (hw : LipschitzOnWith D w (Icc (0:ℝ) 1))
    (hwb : ∀u∈Icc (0:ℝ) 1,w u≤1) (hw0 : w 0≤0)
    (hdw : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 →
      comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
        (hMp 1 (by norm_num)).le α u≤w u →
      (M u)⁻¹≤deriv w u ∧ deriv w u≤
        (reciprocalSquareFloor A B (comparisonSweepQuantile hc
          (reciprocalSquareFloor_continuousOn hB) hkc hm (hMp 1 (by norm_num)).le α u))⁻¹) :
    ∃γ : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      ∀u∈Icc (0:ℝ) 1,γ.val.val ((1-t)*
        (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u)+t*
        (max (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u) (w u)))=u := by
  let k := reciprocalSquareFloor A B
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := reciprocalSquareFloor_continuousOn hB
  have hM1 : 0<M 1 := hMp 1 (by norm_num)
  let r := comparisonSweepQuantile hc hk hkc hm hM1.le α
  let v := fun u=>max (r u) (w u)
  let q := fun u=>(1-t)*r u+t*v u
  have hrl := comparisonSweepQuantile_lipschitzOn hc hk hkc hm hM1.le α
  have hrb (u : ℝ) : r u∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds hc hk hkc hm hM1.le α u
  have hvl : LipschitzOnWith _ v (Icc (0:ℝ) 1) := real_max_lipschitzOn hrl hw
  have hvb : MapsTo v (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
    intro u hu
    exact ⟨(hrb u).1.trans (le_max_left _ _),max_le (hrb u).2 (hwb u hu)⟩
  have hvr := clipped_max_ae_slope_at_parent (lower := fun u=>(M u)⁻¹)
    (upper := fun u=>(k (r u))⁻¹) hrl hw
    (comparisonSweepQuantile_ae_slope hc hk hkc hm hM1.le α hMc hMp) hdw
  have hql : LipschitzOnWith _ q (Icc (0:ℝ) 1) :=
    (barrier_const_mul_lipschitzOn hrl (1-t)).add (barrier_const_mul_lipschitzOn hvl t)
  have hqb : MapsTo q (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
    intro u hu
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hrb u).2 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hvb hu).2 ht.1)
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hrb u).1) (mul_nonneg ht.1 (hvb hu).1)
    · dsimp [q]
      nlinarith
  have hv0 : v 0=0 := by
    dsimp [v,r]
    rw [comparisonSweepQuantile_zero hc hk hkc hm hM1.le α]
    exact max_eq_left hw0
  have hv1 : v 1=1 := by
    dsimp [v,r]
    rw [comparisonSweepQuantile_one hc hk hkc hm hM1.le α]
    exact max_eq_left (hwb 1 (by norm_num))
  have hq0 : q 0=0 := by
    dsimp [q,r]
    rw [comparisonSweepQuantile_zero hc hk hkc hm hM1.le α,hv0]
    ring
  have hq1 : q 1=1 := by
    dsimp [q,r]
    rw [comparisonSweepQuantile_one hc hk hkc hm hM1.le α,hv1]
    ring
  have hacr : AbsolutelyContinuousOnInterval r 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨c⁻¹,inv_nonneg.mpr hc.le⟩)
    simpa only [uIcc_of_le zero_le_one] using hrl
  have hacv : AbsolutelyContinuousOnInterval v 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using hvl
  have hder : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹ := by
    filter_upwards [comparisonSweepQuantile_ae_slope hc hk hkc hm hM1.le α hMc hMp,
      hvr,hacr.ae_differentiableAt,hacv.ae_differentiableAt] with u hr hv hdr hdv hu
    have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
    have hd := (((hdr hu').hasDerivAt.const_mul (1-t)).add ((hdv hu').hasDerivAt.const_mul t)).deriv
    change deriv q u=(1-t)*deriv r u+t*deriv v u at hd
    have hlo := add_le_add (mul_le_mul_of_nonneg_left (hr hu).1 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hv hu).1 ht.1)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left (hr hu).2 (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hv hu).2 ht.1)
    have hrq : r u≤q u := by
      have hh := mul_nonneg ht.1 (sub_nonneg.mpr (show r u≤v u from le_max_left _ _))
      dsimp [q]
      nlinarith
    have hkq : k (q u)≤k (r u) := by
      have hR : 0<r u+B := by linarith [(hrb u).1]
      have hQ : 0<q u+B := by linarith [(hqb hu).1]
      have hs : (r u+B)^2≤(q u+B)^2 := by nlinarith [hrq]
      dsimp [k,reciprocalSquareFloor]
      exact div_le_div_of_nonneg_left hA.le (sq_pos_of_pos hR) hs
    have hkr : 0<k (r u) := hc.trans_le (hkc (r u) (hrb u))
    have hkq' : 0<k (q u) := hc.trans_le (hkc (q u) (hqb hu))
    have hinv := (inv_le_inv₀ hkr hkq').mpr hkq
    rw [hd]
    constructor
    · nlinarith
    · exact (by nlinarith : (1-t)*deriv r u+t*deriv v u≤(k (r u))⁻¹).trans hinv
  exact exists_inverse_profile_of_forward_slope hql hqb hq0 hq1 hk hMc hm
    (fun u hu=>hc.trans_le (hkc u hu)) hMp hder

end
end OAI.SKFluctuations.LaplaceWindowFormalization
