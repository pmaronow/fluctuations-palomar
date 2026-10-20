module

public import ClippedComparisonTrials

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def truncatedBarrierRamp (a b u : ℝ) : ℝ := max 0 (min (u-a) (b-a))
def inverseCapPrimitive (M : ℝ→ℝ) (u : ℝ) : ℝ := ∫v in 0..u,(M v)⁻¹
def upwardRampBarrier (M : ℝ→ℝ) (a b speed u : ℝ) : ℝ :=
  inverseCapPrimitive M u+speed*truncatedBarrierRamp a b u

theorem truncatedBarrierRamp_lipschitz (a b : ℝ) :
    LipschitzWith 1 (truncatedBarrierRamp a b) := by
  have hl : LipschitzWith 1 (fun u : ℝ=>u-a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,NNReal.coe_one,one_mul]
    have he : x-a-(y-a)=x-y := by ring
    rw [he]
  change LipschitzWith 1 (fun u=>max 0 (min (u-a) (b-a)))
  exact (hl.min_const (b-a)).const_max 0

theorem truncatedBarrierRamp_monotone (a b : ℝ) : Monotone (truncatedBarrierRamp a b) := by
  intro u v huv
  unfold truncatedBarrierRamp
  exact max_le_max_left _ (min_le_min_right _ (sub_le_sub_right huv a))

theorem truncatedBarrierRamp_bounds {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    truncatedBarrierRamp a b u∈Icc (0:ℝ) (b-a) := by
  exact ⟨le_max_left _ _,max_le (sub_nonneg.mpr hab) (min_le_right _ _)⟩

theorem truncatedBarrierRamp_before {a b u : ℝ} (hua : u ≤ a) :
    truncatedBarrierRamp a b u=0 := by
  exact max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr hua))

theorem truncatedBarrierRamp_after {a b u : ℝ} (hab : a ≤ b) (hbu : b ≤ u) :
    truncatedBarrierRamp a b u=b-a := by
  unfold truncatedBarrierRamp
  rw [min_eq_right (sub_le_sub_right hbu a),max_eq_right (sub_nonneg.mpr hab)]

theorem truncatedBarrierRamp_deriv_bounds (a b u : ℝ) :
    deriv (truncatedBarrierRamp a b) u∈Icc (0:ℝ) 1 := by
  have hh := norm_deriv_le_of_lipschitz (x₀ := u) (truncatedBarrierRamp_lipschitz a b)
  simp only [Real.norm_eq_abs,NNReal.coe_one] at hh
  exact ⟨(truncatedBarrierRamp_monotone a b).deriv_nonneg,(le_abs_self _).trans hh⟩

section
variable {M : ℝ→ℝ} (hMc : Continuous M)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
include hMc hm hMp

theorem inverseCapPrimitive_integrable : IntervalIntegrable (fun u=>(M u)⁻¹) volume 0 1 :=
  (hMc.continuousOn.inv₀ (fun u hu=>(hMp u hu).ne')).intervalIntegrable_of_Icc zero_le_one

theorem inverseCapPrimitive_nonneg {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    0 ≤ inverseCapPrimitive M u := by
  apply intervalIntegral.integral_nonneg hu.1
  intro v hv
  exact inv_nonneg.mpr (hMp v ⟨hv.1,hv.2.trans hu.2⟩).le

theorem inverseCapPrimitive_le_total {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    inverseCapPrimitive M u ≤ inverseCapPrimitive M 1 := by
  have hi := inverseCapPrimitive_integrable hMc hm hMp
  have hi0 : IntervalIntegrable (fun v=>(M v)⁻¹) volume 0 u := hi.mono_set (by
    simp only [uIcc_of_le zero_le_one,uIcc_of_le hu.1]
    exact Icc_subset_Icc le_rfl hu.2)
  have hi1 : IntervalIntegrable (fun v=>(M v)⁻¹) volume u 1 := hi.mono_set (by
    simp only [uIcc_of_le zero_le_one,uIcc_of_le hu.2]
    exact Icc_subset_Icc hu.1 le_rfl)
  have he := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have hp : 0 ≤ ∫v in u..1,(M v)⁻¹ := intervalIntegral.integral_nonneg hu.2
    (fun v hv=>inv_nonneg.mpr (hMp v ⟨hu.1.trans hv.1,hv.2⟩).le)
  dsimp [inverseCapPrimitive]
  linarith

theorem inverseCapPrimitive_lipschitz :
    LipschitzOnWith ⟨(M 0)⁻¹,inv_nonneg.mpr (hMp 0 (by norm_num)).le⟩
      (inverseCapPrimitive M) (Icc (0:ℝ) 1) := by
  apply integral_primitive_lipschitz zero_le_one (inverseCapPrimitive_integrable hMc hm hMp)
  apply Eventually.of_forall
  intro u hu
  rw [abs_of_pos (inv_pos.mpr (hMp u hu))]
  exact (inv_le_inv₀ (hMp u hu) (hMp 0 (by norm_num))).mpr (hm (by norm_num) hu hu.1)

theorem inverseCapPrimitive_hasDerivAt {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) :
    HasDerivAt (inverseCapPrimitive M) ((M u)⁻¹) u := by
  have hg : ContinuousOn (fun v=>(M v)⁻¹) (Icc (0:ℝ) 1) :=
    hMc.continuousOn.inv₀ (fun v hv=>(hMp v hv).ne')
  have hi : IntervalIntegrable (fun v=>(M v)⁻¹) volume 0 u :=
    (inverseCapPrimitive_integrable hMc hm hMp).mono_set (by
    simp only [uIcc_of_le zero_le_one,uIcc_of_le hu.1.le]
    exact Icc_subset_Icc le_rfl hu.2.le)
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono Ioo_subset_Icc_self) u hu)
    ((hg u ⟨hu.1.le,hu.2.le⟩).continuousAt (Icc_mem_nhds hu.1 hu.2))

theorem upwardRampBarrier_lipschitz (a b speed : ℝ) :
    ∃C : ℝ≥0,LipschitzOnWith C (upwardRampBarrier M a b speed) (Icc (0:ℝ) 1) := by
  have hp := inverseCapPrimitive_lipschitz hMc hm hMp
  have hr : LipschitzOnWith ‖speed‖₊ (fun u=>speed*truncatedBarrierRamp a b u) (Icc (0:ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hh := mul_le_mul_of_nonneg_left ((truncatedBarrierRamp_lipschitz a b).dist_le_mul x y) (norm_nonneg speed)
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,←mul_sub,abs_mul,Real.norm_eq_abs,coe_nnnorm] using hh
  exact ⟨_,hp.add hr⟩

theorem upwardRampBarrier_bounds {a b speed : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    upwardRampBarrier M a b speed u∈Icc (0:ℝ)
      (inverseCapPrimitive M 1+speed*(b-a)) := by
  have hp0 := inverseCapPrimitive_nonneg hMc hm hMp hu
  have hp1 := inverseCapPrimitive_le_total hMc hm hMp hu
  have hr := truncatedBarrierRamp_bounds hab u
  exact ⟨add_nonneg hp0 (mul_nonneg hspeed hr.1),
    add_le_add hp1 (mul_le_mul_of_nonneg_left hr.2 hspeed)⟩

theorem upwardRampBarrier_ae_slope {a b speed : ℝ} (hspeed : 0 ≤ speed) :
    ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M u)⁻¹ ≤ deriv (upwardRampBarrier M a b speed) u ∧
      deriv (upwardRampBarrier M a b speed) u ≤ (M 0)⁻¹+speed := by
  have har : AbsolutelyContinuousOnInterval (truncatedBarrierRamp a b) 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 1)
    exact (truncatedBarrierRamp_lipschitz a b).lipschitzOnWith
  filter_upwards [har.ae_differentiableAt,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with u hd hu0 hu1 hu
  have hui : u∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩
  have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
  have he := ((inverseCapPrimitive_hasDerivAt hMc hm hMp hui).add ((hd hu').hasDerivAt.const_mul speed)).deriv
  change deriv (upwardRampBarrier M a b speed) u=(M u)⁻¹+speed*deriv (truncatedBarrierRamp a b) u at he
  rw [he]
  have hr := truncatedBarrierRamp_deriv_bounds a b u
  have hM0 : (M u)⁻¹ ≤ (M 0)⁻¹ :=
    (inv_le_inv₀ (hMp u hu) (hMp 0 (by norm_num))).mpr (hm (by norm_num) hu hu.1)
  exact ⟨by nlinarith [mul_nonneg hspeed hr.1],by nlinarith [mul_le_mul_of_nonneg_left hr.2 hspeed]⟩

end

theorem explicit_upward_ramp_trial {A B c t a b speed : ℝ} {M : ℝ→ℝ}
    (hA : 0<A) (hB : 0<B) (hc : 0<c) (ht : t∈Icc (0:ℝ) 1)
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (ha : 0 ≤ a) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hrise : inverseCapPrimitive M 1+speed*(b-a) ≤ 1)
    (hspeedroom : (M 0)⁻¹+speed ≤ B^2/A)
    (α : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M) :
    ∃γ : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      ∀u∈Icc (0:ℝ) 1,γ.val.val ((1-t)*
        (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u)+t*
        max (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u) (upwardRampBarrier M a b speed u))=u := by
  obtain ⟨D,hw⟩ := upwardRampBarrier_lipschitz hMc hm hMp a b speed
  apply upward_clipped_comparison_trial hA hB hc ht hkc hMc hm hMp α
    (upwardRampBarrier M a b speed) hw
  · intro u hu
    exact (upwardRampBarrier_bounds hMc hm hMp hab hspeed hu).2.trans hrise
  · simp [upwardRampBarrier,inverseCapPrimitive,truncatedBarrierRamp_before ha]
  · filter_upwards [upwardRampBarrier_ae_slope hMc hm hMp hspeed] with u hd hu _
    refine ⟨(hd hu).1,(hd hu).2.trans (hspeedroom.trans ?_)⟩
    let r := comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
      (hMp 1 (by norm_num)).le α u
    have hr := comparisonSweepQuantile_bounds hc (reciprocalSquareFloor_continuousOn hB) hkc hm
      (hMp 1 (by norm_num)).le α u
    have hR : 0<r+B := by linarith [hr.1]
    have he : (reciprocalSquareFloor A B r)⁻¹=(r+B)^2/A := by
      unfold reciprocalSquareFloor
      field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ hA.le
    nlinarith [hr.1]

end OAI.SKFluctuations.LaplaceWindowFormalization
