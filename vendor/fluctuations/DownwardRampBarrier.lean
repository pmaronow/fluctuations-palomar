module

public import UpwardRampBarrier
public import ReciprocalFloorCoordinate

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def downwardBarrierBase (M : ℝ→ℝ) (H u : ℝ) : ℝ := H+inverseCapPrimitive M u
def downwardBarrierEnvelope (M : ℝ→ℝ) (u : ℝ) : ℝ :=
  1-inverseCapPrimitive M 1+inverseCapPrimitive M u
def downwardBarrierClock (A B : ℝ) (M : ℝ→ℝ) (H b u : ℝ) : ℝ :=
  min (reciprocalFloorTime A B (downwardBarrierEnvelope M u))
    (max (reciprocalFloorTime A B (downwardBarrierBase M H u))
      (reciprocalFloorTime A B (downwardBarrierBase M H b)+(u-b)))
def downwardRampBarrier (A B : ℝ) (M : ℝ→ℝ) (H b u : ℝ) : ℝ :=
  reciprocalFloorInverse A B (downwardBarrierClock A B M H b u)

theorem reciprocalSquareFloor_inverse_baseline {A B r : ℝ}
    (hA : 0<A) (hB : 0<B) (hr : 0 ≤ r) :
    B^2/A ≤ (reciprocalSquareFloor A B r)⁻¹ := by
  have hR : 0<r+B := by linarith
  have he : (reciprocalSquareFloor A B r)⁻¹=(r+B)^2/A := by
    unfold reciprocalSquareFloor
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right (by nlinarith) hA.le

section
variable {A B H b : ℝ} {M : ℝ→ℝ}
variable (hA : 0<A) (hB : 0<B) (hMc : Continuous M)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
variable (hH : 0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1)
include hA hB hMc hm hMp hH hHroom

theorem downwardBarrierBase_mem {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    downwardBarrierBase M H u∈Icc (0:ℝ) 1 := by
  have h0 := inverseCapPrimitive_nonneg hMc hm hMp hu
  have h1 := inverseCapPrimitive_le_total hMc hm hMp hu
  unfold downwardBarrierBase
  constructor <;> linarith

theorem downwardBarrierEnvelope_mem {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    downwardBarrierEnvelope M u∈Icc (0:ℝ) 1 := by
  have h0 := inverseCapPrimitive_nonneg hMc hm hMp hu
  have h1 := inverseCapPrimitive_le_total hMc hm hMp hu
  unfold downwardBarrierEnvelope
  constructor <;> linarith

theorem downwardBarrierClock_mem (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    downwardBarrierClock A B M H b u∈Icc 0 (reciprocalFloorTime A B 1) := by
  have hp := reciprocalFloorTime_mem hA.le hB (downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu)
  have hU := reciprocalFloorTime_mem hA.le hB (downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu)
  exact ⟨le_min hU.1 (hp.1.trans (le_max_left _ _)),(min_le_left _ _).trans hU.2⟩

theorem downwardRampBarrier_mem {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    downwardRampBarrier A B M H b u∈Icc (0:ℝ) 1 :=
  reciprocalFloorInverse_mem hA hB (downwardBarrierClock_mem hA hB hMc hm hMp hH hHroom u hu)

theorem downwardRampBarrier_lipschitz :
    ∃C : ℝ≥0,LipschitzOnWith C (downwardRampBarrier A B M H b) (Icc (0:ℝ) 1) := by
  have hP := inverseCapPrimitive_lipschitz hMc hm hMp
  have hlbase : LipschitzOnWith _ (downwardBarrierBase M H) (Icc (0:ℝ) 1) :=
    (LipschitzWith.const H).lipschitzOnWith.add hP
  have hlU : LipschitzOnWith _ (downwardBarrierEnvelope M) (Icc (0:ℝ) 1) :=
    (LipschitzWith.const (1-inverseCapPrimitive M 1)).lipschitzOnWith.add hP
  obtain ⟨Ct,hlt⟩ := reciprocalFloorTime_lipschitz hA.le hB
  have hbtime := hlt.comp hlbase (fun u hu=>downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu)
  have hUtime := hlt.comp hlU (fun u hu=>downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu)
  have hramp : LipschitzOnWith 1
      (fun u=>reciprocalFloorTime A B (downwardBarrierBase M H b)+(u-b)) (Icc (0:ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    simp only [Real.dist_eq,NNReal.coe_one,one_mul]
    have he : reciprocalFloorTime A B (downwardBarrierBase M H b)+(u-b)-
        (reciprocalFloorTime A B (downwardBarrierBase M H b)+(v-b))=u-v := by ring
    rw [he]
  have hmax := real_max_lipschitzOn hbtime hramp
  have hclock := real_min_lipschitzOn hUtime hmax
  obtain ⟨Ci,hli⟩ := reciprocalFloorInverse_lipschitz hA hB
  have hw := hli.comp hclock (fun u hu=>downwardBarrierClock_mem hA hB hMc hm hMp hH hHroom u hu)
  exact ⟨_,hw⟩

theorem downwardRampBarrier_one (hb : b∈Icc (0:ℝ) 1)
    (htail : b+reciprocalFloorTime A B 1 ≤ 1) :
    downwardRampBarrier A B M H b 1=1 := by
  have hbpos := (reciprocalFloorTime_mem hA.le hB
    (downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hb)).1
  have hU : downwardBarrierEnvelope M 1=1 := by unfold downwardBarrierEnvelope;ring
  have hclock : downwardBarrierClock A B M H b 1=reciprocalFloorTime A B 1 := by
    unfold downwardBarrierClock
    rw [hU]
    apply min_eq_left
    exact (by linarith : reciprocalFloorTime A B 1 ≤
      reciprocalFloorTime A B (downwardBarrierBase M H b)+(1-b)).trans (le_max_right _ _)
  unfold downwardRampBarrier
  rw [hclock]
  exact reciprocalFloorInverse_left hA hB zero_le_one

theorem downwardRampBarrier_ae_slope
    (hspeedroom : (M 0)⁻¹ ≤ B^2/A) :
    ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M u)⁻¹ ≤ deriv (downwardRampBarrier A B M H b) u ∧
      deriv (downwardRampBarrier A B M H b) u ≤
        (reciprocalSquareFloor A B (downwardRampBarrier A B M H b u))⁻¹ := by
  let base := downwardBarrierBase M H
  let U := downwardBarrierEnvelope M
  let pt := fun u=>reciprocalFloorTime A B (base u)
  let Ut := fun u=>reciprocalFloorTime A B (U u)
  let ramp := fun u=>reciprocalFloorTime A B (base b)+(u-b)
  let z := fun u=>max (pt u) (ramp u)
  let y := downwardBarrierClock A B M H b
  let w := downwardRampBarrier A B M H b
  have hP := inverseCapPrimitive_lipschitz hMc hm hMp
  have hlbase : LipschitzOnWith _ base (Icc (0:ℝ) 1) :=
    (LipschitzWith.const H).lipschitzOnWith.add hP
  have hlU : LipschitzOnWith _ U (Icc (0:ℝ) 1) :=
    (LipschitzWith.const (1-inverseCapPrimitive M 1)).lipschitzOnWith.add hP
  obtain ⟨Ct,hlt⟩ := reciprocalFloorTime_lipschitz hA.le hB
  have hpt := hlt.comp hlbase (fun u hu=>downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu)
  have hUt := hlt.comp hlU (fun u hu=>downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu)
  have hramp : LipschitzOnWith 1 ramp (Icc (0:ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,ramp]
    have he : reciprocalFloorTime A B (base b)+(u-b)-
        (reciprocalFloorTime A B (base b)+(v-b))=u-v := by ring
    rw [he]
  have hz : LipschitzOnWith _ z (Icc (0:ℝ) 1) := real_max_lipschitzOn hpt hramp
  have hy : LipschitzOnWith _ y (Icc (0:ℝ) 1) := real_min_lipschitzOn hUt hz
  have hacz : AbsolutelyContinuousOnInterval z 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using hz
  have hacy : AbsolutelyContinuousOnInterval y 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using hy
  filter_upwards [hacz.ae_differentiableAt,hacy.ae_differentiableAt,
      volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with u hdz hdy hu0 hu1 hu
  have hui : u∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩
  have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
  have hbmem := downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu
  have hUmem := downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu
  have hwb := downwardRampBarrier_mem (b := b) hA hB hMc hm hMp hH hHroom hu
  have hdbase : HasDerivAt base ((M u)⁻¹) u :=
    (inverseCapPrimitive_hasDerivAt hMc hm hMp hui).const_add H
  have hdU : HasDerivAt U ((M u)⁻¹) u :=
    (inverseCapPrimitive_hasDerivAt hMc hm hMp hui).const_add (1-inverseCapPrimitive M 1)
  have hdpt : HasDerivAt pt (reciprocalSquareFloor A B (base u)*(M u)⁻¹) u :=
    (reciprocalFloorTime_hasDerivAt (by linarith [hbmem.1] : base u+B≠0)).comp u hdbase
  have hdUt : HasDerivAt Ut (reciprocalSquareFloor A B (U u)*(M u)⁻¹) u :=
    (reciprocalFloorTime_hasDerivAt (by linarith [hUmem.1] : U u+B≠0)).comp u hdU
  have hdramp : HasDerivAt ramp 1 u := by
    simpa only [ramp,id_eq] using
      ((hasDerivAt_id u).sub_const b).const_add (reciprocalFloorTime A B (base b))
  have hdw := ((reciprocalFloorInverse_hasDerivAt hA hB
    (downwardBarrierClock_mem (b := b) hA hB hMc hm hMp hH hHroom u hu)).comp u (hdy hu').hasDerivAt).deriv
  change deriv w u=(reciprocalSquareFloor A B (w u))⁻¹*deriv y u at hdw
  have hell : (M u)⁻¹ ≤ (reciprocalSquareFloor A B (w u))⁻¹ :=
    ((inv_le_inv₀ (hMp u hu) (hMp 0 (by norm_num))).mpr (hm (by norm_num) hu hu.1)).trans
      (hspeedroom.trans (reciprocalSquareFloor_inverse_baseline hA hB hwb.1))
  have hkpos : 0<reciprocalSquareFloor A B (w u) := by
    unfold reciprocalSquareFloor
    have hR : 0<w u+B := by linarith [hwb.1]
    positivity
  change (M u)⁻¹ ≤ deriv w u ∧ deriv w u ≤ (reciprocalSquareFloor A B (w u))⁻¹
  rcases differentiable_min_selection hdUt.differentiableAt (hdz hu') (hdy hu') with h | h
  · change y u=Ut u ∧ deriv y u=deriv Ut u at h
    have hwU : w u=U u := by
      change reciprocalFloorInverse A B (y u)=U u
      rw [h.1]
      exact reciprocalFloorInverse_left hA hB hUmem.1
    rw [hdw,h.2,hdUt.deriv,hwU]
    rw [←mul_assoc,inv_mul_cancel₀ (by simpa only [hwU] using hkpos.ne'),one_mul]
    exact ⟨le_rfl,by simpa only [hwU] using hell⟩
  · change y u=z u ∧ deriv y u=deriv z u at h
    rcases differentiable_max_selection hdpt.differentiableAt hdramp.differentiableAt (hdz hu') with hz | hz
    · change z u=pt u ∧ deriv z u=deriv pt u at hz
      have hwp : w u=base u := by
        change reciprocalFloorInverse A B (y u)=base u
        rw [h.1,hz.1]
        exact reciprocalFloorInverse_left hA hB hbmem.1
      rw [hdw,h.2,hz.2,hdpt.deriv,hwp]
      rw [←mul_assoc,inv_mul_cancel₀ (by simpa only [hwp] using hkpos.ne'),one_mul]
      exact ⟨le_rfl,by simpa only [hwp] using hell⟩
    · change z u=ramp u ∧ deriv z u=deriv ramp u at hz
      rw [hdw,h.2,hz.2,hdramp.deriv,mul_one]
      exact ⟨hell,le_rfl⟩

end

theorem explicit_downward_ramp_trial {A B c t H b : ℝ} {M : ℝ→ℝ}
    (hA : 0<A) (hB : 0<B) (hc : 0<c) (ht : t∈Icc (0:ℝ) 1)
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (hH : 0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1)
    (hb : b∈Icc (0:ℝ) 1) (htail : b+reciprocalFloorTime A B 1 ≤ 1)
    (hspeedroom : (M 0)⁻¹ ≤ B^2/A)
    (α : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M) :
    ∃γ : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      ∀u∈Icc (0:ℝ) 1,γ.val.val (harmonicBarrierRadius B t
        (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u)
        (min (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
          (hMp 1 (by norm_num)).le α u) (downwardRampBarrier A B M H b u)))=u := by
  obtain ⟨D,hw⟩ := downwardRampBarrier_lipschitz (b := b) hA hB hMc hm hMp hH hHroom
  apply downward_clipped_comparison_trial hA hB hc ht hkc hMc hm hMp α
    (downwardRampBarrier A B M H b) hw
  · intro u hu
    exact (downwardRampBarrier_mem (b := b) hA hB hMc hm hMp hH hHroom hu).1
  · rw [downwardRampBarrier_one hA hB hMc hm hMp hH hHroom hb htail]
  · filter_upwards [downwardRampBarrier_ae_slope (b := b) hA hB hMc hm hMp hH hHroom hspeedroom]
      with u hd hu _
    exact hd hu

end OAI.SKFluctuations.LaplaceWindowFormalization
