module

public import DownwardRampBarrier

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem reciprocalFloorTime_explicit_lipschitz {A B : ℝ} (hA : 0 ≤ A) (hB : 0<B) :
    LipschitzOnWith ⟨A*(B^2)⁻¹,mul_nonneg hA (inv_nonneg.mpr (sq_nonneg B))⟩
      (reciprocalFloorTime A B) (Icc (0:ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hi := (positiveReciprocal_lipschitzOn hB).dist_le_mul (x+B)
    (by change B ≤ x+B;linarith [hx.1]) (y+B) (by change B ≤ y+B;linarith [hy.1])
  have he : reciprocalFloorTime A B x-reciprocalFloorTime A B y=
      -A*((x+B)⁻¹-(y+B)⁻¹) := by unfold reciprocalFloorTime;rw [div_eq_mul_inv,div_eq_mul_inv];ring
  simp only [Real.dist_eq,NNReal.coe_mk] at hi ⊢
  change |(x+B)⁻¹-(y+B)⁻¹| ≤ (B^2)⁻¹*|x+B-(y+B)| at hi
  change |reciprocalFloorTime A B x-reciprocalFloorTime A B y| ≤ (A*(B^2)⁻¹)*|x-y|
  rw [he,abs_mul,abs_neg,abs_of_nonneg hA]
  have hxy : x+B-(y+B)=x-y := by ring
  rw [hxy] at hi
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hA

section
variable {A B H b : ℝ} {M : ℝ→ℝ}
variable (hA : 0<A) (hB : 0<B) (hMc : Continuous M)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
variable (hH : 0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1)
include hA hB hMc hm hMp hH hHroom

theorem downwardBarrierBase_le_envelope (u : ℝ) :
    downwardBarrierBase M H u ≤ downwardBarrierEnvelope M u := by
  unfold downwardBarrierBase downwardBarrierEnvelope
  linarith

theorem downwardBarrierBaseClock_unit_lipschitz
    (hspeedroom : (M 0)⁻¹ ≤ B^2/A) :
    LipschitzOnWith 1 (fun u=>reciprocalFloorTime A B (downwardBarrierBase M H u))
      (Icc (0:ℝ) 1) := by
  have hp := inverseCapPrimitive_lipschitz hMc hm hMp
  have hb : LipschitzOnWith _ (downwardBarrierBase M H) (Icc (0:ℝ) 1) :=
    (LipschitzWith.const H).lipschitzOnWith.add hp
  have ht := (reciprocalFloorTime_explicit_lipschitz hA.le hB).comp hb
    (fun u hu=>downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu)
  have hcoef : A*(B^2)⁻¹*(M 0)⁻¹ ≤ 1 := by
    have hh := (le_div_iff₀ hA).mp hspeedroom
    have hsq : 0<B^2 := sq_pos_of_pos hB
    have hd : A*(M 0)⁻¹/B^2 ≤ 1 := (div_le_one hsq).mpr (by simpa only [mul_comm] using hh)
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hd
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hh := ht.dist_le_mul u hu v hv
  simp only [NNReal.coe_one,one_mul] at ⊢
  apply hh.trans
  change (A*(B^2)⁻¹*(0+(M 0)⁻¹))*dist u v ≤ dist u v
  simpa only [zero_add,one_mul] using mul_le_mul_of_nonneg_right hcoef (dist_nonneg)

theorem downwardRampBarrier_before (hspeedroom : (M 0)⁻¹ ≤ B^2/A)
    (hb : b∈Icc (0:ℝ) 1) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (hub : u ≤ b) :
    downwardRampBarrier A B M H b u=downwardBarrierBase M H u := by
  have hh := (downwardBarrierBaseClock_unit_lipschitz hA hB hMc hm hMp hH hHroom hspeedroom).dist_le_mul b hb u hu
  simp only [Real.dist_eq,NNReal.coe_one,one_mul,abs_of_nonneg (sub_nonneg.mpr hub)] at hh
  have hramp : reciprocalFloorTime A B (downwardBarrierBase M H b)+(u-b) ≤
      reciprocalFloorTime A B (downwardBarrierBase M H u) := by
    have hs := (le_abs_self (reciprocalFloorTime A B (downwardBarrierBase M H b)-
      reciprocalFloorTime A B (downwardBarrierBase M H u))).trans hh
    linarith
  have hbase := downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hu
  have hU := downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu
  have hpu := (reciprocalFloorTime_monotoneOn hA.le hB) hbase hU
    (downwardBarrierBase_le_envelope hA hB hMc hm hMp hH hHroom u)
  unfold downwardRampBarrier downwardBarrierClock
  rw [max_eq_left hramp,min_eq_right hpu]
  exact reciprocalFloorInverse_left hA hB hbase.1

theorem downwardRampBarrier_after (hb : b∈Icc (0:ℝ) 1)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (huafter : b+reciprocalFloorTime A B 1 ≤ u) :
    downwardRampBarrier A B M H b u=downwardBarrierEnvelope M u := by
  have hbpos := (reciprocalFloorTime_mem hA.le hB
    (downwardBarrierBase_mem hA hB hMc hm hMp hH hHroom hb)).1
  have hU := downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hHroom hu
  have hup := (reciprocalFloorTime_mem hA.le hB hU).2
  have hramp : reciprocalFloorTime A B (downwardBarrierEnvelope M u) ≤
      reciprocalFloorTime A B (downwardBarrierBase M H b)+(u-b) := by linarith
  unfold downwardRampBarrier downwardBarrierClock
  rw [min_eq_left (hramp.trans (le_max_right _ _))]
  exact reciprocalFloorInverse_left hA hB hU.1

end

theorem comparisonSweepQuantile_cap_envelopes {c : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (α : inverseIntegralConstraints 0 0 k M) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    inverseCapPrimitive M u ≤ comparisonSweepQuantile hc hk hkc hm (hMp 1 (by norm_num)).le α u ∧
      comparisonSweepQuantile hc hk hkc hm (hMp 1 (by norm_num)).le α u ≤ downwardBarrierEnvelope M u := by
  let q := comparisonSweepQuantile hc hk hkc hm (hMp 1 (by norm_num)).le α
  have hqLip := comparisonSweepQuantile_lipschitzOn hc hk hkc hm (hMp 1 (by norm_num)).le α
  have hac : AbsolutelyContinuousOnInterval q 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using hqLip
  have hpi := inverseCapPrimitive_integrable hMc hm hMp
  have hder := comparisonSweepQuantile_ae_slope hc hk hkc hm (hMp 1 (by norm_num)).le α hMc hMp
  have hgap {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab : a ≤ b) :
      inverseCapPrimitive M b-inverseCapPrimitive M a ≤ q b-q a := by
    have hsub : uIcc a b ⊆ uIcc (0:ℝ) 1 := by
      simp only [uIcc_of_le hab,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ha.1 hb.2
    have hac' := hac.mono hsub
    have hpiab := hpi.mono_set hsub
    have hmono : (fun v=>(M v)⁻¹) ≤ᵐ[volume.restrict (Icc a b)] deriv q := by
      change ∀ᵐ v∂volume.restrict (Icc a b),(M v)⁻¹ ≤ deriv q v
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hder] with v hv hvab
      exact (hv ⟨ha.1.trans hvab.1,hvab.2.trans hb.2⟩).1
    have hint := intervalIntegral.integral_mono_ae_restrict hab hpiab hac'.intervalIntegrable_deriv hmono
    rw [hac'.integral_deriv_eq_sub] at hint
    have hpi0a : IntervalIntegrable (fun v=>(M v)⁻¹) volume 0 a := hpi.mono_set (by
      simp only [uIcc_of_le ha.1,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl ha.2)
    have he := intervalIntegral.integral_add_adjacent_intervals hpi0a hpiab
    dsimp only [inverseCapPrimitive]
    linarith
  have hlo := hgap (a := 0) (b := u) (by norm_num) hu hu.1
  have hhi := hgap (a := u) (b := 1) hu (by norm_num) hu.2
  have hq0 : q 0=0 := comparisonSweepQuantile_zero hc hk hkc hm (hMp 1 (by norm_num)).le α
  have hq1 : q 1=1 := comparisonSweepQuantile_one hc hk hkc hm (hMp 1 (by norm_num)).le α
  have hP0 : inverseCapPrimitive M 0=0 := by simp [inverseCapPrimitive]
  change inverseCapPrimitive M u ≤ q u ∧ q u ≤ downwardBarrierEnvelope M u
  unfold downwardBarrierEnvelope
  constructor <;> linarith

theorem downward_clipped_radius_after {A B c H b : ℝ} {M : ℝ→ℝ}
    (hA : 0<A) (hB : 0<B) (hc : 0<c)
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (hH : 0 ≤ H) (hHroom : H+inverseCapPrimitive M 1 ≤ 1)
    (hb : b∈Icc (0:ℝ) 1)
    (α : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (huafter : b+reciprocalFloorTime A B 1 ≤ u) :
    min (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
      (hMp 1 (by norm_num)).le α u) (downwardRampBarrier A B M H b u)=
      comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB) hkc hm
        (hMp 1 (by norm_num)).le α u := by
  rw [downwardRampBarrier_after hA hB hMc hm hMp hH hHroom hb hu huafter]
  exact min_eq_left (comparisonSweepQuantile_cap_envelopes hc
    (reciprocalSquareFloor_continuousOn hB) hkc hMc hm hMp α hu).2

end OAI.SKFluctuations.LaplaceWindowFormalization
