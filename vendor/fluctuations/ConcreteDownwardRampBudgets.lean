module

public import ConcreteRampBudgets
public import DownwardRampBarrier

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem comparisonFloor_total_time_le {N δ U : ℝ} (hN : 0<N) (hU : 0<U) :
    reciprocalFloorTime (N^δ*U^2) (N^(2*δ)*U) 1 ≤ U/N^δ := by
  have hq : N^δ≠0 := (Real.rpow_pos_of_pos hN _).ne'
  have he : N^(2*δ)=(N^δ)^2 := by
    rw [mul_comm (2:ℝ) δ,Real.rpow_mul hN.le,Real.rpow_two]
  have hratio : (N^δ*U^2)/(N^(2*δ)*U)=U/N^δ := by
    rw [he]
    field_simp
  unfold reciprocalFloorTime
  rw [hratio]
  have hmore : 0 ≤ (N^δ*U^2)/(1+N^(2*δ)*U) := by positivity
  linarith

theorem concrete_downward_ramp_trial {N δ U L E d t H b : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L ≤ U) (hE : 0<E) (hd : 0 ≤ d)
    (hpower : 1 ≤ N^δ) (ht : t∈Icc (0:ℝ) 1) (hH : 0 ≤ H)
    (hHroom : H+(L/N^δ)*Real.log ((1+U)/U) ≤ 1)
    (hb : b∈Icc (0:ℝ) 1) (htail : b+U/N^δ ≤ 1) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ := δ) hN hU (r₀ := 0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1)=>comparisonFloor_lower_on (δ := δ) hN hU le_rfl hr
    let hm := comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ := δ) hN hU.le hL hE hd zero_le_one
    ∀α : inverseIntegralConstraints 0 0 k M,
      ∃γ : inverseIntegralConstraints 0 0 k M,∀u∈Icc (0:ℝ) 1,
        γ.val.val (harmonicBarrierRadius (N^(2*δ)*U) t
          (comparisonSweepQuantile hc hk hkc hm hM α u)
          (min (comparisonSweepQuantile hc hk hkc hm hM α u)
            (downwardRampBarrier (N^δ*U^2) (N^(2*δ)*U) M H b u)))=u := by
  dsimp only
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hA : 0<N^δ*U^2 := by positivity
  have hB : 0<N^(2*δ)*U := by positivity
  have hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hkc : ∀r∈Icc (0:ℝ) 1,k 1 ≤ reciprocalSquareFloor (N^δ*U^2) (N^(2*δ)*U) r :=
    fun r hr=>comparisonFloor_lower_on (δ := δ) hN hU le_rfl hr
  have hMc : Continuous M := comparisonCap_continuous N δ U L E d
  have hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd
  have hMp : ∀u∈Icc (0:ℝ) 1,0<M u := fun u hu=>
    (comparisonCap_first_term (δ := δ) hN hU hL hE hd hu.1).1
  have hHroom' : H+inverseCapPrimitive M 1 ≤ 1 :=
    (add_le_add le_rfl (comparisonCapPrimitive_le_log (δ := δ) hN hU hL hE hd)).trans hHroom
  have htail' : b+reciprocalFloorTime (N^δ*U^2) (N^(2*δ)*U) 1 ≤ 1 :=
    (add_le_add le_rfl (comparisonFloor_total_time_le (δ := δ) hN hU)).trans htail
  have hq : 0<N^δ := Real.rpow_pos_of_pos hN _
  have hinv : (N^δ)⁻¹ ≤ 1 := (inv_le_one₀ hq).mpr hpower
  have hcube : 1 ≤ (N^δ)^3 := one_le_pow₀ hpower
  have hspeed' : (M 0)⁻¹ ≤ (N^(2*δ)*U)^2/(N^δ*U^2) := by
    rw [comparisonFloor_reciprocal_square_room hN hU]
    exact (comparisonCap_zero_inverse_le (δ := δ) hN hU hL hLU hE hd).trans (hinv.trans hcube)
  intro α
  exact explicit_downward_ramp_trial hA hB hc ht hkc hMc hm hMp hH hHroom' hb htail' hspeed' α

end OAI.SKFluctuations.LaplaceWindowFormalization
