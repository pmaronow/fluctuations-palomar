module

public import UpwardRampBarrier
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonCapTravel

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem comparisonCap_zero_ge_power {N δ U L E d : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L ≤ U) (hE : 0<E) (hd : 0 ≤ d) :
    N^δ ≤ comparisonCap N δ U L E d 0 := by
  have hq : 0<N^δ := Real.rpow_pos_of_pos hN _
  have hratio : 1 ≤ U/L := (le_div_iff₀ hL).mpr (by simpa using hLU)
  have hmore : 0 ≤ (d^3/E)*U^2 := by positivity
  unfold comparisonCap
  simp only [zero_add]
  nlinarith [mul_le_mul_of_nonneg_left hratio hq.le]

theorem comparisonCap_zero_inverse_le {N δ U L E d : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L ≤ U) (hE : 0<E) (hd : 0 ≤ d) :
    (comparisonCap N δ U L E d 0)⁻¹ ≤ (N^δ)⁻¹ := by
  have hq := Real.rpow_pos_of_pos hN δ
  have hg := comparisonCap_zero_ge_power (δ := δ) hN hU hL hLU hE hd
  exact (inv_le_inv₀ (hq.trans_le hg) hq).mpr hg

theorem comparisonFloor_reciprocal_square_room {N δ U : ℝ} (hN : 0<N) (hU : 0<U) :
    (N^(2*δ)*U)^2/(N^δ*U^2)=(N^δ)^3 := by
  have hq : N^δ≠0 := (Real.rpow_pos_of_pos hN _).ne'
  have he : N^(2*δ)=(N^δ)^2 := by
    rw [mul_comm (2:ℝ) δ,Real.rpow_mul hN.le,Real.rpow_two]
  rw [he]
  field_simp

theorem comparisonCapPrimitive_le_log {N δ U L E d : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0 ≤ d) :
    inverseCapPrimitive (comparisonCap N δ U L E d) 1 ≤
      (L/N^δ)*Real.log ((1+U)/U) := by
  simpa only [inverseCapPrimitive,one_div,zero_add] using
    comparisonCap_log_travel (δ := δ) hN hU hL hE hd (a := 0) (b := 1) le_rfl zero_le_one

theorem concrete_upward_ramp_trial {N δ U L E d t a b speed : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L ≤ U) (hE : 0<E) (hd : 0 ≤ d)
    (ht : t∈Icc (0:ℝ) 1) (ha : 0 ≤ a) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hrise : (L/N^δ)*Real.log ((1+U)/U)+speed*(b-a) ≤ 1)
    (hspeedroom : (N^δ)⁻¹+speed ≤ (N^δ)^3) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ := δ) hN hU (r₀ := 0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1)=>comparisonFloor_lower_on (δ := δ) hN hU le_rfl hr
    let hm := comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ := δ) hN hU.le hL hE hd zero_le_one
    ∀α : inverseIntegralConstraints 0 0 k M,
      ∃γ : inverseIntegralConstraints 0 0 k M,∀u∈Icc (0:ℝ) 1,
        γ.val.val ((1-t)*comparisonSweepQuantile hc hk hkc hm hM α u+t*
          max (comparisonSweepQuantile hc hk hkc hm hM α u) (upwardRampBarrier M a b speed u))=u := by
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
  have hrise' : inverseCapPrimitive M 1+speed*(b-a) ≤ 1 :=
    (add_le_add (comparisonCapPrimitive_le_log (δ := δ) hN hU hL hE hd) le_rfl).trans hrise
  have hspeed' : (M 0)⁻¹+speed ≤ (N^(2*δ)*U)^2/(N^δ*U^2) := by
    rw [comparisonFloor_reciprocal_square_room hN hU]
    exact (add_le_add (comparisonCap_zero_inverse_le (δ := δ) hN hU hL hLU hE hd) le_rfl).trans hspeedroom
  intro α
  exact explicit_upward_ramp_trial hA hB hc ht hkc hMc hm hMp ha hab hspeed hrise' hspeed' α

end OAI.SKFluctuations.LaplaceWindowFormalization
