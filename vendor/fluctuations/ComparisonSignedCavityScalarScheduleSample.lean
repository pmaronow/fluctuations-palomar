module

public import ComparisonSignedCavityScalarFixedHorizon
public import QuantileLawMismatchTransfer

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy

theorem scalarBoundaryClocks_quantile_sample_error {a ε : ℝ}
    (as : List PositiveMass) (ho : MassOrdered a as) (q : ℕ → ℝ) (hq : Monotone q)
    (f : ℝ → ℝ)
    (hnode : ∀ j, j ≤ as.length → |q j-partitionValues f a as j| ≤ ε) (u : ℝ) :
    |scheduleRadiusQuantile (q 0) (scalarBoundaryClocks as q) u-
      partitionSample f a as u| ≤ ε := by
  induction as generalizing a q with
  | nil => simpa only [scalarBoundaryClocks, scheduleRadiusQuantile, heatSteps,
      List.map_nil, stepClockFunction, List.sum_nil, add_zero,
      partitionSample_nil, partitionValues] using hnode 0 le_rfl
  | cons b bs ih =>
    rw [partitionSample_cons]
    by_cases hu : u < b.val
    · rw [ite_eq_left hu]
      have hbefore := scheduleRadiusQuantile_before
        (root := q 0) (cs := scalarBoundaryClocks (b::bs) q)
        (scalarBoundaryClocks_ordered (show MassOrdered b.val (b::bs) from
          ⟨b.property.le,le_rfl,ho.2.2⟩) q) hu
      rw [hbefore]
      simpa only [partitionValues] using hnode 0 (by simp)
    · rw [ite_eq_right hu]
      change |scheduleRadiusQuantile (q 0)
        (⟨b.val,b.property,Real.toNNReal (q 1-q 0)⟩::
          scalarBoundaryClocks bs (fun j => q (j+1))) u-
        partitionSample f b.val bs u| ≤ ε
      rw [scheduleRadiusQuantile_cons, ite_eq_left (not_lt.mp hu)]
      have hroot : q 0 + (Real.toNNReal (q 1-q 0):ℝ) = q 1 := by
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hq (by omega : 0 ≤ 1)))]
        ring
      rw [hroot]
      exact ih ho.2.2 (fun j => q (j+1))
        (hq.comp (monotone_id.add_const 1)) (fun j hj => by
          simpa only [partitionValues] using hnode (j+1) (by simpa using Nat.succ_le_succ hj))

theorem scalarBoundaryClocks_quantile_l1_sample_error {ε mesh : ℝ}
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q : ℕ → ℝ) (hq : Monotone q) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (0:ℝ) 1)) (hm : PartitionMesh mesh 0 as)
    (hnode : ∀ j, j ≤ as.length → |q j-partitionValues f 0 as j| ≤ ε) :
    (∫ u in (0:ℝ)..1, |scheduleRadiusQuantile (q 0) (scalarBoundaryClocks as q) u-f u|) ≤
      ε+mesh*(f 1-f 0) := by
  have hs : IntervalIntegrable (scheduleRadiusQuantile (q 0) (scalarBoundaryClocks as q))
      volume 0 1 :=
    stepClockFunction_intervalIntegrable (fun _ : Fin 1 => q 0)
      (scalarBoundaryClocks_ordered ho q) 0 0 1
  have hp := partitionSample_intervalIntegrable f 0 as 0 1
  have hfi : IntervalIntegrable f volume 0 1 :=
    (show MonotoneOn f (uIcc (0:ℝ) 1) by simpa using hf).intervalIntegrable
  have H := intervalIntegral.integral_mono_on zero_le_one (hs.sub hfi).abs
    (intervalIntegrable_const.add (hp.sub hfi).abs)
    (fun u _ => (abs_sub_le _ (partitionSample f 0 as u) _).trans
      (add_le_add (scalarBoundaryClocks_quantile_sample_error as ho q hq f hnode u) le_rfl))
  rw [intervalIntegral.integral_add intervalIntegrable_const (hp.sub hfi).abs,
    intervalIntegral.integral_const] at H
  simp only [sub_zero, one_smul] at H
  have Hsample := partitionSample_l1_error hf as ho hm
  simp_rw [abs_sub_comm (f _) (partitionSample f 0 as _)] at Hsample
  exact H.trans (add_le_add le_rfl Hsample)

theorem partitionValues_const_mul (f : ℝ → ℝ) (c a : ℝ)
    (as : List PositiveMass) (j : ℕ) :
    partitionValues (fun u => c*f u) a as j = c*partitionValues f a as j := by
  induction as generalizing a j with
  | nil => rfl
  | cons b bs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih b.val j

theorem normalizedScalarScheduleQuantile_l1_sample_error {T ε mesh : ℝ} (hT : 0 < T)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0 = 0) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (0:ℝ) 1)) (hm : PartitionMesh mesh 0 as)
    (hnode : ∀ j, j ≤ as.length → |q j-T*partitionValues f 0 as j| ≤ T*ε) :
    (∫ u in (0:ℝ)..1,
      |normalizedScheduleQuantile T 0 (scalarBoundaryClocks as q) u-f u|) ≤
      ε+mesh*(f 1-f 0) := by
  have hfT : MonotoneOn (fun u => T*f u) (Icc (0:ℝ) 1) :=
    fun u hu v hv huv => mul_le_mul_of_nonneg_left (hf hu hv huv) hT.le
  have H := scalarBoundaryClocks_quantile_l1_sample_error as ho q hq
    (fun u => T*f u) hfT hm (fun j hj => by
      simpa only [partitionValues_const_mul] using hnode j hj)
  have he : (∫ u in (0:ℝ)..1,
      |normalizedScheduleQuantile T 0 (scalarBoundaryClocks as q) u-f u|) =
      (∫ u in (0:ℝ)..1,
        |scheduleRadiusQuantile (q 0) (scalarBoundaryClocks as q) u-T*f u|)/T := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    unfold normalizedScheduleQuantile
    rw [hq0]
    have hh : scheduleRadiusQuantile 0 (scalarBoundaryClocks as q) u/T-f u =
        (scheduleRadiusQuantile 0 (scalarBoundaryClocks as q) u-T*f u)/T := by
      field_simp
    rw [hh,abs_div,abs_of_pos hT]
  rw [he]
  apply (div_le_div_of_nonneg_right H hT.le).trans_eq
  field_simp

end OAI.SKFluctuations.LaplaceWindowFormalization
