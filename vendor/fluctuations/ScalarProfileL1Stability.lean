module

public import QuantileLawContinuity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem scalarPenalty_L1_comparison (α β : boundedMassProfiles) :
    |scalarPenalty α-scalarPenalty β| ≤ ∫ u in (0:ℝ)..1, |α.val u-β.val u| := by
  have hα : IntervalIntegrable α.val volume 0 1 := α.property.2.intervalIntegrable
  have hβ : IntervalIntegrable β.val volume 0 1 := β.property.2.intervalIntegrable
  have hαw : IntervalIntegrable (fun u => u*α.val u) volume 0 1 :=
    by simpa only [id_eq,mul_comm] using hα.mul_continuousOn continuous_id.continuousOn
  have hβw : IntervalIntegrable (fun u => u*β.val u) volume 0 1 :=
    by simpa only [id_eq,mul_comm] using hβ.mul_continuousOn continuous_id.continuousOn
  rw [scalarPenalty_eq,scalarPenalty_eq,← intervalIntegral.integral_sub hαw hβw]
  apply (show |∫ u in (0:ℝ)..1, u*α.val u-u*β.val u| ≤
      ∫ u in (0:ℝ)..1, |u*α.val u-u*β.val u| from by
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
      (f := fun u => u*α.val u-u*β.val u) zero_le_one).trans
  apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (hαw.sub hβw).abs (hα.sub hβ).abs
  intro u hu
  rw [← mul_sub,abs_mul,abs_of_nonneg hu.1.le]
  exact mul_le_of_le_one_left (abs_nonneg _) hu.2.le

theorem scalarParisiValue_L1_comparison {T : ℝ} (hT : 0 < T)
    (α β : boundedMassProfiles) :
    |scalarParisiValue hT α-scalarParisiValue hT β| ≤
      T*(∫ u in (0:ℝ)..1, |α.val u-β.val u|) := by
  have hroot := scalarTerminal.nonnegativeProfileValue_L1_comparison
    (fun _ => 1) scalarTerminal_G_bound (rescaledMassProfile α hT)
    (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0
  have hcdf : (∫ s in (0:ℝ)..T, |α.val (s/T)-β.val (s/T)|) =
      T*(∫ u in (0:ℝ)..1, |α.val u-β.val u|) := by
    rw [intervalIntegral.integral_comp_div (fun z => |α.val z-β.val z|) hT.ne']
    simp only [zero_div,div_self hT.ne',smul_eq_mul]
  norm_num only [one_pow,Fin.sum_univ_one,NNReal.coe_mk,zero_add] at hroot
  change |_ - _| ≤ (1:ℝ)/2*(∫ s in (0:ℝ)..T, |α.val (s/T)-β.val (s/T)|) at hroot
  rw [hcdf] at hroot
  have hpenalty := scalarPenalty_L1_comparison α β
  have hscaled := mul_le_mul_of_nonneg_left hpenalty (show 0 ≤ T/2 by positivity)
  have htri := abs_add_le
    (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (NNReal.mk T hT.le) 0-
      scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0)
    (-(T/2*(scalarPenalty α-scalarPenalty β)))
  rw [abs_neg,abs_mul,abs_of_nonneg (show 0 ≤ T/2 by positivity)] at htri
  simp only [← sub_eq_add_neg] at htri
  unfold scalarParisiValue
  change |(scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT)
    0 (NNReal.mk T hT.le) 0-T/2*scalarPenalty α-T/4)-
    (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT)
    0 (NNReal.mk T hT.le) 0-T/2*scalarPenalty β-T/4)| ≤ _
  have he :
      scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (NNReal.mk T hT.le) 0-
        T/2*scalarPenalty α-T/4-
      (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0-
        T/2*scalarPenalty β-T/4) =
      (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (NNReal.mk T hT.le) 0-
        scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0)-
        T/2*(scalarPenalty α-scalarPenalty β) := by ring
  rw [he]
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
