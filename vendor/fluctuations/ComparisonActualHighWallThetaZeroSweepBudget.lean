module

public import ComparisonActualHighWallThetaZeroDirectSweep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

private theorem theta_zero_profile_nonempty : a.Profile.Nonempty :=
  concreteWallConstraints_nonempty a.hN a.hE a.hd a.hd1
    ⟨a.hs.1.le,a.hs.2.trans (by norm_num)⟩ a.hq a.hsmall

theorem theta_zero_sweep_cost_lipschitz :
    LipschitzOnWith 1 a.thetaZeroSweepCost (Icc (0:ℝ) (a.d^2)) := by
  exact omittedComparisonSweepCost_lipschitz a.hrbounds.1.le a.hr
    ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM n a.hn
    a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.hd.ne'
    a.thetaZeroHighOnlyData.hcut a.thetaZeroHighOnlyData.hcross
    a.thetaZeroHighOnlyData.hb a.thetaZeroHighOnlyData.hb0
    a.thetaZeroHighOnlyData.hh a.thetaZeroHighOnlyData.hh0
    (concreteWallCap_continuous _ _ _ _) a.theta_zero_profile_nonempty

theorem theta_zero_sweep_cost_zero : a.thetaZeroSweepCost 0=0 := by
  exact omittedComparisonSweepCost_zero a.hrbounds.1.le a.hr
    ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM n a.hn
    a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.hd.ne'
    a.thetaZeroHighOnlyData.hb a.thetaZeroHighOnlyData.hb0
    a.thetaZeroHighOnlyData.hh a.thetaZeroHighOnlyData.hh0
    (concreteWallCap_continuous _ _ _ _) a.theta_zero_profile_nonempty

theorem theta_zero_sweep_cost_mem {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    a.thetaZeroSweepCost lam∈Icc (0:ℝ) lam := by
  constructor
  · exact omittedComparisonSweepCost_nonneg a.hrbounds.1.le a.hr
      ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM n a.hn
      a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.hd.ne'
      a.thetaZeroHighOnlyData.hcut a.thetaZeroHighOnlyData.hcross
      a.thetaZeroHighOnlyData.hb a.thetaZeroHighOnlyData.hb0
      a.thetaZeroHighOnlyData.hh a.thetaZeroHighOnlyData.hh0
      (concreteWallCap_continuous _ _ _ _) a.theta_zero_profile_nonempty hlam
  · have hh:=a.theta_zero_sweep_cost_lipschitz.dist_le_mul lam hlam 0
      ⟨le_rfl,(sq_nonneg a.d)⟩
    rw [a.theta_zero_sweep_cost_zero] at hh
    have hbound : |a.thetaZeroSweepCost lam|≤lam := by
      simpa only [Real.dist_eq,sub_zero,NNReal.coe_one,one_mul,abs_of_nonneg hlam.1] using hh
    exact (le_abs_self _).trans hbound

theorem theta_zero_sweep_log_derivative_envelope :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) (a.d^2)),
      ∃alpha : a.Profile,
        omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha=
          omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
            a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam ∧
        lam*deriv a.thetaZeroSweepCost lam≤(1/4:ℝ)*a.thetaZeroOriginalSweepDensity lam alpha := by
  simpa only [thetaZeroSweepCost,thetaZeroOriginalSweepDensity] using
    omittedComparisonSweepCost_ae_log_derivative_le a.hrbounds.1.le a.hr
      ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM n a.hn
      a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.hd.ne'
      (sq_pos_of_pos a.hd) a.thetaZeroHighOnlyData.hcut
      a.thetaZeroHighOnlyData.hcross a.thetaZeroHighOnlyData.hb
      a.thetaZeroHighOnlyData.hb0 a.thetaZeroHighOnlyData.hh
      a.thetaZeroHighOnlyData.hh0
      (concreteWallCap_continuous _ _ _ _) a.theta_zero_profile_nonempty

theorem theta_zero_sweep_cost_le_of_original_density {tau B : ℝ}
    (htau : 0 < tau) (htauL : tau ≤ a.d^2)
    (hdensity : ∀lam∈Ioo tau (a.d^2),∀alpha : a.Profile,
      omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
        a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha=
      omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
        a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam →
      a.thetaZeroOriginalSweepDensity lam alpha ≤ B) :
    a.thetaZeroSweepCost (a.d^2) ≤ tau+(B/4)*Real.log (a.d^2/tau) := by
  have hL : 0<a.d^2:=sq_pos_of_pos a.hd
  have hv:=a.theta_zero_sweep_cost_lipschitz
  have hsmall : a.thetaZeroSweepCost tau ≤ tau := by
    have H:=hv.dist_le_mul tau ⟨htau.le,htauL⟩ 0 ⟨le_rfl,hL.le⟩
    change dist (a.thetaZeroSweepCost tau) (a.thetaZeroSweepCost 0) ≤
      (1:ℝ)*dist tau 0 at H
    rw [a.theta_zero_sweep_cost_zero,Real.dist_eq,Real.dist_eq,sub_zero,
      sub_zero,abs_of_pos htau,one_mul] at H
    exact (le_abs_self _).trans H
  have hac : AbsolutelyContinuousOnInterval a.thetaZeroSweepCost tau (a.d^2) :=
    (show LipschitzOnWith 1 a.thetaZeroSweepCost (uIcc tau (a.d^2)) from hv.mono (by
      rw [uIcc_of_le htauL];exact Icc_subset_Icc htau.le le_rfl)).absolutelyContinuousOnInterval
  have hinv : IntervalIntegrable (fun t:ℝ=>t⁻¹) volume tau (a.d^2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    rw [uIcc_of_le htauL] at ht
    exact (htau.trans_le ht.1).ne'
  have hlarge : a.thetaZeroSweepCost (a.d^2)-a.thetaZeroSweepCost tau ≤
      ∫t in tau..(a.d^2),(B/4)*t⁻¹ := by
    rw [←hac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_mono_ae_restrict htauL hac.intervalIntegrable_deriv
      (hinv.const_mul _)
    change ∀ᵐt ∂volume.restrict (Icc tau (a.d^2)),
      deriv a.thetaZeroSweepCost t≤(B/4)*t⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    have hd':=(ae_restrict_iff' measurableSet_Ioo).mp a.theta_zero_sweep_log_derivative_envelope
    filter_upwards [hd',volume.ae_ne tau,volume.ae_ne (a.d^2)] with t ht hnt hnL hti
    have htt:t∈Ioo tau (a.d^2):=
      ⟨lt_of_le_of_ne hti.1 (Ne.symm hnt),lt_of_le_of_ne hti.2 hnL⟩
    obtain ⟨alpha,hattained,hbound⟩:=ht ⟨htau.trans htt.1,htt.2⟩
    have hD:=hdensity t htt alpha hattained
    have hmul:t*deriv a.thetaZeroSweepCost t≤B/4:=hbound.trans (by linarith)
    have hpos:0<t:=htau.trans htt.1
    have hdv:=(le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmul)
    simpa only [div_eq_mul_inv] using hdv
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos htau hL] at hlarge
  linarith

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
