module

public import ComparisonActualHighWallDescendantSource
public import ComparisonNativeActualChildSweep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ}

def originalSweepDensity (a : ActualHighOnlyComparisonData n delta)
    (lam : ℝ) (alpha : a.Profile) : ℝ :=
  ∫u in (0:ℝ)..1,a.coefficient alpha lam u*
    ((orderedPathB n (a.bf alpha lam) (a.hf alpha lam) u-
      (orderedPathS n (a.bf alpha lam) (a.hf alpha lam) u)^2)+
      (orderedPathS n (a.bf alpha lam) (a.hf alpha lam) u-a.R alpha u)^2)

theorem cost_le_of_original_density (a : ActualHighOnlyComparisonData n delta)
    {tau B : ℝ} (htau : 0 < tau) (htauL : tau ≤ a.d^2)
    (hdensity : ∀lam∈Ioo tau (a.d^2),∀alpha : a.Profile,
      a.objective lam alpha=a.minimum lam → a.originalSweepDensity lam alpha ≤ B) :
    a.cost (a.d^2) ≤ tau+(B/4)*Real.log (a.d^2/tau) := by
  have hL : 0 < a.d^2:=sq_pos_of_pos a.hd
  have hv:=a.cost_lipschitz
  have hsmall : a.cost tau ≤ tau := by
    have H:=hv.dist_le_mul tau ⟨htau.le,htauL⟩ 0 ⟨le_rfl,hL.le⟩
    change dist (a.cost tau) (a.cost 0) ≤ (1:ℝ)*dist tau 0 at H
    rw [a.cost_zero,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,abs_of_pos htau,one_mul] at H
    exact (le_abs_self _).trans H
  have hac : AbsolutelyContinuousOnInterval a.cost tau (a.d^2) :=
    (show LipschitzOnWith 1 a.cost (uIcc tau (a.d^2)) from hv.mono (by
      rw [uIcc_of_le htauL]; exact Icc_subset_Icc htau.le le_rfl)).absolutelyContinuousOnInterval
  have hinv : IntervalIntegrable (fun t : ℝ=>t⁻¹) volume tau (a.d^2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    rw [uIcc_of_le htauL] at ht
    exact (htau.trans_le ht.1).ne'
  have hlarge : a.cost (a.d^2)-a.cost tau ≤ ∫t in tau..(a.d^2),(B/4)*t⁻¹ := by
    rw [←hac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_mono_ae_restrict htauL hac.intervalIntegrable_deriv (hinv.const_mul _)
    change ∀ᵐ t ∂volume.restrict (Icc tau (a.d^2)),deriv a.cost t ≤ (B/4)*t⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    have hd' := (ae_restrict_iff' measurableSet_Ioo).mp a.log_derivative_envelope
    filter_upwards [hd',volume.ae_ne tau,volume.ae_ne (a.d^2)] with t ht hnt hnL hti
    have htt : t∈Ioo tau (a.d^2) :=
      ⟨lt_of_le_of_ne hti.1 (Ne.symm hnt),lt_of_le_of_ne hti.2 hnL⟩
    obtain ⟨alpha,hattained,hbound⟩:=ht ⟨htau.trans htt.1,htt.2⟩
    have hD:=hdensity t htt alpha hattained
    change t*deriv a.cost t ≤ (1/4:ℝ)*a.originalSweepDensity t alpha at hbound
    have hmul : t*deriv a.cost t ≤ B/4 := hbound.trans (by linarith)
    have hpos : 0 < t := htau.trans htt.1
    have hdv := (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmul)
    simpa only [div_eq_mul_inv] using hdv
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos htau hL] at hlarge
  linarith

theorem pressure_failure_selects_original_density
    (a : ActualHighOnlyComparisonData n delta) {tau B : ℝ}
    (htau : 0 < tau) (htauL : tau ≤ a.d^2)
    (hfail : tau+(B/4)*Real.log (a.d^2/tau) < a.cost (a.d^2)) :
    ∃lam∈Ioo tau (a.d^2),∃alpha : a.Profile,
      a.objective lam alpha=a.minimum lam ∧ B<a.originalSweepDensity lam alpha := by
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (a.cost_le_of_original_density htau htauL hno) hfail

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
