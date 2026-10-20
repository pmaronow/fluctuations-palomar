module

public import ConcreteVariableEndpointStrengthSweep
public import ComparisonNativeSuccessfulChildBarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def nativeActualSweepDensity (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ)
    (α : inverseIntegralConstraints 0 0 k M) : ℝ :=
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  ∫u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
    ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
      (orderedPathS n bf hf u-R u)^2)

theorem native_actual_sweep_cost_le_of_density
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ) {d L tau B : ℝ}
    (hd : d≠0) (hL : 0 < L) (hLb : L ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints 0 0 k M).Nonempty)
    (htau : 0 < tau) (htauL : tau ≤ L)
    (hdensity : ∀lam∈Ioo tau L,∀α : inverseIntegralConstraints 0 0 k M,
      variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
        variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam →
      nativeActualSweepDensity hc hk hkc hm hM n b h d lam α ≤ B) :
    variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d L ≤
      tau+(B/4)*Real.log (L/tau) := by
  let v:=variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d
  have hv:=variableEndpointComparisonSweepCost_lipschitz hc hk hkc hm hM n hn
    b h hd hLb hb hh hh0 hMc hne
  have hz : v 0=0 := variableEndpointComparisonSweepCost_zero hc hk hkc hm hM
    n hn b h hd (hL.le.trans hLb) hb hh hh0 hMc hne
  have hsmall : v tau ≤ tau := by
    have h:=hv.dist_le_mul tau ⟨htau.le,htauL⟩ 0 ⟨le_rfl,hL.le⟩
    change dist (v tau) (v 0) ≤ (1:ℝ)*dist tau 0 at h
    rw [hz,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,abs_of_pos htau,one_mul] at h
    exact (le_abs_self _).trans h
  have hac : AbsolutelyContinuousOnInterval v tau L :=
    (show LipschitzOnWith 1 v (uIcc tau L) from hv.mono (by
      rw [uIcc_of_le htauL]; exact Icc_subset_Icc htau.le le_rfl)).absolutelyContinuousOnInterval
  have hinv : IntervalIntegrable (fun t : ℝ=>t⁻¹) volume tau L := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    rw [uIcc_of_le htauL] at ht
    exact (htau.trans_le ht.1).ne'
  have hder:=variableEndpointComparisonSweepCost_ae_log_derivative_le hc hk hkc hm hM
    n hn b h hd hL hLb hb hh hh0 hMc hne
  have hlarge : v L-v tau ≤ ∫t in tau..L,(B/4)*t⁻¹ := by
    rw [←hac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_mono_ae_restrict htauL hac.intervalIntegrable_deriv (hinv.const_mul _)
    change ∀ᵐ t ∂volume.restrict (Icc tau L),deriv v t ≤ (B/4)*t⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    have hd' := (ae_restrict_iff' measurableSet_Ioo).mp hder
    filter_upwards [hd',volume.ae_ne tau,volume.ae_ne L] with t ht hnt hnL hti
    have htt : t∈Ioo tau L := ⟨lt_of_le_of_ne hti.1 (Ne.symm hnt),lt_of_le_of_ne hti.2 hnL⟩
    obtain ⟨α,hα,hbound⟩:=ht ⟨htau.trans htt.1,htt.2⟩
    have hD:=hdensity t htt α hα
    change t*deriv v t ≤ (1/4:ℝ)*nativeActualSweepDensity hc hk hkc hm hM n b h d t α at hbound
    have hmul : t*deriv v t ≤ B/4 := hbound.trans (by linarith)
    have hpos : 0 < t := htau.trans htt.1
    have hdv := (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmul)
    simpa only [div_eq_mul_inv] using hdv
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos htau hL] at hlarge
  dsimp only [v] at hsmall hlarge ⊢
  linarith

theorem native_actual_sweep_failure_selects_density
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ) {d L tau B : ℝ}
    (hd : d≠0) (hL : 0 < L) (hLb : L ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints 0 0 k M).Nonempty)
    (htau : 0 < tau) (htauL : tau ≤ L)
    (hfail : tau+(B/4)*Real.log (L/tau) <
      variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d L) :
    ∃lam∈Ioo tau L,∃α : inverseIntegralConstraints 0 0 k M,
      variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
        variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam ∧
      B < nativeActualSweepDensity hc hk hkc hm hM n b h d lam α := by
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (native_actual_sweep_cost_le_of_density hc hk hkc hm hM
    n hn b h hd hL hLb hb hh hh0 hMc hne htau htauL hno) hfail

end
end OAI.SKFluctuations.LaplaceWindowFormalization
