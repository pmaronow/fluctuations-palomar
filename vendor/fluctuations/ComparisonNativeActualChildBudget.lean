module

public import ComparisonNativeActualChildConstruction
public import ComparisonActualChildMargins
public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem eventually_actual_child_log_budget {m delta gamma : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,∀E L : ℝ,
      gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m) ≤ E →
      (n:ℝ)^(-10:ℝ) ≤ L → L ≤ 1 →
      (n:ℝ)^(-10:ℝ)+((n:ℝ)^(10*delta)*E/4)*Real.log (L/(n:ℝ)^(-10:ℝ)) ≤
        (n:ℝ)^(20*delta)*E := by
  have hinit:=eventually_coefficient_rpow_le (c:=1) (d:=gamma^2/2)
    (q:=-10) (r:=20*delta-(5:ℝ)/6+2*m) (by positivity) (by linarith)
  have hlog:=comparison_radius_log_power_tendsto (show 0 < 10*delta by positivity)
  filter_upwards [hinit,hlog.eventually (gt_mem_nhds (show (0:ℝ) < 1/5 by norm_num)),
    eventually_gt_atTop (0:ℕ)] with n hni hnl hn E L hE hL hL1
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp : 0 < (n:ℝ)^(10*delta) := Real.rpow_pos_of_pos hN _
  have hp20 : 0 ≤ (n:ℝ)^(20*delta) := (Real.rpow_pos_of_pos hN _).le
  have hE0 : 0 < E := (mul_pos (sq_pos_of_pos hgamma) (Real.rpow_pos_of_pos hN _)).trans_le hE
  have htau : 0 < (n:ℝ)^(-10:ℝ) := Real.rpow_pos_of_pos hN _
  have hL0 : 0 < L := htau.trans_le hL
  have hid : (n:ℝ)^(20*delta-(5:ℝ)/6+2*m)=
      (n:ℝ)^(20*delta)*(n:ℝ)^(-(5:ℝ)/6+2*m) := by
    rw [←Real.rpow_add hN]; congr 1; ring
  have hsmall : (n:ℝ)^(-10:ℝ) ≤ ((n:ℝ)^(20*delta)*E)/2 := by
    rw [one_mul,hid] at hni
    have hh:=mul_le_mul_of_nonneg_left hE hp20
    nlinarith
  have hlogbound : Real.log (L/(n:ℝ)^(-10:ℝ)) ≤ 10*Real.log (n:ℝ) := by
    calc
      _ ≤ Real.log (1/(n:ℝ)^(-10:ℝ)) := Real.log_le_log
        (div_pos hL0 htau) (div_le_div_of_nonneg_right hL1 htau.le)
      _ = _ := by rw [one_div,Real.log_inv,Real.log_rpow hN]; ring
  have hlogsmall : 10*Real.log (n:ℝ) ≤ 2*(n:ℝ)^(10*delta) := by
    have hh:Real.log (n:ℝ)/(n:ℝ)^(10*delta) < 1/5:=hnl
    have hh':= (div_lt_iff₀ hp).mp hh
    linarith
  have hid20 : (n:ℝ)^(10*delta)*(n:ℝ)^(10*delta)=(n:ℝ)^(20*delta) := by
    rw [←Real.rpow_add hN]; congr 1; ring
  have hlarge := mul_le_mul_of_nonneg_left (hlogbound.trans hlogsmall)
    (show 0 ≤ (n:ℝ)^(10*delta)*E/4 by positivity)
  rw [show ((n:ℝ)^(10*delta)*E/4)*(2*(n:ℝ)^(10*delta))=
      ((n:ℝ)^(10*delta)*(n:ℝ)^(10*delta))*E/2 by ring,hid20] at hlarge
  linarith

theorem eventually_native_actual_child_cost_of_density {m delta gamma : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,∀(child : NativeChildBarrierParameters n delta)
      (b h : ℝ → ℝ) (L : ℝ),
      0 < L → L ≤ 1 → L ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*child.d ≤ child.E →
      child.E ≤ child.d^2/Real.sqrt n → 2 ≤ child.N^delta →
      (∀lam∈Ioo ((n:ℝ)^(-10:ℝ)) L,∀α : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          n b h child.d lam α=
        variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
          n b h child.d lam →
        nativeActualSweepDensity child.hc child.hk child.hkc child.hm child.hM
          n b h child.d lam α ≤ (n:ℝ)^(10*delta)*child.E) →
      variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        n b h child.d L ≤ (n:ℝ)^(20*delta)*child.E := by
  filter_upwards [eventually_actual_child_log_budget hm hdelta hgamma] with n hn
  intro child b h L hL hL1 hLb hb hh hh0 hlo hup hq hD
  have hE:= (comparison_parent_scale_lower_bounds child.hN hgamma child.hd hlo hup).2.1
  have htau : 0 < (n:ℝ)^(-10:ℝ) := Real.rpow_pos_of_pos child.hN _
  have hMc : Continuous child.M := comparisonCap_continuous _ _ _ _ _ _
  have hne:=child.profile_nonempty hq
  by_cases hsmall : L ≤ (n:ℝ)^(-10:ℝ)
  · have hv:=variableEndpointComparisonSweepCost_lipschitz child.hc child.hk child.hkc
      child.hm child.hM n child.hn b h child.hd.ne' hLb hb hh hh0 hMc hne
    have hz:=variableEndpointComparisonSweepCost_zero child.hc child.hk child.hkc child.hm child.hM
      n child.hn b h child.hd.ne' (hL.le.trans hLb) hb hh hh0 hMc hne
    have hh:=hv.dist_le_mul L ⟨hL.le,le_rfl⟩ 0 ⟨le_rfl,hL.le⟩
    rw [hz,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,abs_of_pos hL,NNReal.coe_one,one_mul] at hh
    have htau1 : (n:ℝ)^(-10:ℝ) ≤ 1 := by
      have hN1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast child.hn
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
    have hi:=hn child.E ((n:ℝ)^(-10:ℝ)) hE le_rfl htau1
    rw [div_self htau.ne',Real.log_one,mul_zero,add_zero] at hi
    exact (le_abs_self _).trans (hh.trans (hsmall.trans hi))
  · have hcut : (n:ℝ)^(-10:ℝ) ≤ L := (lt_of_not_ge hsmall).le
    exact (native_actual_sweep_cost_le_of_density child.hc child.hk child.hkc child.hm child.hM
      n child.hn b h child.hd.ne' hL hLb hb hh hh0 hMc hne htau hcut hD).trans
      (hn child.E L hE hcut hL1)

theorem eventually_native_actual_child_failure_selects_density {m delta gamma : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,∀(child : NativeChildBarrierParameters n delta)
      (b h : ℝ → ℝ) (L : ℝ),
      0 < L → L ≤ 1 → L ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*child.d ≤ child.E →
      child.E ≤ child.d^2/Real.sqrt n → 2 ≤ child.N^delta →
      (n:ℝ)^(20*delta)*child.E <
        variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
          n b h child.d L →
      ∃lam∈Ioo ((n:ℝ)^(-10:ℝ)) L,∃α : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          n b h child.d lam α=
        variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
          n b h child.d lam ∧
        (n:ℝ)^(10*delta)*child.E <
          nativeActualSweepDensity child.hc child.hk child.hkc child.hm child.hM
            n b h child.d lam α := by
  filter_upwards [eventually_native_actual_child_cost_of_density hm hdelta hgamma] with n hn
  intro child b h L hL hL1 hLb hb hh hh0 hlo hup hq hfail
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (hn child b h L hL hL1 hLb hb hh hh0 hlo hup hq hno) hfail

end OAI.SKFluctuations.LaplaceWindowFormalization
