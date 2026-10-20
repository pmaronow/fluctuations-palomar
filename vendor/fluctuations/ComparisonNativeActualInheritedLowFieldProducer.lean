module

public import ComparisonNativeActualHistoryCapAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 9000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_child_error_doubles
    {c0 : ℝ} (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      0 < x → comparisonConditionalScale P.context.N delta P.context.E P.lam ≤ x →
      laplaceComparisonStrength P.context.d P.lam x ≤ x^2 →
      2*P.context.E ≤ actualChildErrorBudget (n+1) delta c0 P.context.d P.lam x := by
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  have hpow : ∀ᶠn : ℕ in atTop,2 ≤ ((n+1:ℕ):ℝ)^(delta/4) :=
    (((tendsto_rpow_atTop (by linarith : 0 < delta/4)).comp tendsto_natCast_atTop_atTop).comp hs).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hs.eventually (eventually_actual_child_parameters_from_target hm hdelta
    (one_div_pos.mpr hC0) hc0 hmargin),hpow] with n hn hn2
  intro P x hx htarget hweak
  have hlo : (1/C0)*P.context.N^(-(2:ℝ)/3+m)*P.context.d ≤ P.context.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using P.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : P.context.E ≤ P.context.d^2/Real.sqrt (n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr P.context.hN)).mpr (by simpa only [mul_comm] using P.hupper)
  have H:=hn P.context.d P.lam P.context.E x P.context.hd P.hlam P.hld P.context.hE hx
    hlo hup htarget hweak
  exact (mul_le_mul_of_nonneg_right hn2 P.context.hE.le).trans H.2.2.1

theorem eventually_actual_child_history_error_growth
    {c0 : ℝ} (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)) (x : ℝ),
      0 < x → comparisonConditionalScale P.context.N delta P.context.E P.lam ≤ x →
      laplaceComparisonStrength P.context.d P.lam x ≤ x^2 →
      M.context.E=actualChildErrorBudget (n+1) delta c0 P.context.d P.lam x →
      ActualHistoryErrorGrowth ps P.context.E → ActualHistoryErrorGrowth (P::ps) M.context.E := by
  filter_upwards [eventually_actual_child_error_doubles (cl:=cl) (cu:=cu) (Az:=Az)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hC0 hc0 hmargin] with n hn
  intro P M ps x hx htarget hweak hchild hg
  exact ⟨by rw [hchild];exact hn P x hx htarget hweak,hg⟩

theorem actual_shell_conditional_history_low_field_bound
    {n : ℕ} (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {T epsilon shell : ℝ} (hT : 0 ≤ T) (hepsilon : 0 ≤ epsilon)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u)
    (hh : ∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u)
    (hxs : M.xs=comparisonConditionalScale M.context.N delta M.context.E M.lam)
    (hparent : ∀P∈ps,P.xs=comparisonConditionalScale P.context.N delta P.context.E P.lam)
    (hg : ActualHistoryErrorGrowth ps M.context.E)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.h u ≤ (Az*D^2+T/cl)*(M.xs+u) := by
  have H:=M.actual_shell_history_field_le_regular_caps ps hcl hepsilon hb hh hu
  have Hcap:=M.actual_history_regular_caps_le_current_scale ps hAz hxs hparent hg
  have hx:=M.hxs
  have hcoef : 0 ≤ T/cl:=div_nonneg hT hcl.le
  have hcapcoef : 0 ≤ Az*D^2:=mul_nonneg hAz (sq_nonneg D)
  nlinarith [mul_nonneg hcoef hx.le,mul_nonneg hcapcoef hu.1]

theorem actual_shell_history_compensated_field_le_regular_caps
    {n : ℕ} (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {T epsilon shell : ℝ} (hT : 0 ≤ T) (hepsilon : 0 ≤ epsilon)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u)
    (hh : ∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.hf u:ℝ) ≤ actualHistoryRegularCapSum ps+
      (T/cl+bareSourceClockConstant cl Az D)*(M.xs+u) := by
  have Hfield:=M.actual_shell_history_field_le_regular_caps ps hcl hepsilon hb hh hu
  have hdD : M.context.d^2 ≤ D^2:=pow_le_pow_left₀ M.context.hd.le M.hdD 2
  have Hstrength:=(laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
    (M.hld.trans hdD)
  have hr:=(comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u).1
  have Hcomp:=mul_le_mul_of_nonneg_right Hstrength hr
  have Hrad:=mul_le_mul_of_nonneg_left (M.inverse_radius_le_source_mass hcl hAz hu) (sq_nonneg D)
  have Hextra:=mul_nonneg (div_nonneg hT hcl.le) M.hxs.le
  rw [(M.inherited_clock_coe hu).2]
  dsimp only [bareSourceClockConstant] at *
  nlinarith only [Hfield,Hcomp,Hrad,Hextra]

theorem actual_shell_conditional_history_source_clock_bounds
    {n : ℕ} (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {T epsilon shell : ℝ} (hT : 0 ≤ T) (hepsilon : 0 ≤ epsilon)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u)
    (hh : ∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u)
    (hxs : M.xs=comparisonConditionalScale M.context.N delta M.context.E M.lam)
    (hparent : ∀P∈ps,P.xs=comparisonConditionalScale P.context.N delta P.context.E P.lam)
    (hg : ActualHistoryErrorGrowth ps M.context.E)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    0 ≤ (M.bf u:ℝ) ∧ (M.bf u:ℝ) ≤ T ∧ 0 ≤ (M.hf u:ℝ) ∧
      (M.hf u:ℝ) ≤ (Az*D^2+T/cl+bareSourceClockConstant cl Az D)*(M.xs+u) := by
  have Hfield:=M.actual_shell_conditional_history_low_field_bound ps hcl hAz hT hepsilon
    hb hh hxs hparent hg hu
  have hdD : M.context.d^2 ≤ D^2:=pow_le_pow_left₀ M.context.hd.le M.hdD 2
  have Hstrength:=(laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
    (M.hld.trans hdD)
  have hr:=(comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u).1
  have Hcomp:=mul_le_mul_of_nonneg_right Hstrength hr
  have Hrad:=mul_le_mul_of_nonneg_left (M.inverse_radius_le_source_mass hcl hAz hu) (sq_nonneg D)
  have Hb : M.b u ≤ T := by
    rw [hb]
    unfold historyMatrixClock
    have Hred : 0 ≤ historyMatrixReduction (ps.map (fun P=>P.toHistoryTerm)) u := by
      clear hb hh hparent hg
      induction ps with
      | nil => exact le_rfl
      | cons P ps ih =>
        exact add_nonneg (laplaceComparisonStrength_pos P.context.d P.hlam (P.R u)).le ih
    have Hshell : initialShellMatrixClock T epsilon shell u ≤ T := by
      unfold initialShellMatrixClock
      split_ifs <;> linarith
    linarith
  have he:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
  rw [(M.inherited_clock_coe hu).1,(M.inherited_clock_coe hu).2]
  refine ⟨?_,by linarith,?_,?_⟩
  · rw [←(M.inherited_clock_coe hu).1]
    exact NNReal.coe_nonneg _
  · rw [←(M.inherited_clock_coe hu).2]
    exact NNReal.coe_nonneg _
  · dsimp only [bareSourceClockConstant] at *
    nlinarith only [Hfield,Hcomp,Hrad]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
