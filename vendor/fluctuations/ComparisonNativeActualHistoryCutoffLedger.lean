module

public import ComparisonNativeActualChildCapScale
public import ComparisonNativeActualInheritedLowFieldProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

def ActualHistoryCutoffChain (c0 : ℝ) :
    List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) →
      NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock → Prop
  | [],_=>True
  | P::ps,M=>∃x : ℝ,0<x ∧
      comparisonConditionalScale P.context.N delta P.context.E P.lam≤x ∧
      laplaceComparisonStrength P.context.d P.lam x≤x^2 ∧ P.z≤Az*x ∧
      M.context.d=actualChildRadius c0 x ∧
      M.context.E=actualChildErrorBudget n delta c0 P.context.d P.lam x ∧
      (∀u,M.b u=P.b u-laplaceComparisonStrength P.context.d P.lam (P.R u)) ∧
      (∀u,M.h u=P.h u+laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u) ∧
      ActualHistoryCutoffChain c0 ps P

theorem actual_history_cutoff_chain_cons
    (P M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock))
    (x : ℝ) (hx : 0<x)
    (htarget : comparisonConditionalScale P.context.N delta P.context.E P.lam≤x)
    (hweak : laplaceComparisonStrength P.context.d P.lam x≤x^2) (hz : P.z≤Az*x)
    (hd : M.context.d=actualChildRadius c0 x)
    (hE : M.context.E=actualChildErrorBudget n delta c0 P.context.d P.lam x)
    (hb : ∀u,M.b u=P.b u-laplaceComparisonStrength P.context.d P.lam (P.R u))
    (hh : ∀u,M.h u=P.h u+laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u)
    (hchain : ActualHistoryCutoffChain c0 ps P) :
    ActualHistoryCutoffChain c0 (P::ps) M :=
  ⟨x,hx,htarget,hweak,hz,hd,hE,hb,hh,hchain⟩

theorem eventually_actual_parent_cap_and_cutoff_inherit
    (hm : 0 < m) (hdelta : 0<delta) (hAz : 0≤Az) (hC0 : 0<C0) (hc0 : 0<c0)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m) :
    ∀ᶠn : ℕ in atTop,
      ∀(P M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      0<x → comparisonConditionalScale P.context.N delta P.context.E P.lam≤x →
      laplaceComparisonStrength P.context.d P.lam x≤x^2 → P.z≤Az*x →
      M.context.d=actualChildRadius c0 x →
      M.context.E=actualChildErrorBudget (n+1) delta c0 P.context.d P.lam x →
      P.lam*P.z≤(Az*max 1 (D^2/c0))*comparisonLowerScale M.context.N M.context.E M.context.d ∧
      comparisonLowerScale P.context.N P.context.E P.context.d≤
        comparisonLowerScale M.context.N M.context.E M.context.d := by
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [hs.eventually (eventually_actual_parent_strength_radius_le_child_cutoff
    (D:=D) (one_div_pos.mpr hC0) hc0 hcapmargin),
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hncap hnchild
  intro P M x hx htarget hweak hz hd hE
  have hlo : (1/C0)*P.context.N^(-(2:ℝ)/3+m)*P.context.d≤P.context.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using P.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : P.context.E≤P.context.d^2/Real.sqrt (n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr P.context.hN)).mpr (by simpa only [mul_comm] using P.hupper)
  have hax : comparisonLowerScale P.context.N P.context.E P.context.d≤x :=
    (comparison_conditional_scale_ge_lower (by exact_mod_cast P.context.hn) hdelta.le
      P.context.hE P.context.hd P.hlam P.hld).trans htarget
  have Hcap:=hncap P.context.d P.lam P.context.E x P.context.hd P.hlam P.hld P.hdD hx hlo hup hax
  have Hchild:=hnchild P.context.d P.lam P.context.E x P.context.hd P.hlam P.hld
    P.context.hE hx hlo hup htarget hweak
  have heq : comparisonLowerScale M.context.N M.context.E M.context.d=
      actualChildCutoff (n+1) delta c0 P.context.d P.lam x := by
    unfold comparisonLowerScale actualChildCutoff
    rw [hE,hd]
  rw [heq]
  constructor
  · have H1:=mul_le_mul_of_nonneg_left hz P.hlam.le
    have H2:=mul_le_mul_of_nonneg_left Hcap hAz
    nlinarith only [H1,H2]
  · exact Hchild.2.2.2.1

theorem eventually_actual_history_regular_caps_le_cutoff
    (hm : 0 < m) (hdelta : 0<delta) (hAz : 0≤Az) (hC0 : 0<C0) (hc0 : 0<c0)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m) :
    ∀ᶠn : ℕ in atTop,
      ∀(ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
        (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock),
      ActualHistoryCutoffChain c0 ps M →
      actualHistoryRegularCapSum ps≤(Az*max 1 (D^2/c0))*(ps.length:ℝ)*
        comparisonLowerScale M.context.N M.context.E M.context.d := by
  filter_upwards [eventually_actual_parent_cap_and_cutoff_inherit (cl:=cl) (cu:=cu)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin] with n hn
  intro ps
  induction ps with
  | nil => intro M hchain;simp [actualHistoryRegularCapSum]
  | cons P ps ih =>
    intro M hchain
    obtain ⟨x,hx,htarget,hweak,hz,hd,hE,hb,hh,hchain⟩:=hchain
    have H:=hn P M x hx htarget hweak hz hd hE
    have HI:=ih P hchain
    have Hup:=mul_le_mul_of_nonneg_left H.2
      (show 0≤(Az*max 1 (D^2/c0))*(ps.length:ℝ) by positivity)
    change P.lam*P.z+actualHistoryRegularCapSum ps≤_
    calc
      _≤(Az*max 1 (D^2/c0))*comparisonLowerScale M.context.N M.context.E M.context.d+
        (Az*max 1 (D^2/c0))*(ps.length:ℝ)*comparisonLowerScale M.context.N M.context.E M.context.d :=
          add_le_add H.1 (HI.trans Hup)
      _=_ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one];ring

theorem eventually_actual_history_regular_caps_le_working_scale
    (hm : 0 < m) (hdelta : 0<delta) (hAz : 0≤Az) (hC0 : 0<C0) (hc0 : 0<c0)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m)
    (depth : ℕ) :
    ∀ᶠn : ℕ in atTop,
      ∀(ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
        (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock),
      ActualHistoryCutoffChain c0 ps M → ps.length≤depth →
      actualHistoryRegularCapSum ps≤((Az*max 1 (D^2/c0))*(depth:ℝ))*M.xs := by
  filter_upwards [eventually_actual_history_regular_caps_le_cutoff (cl:=cl) (cu:=cu)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin] with n hn
  intro ps M hchain hdepth
  apply (hn ps M hchain).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdepth) (by positivity)
  · exact M.hscale
  · unfold comparisonLowerScale
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) M.context.hE.le) M.context.hd.le
  · positivity

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
