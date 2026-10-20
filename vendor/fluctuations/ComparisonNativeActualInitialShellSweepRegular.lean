module

public import ComparisonNativeActualWeakBoundedShellPropagation
public import ComparisonNativeActualBadScaleMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false

theorem exists_actual_initial_shell_sweep_regular
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2)
    {m delta C0 : ℝ} (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hC0 : 0 < C0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) :
    ∃cl cu : ℝ,0 < cl ∧ 0 < cu ∧ cl ≤ 1 ∧ 1 ≤ cu ∧
      ∀c : (n:ℕ)→NativeChildBarrierParameters (n+1) delta,
      Tendsto (fun n=>(c n).d) atTop (𝓝 0) →
      (∀n,(c n).d ≤ 1 ∧ Real.sqrt (c n).N*(c n).E ≤ (c n).d^2 ∧
        (c n).N^(-(2:ℝ)/3+m)*(c n).d ≤ C0*(c n).E) →
      ∀epsilon shell : ℕ→ℝ,
      (∀n,epsilon n∈Icc (0:ℝ) (((n+1:ℕ):ℝ)^(-(1:ℝ)/3))) →
      (∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      ∀ᶠn : ℕ in atTop,∀lam∈Ioc (0:ℝ) ((c n).d^2),∀alpha : (c n).Profile,
        variableEndpointComparisonSweepObjective (c n).hc (c n).hk (c n).hkc (c n).hm (c n).hM
          (n+1) (initialShellMatrixClock ((beta:ℝ)^2) (epsilon n) (shell n)) (fun _=>0)
            (c n).d lam alpha=
        variableEndpointComparisonSweepMinimum (c n).hc (c n).hk (c n).hkc (c n).hm (c n).hM
          (n+1) (initialShellMatrixClock ((beta:ℝ)^2) (epsilon n) (shell n)) (fun _=>0)
            (c n).d lam →
        ∀r∈Icc (min (comparisonConditionalScale (c n).N delta (c n).E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r := by
  classical
  let T:ℝ:=(beta:ℝ)^2
  have hT : 0 < T:=zero_lt_one.trans hTemp
  obtain ⟨lower,upper,hlower,hupper,Hprop⟩:=exists_actual_weak_bounded_shell_finite_propagation hbeta hTemp
  let cl:=min lower (min 1 (T*Real.exp (-12*T)/2))
  let cu:=max upper (max 1 (T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T))+1))
  have hcl : 0 < cl := by dsimp [cl];exact lt_min hlower (lt_min zero_lt_one (by positivity))
  have hcu : 0 < cu := hupper.trans_le (le_max_left _ _)
  have hcl1 : cl ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcu1 : 1 ≤ cu := (le_max_left _ _).trans (le_max_right _ _)
  have hclMacro : cl ≤ lower := min_le_left _ _
  have hcuMacro : upper ≤ cu := le_max_left _ _
  have hclTemp : cl < T*Real.exp (-12*T) := by
    have H : cl ≤ T*Real.exp (-12*T)/2 := (min_le_right _ _).trans (min_le_right _ _)
    have HP : 0 < T*Real.exp (-12*T) := by positivity
    linarith
  have hcuTemp : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu := by
    have H : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T))+1 ≤ cu :=
      (le_max_right _ _).trans (le_max_right _ _)
    linarith
  let depth:=actualPropagationDepth delta
  let den:ℝ:=(depth:ℝ)+2
  have hden : 0 < den := by dsimp [den];positivity
  let c0:=min (1/2) (Real.sqrt ((T-1)/den)/2)
  have hc0 : 0 < c0 := by dsimp [c0];exact lt_min (by norm_num) (by positivity [sub_pos.mpr hTemp])
  have hc01 : c0 ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hbudget : (((actualPropagationDepth delta:ℕ):ℝ)+2)*c0^2 ≤ T-1 := by
    have HS : c0 ≤ Real.sqrt ((T-1)/den) := by
      have H:=min_le_right (1/2:ℝ) (Real.sqrt ((T-1)/den)/2)
      dsimp only [c0]
      linarith [Real.sqrt_nonneg ((T-1)/den)]
    have Hsq:=pow_le_pow_left₀ hc0.le HS 2
    rw [Real.sq_sqrt (by positivity : 0 ≤ (T-1)/den)] at Hsq
    have H:=(le_div_iff₀ hden).mp Hsq
    simpa only [den,depth,mul_comm] using H
  refine ⟨cl,cu,hcl,hcu,hcl1,hcu1,?_⟩
  intro c hdlim hnum epsilon shell hepsilon hshell hshelllim
  have HDsquare : Tendsto (fun n=>(c n).d^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] using hdlim.pow 2
  have HmatrixGate:=HDsquare.eventually (eventually_le_nhds (by dsimp only [T];linarith : 0 < T-1))
  by_contra Hnot
  have Hfreq : ∃ᶠn : ℕ in atTop,¬(∀lam∈Ioc (0:ℝ) ((c n).d^2),∀alpha : (c n).Profile,
      variableEndpointComparisonSweepObjective (c n).hc (c n).hk (c n).hkc (c n).hm (c n).hM
        (n+1) (initialShellMatrixClock T (epsilon n) (shell n)) (fun _=>0) (c n).d lam alpha=
      variableEndpointComparisonSweepMinimum (c n).hc (c n).hk (c n).hkc (c n).hm (c n).hM
        (n+1) (initialShellMatrixClock T (epsilon n) (shell n)) (fun _=>0) (c n).d lam →
      ∀r∈Icc (min (comparisonConditionalScale (c n).N delta (c n).E lam) 1) 1,
        cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) := by
    simpa only [Filter.Frequently,not_not] using Hnot
  obtain ⟨phi,hphi,Hphi⟩:=extraction_of_frequently_atTop (Hfreq.and_eventually HmatrixGate)
  have Hex n : ∃lam∈Ioc (0:ℝ) ((c (phi n)).d^2),∃alpha : (c (phi n)).Profile,
      variableEndpointComparisonSweepObjective (c (phi n)).hc (c (phi n)).hk (c (phi n)).hkc
        (c (phi n)).hm (c (phi n)).hM (phi n+1)
        (initialShellMatrixClock T (epsilon (phi n)) (shell (phi n))) (fun _=>0) (c (phi n)).d lam alpha=
      variableEndpointComparisonSweepMinimum (c (phi n)).hc (c (phi n)).hk (c (phi n)).hkc
        (c (phi n)).hm (c (phi n)).hM (phi n+1)
        (initialShellMatrixClock T (epsilon (phi n)) (shell (phi n))) (fun _=>0) (c (phi n)).d lam ∧
      ∃r∈Icc (min (comparisonConditionalScale (c (phi n)).N delta (c (phi n)).E lam) 1) 1,
        alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
    have H:=(Hphi n).1
    push Not at H
    obtain ⟨lam,hlam,alpha,hattained,r,hr,hbad⟩:=H
    refine ⟨lam,hlam,alpha,hattained,r,hr,?_⟩
    by_cases hlo : cl*r ≤ alpha.val.val r
    · exact Or.inr (hbad hlo)
    · exact Or.inl (lt_of_not_ge hlo)
  choose lam hlam alpha hattained r hr hbad using Hex
  have HM n : ∃M : NativeOverlapMinimum (phi n+1) m delta cl cu 2 C0 1 1 T,
      M.context=(c (phi n)).toOverlapContext ∧ M.lam=lam n ∧ HEq M.alpha (alpha n) ∧
      M.b=initialShellMatrixClock T (epsilon (phi n)) (shell (phi n)) ∧ M.h=(fun _=>0) ∧
      M.R=(c (phi n)).R (alpha n) ∧
      M.xs∈Icc (comparisonConditionalScale (c (phi n)).N delta (c (phi n)).E (lam n)) 1 ∧
      M.z=min (2*M.xs) 1 ∧ (M.alpha.val.val M.xs < cl*M.xs ∨ cu*M.xs < M.alpha.val.val M.xs) := by
    have hN1 : (1:ℝ) ≤ ((phi n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hEps1 : epsilon (phi n) ≤ 1 := (hepsilon (phi n)).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num))
    have HB : MonotoneOn (initialShellMatrixClock T (epsilon (phi n)) (shell (phi n))) (Icc (0:ℝ) 1) := by
      intro u hu v hv huv
      unfold initialShellMatrixClock
      split_ifs <;> linarith [(hepsilon (phi n)).1]
    have HL : lam n ≤ initialShellMatrixClock T (epsilon (phi n)) (shell (phi n)) 0 := by
      unfold initialShellMatrixClock
      split_ifs <;> linarith [(hlam n).2,(Hphi n).2]
    have HT : ∀u∈Icc (0:ℝ) 1,(0:ℝ)+initialShellMatrixClock T (epsilon (phi n)) (shell (phi n)) u ≤ T := by
      intro u hu
      unfold initialShellMatrixClock
      split_ifs <;> linarith [(hepsilon (phi n)).1]
    exact (c (phi n)).toOverlapContext.exists_selected_bad_scale_minimum_of_attained
      (alpha n) (initialShellMatrixClock T (epsilon (phi n)) (shell (phi n))) (fun _=>0)
      (hlam n).1 (hlam n).2 hdelta.le HB HL (fun _ _ _ _ _=>le_rfl) le_rfl (hattained n)
      (hnum (phi n)).1 (hnum (phi n)).2.1 (hnum (phi n)).2.2 HT le_rfl le_rfl hcl1 hcu1
      ⟨r n,hr n,hbad n⟩
  choose M hcontext hlamM halpha hbM hhM hRM hxsM hzM hbadM using HM
  have HD : Tendsto (fun n=>(M n).context.d) atTop (𝓝 0) := by
    simpa only [hcontext,NativeChildBarrierParameters.toOverlapContext,Function.comp_def] using hdlim.comp hphi.tendsto_atTop
  have Hcap:=HD.eventually (eventually_le_nhds hc0)
  have Htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta
      (M n).context.E (M n).lam ≤ (M n).xs := by
    filter_upwards [] with n
    rw [hcontext,hlamM]
    exact (hxsM n).1
  have Hbad : ∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs) := by
    filter_upwards [] with n
    rcases hbadM n with Hlo|Hhi
    · exact fun H=>not_lt_of_ge H.1 Hlo
    · exact fun H=>not_lt_of_ge H.2 Hhi
  exact Hprop m delta cl cu 2 C0 1 1 c0 hm hdelta hroom hcl hcu le_rfl hC0 le_rfl le_rfl
    hc0 hc01 hc01 hbudget hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    phi hphi.tendsto_atTop M (fun n=>epsilon (phi n)) (fun n=>shell (phi n))
    (fun n=>hepsilon (phi n)) (fun n=>hshell (phi n)) (hshelllim.comp hphi.tendsto_atTop)
    (Eventually.of_forall (fun n u=>congrFun (hbM n) u))
    (Eventually.of_forall (fun n u=>congrFun (hhM n) u)) Hcap (fun n=>(hxsM n).2) Htarget Hbad

end OAI.SKFluctuations.LaplaceWindowFormalization
