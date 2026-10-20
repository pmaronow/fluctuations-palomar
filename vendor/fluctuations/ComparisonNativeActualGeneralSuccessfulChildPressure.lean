module

public import ComparisonNativeActualGeneralSuccessfulChildTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

def actualCompensatedChildPressureCost
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock c0 x : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hc0 : 0 < c0) (hx : 0 < x) : ℝ :=
  let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
  variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
    n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
      (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
      child.d ((c0*x)^2)

theorem exists_actual_successful_child_strict_parent_from_pressure
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hroom : ∀n,(M n).lam+(c0*x n)^2 ≤ (M n).b 0)
    (hq : ∀n,2 ≤ ((dim n+1:ℕ):ℝ)^delta)
    (hcost : ∀ᶠn in atTop,(M n).actualCompensatedChildPressureCost hc0
      ((M n).hxs.trans_le (hxs n)) ≤ (M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n)) :
    ∃sigma : ℕ→ℕ,StrictMono sigma ∧ ∀ᶠn in atTop,
      cl*x (sigma n) < (M (sigma n)).alpha.val.val (x (sigma n)) ∧
        (M (sigma n)).alpha.val.val (x (sigma n)) < cu*x (sigma n) := by
  classical
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  choose beta a H using fun n=>(M n).exists_actual_child_attained hc0 (hx n) (hroom n) (hq n)
  have hparent n : (a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧ (a n).R=(M n).R := by
    rcases H n with ⟨hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr,hattained⟩
    refine ⟨?_,?_,hlam,hR⟩ <;> rw [hcontext] <;> rfl
  have hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (dim n+1:ℕ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n) := by
    filter_upwards [hcost] with n hn
    rcases H n with ⟨hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr,hattained⟩
    refine ⟨hd,hl,?_⟩
    rw [he]
    exact hn
  exact exists_actual_successful_child_strict_parent_profile_along
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G a x hxs hxlim hparent hchild htarget hweak hclmargin hcumargin hroom beta
    (fun n=>(H n).2.2.2.2.2.2.2.2.1) (fun n=>(H n).2.2.2.2.2.2.2.2.2.2.2)

theorem eventually_actual_bad_weak_history_child_pressure_fails
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hroom : ∀n,(M n).lam+(c0*x n)^2 ≤ (M n).b 0)
    (hq : ∀n,2 ≤ ((dim n+1:ℕ):ℝ)^delta)
    (Hbad : ∀ᶠn in atTop,¬(cl*x n ≤ (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) ≤ cu*x n)) :
    ∀ᶠn in atTop,(M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n) <
      (M n).actualCompensatedChildPressureCost hc0 ((M n).hxs.trans_le (hxs n)) := by
  classical
  by_contra Hnone
  have Hfreq : ∃ᶠn in atTop,(M n).actualCompensatedChildPressureCost hc0
      ((M n).hxs.trans_le (hxs n)) ≤ (M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n) := by
    simpa only [Filter.Frequently,not_not,not_le] using Hnone
  obtain ⟨phi,hphi,Hphi⟩:=extraction_of_frequently_atTop Hfreq
  obtain ⟨sigma,hsigma,Hgood⟩:=exists_actual_successful_child_strict_parent_from_pressure
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>x (phi n)) (fun n=>hxs (phi n))
    (hxlim.comp hphi.tendsto_atTop) (hphi.tendsto_atTop.eventually htarget)
    (hweak.comp hphi.tendsto_atTop) hclmargin hcumargin
    (fun n=>hroom (phi n)) (fun n=>hq (phi n)) (Eventually.of_forall Hphi)
  obtain ⟨n,hn⟩:=(Hgood.and ((hphi.comp hsigma).tendsto_atTop.eventually Hbad)).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

theorem eventually_actual_bad_weak_history_child_pressure_fails_of_eventual_room
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hroom : ∀ᶠn in atTop,(M n).lam+(c0*x n)^2 ≤ (M n).b 0)
    (Hbad : ∀ᶠn in atTop,¬(cl*x n ≤ (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) ≤ cu*x n)) :
    ∀ᶠn in atTop,(M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n) <
      (M n).actualCompensatedChildPressureCost hc0 ((M n).hxs.trans_le (hxs n))  := by
  have Hq : ∀ᶠn in atTop,2 ≤ ((dim n+1:ℕ):ℝ)^delta :=
    ((tendsto_rpow_atTop hdelta).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))).eventually
        (eventually_ge_atTop 2)
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp (hroom.and Hq)
  let shift:=fun n:ℕ=>n+n0
  have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij n0
  have Hfail:=eventually_actual_bad_weak_history_child_pressure_fails
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (shift n)) (hdim.comp hshift.tendsto_atTop)
    (fun n=>M (shift n)) (G.comp shift hshift) (fun n=>x (shift n)) (fun n=>hxs (shift n))
    (hxlim.comp hshift.tendsto_atTop) (hshift.tendsto_atTop.eventually htarget)
    (hweak.comp hshift.tendsto_atTop) hclmargin hcumargin
    (fun n=>(Hn0 (shift n) (Nat.le_add_left n0 n)).1)
    (fun n=>(Hn0 (shift n) (Nat.le_add_left n0 n)).2)
    (hshift.tendsto_atTop.eventually Hbad)
  rw [←map_add_atTop_eq_nat n0]
  exact Hfail

theorem eventually_actual_selected_bad_weak_history_child_pressure_fails
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (hd : ∀ᶠn in atTop,(M n).context.d ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ (M n).xs)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hroom : ∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b 0)
    (Hbad : ∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    ∀ᶠn in atTop,(M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (M n).xs <
      (M n).actualCompensatedChildPressureCost hc0 (M n).hxs := by
  have HW:=eventually_actual_weak_history_working_scale_le_one M G hd
  have Hweak:=actual_weak_history_bad_test_strength_tendsto_zero
    hm hdelta hroomdelta hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G HW hclmargin hcumargin Hbad
  exact eventually_actual_bad_weak_history_child_pressure_fails_of_eventual_room
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G (fun n=>(M n).xs) (fun _=>le_rfl) G.xs_zero htarget Hweak
    hclmargin hcumargin hroom Hbad

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
