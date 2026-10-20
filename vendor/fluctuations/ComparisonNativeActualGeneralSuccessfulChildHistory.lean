module

public import ComparisonNativeActualGeneralProfileHistoryAssembly
public import ComparisonNativeActualSuccessfulChildMinimum
public import ComparisonNativeActualOuterChildRadiusBounds
public import ComparisonNativeActualGeneralHistoryCompleteProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

def ActualNativeProfileHistory.append_successful_child
    {m delta cl cu Az C0 Ct D Bclock T c0 C : ℝ} {dim : ℕ→ℕ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hC : 0 ≤ C) (hAzC : Az ≤ 4*C/cl)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeProfileHistory M T c0)
    (Q : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta (cl/4) (4*cu) (4*C/cl)
      C0 (max Ct 1) (max D 1) (max Bclock T))
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(Q n).context.d=actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop,(Q n).context.E=actualChildErrorBudget (dim n+1) delta c0
      (M n).context.d (M n).lam (x n))
    (hb : ∀ᶠn in atTop,∀u,(Q n).b u=(M n).b u-
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
    (hh : ∀ᶠn in atTop,∀u,(Q n).h u=(M n).h u+
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u)
    (hQxs : ∀n,(Q n).xs=x n) :
    ActualNativeProfileHistory Q T c0 := by
  have hclW : cl/4 ≤ cl := by linarith
  have hcuW : cu ≤ 4*cu := by linarith
  let GW := G.weaken_constants hclW hcuW hAzC (le_max_left Ct 1)
    (le_max_left D 1) (le_max_left Bclock T)
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcap : ∀ᶠn in atTop,(M n).z ≤ (4*C/cl)*x n := by
    filter_upwards [] with n
    exact (M n).hzxs.trans ((mul_le_mul_of_nonneg_left (hxs n) hAz).trans
      (mul_le_mul_of_nonneg_right hAzC (hx n).le))
  have hQlim : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) := by
    simpa only [hQxs] using hxlim
  exact GW.append_child hm hdelta (by positivity) (by positivity) hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hdim Q x hx
    (hxlim.eventually (eventually_le_nhds zero_lt_one)) htarget hcap hweak hd hE hb hh hQlim

theorem exists_actual_successful_child_native_weak_history_along
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (a : (n:ℕ)→NativeChildBarrierCall (dim n+1) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧ (a n).R=(M n).R)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (dim n+1:ℕ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hroom : ∀n,(M n).lam+(c0*x n)^2 ≤ (M n).b 0)
    (beta : (n:ℕ)→((M n).context.toChildBarrierParameters.actualChild (M n).hlam hc0
      ((M n).hxs.trans_le (hxs n))).Profile)
    (hZ : ∀n,(a n).Z=
      ((M n).context.toChildBarrierParameters.actualChild (M n).hlam hc0
        ((M n).hxs.trans_le (hxs n))).R (beta n))
    (hattained : ∀n,
      let child := (M n).context.toChildBarrierParameters.actualChild (M n).hlam hc0
        ((M n).hxs.trans_le (hxs n))
      variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
        (dim n+1) (fun u=>(M n).b u-laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
          (fun u=>(M n).h u+laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u)
          (c0*x n) ((c0*x n)^2) (beta n)=
      variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
        (dim n+1) (fun u=>(M n).b u-laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
          (fun u=>(M n).h u+laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u)
          (c0*x n) ((c0*x n)^2)) :
    ∃C : ℝ,1 ≤ C ∧ Az ≤ 4*C/cl ∧ ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃Q : (n:ℕ)→NativeOverlapMinimum (dim (phi n)+1) m delta (cl/4) (4*cu) (4*C/cl)
        C0 (max Ct 1) (max D 1) (max Bclock T),
        Nonempty (ActualNativeProfileHistory Q T c0) ∧
          (∀n,(Q n).xs=x (phi n)) ∧ (∀n,(Q n).R=(a (phi n)).Z) ∧
          (∀n,(Q n).context.d=c0*x (phi n)) ∧
          (∀n,(Q n).lam=(c0*x (phi n))^2) := by
  classical
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨C0band,hC0band,Hband⟩:=actual_minimum_successful_child_outer_radius_bounds
    hm hdelta hcl hcu hAz hC0 hc0 (fun n=>dim n+1) ((tendsto_add_atTop_nat 1).comp hdim)
    M a x hxs hxlim hparent hchild hweak
  let C:=max C0band (cl*Az/4)
  have hC : 1 ≤ C := hC0band.trans (le_max_left _ _)
  have hAzC : Az ≤ 4*C/cl := by
    apply (le_div_iff₀ hcl).mpr
    nlinarith [le_max_right C0band (cl*Az/4)]
  have Hband' : ∀ᶠn in atTop,∀u∈Icc (C*x n) 1,
      u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
    filter_upwards [Hband] with n hn u hu
    exact hn u ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (hx n).le).trans hu.1,hu.2⟩
  have Hparam:=eventually_actual_successful_child_minimum_parameters hm hdelta hC0 hc0 hc01
    hmargin dim hdim M x hx htarget hweak
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp
    (Hparam.and (Hband'.and (G.total_root.and (hxlim.eventually (eventually_le_nhds zero_lt_one)))))
  let phi:=fun n:ℕ=>n+n0
  have hphi : StrictMono phi := fun i j hij=>Nat.add_lt_add_right hij n0
  have HP n := Hn0 (phi n) (Nat.le_add_left n0 n)
  let Q:=fun n=>((M (phi n)).actualSuccessfulChildMinimum hc0 hc01 (hx (phi n)) hcl hcu
    (zero_lt_one.trans_le hC).le (beta (phi n)) (hroom (phi n)) (hattained (phi n))
    (show c0*x (phi n) ≤ max D 1 from
      (by simpa only [one_mul] using
        mul_le_mul hc01 (HP n).2.2.2 (hx (phi n)).le zero_le_one : c0*x (phi n) ≤ 1).trans
        (le_max_right _ _))
    (HP n).1.2.1 (HP n).2.2.1.1 (by
      intro u hu
      rw [←hZ (phi n)]
      exact (HP n).2.1 u hu)).weakenConstants le_rfl le_rfl le_rfl
        (le_max_right Ct 1) le_rfl (le_max_right Bclock T)
  have hQxs n : (Q n).xs=x (phi n) := rfl
  have hQR n : (Q n).R=(a (phi n)).Z := (hZ (phi n)).symm
  let GQ := (G.comp phi hphi).append_successful_child hm hdelta hcl hcu hAz hC0 hc0 hc01
    (zero_lt_one.trans_le hC).le hAzC hmargin hcapmargin hgapmargin
    (hdim.comp hphi.tendsto_atTop) Q (fun n=>x (phi n)) (fun n=>hxs (phi n))
    (hxlim.comp hphi.tendsto_atTop) (hphi.tendsto_atTop.eventually htarget)
    (hweak.comp hphi.tendsto_atTop) (Eventually.of_forall (fun _=>rfl))
    (Eventually.of_forall (fun _=>rfl)) (Eventually.of_forall (fun _ _=>rfl))
    (Eventually.of_forall (fun _ _=>rfl)) hQxs
  exact ⟨C,hC,hAzC,phi,hphi,Q,⟨GQ⟩,hQxs,hQR,fun _=>rfl,fun _=>rfl⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
