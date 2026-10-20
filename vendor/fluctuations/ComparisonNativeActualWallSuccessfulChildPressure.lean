module

public import ComparisonNativeActualGeneralSuccessfulChildPressure
public import ComparisonNativeActualWallProfileHistory

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

def ActualNativeWallProfileHistory.append_successful_child
    {m delta cl cu Az C0 Ct D Bclock T c0 C : ℝ} {dim : ℕ→ℕ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hC : 0 ≤ C) (hAzC : Az ≤ 4*C/cl)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeWallProfileHistory M T c0)
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
    ActualNativeWallProfileHistory Q T c0 := by
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
  exact GW.append_child Q x hx
    (hxlim.eventually (eventually_le_nhds zero_lt_one)) htarget hcap hweak hd hE hb hh hQlim

theorem exists_actual_successful_child_native_weak_history_along_over_wall
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeWallProfileHistory M T c0)
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
        Nonempty (ActualNativeWallProfileHistory Q T c0) ∧
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
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum
theorem exists_actual_successful_child_strict_parent_profile_along_over_wall
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeWallProfileHistory M T c0)
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
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
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
    ∃sigma : ℕ→ℕ,StrictMono sigma ∧ ∀ᶠn in atTop,
      cl*x (sigma n) < (M (sigma n)).alpha.val.val (x (sigma n)) ∧
        (M (sigma n)).alpha.val.val (x (sigma n)) < cu*x (sigma n) := by
  classical
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨C,hC,hAzC,phi,hphi,Q,⟨GQ⟩,hQxs,hQR,hQd,hQlam⟩:=
    exists_actual_successful_child_native_weak_history_along_over_wall
      hm hdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G a x hxs hxlim hparent hchild htarget hweak hroom beta hZ hattained
  let Ccal:=max 1 (1/c0^3)
  have hCcal : 1 ≤ Ccal := le_max_left _ _
  have Hcompare n : (Q n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (Q n).context.d (Q n).lam (Q n).xs := by
    rw [hQxs,hQd,hQlam]
    exact (actual_child_direct_calibration_at_parent_test (delta:=delta)
      (d:=(M (phi n)).context.d) (M (phi n)).context.hn hc0 hc01 (M (phi n)).hlam
      (hx (phi n))).2.2
  have HD : Tendsto (fun n=>(Q n).context.d) atTop (𝓝 0) := by
    simpa only [hQd,mul_zero,Function.comp_def] using (hxlim.comp hphi.tendsto_atTop).const_mul c0
  have Hcan := actual_canonical_band_tendsto_zero_of_radius_tendsto_along
    Q (zero_le_one.trans hCcal) Hcompare HD
  obtain ⟨GQc⟩:=GQ.exists_context hm hdelta (by positivity : 0 < cl/4)
    (by positivity : 0 ≤ 4*C/cl) hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    (hdim.comp hphi.tendsto_atTop)
  obtain ⟨psi,hpsi,htotal,d,HU,HV,hklo,hkup,Hklo,Hkup,Hinv,Hsigma,Hslope,Hresponse,Hlimits⟩:=
    exists_actual_selected_bad_history_complete_direct_profile_along_comparable_shrinking
      hm hdelta hroomdelta (by positivity : 0 < cl/4) (by positivity : 0 < 4*cu)
      (by positivity : 0 ≤ 4*C/cl) hC0 (zero_le_one.trans (le_max_right Ct 1))
      hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) Q GQc
      (fun n=>(Q n).canonicalDirectTestBandScale) (fun _=>rfl) Hcan Hcompare
  let kappa:=(T/T)*scalarInitialDensityConstant GQ.hT d.beta
  have hkappaLo : cl < kappa := by
    have Hpositive : 0 < T*Real.exp (-12*T) := mul_pos G.hT (Real.exp_pos _)
    change 2*T*Real.exp (-12*T) ≤ kappa at Hklo
    nlinarith only [Hklo,Hpositive,hclmargin]
  have hkappaHi : kappa < cu := Hkup.trans_lt hcumargin
  have HchildProfile : TendstoLocallyUniformlyOn
      (fun n v=>(a (phi (psi n))).Z (x (phi (psi n))*v)/x (phi (psi n)))
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [hQxs,hQR] using Hinv
  let sigma:=phi ∘ psi
  have hsigma : StrictMono sigma:=hphi.comp hpsi
  have Htransfer:=actual_minimum_successful_child_parent_profile_transfer
    hm hdelta hcl hcu hAz hC0 hc0 (fun n=>dim (sigma n)+1)
    ((tendsto_add_atTop_nat 1).comp (hdim.comp hsigma.tendsto_atTop))
    (fun n=>M (sigma n)) (fun n=>a (sigma n)) (fun n=>x (sigma n))
    (fun n=>hxs (sigma n)) (hxlim.comp hsigma.tendsto_atTop)
    (fun n=>hparent (sigma n)) (hsigma.tendsto_atTop.eventually hchild)
    (hweak.comp hsigma.tendsto_atTop) hkappaLo hkappaHi HchildProfile
  exact ⟨sigma,hsigma,Htransfer.2⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

theorem exists_actual_successful_child_strict_parent_from_pressure_over_wall
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeWallProfileHistory M T c0)
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
  exact exists_actual_successful_child_strict_parent_profile_along_over_wall
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G a x hxs hxlim hparent hchild htarget hweak hclmargin hcumargin hroom beta
    (fun n=>(H n).2.2.2.2.2.2.2.2.1) (fun n=>(H n).2.2.2.2.2.2.2.2.2.2.2)

theorem eventually_actual_bad_weak_history_child_pressure_fails_over_wall
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeWallProfileHistory M T c0)
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
  obtain ⟨sigma,hsigma,Hgood⟩:=exists_actual_successful_child_strict_parent_from_pressure_over_wall
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>x (phi n)) (fun n=>hxs (phi n))
    (hxlim.comp hphi.tendsto_atTop) (hphi.tendsto_atTop.eventually htarget)
    (hweak.comp hphi.tendsto_atTop) hclmargin hcumargin
    (fun n=>hroom (phi n)) (fun n=>hq (phi n)) (Eventually.of_forall Hphi)
  obtain ⟨n,hn⟩:=(Hgood.and ((hphi.comp hsigma).tendsto_atTop.eventually Hbad)).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

theorem eventually_actual_bad_weak_history_child_pressure_fails_of_eventual_room_over_wall
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeWallProfileHistory M T c0)
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
  have Hfail:=eventually_actual_bad_weak_history_child_pressure_fails_over_wall
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

theorem eventually_actual_selected_bad_weak_history_child_pressure_fails_over_wall
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeWallProfileHistory M T c0)
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
  obtain ⟨Gc⟩:=G.exists_context hm hdelta hcl hAz hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hdim
  have HW:=eventually_actual_comparable_context_working_scale_le_one M Gc hd
  have Hweak:=actual_comparable_context_bad_test_strength_tendsto_zero
    hm hdelta hroomdelta hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M Gc HW hclmargin hcumargin Hbad
  exact eventually_actual_bad_weak_history_child_pressure_fails_of_eventual_room_over_wall
    hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G (fun n=>(M n).xs) (fun _=>le_rfl) G.xs_zero htarget Hweak
    hclmargin hcumargin hroom Hbad

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
