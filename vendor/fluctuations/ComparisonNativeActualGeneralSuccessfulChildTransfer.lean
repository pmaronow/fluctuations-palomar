module

public import ComparisonNativeActualGeneralSuccessfulChildHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum
theorem exists_actual_successful_child_strict_parent_profile_along
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m) (hcl : 0 < cl) (hcu : 0 < cu)
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
    exists_actual_successful_child_native_weak_history_along
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
  obtain ⟨psi,hpsi,htotal,d,HU,HV,hklo,hkup,Hklo,Hkup,Hinv,Hsigma,Hslope,Hresponse,Hlimits⟩:=
    exists_actual_selected_bad_history_complete_direct_profile_along_weak_general
      hm hdelta hroomdelta (by positivity : 0 < cl/4) (by positivity : 0 < 4*cu)
      (by positivity : 0 ≤ 4*C/cl) hC0 (zero_le_one.trans (le_max_right Ct 1))
      hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) Q GQ
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
