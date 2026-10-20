module

public import SKProof.OriginalQNativeSuccessfulChildContext
public import ComparisonNativeSuccessfulChildFiniteInverseCDF
public import ComparisonNativeActualChildDirectCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem successful_native_child_comparable_profile_transfers_to_parent_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → NativeChildBarrierCall (dim n+1) delta)
    (x : ℕ → ℝ) (hxs : ∀n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n, (a n).context.E = (M n).context.E ∧
      (a n).context.d = (M n).context.d ∧
      (a n).lam = (M n).lam ∧ (a n).R = (M n).R)
    (hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).context.d (M n).lam (x n))
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (Q : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0
        (max Ct 1) (max D 1) (max Bclock T))
    (GQ : NativeActualComparableBandContext Q T)
    (hQxs : ∀n, (Q n).xs = x n)
    (hQR : ∀n, (Q n).R = (a n).Z)
    (hQd : ∀n, (Q n).context.d = c0*x n)
    (hQlam : ∀n, (Q n).lam = (c0*x n)^2) :
    ∃sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ᶠn in atTop,
      cl*x (sigma n) < (M (sigma n)).alpha.val.val (x (sigma n)) ∧
      (M (sigma n)).alpha.val.val (x (sigma n)) < cu*x (sigma n) := by
  let Ccal : ℝ := max 1 (1/c0^3)
  have hCcal : 1 ≤ Ccal := le_max_left _ _
  have hAzQ : 0 ≤ 4*C/cl :=
    nonneg_of_mul_nonneg_left ((Q 0).hz.1.trans (Q 0).hzxs) (Q 0).hxs
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcompare n : (Q n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (Q n).context.d (Q n).lam (Q n).xs := by
    rw [hQxs,hQd,hQlam]
    exact (actual_child_direct_calibration_at_parent_test (delta:=delta)
      (d:=(M n).context.d) (M n).context.hn hc0 hc01
      (M n).hlam (hx n)).2.2
  have hD : Tendsto (fun n => (Q n).context.d) atTop (𝓝 0) := by
    simpa only [hQd, mul_zero] using hxlim.const_mul c0
  have hWupper := eventually_actual_comparable_context_working_scale_le_one
    Q GQ (hD.eventually (eventually_le_nhds zero_lt_one))
  obtain ⟨psi,hpsi,htotal,d,HU,HV,hklo,hkup,Hklo,Hkup,Hinv,
    Hsigma,Hslope,Hresponse,Hlimits⟩ :=
    exists_actual_comparable_context_complete_direct_profile
      hm hdelta hroom (by positivity : 0 < cl/4)
      (by positivity : 0 < 4*cu)
      hAzQ
      hC0 (zero_le_one.trans (le_max_right Ct 1))
      hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim Q GQ hWupper hcompare
  let kappa := (T/T)*scalarInitialDensityConstant GQ.hT d.beta
  have hkappaLo : cl < kappa := by
    have hTpos : 0 < T*Real.exp (-12*T) :=
      mul_pos GQ.hT (Real.exp_pos _)
    change 2*T*Real.exp (-12*T) ≤ kappa at Hklo
    nlinarith only [Hklo,hTpos,hclmargin]
  have hkappaHi : kappa < cu := Hkup.trans_lt hcumargin
  have hchildProfile : TendstoLocallyUniformlyOn
      (fun n v => (a (psi n)).Z (x (psi n)*v)/x (psi n))
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [hQxs,hQR] using Hinv
  have htransfer := actual_minimum_successful_child_parent_profile_transfer
    hm hdelta hcl hcu hAz hC0 hc0 (fun n => dim (psi n)+1)
    ((tendsto_add_atTop_nat 1).comp
      (hdim.comp hpsi.tendsto_atTop))
    (fun n => M (psi n)) (fun n => a (psi n))
    (fun n => x (psi n)) (fun n => hxs (psi n))
    (hxlim.comp hpsi.tendsto_atTop)
    (fun n => hparent (psi n))
    (hpsi.tendsto_atTop.eventually hchild)
    (hweak.comp hpsi.tendsto_atTop)
    hkappaLo hkappaHi hchildProfile
  exact ⟨psi,hpsi,htransfer.2⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
