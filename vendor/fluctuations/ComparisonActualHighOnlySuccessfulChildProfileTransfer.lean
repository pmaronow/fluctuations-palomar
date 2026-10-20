module

public import ComparisonActualHighOnlyTwoScaleChildAgreement
public import ComparisonNativeSuccessfulChildFiniteInverseCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 22000000
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_inverse_test_strict_of_linear_high_only_radius_profile
    {N : ℕ→ℕ}
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    {kappa : ℝ} (hcl : 0 < cl) (hclmargin : cl < kappa) (hcumargin : kappa < cu)
    (hprofile : TendstoLocallyUniformlyOn (fun n v=>(M n).R (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ))) :
    ∀ᶠn in atTop,cl*x n < (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) < cu*x n := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hcu : 0 < cu := hkappa.trans hcumargin
  have Hlo := (hprofile.tendsto_at hcl).eventually
    (gt_mem_nhds (show cl/kappa < 1 from (div_lt_one₀ hkappa).mpr hclmargin))
  have Hup := (hprofile.tendsto_at hcu).eventually
    (lt_mem_nhds (show 1 < cu/kappa from (one_lt_div₀ hkappa).mpr hcumargin))
  have Hx := hxlim.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [Hlo,Hup,Hx] with n hnlo hnup hnx
  have hRx := omittedSweepQuantile_inverse zero_le_one
    ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).data.hc (M n).data.hk
    (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha
    (show x n∈Icc (0:ℝ) 1 from ⟨(hx n).le,hnx.le⟩)
  have Hmono := omittedSweepQuantile_monotone zero_le_one
    ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).data.hc (M n).data.hk
    (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha
  have Hradlo : (M n).R (cl*x n) < x n := by
    simpa only [mul_comm, mul_one] using (div_lt_iff₀ (hx n)).mp hnlo
  have Hradup : x n < (M n).R (cu*x n) := by
    simpa only [mul_comm, mul_one] using (lt_div_iff₀ (hx n)).mp hnup
  constructor
  · by_contra H
    have Hord := Hmono (not_lt.mp H)
    rw [hRx] at Hord
    exact (not_le_of_gt Hradlo) Hord
  · by_contra H
    have Hord := Hmono (not_lt.mp H)
    rw [hRx] at Hord
    exact (not_le_of_gt Hradup) Hord

theorem actual_high_only_successful_child_parent_profile_transfer
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualHighOnlyChildBarrierCall (N n) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧
      (a n).R=(M n).R ∧ (a n).context.s=(M n).context.s)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*
        actualChildErrorBudget (N n) delta c0 (M n).context.d (M n).lam (x n))
    (homission : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    {kappa : ℝ} (hclmargin : cl < kappa) (hcumargin : kappa < cu)
    (hprofile : TendstoLocallyUniformlyOn (fun n v=>(a n).Z (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ))) :
    TendstoLocallyUniformlyOn (fun n v=>(M n).R (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧
      ∀ᶠn in atTop,cl*x n < (M n).alpha.val.val (x n) ∧
        (M n).alpha.val.val (x n) < cu*x n := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have Hagree := actual_high_only_successful_child_two_scale_agreement hm hdelta hcl hcu
    hAz hC0 hc0 N hN M a x hxs hxlim hparent hchild homission hweak
  have Hband left right eps theta (hleft : 0 < left) (hlr : left < right)
      (heps : 0 < eps) (htheta : 0 < theta) :
      ∀ᶠn in atTop,volume (physicalPropagationDisagreementMassSet (M n).R (a n).Z
        (x n*left) (x n*right) (eps*x n)) < ENNReal.ofReal (theta*x n) := by
    have Hright : Tendsto (fun n=>x n*right) atTop (𝓝 0) := by
      simpa using hxlim.mul_const right
    filter_upwards [Hagree 1 left right eps theta zero_lt_one hleft hlr heps htheta,
      Hright.eventually (gt_mem_nhds zero_lt_one)] with n hn hnr
    exact hn (x n) (by simp) hnr.le
  have Hparent := selective_propagation_transfer_working_child_locally_uniform
    (fun n=>(M n).R) (fun n=>(a n).Z) x (inv_pos.mpr hkappa) hx hxlim
    (fun n=>(omittedSweepQuantile_monotone zero_le_one
      ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).data.hc (M n).data.hk
      (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha).monotoneOn _)
    (fun n=>(a n).child_radius_monotone.monotoneOn _)
    (fun v hv=>by simpa only [div_eq_mul_inv,mul_comm] using hprofile.tendsto_at hv) Hband
  have Hparent' : TendstoLocallyUniformlyOn (fun n v=>(M n).R (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_comm] using Hparent
  exact ⟨Hparent',eventually_inverse_test_strict_of_linear_high_only_radius_profile
    M x hx hxlim hcl hclmargin hcumargin Hparent'⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
