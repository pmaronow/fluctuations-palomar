module

public import SKProof.OriginalQAllMassSuccessfulZeroMassChildMinimum
public import ComparisonActualHighOnlySuccessfulChildDirectProfile
public import SKProof.OriginalQWeakHighOnlyFirstChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_successful_zero_mass_child_parent_direct_profile_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hC : 1 ≤ C)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → ActualShiftedAllMassParentChildCall (dim n+1) delta)
    (V : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0 1 1 T)
    (G : ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext V T)
    (hxs0 : Tendsto (fun n => (P n).xs) atTop (𝓝 0))
    (hcontext : ∀n, (a n).context =
      (P n).data.thetaZeroShiftedParentData
        (P n).lam (P n).hlam (P n).hld)
    (hR : ∀n, (a n).R = (P n).data.wallRadius (P n).alpha)
    (hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*(P n).xs ∧
      (a n).childLam = (c0*(P n).xs)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (P n).data.d (P n).lam (P n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (P n).data.d (P n).lam (P n).xs/(P n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (P n).data.s/(P n).xs)
      atTop (𝓝 0))
    (hr : Tendsto (fun n => (P n).data.rmin/(P n).xs)
      atTop (𝓝 0))
    (hV : ∀n, (V n).R = (a n).Z ∧
      (V n).xs = (P n).xs ∧
      (V n).context.d = c0*(P n).xs ∧
      (V n).lam = (c0*(P n).xs)^2) :
    ∃phi : ℕ → ℕ, StrictMono phi ∧ ∃kappa : ℝ,
      cl < kappa ∧ kappa < cu ∧
      TendstoLocallyUniformlyOn
        (fun n v => (P (phi n)).data.wallRadius (P (phi n)).alpha
          ((P (phi n)).xs*v)/(P (phi n)).xs)
        (fun v => v/kappa) atTop (Ioi (0:ℝ)) ∧
      (∀ᶠn in atTop,
        cl*(P (phi n)).xs <
          (P (phi n)).alpha.val.val (P (phi n)).xs ∧
        (P (phi n)).alpha.val.val (P (phi n)).xs <
          cu*(P (phi n)).xs) := by
  have hclChild : 0 < cl/4 := by positivity
  have hcuChild : 0 < 4*cu := by positivity
  have hAzChild : 0 ≤ 4*C/cl := by positivity
  have hx n : 0 < (P n).xs := (P n).hxs
  obtain ⟨phi,hphi,kappa,Hklo,Hkup,Hlinear⟩ :=
    ActualHighOnlyOverlapMinimum.exists_full_strength_successful_child_linear_profile
      hm hdelta hroom hclChild hcuChild hAzChild hC0 zero_le_one
      hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim V G (fun n => (P n).xs) hx hxs0
      (fun n => (hV n).2.1) (fun n => (hV n).2.2.1)
      (fun n => (hV n).2.2.2)
  have hklo : cl < kappa := hclmargin.trans_le Hklo
  have hkup : kappa < cu := Hkup.trans_lt hcumargin
  have heq (n : ℕ) : (V n).R = (a n).Z := (hV n).1
  have HZ : TendstoLocallyUniformlyOn
      (fun n v => (a (phi n)).Z
        ((P (phi n)).xs*v)/(P (phi n)).xs)
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [heq] using Hlinear
  have Hagree := theta_zero_successful_all_mass_child_two_scale_agreement_original_q
    hm hdelta hcl hcu hAz hC0 hc0
    (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n => P (phi n)) (fun n => a (phi n))
    (fun n => (P (phi n)).xs) (fun _ => le_rfl)
    (hxs0.comp hphi.tendsto_atTop)
    (fun n => hcontext (phi n)) (fun n => hR (phi n))
    (hphi.tendsto_atTop.eventually hchild)
    (hweak.comp hphi.tendsto_atTop)
    (hs.comp hphi.tendsto_atTop)
    (hr.comp hphi.tendsto_atTop)
  have Hmono n : MonotoneOn (a (phi n)).Z (Icc (0:ℝ) 1) :=
    (a (phi n)).child_radius_monotone.monotoneOn _
  have HagreeBand : ∀left right eps theta : ℝ,
      0<left → left<right → 0<eps → 0<theta →
      ∀ᶠn in atTop,
        volume (physicalPropagationDisagreementMassSet
          ((P (phi n)).data.wallRadius (P (phi n)).alpha)
          (a (phi n)).Z ((P (phi n)).xs*left)
          ((P (phi n)).xs*right) (eps*(P (phi n)).xs)) <
          ENNReal.ofReal (theta*(P (phi n)).xs) := by
    intro left right eps theta hleft hlr heps htheta
    have Hraw := Hagree 1 left right eps theta zero_lt_one
      hleft hlr heps htheta
    have Hlimit : Tendsto (fun n => right*(P (phi n)).xs) atTop (𝓝 0) := by
      simpa only [mul_zero,Function.comp_def] using
        (hxs0.comp hphi.tendsto_atTop).const_mul right
    have Hunit := Hlimit.eventually
      (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [Hraw,Hunit] with n hn hnunit
    have H := hn (P (phi n)).xs (by simp)
      (by simpa only [mul_comm] using hnunit)
    simpa only [one_mul] using H
  have Hparent := working_child_profile_transfer_original_q
    (fun n => dim (phi n)) (fun n => P (phi n))
    (fun n => (a (phi n)).Z) Hmono
    (hxs0.comp hphi.tendsto_atTop)
    (hr.comp hphi.tendsto_atTop)
    HagreeBand hcl hklo hkup HZ
  exact ⟨phi,hphi,kappa,hklo,hkup,Hparent.1,Hparent.2⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
