module

public import ComparisonActualHighWallThetaZeroHighOnlyCofinalProfileIsolatedDraft
public import ComparisonActualHighWallThetaZeroWeakHighOnlyTwoScaleIsolated
public import ComparisonActualHighWallThetaZeroLiteralHighOnlyChildCallDraft
public import ComparisonActualHighWallInnovation
public import SelectivePropagationIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal

theorem working_child_profile_transfer_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ → ℕ)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (Z : ℕ → ℝ → ℝ)
    (hZmono : ∀n, MonotoneOn (Z n) (Icc (0:ℝ) 1))
    (hxs0 : Tendsto (fun n => (Q n).xs) atTop (𝓝 0))
    (hr : Tendsto (fun n => (Q n).data.rmin/(Q n).xs) atTop (𝓝 0))
    (hagree : ∀a b eps theta : ℝ, 0<a → a<b → 0<eps → 0<theta →
      ∀ᶠn in atTop,
        volume (physicalPropagationDisagreementMassSet
          ((Q n).data.wallRadius (Q n).alpha) (Z n)
          ((Q n).xs*a) ((Q n).xs*b) (eps*(Q n).xs)) <
          ENNReal.ofReal (theta*(Q n).xs))
    {kappa : ℝ} (hcl : 0 < cl) (hclmargin : cl < kappa)
    (hcumargin : kappa < cu)
    (hchild : TendstoLocallyUniformlyOn
      (fun n v => Z n ((Q n).xs*v)/(Q n).xs)
      (fun v => v/kappa) atTop (Ioi (0:ℝ))) :
    TendstoLocallyUniformlyOn
      (fun n v => (Q n).data.wallRadius (Q n).alpha
        ((Q n).xs*v)/(Q n).xs)
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) ∧
    (∀ᶠn in atTop,
      cl*(Q n).xs < (Q n).alpha.val.val (Q n).xs ∧
        (Q n).alpha.val.val (Q n).xs < cu*(Q n).xs) := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hx (n : ℕ) : 0 < (Q n).xs := (Q n).hxs
  have Hparent := selective_propagation_transfer_working_child_locally_uniform
    (fun n => (Q n).data.wallRadius (Q n).alpha) Z
    (fun n => (Q n).xs) (inv_pos.mpr hkappa) hx hxs0
    (fun n => ((Q n).data.wallRadius_monotone (Q n).alpha).monotoneOn _)
    hZmono
    (fun v hv => by simpa only [div_eq_mul_inv,mul_comm] using hchild.tendsto_at hv)
    hagree
  have Hparent' : TendstoLocallyUniformlyOn
      (fun n v => (Q n).data.wallRadius (Q n).alpha
        ((Q n).xs*v)/(Q n).xs)
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_comm] using Hparent
  have Horigin : ∀ᶠn in atTop, (Q n).data.rmin ≤ (Q n).xs := by
    filter_upwards [hr.eventually (eventually_le_nhds zero_lt_one)] with n hn
    simpa only [one_mul] using (div_le_iff₀ (hx n)).mp hn
  have Hlo := (Hparent'.tendsto_at hcl).eventually
    (gt_mem_nhds (show cl/kappa < 1 from
      (div_lt_one₀ hkappa).mpr hclmargin))
  have Hup := (Hparent'.tendsto_at
      (show cu ∈ Ioi (0:ℝ) from hcl.trans (hclmargin.trans hcumargin))).eventually
    (lt_mem_nhds (show 1 < cu/kappa from
      (one_lt_div₀ hkappa).mpr hcumargin))
  refine ⟨Hparent',?_⟩
  filter_upwards [Hlo,Hup,Horigin,hxs0.eventually
      (eventually_le_nhds zero_lt_one)] with n hnlo hnup hnorigin hunit
  have Hradlo : (Q n).data.wallRadius (Q n).alpha ((Q n).xs*cl) <
      (Q n).xs := by
    simpa only [one_mul] using (div_lt_iff₀ (hx n)).mp hnlo
  have Hradup : (Q n).xs <
      (Q n).data.wallRadius (Q n).alpha ((Q n).xs*cu) := by
    simpa only [one_mul] using (lt_div_iff₀ (hx n)).mp hnup
  have Hinv := (Q n).data.wallRadius_inverse (Q n).alpha
    ⟨hnorigin,hunit⟩
  constructor
  · by_contra H
    have Hmono := (Q n).data.wallRadius_monotone (Q n).alpha
      (show (Q n).alpha.val.val (Q n).xs ≤ (Q n).xs*cl by
        simpa only [mul_comm] using not_lt.mp H)
    rw [Hinv] at Hmono
    exact not_lt_of_ge Hmono Hradlo
  · by_contra H
    have Hmono := (Q n).data.wallRadius_monotone (Q n).alpha
      (show (Q n).xs*cu ≤ (Q n).alpha.val.val (Q n).xs by
        simpa only [mul_comm] using not_lt.mp H)
    rw [Hinv] at Hmono
    exact not_lt_of_ge Hmono Hradup

theorem eventually_first_child_cost_failure_of_agreement_profile_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ → ℕ)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (Z : ℕ → ℝ → ℝ) (pressure budget : ℕ → ℝ)
    (hcl : 0 < cl)
    (hZmono : ∀n, MonotoneOn (Z n) (Icc (0:ℝ) 1))
    (hxs0 : Tendsto (fun n => (Q n).xs) atTop (𝓝 0))
    (hr : Tendsto (fun n => (Q n).data.rmin/(Q n).xs) atTop (𝓝 0))
    (hbad : ∀ᶠn in atTop,
      ¬(cl*(Q n).xs ≤ (Q n).alpha.val.val (Q n).xs ∧
        (Q n).alpha.val.val (Q n).xs ≤ cu*(Q n).xs))
    (hagree : ∀phi : ℕ → ℕ, StrictMono phi →
      (∀n, pressure (phi n) ≤ budget (phi n)) →
      ∀a b eps theta : ℝ, 0<a → a<b → 0<eps → 0<theta →
        ∀ᶠn in atTop,
          volume (physicalPropagationDisagreementMassSet
            ((Q (phi n)).data.wallRadius (Q (phi n)).alpha)
            (Z (phi n)) ((Q (phi n)).xs*a) ((Q (phi n)).xs*b)
            (eps*(Q (phi n)).xs)) <
            ENNReal.ofReal (theta*(Q (phi n)).xs))
    (hprofile : ∀phi : ℕ → ℕ, ∀_hphi : StrictMono phi,
      (∀n, pressure (phi n) ≤ budget (phi n)) →
      ∃psi : ℕ → ℕ, StrictMono psi ∧ ∃kappa : ℝ,
        cl < kappa ∧ kappa < cu ∧
        TendstoLocallyUniformlyOn
          (fun n v => Z (phi (psi n))
            ((Q (phi (psi n))).xs*v)/(Q (phi (psi n))).xs)
          (fun v => v/kappa) atTop (Ioi (0:ℝ))) :
    ∀ᶠn in atTop, budget n < pressure n := by
  classical
  by_contra Hfailure
  have Hfrequent : ∃ᶠn in atTop, pressure n ≤ budget n := by
    simpa only [Filter.Frequently,not_le] using Hfailure
  obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop Hfrequent
  obtain ⟨psi,hpsi,kappa,hklo,hkup,Hlinear⟩ :=
    hprofile phi hphi Hphi
  let sigma := phi ∘ psi
  have hsigma : StrictMono sigma := hphi.comp hpsi
  have Hsuccess (n : ℕ) : pressure (sigma n) ≤ budget (sigma n) :=
    Hphi (psi n)
  have Hagree := hagree sigma hsigma Hsuccess
  have Hparent := working_child_profile_transfer_original_q
    (fun n => dim (sigma n)) (fun n => Q (sigma n))
    (fun n => Z (sigma n)) (fun n => hZmono (sigma n))
    (hxs0.comp hsigma.tendsto_atTop)
    (hr.comp hsigma.tendsto_atTop) Hagree hcl hklo hkup Hlinear
  have Hbad := hsigma.tendsto_atTop.eventually hbad
  obtain ⟨n,hn⟩ := (Hparent.2.and Hbad).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

namespace ActualThetaZeroOverlapMinimum

theorem eventually_high_only_first_child_sharp_failure_original_q
    {m delta cl cu Az C0 T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hTpos : 0 < T) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 1 1 T)
    (hgap : ∀n,∀u∈Ico (0:ℝ) (M n).data.s,
      ((M n).data.thetaZeroShiftedParentData (M n).lam
        (M n).hlam (M n).hld).b u-
      ((M n).data.thetaZeroShiftedParentData (M n).lam
        (M n).hlam (M n).hld).coefficient (M n).alpha u+
        (c0*(M n).xs)^2 ≤
      ((M n).data.thetaZeroShiftedParentData (M n).lam
        (M n).hlam (M n).hld).b (M n).data.s-
      ((M n).data.thetaZeroShiftedParentData (M n).lam
        (M n).hlam (M n).hld).coefficient (M n).alpha (M n).data.s)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hT : ∀ᶠn in atTop,(M n).data.T=T)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale
      (M n).data.N delta (M n).data.E (M n).lam ≤ (M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/(M n).xs) atTop (𝓝 0))
    (hsCut : Tendsto (fun n=>(M n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (M n).data.d (M n).lam (M n).xs) atTop (𝓝 0))
    (hbad : ∀ᶠn in atTop,
      ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    ∀ᶠn in atTop,
      ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).data.d (M n).lam (M n).xs <
      (M n).highOnlyChildSweepCost hc0 (hgap n) := by
  classical
  have Hfactory (n:ℕ) :
      ∃a : ActualShiftedParentChildCall (dim n+1) delta,
        a.context=(M n).data.thetaZeroShiftedParentData
          (M n).lam (M n).hlam (M n).hld ∧
        a.R=(M n).data.wallRadius (M n).alpha ∧
        a.childRadius=c0*(M n).xs ∧
        a.childLam=(c0*(M n).xs)^2 ∧
        a.childData.E=actualChildErrorBudget (dim n+1)
          delta c0 (M n).data.d (M n).lam (M n).xs ∧
        a.err=(M n).highOnlyChildSweepCost hc0 (hgap n) := by
    obtain ⟨a,hctx,_hopt,hRchild,_hdata,hD,hLam,hE,herr⟩ :=
      (M n).exists_literal_high_only_first_child_call hc0 (hgap n)
    exact ⟨a,hctx,hRchild,hD,hLam,hE,herr⟩
  choose a hcontext hR hchildD hchildLam hchildE herr using Hfactory
  let budget := fun n=>((dim n+1:ℕ):ℝ)^(20*delta)*
    actualChildErrorBudget (dim n+1) delta c0
      (M n).data.d (M n).lam (M n).xs
  let pressure := fun n=>(M n).highOnlyChildSweepCost hc0 (hgap n)
  have hZmono (n:ℕ) : MonotoneOn (a n).Z (Icc (0:ℝ) 1) :=
    (a n).child_radius_monotone.monotoneOn _
  have Hagree : ∀phi : ℕ→ℕ,StrictMono phi →
      (∀n,pressure (phi n)≤budget (phi n)) →
      ∀left right eps theta : ℝ,0<left → left<right → 0<eps → 0<theta →
      ∀ᶠn in atTop,
        volume (physicalPropagationDisagreementMassSet
          ((M (phi n)).data.wallRadius (M (phi n)).alpha)
          (a (phi n)).Z ((M (phi n)).xs*left)
          ((M (phi n)).xs*right) (eps*(M (phi n)).xs)) <
          ENNReal.ofReal (theta*(M (phi n)).xs) := by
    intro phi hphi hsuccess left right eps theta hleft hlr heps htheta
    let M0 := fun n=>M (phi n)
    let a0 := fun n=>a (phi n)
    let x0 := fun n=>(M0 n).xs
    have hphiLim := hphi.tendsto_atTop
    have hxlim0 : Tendsto x0 atTop (𝓝 0) := hxlim.comp hphiLim
    have hchild : ∀ᶠn in atTop,
        (a0 n).childRadius=c0*x0 n ∧
        (a0 n).childLam=(c0*x0 n)^2 ∧
        (a0 n).err ≤ ((dim (phi n)+1:ℕ):ℝ)^(20*delta)*
          actualChildErrorBudget (dim (phi n)+1) delta c0
            (M0 n).data.d (M0 n).lam (x0 n) := by
      apply Eventually.of_forall
      intro n
      exact ⟨hchildD (phi n),hchildLam (phi n),
        (herr (phi n)).trans_le (hsuccess n)⟩
    have H := theta_zero_successful_high_only_child_two_scale_agreement
      hm hdelta hcl hcu hAz hC0 hc0
      (fun n=>dim (phi n)) (hdim.comp hphiLim)
      M0 a0 x0 (fun _=>le_rfl) hxlim0
      (fun n=>hcontext (phi n)) (fun n=>hR (phi n))
      hchild (hweak.comp hphiLim) (hs.comp hphiLim)
      (hr.comp hphiLim)
    have hright : 0 < right := hleft.trans hlr
    have Hband := H 1 left right eps theta zero_lt_one hleft hlr heps htheta
    have Hunit := hxlim0.eventually
      (eventually_le_nhds (show (0:ℝ)<1/right by positivity))
    filter_upwards [Hband,Hunit] with n hn hnunit
    exact hn (x0 n) (by simp) ((le_div_iff₀ hright).mp hnunit)
  have Hprofile : ∀phi : ℕ→ℕ,∀hphi : StrictMono phi,
      (∀n,pressure (phi n)≤budget (phi n)) →
      ∃psi : ℕ→ℕ,StrictMono psi ∧ ∃kappa : ℝ,
        cl<kappa ∧ kappa<cu ∧
        TendstoLocallyUniformlyOn
          (fun n v=>(a (phi (psi n))).Z
            ((M (phi (psi n))).xs*v)/(M (phi (psi n))).xs)
          (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
    intro phi hphi hsuccess
    let M0 := fun n=>M (phi n)
    let a0 := fun n=>a (phi n)
    have hphiLim := hphi.tendsto_atTop
    exact theta_zero_successful_high_only_same_child_cofinal_profile
      hm hdelta hroom hcl hcu hAz hC0 hTpos hc0 hc01
      hmargin hcapmargin hgapmargin hclSlack hcuSlack
      (fun n=>dim (phi n)) (hdim.comp hphiLim)
      M0 a0 (hxlim.comp hphiLim)
      (fun n=>hcontext (phi n)) (fun n=>hR (phi n))
      (fun n=>hchildD (phi n)) (fun n=>hchildLam (phi n))
      (fun n=>hchildE (phi n))
      (fun n=>(herr (phi n)).trans_le (hsuccess n))
      (hphiLim.eventually hT) (hphiLim.eventually htarget)
      (hweak.comp hphiLim) (hs.comp hphiLim)
      (hr.comp hphiLim) (hsCut.comp hphiLim)
  have Hfailure :=
    eventually_first_child_cost_failure_of_agreement_profile_original_q
      dim M (fun n=>(a n).Z) pressure budget hcl hZmono
      hxlim hr hbad Hagree Hprofile
  simpa only [pressure,budget] using Hfailure

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
