module

public import ComparisonActualHighWallThetaZeroSuccessfulHighOnlyProfileIsolatedDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_successful_high_only_same_child_cofinal_profile
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
    (P : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 1 1 T)
    (a : (n:ℕ)→ActualShiftedParentChildCall (dim n+1) delta)
    (hxlim : Tendsto (fun n=>(P n).xs) atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(P n).data.thetaZeroShiftedParentData
      (P n).lam (P n).hlam (P n).hld)
    (hR : ∀n,(a n).R=(P n).data.wallRadius (P n).alpha)
    (hchildD : ∀n,(a n).childRadius=c0*(P n).xs)
    (hchildLam : ∀n,(a n).childLam=(c0*(P n).xs)^2)
    (hchildE : ∀n,(a n).childData.E=actualChildErrorBudget (dim n+1)
      delta c0 (P n).data.d (P n).lam (P n).xs)
    (hsuccess : ∀n,(a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
      actualChildErrorBudget (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale
      (P n).data.N delta (P n).data.E (P n).lam ≤ (P n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d
      (P n).lam (P n).xs/(P n).xs^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(P n).data.s/(P n).xs) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(P n).data.rmin/(P n).xs) atTop (𝓝 0))
    (hsCut : Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0)) :
    ∃sigma : ℕ→ℕ,StrictMono sigma ∧ ∃kappa : ℝ,
      cl < kappa ∧ kappa < cu ∧
      TendstoLocallyUniformlyOn
        (fun n v=>(a (sigma n)).Z ((P (sigma n)).xs*v)/
          (P (sigma n)).xs)
        (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
  classical
  let x := fun n=>(P n).xs
  have hchild : ∀ᶠn in atTop,
      (a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (P n).data.d (P n).lam (x n) :=
    Eventually.of_forall (fun n=>⟨hchildD n,hchildLam n,hsuccess n⟩)
  have hTle : ∀ᶠn in atTop,(P n).data.T≤T :=
    hT.mono (fun _ hn=>hn.le)
  obtain ⟨C,hC,hAzC,HQ⟩ :=
    eventually_exists_theta_zero_successful_high_only_child_minimum
      hm hdelta hcl hcu hAz hC0 hc0 hc01 hmargin
      dim hdim P a x (fun _=>le_rfl) hxlim hcontext hR hchild
      (Eventually.of_forall hchildE) htarget hTle hweak hs hr
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp HQ
  let shift := fun n:ℕ=>n+n0
  have hshift : StrictMono shift := fun i j hij=>Nat.add_lt_add_right hij n0
  have hshiftlim := hshift.tendsto_atTop
  have Htail (n:ℕ) := Hn0 (shift n) (by dsimp [shift]; omega)
  choose Q hQdata hQlam hQopt hQxs hQz hQR using Htail
  let dim1 := fun n=>dim (shift n)
  let P1 := fun n=>P (shift n)
  let a1 := fun n=>a (shift n)
  let x1 := fun n=>x (shift n)
  have hdim1 : Tendsto dim1 atTop atTop := hdim.comp hshiftlim
  have hxlim1 : Tendsto x1 atTop (𝓝 0) := hxlim.comp hshiftlim
  have hQlam1 (n:ℕ) : (Q n).lam=(c0*x1 n)^2 :=
    (hQlam n).trans (hchildLam (shift n))
  have hQd1 (n:ℕ) : (Q n).context.d=c0*x1 n := by
    change (Q n).data.d=_
    rw [hQdata n]
    exact hchildD (shift n)
  have HG := theta_zero_successful_high_only_child_physical_context
    hm hdelta hcl hcu hC0 hc0 hc01 hTpos hC hAzC
    hmargin hcapmargin hgapmargin dim1 hdim1 P1 a1 Q x1
    (fun _=>le_rfl) (fun _=>rfl) hxlim1
    (fun n=>hcontext (shift n)) (fun n=>hR (shift n))
    hQdata (fun n=>hchildD (shift n))
    (fun n=>hchildE (shift n)) hQlam1 hQxs
    (hshiftlim.eventually hT)
    (hxlim1.eventually (eventually_le_nhds zero_lt_one))
    (hshiftlim.eventually htarget) (hweak.comp hshiftlim)
    (hsCut.comp hshiftlim)
  obtain ⟨G⟩ := HG.1
  have hx1 (n:ℕ) : 0 < x1 n := (P1 n).hxs
  obtain ⟨psi,hpsi,kappa,hklo,hkup,Hprofile⟩ :=
    theta_zero_successful_high_only_child_linear_profile_from_context
      hm hdelta hroom (show 0 < cl/4 by positivity)
      (show 0 < 4*cu by positivity)
      (show 0 ≤ 4*C/cl by positivity) hC0 zero_le_one hc0 hc01
      hmargin hcapmargin hgapmargin dim1 hdim1 Q G x1 hx1 hxlim1
      hQxs hQd1 hQlam1
  let sigma := shift ∘ psi
  have hsigma : StrictMono sigma := hshift.comp hpsi
  refine ⟨sigma,hsigma,kappa,hclSlack.trans_le hklo,
    hkup.trans_lt hcuSlack,?_⟩
  simpa only [sigma,Function.comp_apply,hQR,hQxs] using Hprofile

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
