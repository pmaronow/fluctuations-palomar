module

public import SKProof.OriginalQAllMassZeroMassComparableContext
public import SKProof.OriginalQAllMassSuccessfulZeroMassDirectProfile
public import ComparisonActualHighWallThetaZeroWeakenConstantsIsolatedDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_zero_mass_child_context_profile_join_original_q
    {m delta cl cu Az C0 T c0 C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hTpos : 0 < T)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hC : 1 ≤ C)
    (hAzC : Az ≤ 4*C/cl)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 1 1 T)
    (a : (n : ℕ) → ActualShiftedAllMassParentChildCall (dim n+1) delta)
    (V : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0 1 1 T)
    (hxs0 : Tendsto (fun n => (P n).xs) atTop (𝓝 0))
    (hT : ∀ᶠn in atTop, (P n).data.T = T)
    (hunit : ∀ᶠn in atTop, (P n).xs ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).data.N delta
        (P n).data.E (P n).lam ≤ (P n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (P n).data.d (P n).lam (P n).xs/(P n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (P n).data.s/(P n).xs)
      atTop (𝓝 0))
    (hr : Tendsto (fun n => (P n).data.rmin/(P n).xs)
      atTop (𝓝 0))
    (hsCut : Tendsto (fun n => (P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0))
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
    (hVE : ∀n, (V n).context.E =
      actualChildErrorBudget (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs)
    (hVd : ∀n, (V n).context.d = c0*(P n).xs)
    (hVzero : ∀n, (V n).data.s = 0)
    (hVb : ∀n, (V n).b = (P n).changedBare)
    (hVh : ∀n, (V n).h = (P n).changedField)
    (hV : ∀n, (V n).R = (a n).Z ∧
      (V n).xs = (P n).xs ∧
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
  have hAzChild : 0 ≤ 4*C/cl := by positivity
  have hclWeaken : cl/4 ≤ cl := by linarith only [hcl]
  have hcuWeaken : cu ≤ 4*cu := by linarith only [hcu]
  let PW := fun n => (P n).weakenConstants
    hclWeaken hcuWeaken hAzC le_rfl le_rfl le_rfl
  have hcut : ∀ᶠn in atTop,
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs ≤
      comparisonLowerScale (V n).context.N
        (V n).context.E (V n).context.d := by
    apply Eventually.of_forall
    intro n
    rw [hVE n,hVd n]
    rfl
  have Hcontext :=
    ActualHighOnlyOverlapMinimum.ActualWeakHighOnlyHistoryChain.exists_theta_zero_zero_mass_comparable_context_original_q
      hm hdelta hclChild hAzChild hC0 hc0 hc01 hTpos
      hmargin hcapmargin hgapmargin dim hdim PW V V
      (.root : ActualHighOnlyOverlapMinimum.ActualWeakHighOnlyHistoryChain c0 V V)
      hT (Eventually.of_forall hVzero) hunit htarget hweak hsCut
      hcut (Eventually.of_forall (fun n u => congrFun (hVb n) u))
      (Eventually.of_forall (fun n u => congrFun (hVh n) u))
      (by
        have HVxs : (fun n => (V n).xs) =
            (fun n => (P n).xs) := funext (fun n => (hV n).2.1)
        rw [HVxs]
        exact hxs0)
  obtain ⟨G⟩ := Hcontext
  exact theta_zero_successful_zero_mass_child_parent_direct_profile_original_q
    hm hdelta hroom hcl hcu hAz hC0 hc0 hc01 hC
    hmargin hcapmargin hgapmargin hclmargin hcumargin
    dim hdim P a V G hxs0 hcontext hR hchild hweak hs hr
    (fun n => ⟨(hV n).1,(hV n).2.1,hVd n,(hV n).2.2⟩)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
