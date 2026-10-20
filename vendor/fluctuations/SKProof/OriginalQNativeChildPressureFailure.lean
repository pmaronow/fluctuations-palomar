module

public import SKProof.OriginalQNativeSuccessfulParentProfile
public import ComparisonNativeActualGeneralSuccessfulChildPressure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem eventually_bad_weak_child_pressure_fails_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0)
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
    (G : OriginalQNativeRootHistory M T c0)
    (x : ℕ → ℝ) (hxs : ∀n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta
        (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (M n).context.d (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hroom : ∀ᶠn in atTop,
      (M n).lam+(c0*x n)^2 ≤ (M n).b 0)
    (hbad : ∀ᶠn in atTop,
      ¬(cl*x n ≤ (M n).alpha.val.val (x n) ∧
        (M n).alpha.val.val (x n) ≤ cu*x n)) :
    ∀ᶠn in atTop,
      (M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).context.d (M n).lam (x n) <
        (M n).actualCompensatedChildPressureCost hc0
          ((M n).hxs.trans_le (hxs n)) := by
  classical
  by_contra hnone
  have hfreq : ∃ᶠn in atTop,
      (M n).actualCompensatedChildPressureCost hc0
          ((M n).hxs.trans_le (hxs n)) ≤
      (M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).context.d (M n).lam (x n) := by
    simpa only [Filter.Frequently,not_not,not_le] using hnone
  obtain ⟨theta,htheta,Htheta⟩ := extraction_of_frequently_atTop
    (hfreq.and_eventually hroom)
  have hq : ∀ᶠn in atTop,
      2 ≤ ((dim n+1:ℕ):ℝ)^delta :=
    ((tendsto_rpow_atTop hdelta).comp
      (tendsto_natCast_atTop_atTop.comp
        ((tendsto_add_atTop_nat 1).comp hdim))).eventually
        (eventually_ge_atTop 2)
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp
    (htheta.tendsto_atTop.eventually hq)
  let shift := fun n : ℕ => n+n0
  have hshift : StrictMono shift :=
    fun i j hij => Nat.add_lt_add_right hij n0
  let phi := theta ∘ shift
  have hphi : StrictMono phi := htheta.comp hshift
  have hroom' n : (M (phi n)).lam+(c0*x (phi n))^2 ≤
      (M (phi n)).b 0 := (Htheta (shift n)).2
  have hcost' n :
      (M (phi n)).actualCompensatedChildPressureCost hc0
          ((M (phi n)).hxs.trans_le (hxs (phi n))) ≤
      (M (phi n)).context.N^(20*delta)*
        actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (x (phi n)) :=
    (Htheta (shift n)).1
  choose beta a H using fun n =>
    (M (phi n)).exists_actual_child_attained hc0
      ((M (phi n)).hxs.trans_le (hxs (phi n)))
      (hroom' n) (Hn0 (shift n) (Nat.le_add_left n0 n))
  have hparent n :
      (a n).context.E = (M (phi n)).context.E ∧
      (a n).context.d = (M (phi n)).context.d ∧
      (a n).lam = (M (phi n)).lam ∧
      (a n).R = (M (phi n)).R := by
    rcases H n with
      ⟨hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr,hattained⟩
    refine ⟨?_,?_,hlam,hR⟩ <;> rw [hcontext] <;> rfl
  have hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*x (phi n) ∧
      (a n).childLam = (c0*x (phi n))^2 ∧
      (a n).err ≤ ((dim (phi n)+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (x (phi n)) := by
    apply Eventually.of_forall
    intro n
    rcases H n with
      ⟨hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr,hattained⟩
    refine ⟨hd,hl,?_⟩
    rw [he]
    exact hcost' n
  obtain ⟨sigma,hsigma,Hgood⟩ :=
    exists_successful_child_strict_parent_profile_original_q
      hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01
      hmargin hcapmargin hgapmargin hclmargin hcumargin
      (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n => M (phi n)) (G.comp_original_q phi hphi) a
      (fun n => x (phi n)) (fun n => hxs (phi n))
      (hxlim.comp hphi.tendsto_atTop) hparent hchild
      (hphi.tendsto_atTop.eventually htarget)
      (hweak.comp hphi.tendsto_atTop) hroom'
      beta (fun n => (H n).2.2.2.2.2.2.2.2.1)
      (fun n => (H n).2.2.2.2.2.2.2.2.2.2.2)
  obtain ⟨n,hn⟩ :=
    (Hgood.and ((hphi.comp hsigma).tendsto_atTop.eventually hbad)).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
