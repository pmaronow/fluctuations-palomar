module

public import ComparisonActualHighWallSuccessfulChildDirectProfileFromContext
public import ComparisonActualHighWallSuccessfulHighOnlyChildContextCompatible
public import ComparisonActualHighWallOriginsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 28000000
namespace ActualHighWallOverlapMinimum

theorem eventually_fixed_wall_shrinking_high_only_first_child_pressure_failure
    {m cl cu Az C0 T c0 : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hTpos : 0 < T) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 1 1 T)
    (hT : ∀ᶠ n in atTop, (P n).data.T = T)
    (hE : ∀ᶠ n in atTop, (P n).data.E = wallHighError m (dim n+1))
    (hd : ∀ᶠ n in atTop, (P n).data.d = wallHighD m (dim n+1))
    (hs : ∀ᶠ n in atTop, (P n).data.s = wallHighMass m (dim n+1))
    (hdxs : ∀ n, (P n).data.d ≤ (P n).xs)
    (hxlim : Tendsto (fun n => (P n).xs) atTop (𝓝 0))
    (hweak : Tendsto (fun n => (P n).data.g (P n).xs/(P n).xs^2)
      atTop (𝓝 0))
    (heps : ∀ᶠ n in atTop, T/4 ≤ (P n).data.epsilon)
    (Hbad : ∀ᶠ n in atTop,
      ¬(cl*(P n).xs ≤ (P n).alpha.val.val (P n).xs ∧
        (P n).alpha.val.val (P n).xs ≤ cu*(P n).xs)) :
    ∀ᶠ n in atTop, ((dim n+1:ℕ):ℝ)^(20*(m/10000))*
      actualChildErrorBudget (dim n+1) (m/10000) c0
        (P n).data.d ((P n).data.d^2) (P n).xs <
          (P n).macroHighOnlyChildSweepCost hc0 := by
  classical
  have hdelta : 0 < m/10000 := by positivity
  have Hs := concrete_omission_over_larger_scale_tendsto_zero
    hm dim hdim P hE hd hs (fun n => (P n).xs) (fun _ => le_rfl)
  have Hr := rmin_over_larger_scale_tendsto_zero
    hdelta dim hdim P (fun n => (P n).xs) hdxs
  have Htarget : ∀ᶠ n in atTop, comparisonConditionalScale (P n).data.N (m/10000)
      (P n).data.E ((P n).data.d^2) ≤ (P n).xs := by
    filter_upwards [hE, hd] with n hnE hnd
    have H := concrete_wall_conditional_scale_le_d hm.le (P n).data.hn
    rw [←hnE, ←hnd] at H
    exact H.trans (hdxs n)
  have Hdlim : Tendsto (fun n => (P n).data.d) atTop (𝓝 0) :=
    squeeze_zero (fun n => (P n).data.hd.le) hdxs hxlim
  have Hsum : Tendsto (fun n => (P n).data.d^2+(c0*(P n).xs)^2)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero] using
      (Hdlim.pow 2).add ((hxlim.const_mul c0).pow 2)
  have Hreserve : ∀ᶠ n in atTop,
      (P n).data.d^2+(c0*(P n).xs)^2 ≤ (P n).data.epsilon := by
    filter_upwards [Hsum.eventually (eventually_le_nhds (by positivity : (0:ℝ) < T/4)), heps]
      with n hn he
    exact hn.trans he
  by_contra Hnone
  have Hfreq : ∃ᶠ n in atTop, (P n).macroHighOnlyChildSweepCost hc0 ≤
      ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (P n).data.d ((P n).data.d^2) (P n).xs := by
    simpa only [Filter.Frequently, not_le] using Hnone
  obtain ⟨phi, hphi, Hphi⟩ := extraction_of_frequently_atTop
    (Hfreq.and_eventually Hreserve)
  let dim0 := fun n => dim (phi n)
  let M := fun n => P (phi n)
  let x := fun n => (M n).xs
  have hdim0 : Tendsto dim0 atTop atTop := hdim.comp hphi.tendsto_atTop
  have hxlim0 : Tendsto x atTop (𝓝 0) := hxlim.comp hphi.tendsto_atTop
  have hreserve (n : ℕ) : (M n).data.d^2+(c0*x n)^2 ≤ (M n).data.epsilon :=
    (Hphi n).2
  choose a ha using fun n =>
    (M n).exists_attained_high_only_child_at_test hc0 (M n).hxs (hreserve n)
  have hcontext (n : ℕ) : (a n).context = (M n).data.shiftedParentData := (ha n).1
  have hR (n : ℕ) : (a n).R = (M n).data.wallRadius (M n).alpha := (ha n).2.2.1
  have hdata (n : ℕ) : (a n).childData = (M n).actualHighOnlyChild
      hc0 (M n).hxs (hreserve n) := (ha n).2.2.2.1
  have hchildD (n : ℕ) : (a n).childRadius = c0*x n := by
    rcases ha n with ⟨_, _, _, _, hD, _, _, _, _, _, _⟩
    exact hD
  have hchildLam (n : ℕ) : (a n).childLam = (c0*x n)^2 := by
    rcases ha n with ⟨_, _, _, _, _, hL, _, _, _, _, _⟩
    exact hL
  have hchildE (n : ℕ) : (a n).childData.E = actualChildErrorBudget
      (dim0 n+1) (m/10000) c0 (M n).data.d ((M n).data.d^2) (x n) := by
    rcases ha n with ⟨_, _, _, _, _, _, hEc, _, _, _, _⟩
    exact hEc
  have hchild : ∀ᶠ n in atTop, (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧ (a n).err ≤
        ((dim0 n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
          (dim0 n+1) (m/10000) c0 (M n).data.d ((M n).data.d^2) (x n) := by
    apply Eventually.of_forall
    intro n
    rcases ha n with ⟨_, _, _, _, _, _, _, _, _, _, herr⟩
    refine ⟨hchildD n, hchildLam n, ?_⟩
    rw [herr]
    exact (Hphi n).1
  obtain ⟨C, hC, hAzC, HQ⟩ := eventually_exists_successful_high_only_child_minimum
    hm hdelta hcl hcu hAz hC0 hc0 hc01 (by linarith)
    dim0 hdim0 M a x (fun _ => le_rfl) hxlim0 hcontext hR hchild
    (Eventually.of_forall hchildE) (hphi.tendsto_atTop.eventually Htarget)
    ((hphi.tendsto_atTop.eventually hT).mono (fun _ hn => hn.le))
    (hweak.comp hphi.tendsto_atTop) (Hs.comp hphi.tendsto_atTop)
    (Hr.comp hphi.tendsto_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp HQ
  let shift := fun n : ℕ => n+N
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij N
  have Htail (n : ℕ) := hN (shift n) (by dsimp [shift]; omega)
  choose Q hQdata hQlam hQopt hQxs hQz hQR using Htail
  let dim1 := fun n => dim0 (shift n)
  let M1 := fun n => M (shift n)
  let a1 := fun n => a (shift n)
  let x1 := fun n => x (shift n)
  have hdim1 : Tendsto dim1 atTop atTop := hdim0.comp hshift.tendsto_atTop
  have hxlim1 : Tendsto x1 atTop (𝓝 0) := hxlim0.comp hshift.tendsto_atTop
  have hdata1 (n : ℕ) : (Q n).data = (M1 n).actualHighOnlyChild
      hc0 (M1 n).hxs (hreserve (shift n)) := (hQdata n).trans (hdata (shift n))
  have hlam1 (n : ℕ) : (Q n).lam = (c0*x1 n)^2 :=
    (hQlam n).trans (hchildLam (shift n))
  have hd1 (n : ℕ) : (Q n).context.d = c0*x1 n := by
    change (Q n).data.d = _
    rw [hdata1 n]
    rfl
  have Htemp1 := hshift.tendsto_atTop.eventually (hphi.tendsto_atTop.eventually hT)
  have HE1 := hshift.tendsto_atTop.eventually (hphi.tendsto_atTop.eventually hE)
  have HD1 := hshift.tendsto_atTop.eventually (hphi.tendsto_atTop.eventually hd)
  have HS1 := hshift.tendsto_atTop.eventually (hphi.tendsto_atTop.eventually hs)
  have Htarget1 := hshift.tendsto_atTop.eventually (hphi.tendsto_atTop.eventually Htarget)
  have Hweak1 := (hweak.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop
  have HG := successful_high_only_child_physical_context_compatible
    hm hmsmall hcl hcu hC0 hc0 hc01 hTpos hC hAzC dim1 hdim1 M1 x1
    (fun _ => le_rfl) hxlim1 (fun n => hreserve (shift n)) Q hdata1 hlam1 hQxs
    Htemp1 HE1 HD1 HS1 (hxlim1.eventually (eventually_le_nhds zero_lt_one))
    Htarget1 Hweak1
  obtain ⟨G⟩ := HG.1
  have Hjoin (n : ℕ) : (Q n).R = (a1 n).Z ∧ (Q n).xs = x1 n ∧
      (Q n).context.d = c0*x1 n ∧ (Q n).lam = (c0*x1 n)^2 :=
    ⟨hQR n, hQxs n, hd1 n, hlam1 n⟩
  obtain ⟨psi, hpsi, kappa, hklo, hkup, Hprofile, Hstrict⟩ :=
    successful_high_only_child_parent_direct_profile_from_context
      hm hdelta (by linarith) hcl hcu hAz hC0 hc0 hc01 hC zero_le_one
      (by linarith) (by linarith) (by linarith) hclSlack hcuSlack
      dim1 hdim1 M1 a1 Q G x1 (fun _ => le_rfl) hxlim1
      (fun n => hcontext (shift n)) (fun n => hR (shift n))
      (hshift.tendsto_atTop.eventually hchild) Hweak1
      ((Hs.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop)
      ((Hr.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop) Hjoin
  have Hbad1 := hpsi.tendsto_atTop.eventually
    (hshift.tendsto_atTop.eventually (hphi.tendsto_atTop.eventually Hbad))
  obtain ⟨n, hn⟩ := (Hstrict.and Hbad1).exists
  exact hn.2 ⟨hn.1.1.le, hn.1.2.le⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
