module

public import ComparisonActualHighWallFixedWallShrinkingHighOnlyChildFailure
public import ComparisonActualHighWallFixedWallShrinkingAllMassChildFailure
public import ComparisonActualHighWallStrongBadFromPhysicalReaders
public import ComparisonActualHighWallMacroscopicCovarianceUnion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 36000000
namespace ActualHighWallOverlapMinimum

theorem exists_concrete_fixed_wall_first_child_pressure_failure_from_physical_readers
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 c0 : ℝ,
        0 < m → m < 1/300 → 0 < cl → 0 < cu → 0 ≤ Az → 0 < C0 →
        ∀ hc0 : 0 < c0, c0 ≤ 1 → c0^2 < (beta:ℝ)^2/4 →
        cl ≤ lower → upper ≤ cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀ P : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 1 1 ((beta:ℝ)^2),
        (∀ n, (P n).data.T = (beta:ℝ)^2) →
        (∀ᶠ n in atTop, (P n).data.E = wallHighError m (dim n+1)) →
        (∀ᶠ n in atTop, (P n).data.d = wallHighD m (dim n+1)) →
        (∀ᶠ n in atTop, (P n).data.s = wallHighMass m (dim n+1)) →
        (∀ n, (P n).xs ≤ 1) →
        (∀ᶠ n in atTop, (P n).data.d ≤ (P n).xs ∧
          ((P n).alpha.val.val (P n).xs < cl*(P n).xs ∨
            cu*(P n).xs < (P n).alpha.val.val (P n).xs)) →
        ∀ᶠ n in atTop, ((dim n+1:ℕ):ℝ)^(20*(m/10000))*
          actualChildErrorBudget (dim n+1) (m/10000) c0
            (P n).data.d ((P n).data.d^2) (P n).xs <
              (P n).macroFixedMarginChildSweepCost hc0 := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hmacro⟩ :=
    macro_fixed_margin_successful_child_literal_bad_witness_excluded hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 c0 hm hmmax hcl hcu hAz hC0 hc0 hc01 hc0Temp
    hclMacro hcuMacro hclSlack hcuSlack dim hdim P hTeq hE hd hs hunit Htest
  let T : ℝ := (beta:ℝ)^2
  have hTpos : 0 < T := zero_lt_one.trans hTemp
  have hdelta : 0 < m/10000 := by positivity
  have hmsmall : m ≤ (1:ℝ)/120 := by linarith
  have HN : Tendsto (fun n => ((dim n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have HDlim : Tendsto (fun n => (P n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-15*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hd] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighD
    congr 1
    ring
  have HSlim : Tendsto (fun n => (P n).data.s) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-5*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hs] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighMass
    congr 1
    ring
  have HSratio : Tendsto (fun n => (P n).data.s/(P n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ) < 10) hm)).comp HN
    apply H.congr'
    filter_upwards [hs, hd] with n hns hnd
    simp only [Function.comp_apply]
    rw [hns, hnd]
    unfold wallHighMass wallHighD
    rw [←Real.rpow_sub (by positivity : (0:ℝ) < ((dim n+1:ℕ):ℝ))]
    congr 1
    ring
  have Hweak := actual_high_wall_bad_test_strength_tendsto_zero_from_physical_readers
    hm hdelta (by linarith) hcl hcu hAz hC0 zero_lt_one hTpos
    hclSlack hcuSlack dim hdim P hTeq HDlim HSratio Htest
  by_contra Hnone
  have Hfreq : ∃ᶠ n in atTop, (P n).macroFixedMarginChildSweepCost hc0 ≤
      ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (P n).data.d ((P n).data.d^2) (P n).xs := by
    simpa only [Filter.Frequently, not_le] using Hnone
  obtain ⟨phi, hphi, Hphi⟩ := extraction_of_frequently_atTop (Hfreq.and_eventually Htest)
  let dim0 := fun n => dim (phi n)
  let M := fun n => P (phi n)
  have hdim0 : Tendsto dim0 atTop atTop := hdim.comp hphi.tendsto_atTop
  have hdxs (n : ℕ) : (M n).data.d ≤ (M n).xs := (Hphi n).2.1
  have Hbad : ∀ᶠ n in atTop,
      ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs) := by
    apply Eventually.of_forall
    intro n Hband
    rcases (Hphi n).2.2 with Hlo | Hhi
    · exact (not_lt_of_ge Hband.1) Hlo
    · exact (not_lt_of_ge Hband.2) Hhi
  by_cases HX : Tendsto (fun n => (M n).xs) atTop (𝓝 0)
  · by_cases Hlow : ∀ᶠ n in atTop, (M n).data.epsilon < T/4
    · have Hsuccess : ∀ᶠ n in atTop, (M n).macroAllMassChildSweepCost hc0 ≤
          ((dim0 n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
            (dim0 n+1) (m/10000) c0 (M n).data.d ((M n).data.d^2) (M n).xs := by
        filter_upwards [Hlow] with n hn
        have He : (M n).data.epsilon < (M n).data.T/4 := by
          simpa only [M, hTeq] using hn
        have H := (Hphi n).1
        change (M n).macroFixedMarginChildSweepCost hc0 ≤ _ at H
        rw [macroFixedMarginChildSweepCost, ite_eq_left He] at H
        exact H
      have Hfailure := eventually_fixed_wall_shrinking_all_mass_first_child_pressure_failure
        hm hmsmall hcl hcu hAz hC0 hTpos hc0 hc01 hclSlack hcuSlack
        dim0 hdim0 M (Eventually.of_forall (fun n => hTeq (phi n)))
        (hphi.tendsto_atTop.eventually hE) (hphi.tendsto_atTop.eventually hd)
        (hphi.tendsto_atTop.eventually hs) hdxs HX
        (Hweak.comp hphi.tendsto_atTop) (Hlow.mono (fun _ hn => hn.le)) Hbad
      obtain ⟨n, hn⟩ := (Hfailure.and Hsuccess).exists
      exact (not_lt_of_ge hn.2) hn.1
    · have Hhigh : ∃ᶠ n in atTop, T/4 ≤ (M n).data.epsilon := by
        simpa only [Filter.Frequently, not_le] using Hlow
      obtain ⟨psi, hpsi, Hpsi⟩ := extraction_of_frequently_atTop Hhigh
      let sigma := phi ∘ psi
      have hsigma : StrictMono sigma := hphi.comp hpsi
      let dim1 := fun n => dim (sigma n)
      let Q := fun n => P (sigma n)
      have Hsuccess : ∀ᶠ n in atTop, (Q n).macroHighOnlyChildSweepCost hc0 ≤
          ((dim1 n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
            (dim1 n+1) (m/10000) c0 (Q n).data.d ((Q n).data.d^2) (Q n).xs := by
        apply Eventually.of_forall
        intro n
        have He : ¬(Q n).data.epsilon < (Q n).data.T/4 := by
          rw [show (Q n).data.T = T from hTeq (sigma n)]
          exact not_lt_of_ge (Hpsi n)
        have H := (Hphi (psi n)).1
        change (Q n).macroFixedMarginChildSweepCost hc0 ≤ _ at H
        rw [macroFixedMarginChildSweepCost, ite_eq_right He] at H
        exact H
      have Hfailure := eventually_fixed_wall_shrinking_high_only_first_child_pressure_failure
        hm hmsmall hcl hcu hAz hC0 hTpos hc0 hc01 hclSlack hcuSlack
        dim1 (hdim.comp hsigma.tendsto_atTop) Q
        (Eventually.of_forall (fun n => hTeq (sigma n)))
        (hsigma.tendsto_atTop.eventually hE) (hsigma.tendsto_atTop.eventually hd)
        (hsigma.tendsto_atTop.eventually hs) (fun n => hdxs (psi n))
        (HX.comp hpsi.tendsto_atTop) (Hweak.comp hsigma.tendsto_atTop)
        (Eventually.of_forall Hpsi) (hpsi.tendsto_atTop.eventually Hbad)
      obtain ⟨n, hn⟩ := (Hfailure.and Hsuccess).exists
      exact (not_lt_of_ge hn.2) hn.1
  · obtain ⟨xlo, hxlo, psi, hpsi, Hpsi⟩ :=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
        (fun n => (M n).xs) (fun n => (M n).hxs.le) HX
    let sigma := phi ∘ psi
    have hsigma : StrictMono sigma := hphi.comp hpsi
    have Hgood := Hmacro m (m/10000) cl cu Az C0 1 1 T c0
      hm hdelta hC0 hc0 hc0Temp hclMacro hcuMacro
      (fun n => dim (sigma n)) (hdim.comp hsigma.tendsto_atTop)
      (fun n => P (sigma n)) xlo hxlo
      (fun n => ⟨Hpsi n, hunit (sigma n)⟩) (fun n => hTeq (sigma n))
      (HSlim.comp hsigma.tendsto_atTop) (Hweak.comp hsigma.tendsto_atTop)
      (Eventually.of_forall (fun n => (Hphi (psi n)).1))
    obtain ⟨n, hn⟩ := (Hgood.and (hpsi.tendsto_atTop.eventually Hbad)).exists
    exact hn.2 hn.1

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
