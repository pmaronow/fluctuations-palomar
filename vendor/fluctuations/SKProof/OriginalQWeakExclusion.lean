module

public import SKProof.OriginalQWeakExclusionsHigh
public import SKProof.OriginalQLowGapTerminal
public import SKProof.OriginalQWeakAllMassFailure
public import Mathlib.Order.OrderIsoNat

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set Filter Hierarchy
open scoped Topology NNReal
open OriginalQFixedTStoppingDraft

theorem exists_weak_exclusion_low_branch_original_q
    {T m : ℝ} (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ cl cu : ℝ, 0 < cl → cl ≤ lower → upper ≤ cu →
      cl < T*Real.exp (-12*T) →
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu →
      ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
        (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 1 1 1 T),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      (∀ n, (Q n).data.epsilon ≤ T/4) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0) → False := by
  obtain ⟨beta, hbeta, hTemp, rfl⟩ := temperature_root_original_q hT
  obtain ⟨lower, upper, hlower, hupper, Hterminal⟩ :=
    ActualThetaZeroOverlapMinimum.exists_low_gap_first_root_finite_contradiction_original_q
      hbeta hTemp
  have hTpos : 0 < (beta : ℝ)^2 := zero_lt_one.trans hTemp
  obtain ⟨c0, hc0, hc01, hc0T, hbudget⟩ :=
    exists_uniform_large_epsilon_high_only_radius ((beta : ℝ)^2) (m/10000) hTpos
  have hbudgetLow :
      (((actualPropagationDepth (m/10000) : ℕ) : ℝ)+2)*c0^2 ≤ (beta : ℝ)^2/2 :=
    hbudget.trans (by linarith only [hTpos])
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro cl cu hcl hclBound hcuBound hclTemp hcuTemp dim hdim Q hQ heps hxs0 hweak
  have hcu : 0 < cu := hupper.trans_le hcuBound
  have hWallT := Eventually.of_forall (f := atTop) (fun n => (hQ n).1)
  have hE := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.1)
  have hd := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.2.1)
  have hs := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.2.2.1)
  have htarget := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.2.2.2.2.2.2.2.1)
  have hunit := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.2.2.2.2.2.2.2.2.1)
  have heps1 := Eventually.of_forall (f := atTop) heps
  obtain ⟨hs0, _hd0, _hsLower, hsTest, hrTest⟩ :=
    concrete_limits_original_q hm hmmax zero_lt_one hdim.tendsto_atTop Q hE hd hs
  have hsCut := child_cutoff_ratio_original_q hm hmmax zero_lt_one hdim.tendsto_atTop Q
    hc0 htarget hweak hE hd hs
  have hbad : ∀ᶠ n in atTop,
      ¬(cl*(Q n).xs ≤ (Q n).alpha.val.val (Q n).xs ∧
        (Q n).alpha.val.val (Q n).xs ≤ cu*(Q n).xs) := by
    apply Eventually.of_forall
    intro n hn
    rcases (hQ n).2.2.2.2.2.2.2.2.2.2 with hlo | hhi
    · exact (not_lt_of_ge hn.1) hlo
    · exact (not_lt_of_ge hn.2) hhi
  have hclSlack : cl < 2*(beta : ℝ)^2*Real.exp (-12*(beta : ℝ)^2) := by
    have hp : 0 < (beta : ℝ)^2*Real.exp (-12*(beta : ℝ)^2) :=
      mul_pos hTpos (Real.exp_pos _)
    linarith only [hclTemp, hp]
  have hcost :=
    ActualThetaZeroOverlapMinimum.eventually_weak_shrinking_all_mass_first_child_failure_original_q
      hm (show 0 < m/10000 by positivity) (by linarith : m/10000 < 3*m)
      hcl hcu (by norm_num : (0 : ℝ) ≤ 2) zero_lt_one hTpos hc0 hc01
      (by linarith : (m/10000)/4 < 3*m-99*(m/10000))
      (by linarith : 100*(m/10000) < (1 : ℝ)/3+m)
      (by linarith : 0 < 9*m-298*(m/10000)) hclSlack hcuTemp
      dim hdim.tendsto_atTop Q hWallT heps1 hunit htarget hxs0 hweak hsTest hrTest hsCut hbad
  exact Hterminal m cl cu c0 hm hmmax hcl hcu hclBound hcuBound hclTemp hcuTemp
    hc0 hc01 hc0T hbudgetLow dim hdim.tendsto_atTop Q
    hWallT hunit htarget hweak hs0 hsCut heps1 hcost

theorem exists_weak_exclusion_original_q
    {T m : ℝ} (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ cl cu : ℝ, 0 < cl → cl ≤ lower → upper ≤ cu →
      cl < T*Real.exp (-12*T) →
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu →
      ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
        (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 1 1 1 T),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0) → False := by
  obtain ⟨lowerH, upperH, hlowerH, hupperH, Hhigh⟩ :=
    exists_weak_exclusion_high_branch_original_q hT hm hmmax
  obtain ⟨lowerL, upperL, hlowerL, hupperL, Hlow⟩ :=
    exists_weak_exclusion_low_branch_original_q hT hm hmmax
  refine ⟨min lowerH lowerL, max upperH upperL, lt_min hlowerH hlowerL,
    hupperH.trans_le (le_max_left _ _), ?_⟩
  intro cl cu hcl hclBound hcuBound hclTemp hcuTemp dim hdim Q hQ hxs0 hweak
  have hclH : cl ≤ lowerH := hclBound.trans (min_le_left _ _)
  have hcuH : upperH ≤ cu := (le_max_left _ _).trans hcuBound
  have hclL : cl ≤ lowerL := hclBound.trans (min_le_right _ _)
  have hcuL : upperL ≤ cu := (le_max_right _ _).trans hcuBound
  obtain ⟨phi, hbranch⟩ := Nat.exists_subseq_of_forall_mem_union
    (s := Ici (T/4)) (t := Iic (T/4))
    (fun n => (Q n).data.epsilon)
    (fun n => le_total (T/4) (Q n).data.epsilon)
  let dim1 : ℕ → ℕ := fun n => dim (phi n)
  let M := fun n => Q (phi n)
  have hdim1 : StrictMono dim1 := hdim.comp phi.strictMono
  have hM : ∀ n, RetainedBadQ T (dim1 n) (M n) := fun n => hQ (phi n)
  have hxs1 : Tendsto (fun n => (M n).xs) atTop (𝓝 0) :=
    hxs0.comp phi.strictMono.tendsto_atTop
  have hweak1 : Tendsto (fun n => laplaceComparisonStrength (M n).data.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) :=
    hweak.comp phi.strictMono.tendsto_atTop
  rcases hbranch with heps | heps
  · exact Hhigh cl cu hcl hclH hcuH hclTemp hcuTemp dim1 hdim1 M hM heps hxs1 hweak1
  · exact Hlow cl cu hcl hclL hcuL hclTemp hcuTemp dim1 hdim1 M hM heps hxs1 hweak1

end OAI.SKFluctuations.LaplaceWindowFormalization
