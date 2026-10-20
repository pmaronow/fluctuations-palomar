module

public import SKProof.OriginalQWeakExclusionsHigh
public import SKProof.OriginalQLowGapTerminal
public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroWeakLowGapFailure
public import Mathlib.Order.OrderIsoNat

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set Filter Hierarchy
open scoped Topology NNReal
open OriginalQFixedTStoppingDraft

theorem exists_macro_weak_exclusion_low_branch_original_q
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
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
      (∀ n, eta ≤ (Q (phi n)).xs) →
      Tendsto (fun n => laplaceComparisonStrength (Q (phi n)).data.d
        (Q (phi n)).lam (Q (phi n)).xs/(Q (phi n)).xs^2) atTop (𝓝 0) → False := by
  obtain ⟨beta, hbeta, hTemp, rfl⟩ := temperature_root_original_q hT
  obtain ⟨lowerF, upperF, hlowerF, hupperF, Hterminal⟩ :=
    ActualThetaZeroOverlapMinimum.exists_low_gap_first_root_finite_contradiction_original_q
      hbeta hTemp
  obtain ⟨lowerM, upperM, hlowerM, hupperM, Hmacro⟩ :=
    ActualThetaZeroOverlapMinimum.theta_zero_macro_weak_low_gap_bad_forces_sharp_all_mass_failure
      hbeta hTemp
  have hTpos : 0 < (beta : ℝ)^2 := zero_lt_one.trans hTemp
  obtain ⟨c0, hc0, hc01, hc0T, hbudget⟩ :=
    exists_uniform_large_epsilon_high_only_radius ((beta : ℝ)^2) (m/10000) hTpos
  have hbudgetLow :
      (((actualPropagationDepth (m/10000) : ℕ) : ℝ)+2)*c0^2 ≤ (beta : ℝ)^2/2 :=
    hbudget.trans (by linarith only [hTpos])
  refine ⟨min lowerF lowerM, max upperF upperM, lt_min hlowerF hlowerM,
    hupperF.trans_le (le_max_left _ _), ?_⟩
  intro cl cu hcl hclBound hcuBound hclTemp hcuTemp dim hdim Q hQ heps
    eta heta phi hphi hxs hweak
  have hclF : cl ≤ lowerF := hclBound.trans (min_le_left _ _)
  have hcuF : upperF ≤ cu := (le_max_left _ _).trans hcuBound
  have hclM : cl ≤ lowerM := hclBound.trans (min_le_right _ _)
  have hcuM : upperM ≤ cu := (le_max_right _ _).trans hcuBound
  have hcu : 0 < cu := hupperF.trans_le hcuF
  let dim1 : ℕ → ℕ := fun n => dim (phi n)
  let M := fun n => Q (phi n)
  have hdim1 : Tendsto dim1 atTop atTop := hdim.tendsto_atTop.comp hphi.tendsto_atTop
  have hM : ∀ n, RetainedBadQ ((beta : ℝ)^2) (dim1 n) (M n) := fun n => hQ (phi n)
  have hTfix : ∀ n, (M n).data.T = (beta : ℝ)^2 := fun n => (hM n).1
  have hE := Eventually.of_forall (f := atTop) (fun n => (hM n).2.1)
  have hd := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.1)
  have hs := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.1)
  have htarget := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.2.2.2.2.2.1)
  have hxsBand : ∀ n, (M n).xs ∈ Icc eta 1 :=
    fun n => ⟨hxs n, (hM n).2.2.2.2.2.2.2.2.2.1⟩
  have heps1 := Eventually.of_forall (f := atTop) (fun n => heps (phi n))
  have hs0 := (concrete_limits_original_q hm hmmax zero_lt_one hdim1 M hE hd hs).1
  have hsCut := child_cutoff_ratio_original_q hm hmmax zero_lt_one hdim1 M
    hc0 htarget hweak hE hd hs
  have hcost := Hmacro m (m/10000) cl cu 2 1 1 1 ((beta : ℝ)^2) c0
    hm (show 0 < m/10000 by positivity) zero_lt_one hc0 hc0T hclM hcuM
    dim1 hdim1 M eta heta hxsBand hTfix hs0 hweak heps1
    (fun n => (hM n).2.2.2.2.2.2.2.2.2.2)
  exact Hterminal m cl cu c0 hm hmmax hcl hcu hclF hcuF hclTemp hcuTemp
    hc0 hc01 hc0T hbudgetLow dim1 hdim1 M (Eventually.of_forall hTfix)
    (Eventually.of_forall (fun n => (hxsBand n).2)) htarget hweak hs0 hsCut heps1 hcost

theorem exists_macro_weak_exclusion_original_q
    {T m : ℝ} (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ cl cu : ℝ, 0 < cl → cl ≤ lower → upper ≤ cu →
      cl < T*Real.exp (-12*T) →
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu →
      ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
        (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 1 1 1 T),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
      (∀ n, eta ≤ (Q (phi n)).xs) →
      Tendsto (fun n => laplaceComparisonStrength (Q (phi n)).data.d
        (Q (phi n)).lam (Q (phi n)).xs/(Q (phi n)).xs^2) atTop (𝓝 0) → False := by
  obtain ⟨lowerH, upperH, hlowerH, hupperH, Hhigh⟩ :=
    exists_macro_weak_exclusion_high_branch_original_q hT hm hmmax
  obtain ⟨lowerL, upperL, hlowerL, hupperL, Hlow⟩ :=
    exists_macro_weak_exclusion_low_branch_original_q hT hm hmmax
  refine ⟨min lowerH lowerL, max upperH upperL, lt_min hlowerH hlowerL,
    hupperH.trans_le (le_max_left _ _), ?_⟩
  intro cl cu hcl hclBound hcuBound hclTemp hcuTemp dim hdim Q hQ
    eta heta phi hphi hxs hweak
  have hclH : cl ≤ lowerH := hclBound.trans (min_le_left _ _)
  have hcuH : upperH ≤ cu := (le_max_left _ _).trans hcuBound
  have hclL : cl ≤ lowerL := hclBound.trans (min_le_right _ _)
  have hcuL : upperL ≤ cu := (le_max_right _ _).trans hcuBound
  obtain ⟨psi, hbranch⟩ := Nat.exists_subseq_of_forall_mem_union
    (s := Ici (T/4)) (t := Iic (T/4))
    (fun n => (Q (phi n)).data.epsilon)
    (fun n => le_total (T/4) (Q (phi n)).data.epsilon)
  let sigma : ℕ → ℕ := fun n => phi (psi n)
  have hsigma : StrictMono sigma := hphi.comp psi.strictMono
  let dim1 : ℕ → ℕ := fun n => dim (sigma n)
  let M := fun n => Q (sigma n)
  have hdim1 : StrictMono dim1 := hdim.comp hsigma
  have hM : ∀ n, RetainedBadQ T (dim1 n) (M n) := fun n => hQ (sigma n)
  have hxs1 : ∀ n, eta ≤ (M n).xs := fun n => hxs (psi n)
  have hweak1 : Tendsto (fun n => laplaceComparisonStrength (M n).data.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) :=
    hweak.comp psi.strictMono.tendsto_atTop
  rcases hbranch with heps | heps
  · exact Hhigh cl cu hcl hclH hcuH hclTemp hcuTemp dim1 hdim1 M hM heps
      eta heta id strictMono_id hxs1 hweak1
  · exact Hlow cl cu hcl hclL hcuL hclTemp hcuTemp dim1 hdim1 M hM heps
      eta heta id strictMono_id hxs1 hweak1

end OAI.SKFluctuations.LaplaceWindowFormalization
