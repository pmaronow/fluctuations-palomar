module

public import SKProof.OriginalQWeakLimits
public import SKProof.OriginalQWeakHighOnlyFirstChild
public import SKProof.OriginalQHighGapTerminal
public import SKProof.OriginalQMacroHighGap
public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroWeakHighGapFailure
public import ComparisonActualHighWallLargeEpsilonHighOnlyJoin
public import ComparisonActualHighWallThetaZeroFixedTStoppingCarrierDraft

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set Filter Hierarchy
open scoped Topology NNReal
open OriginalQFixedTStoppingDraft

private theorem retained_high_tail_original_q
    {T m cl cu c0 : ℝ} (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1/300)
    (hc0 : 0 < c0) (hc0T : c0^2 < T/4)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m (m/10000) cl cu 2 1 1 1 T)
    (hQ : ∀ n, RetainedBadQ T (dim n) (Q n))
    (hweak : Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
      (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0))
    (heps : ∀ n, T/4 ≤ (Q n).data.epsilon) :
    ∃ N : ℕ,
      (∀ n, (Q (n+N)).data.d^2 ≤ T/8) ∧
      (∀ n, ∀ u ∈ Ico (0 : ℝ) (Q (n+N)).data.s,
        (Q (n+N)).changedBare u + (c0*(Q (n+N)).xs)^2 ≤
          (Q (n+N)).changedBare (Q (n+N)).data.s) := by
  have hE := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.1)
  have hd := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.2.1)
  have hs := Eventually.of_forall (f := atTop) (fun n => (hQ n).2.2.2.1)
  have hd0 := (concrete_limits_original_q hm hmmax zero_lt_one hdim Q hE hd hs).2.1
  have hdSq : Tendsto (fun n => (Q n).data.d^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hd0.pow 2
  obtain ⟨k, hk⟩ := eventually_atTop.mp
    (hdSq.eventually (eventually_le_nhds (show (0 : ℝ) < T/8 by positivity)))
  let shift : ℕ → ℕ := fun n => n+k
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij k
  obtain ⟨l, hl⟩ := eventually_original_q_macro_high_gap hc0 hc0T
    (fun n => Q (shift n))
    (fun n => (hQ (shift n)).2.2.2.2.2.2.2.2.2.1)
    (hweak.comp hshift.tendsto_atTop)
    (Eventually.of_forall (fun n => heps (shift n)))
  refine ⟨l+k, ?_, ?_⟩
  · intro n
    exact hk (n+(l+k)) (by omega)
  · intro n
    rw [← Nat.add_assoc]
    exact hl n

theorem exists_weak_exclusion_high_branch_original_q
    {T m : ℝ} (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ cl cu : ℝ, 0 < cl → cl ≤ lower → upper ≤ cu →
      cl < T*Real.exp (-12*T) →
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu →
      ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
        (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 1 1 1 T),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      (∀ n, T/4 ≤ (Q n).data.epsilon) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0) → False := by
  obtain ⟨beta, hbeta, hTemp, rfl⟩ := temperature_root_original_q hT
  obtain ⟨lower, upper, hlower, hupper, Hterminal⟩ :=
    ActualThetaZeroOverlapMinimum.exists_high_gap_first_root_finite_contradiction_original_q
      hbeta hTemp
  have hTpos : 0 < (beta : ℝ)^2 := zero_lt_one.trans hTemp
  obtain ⟨c0, hc0, hc01, hc0T, hbudget⟩ :=
    exists_uniform_large_epsilon_high_only_radius ((beta : ℝ)^2) (m/10000) hTpos
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro cl cu hcl hclBound hcuBound hclTemp hcuTemp dim hdim Q hQ heps hxs0 hweak
  have hcu : 0 < cu := hupper.trans_le hcuBound
  obtain ⟨N, hdSmall, hgap⟩ := retained_high_tail_original_q
    hTpos hm hmmax hc0 hc0T dim hdim.tendsto_atTop Q hQ hweak heps
  let shift : ℕ → ℕ := fun n => n+N
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij N
  let dim1 : ℕ → ℕ := fun n => dim (shift n)
  let M := fun n => Q (shift n)
  have hdim1 : Tendsto dim1 atTop atTop := hdim.tendsto_atTop.comp hshift.tendsto_atTop
  have hM : ∀ n, RetainedBadQ ((beta : ℝ)^2) (dim1 n) (M n) := fun n => hQ (shift n)
  have hWallT := Eventually.of_forall (f := atTop) (fun n => (hM n).1)
  have hE := Eventually.of_forall (f := atTop) (fun n => (hM n).2.1)
  have hd := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.1)
  have hs := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.1)
  have htarget := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.2.2.2.2.2.1)
  have hunit := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.2.2.2.2.2.2.1)
  have hweak1 := hweak.comp hshift.tendsto_atTop
  obtain ⟨hs0, _hd0, _hsLower, hsTest, hrTest⟩ :=
    concrete_limits_original_q hm hmmax zero_lt_one hdim1 M hE hd hs
  have hsCut := child_cutoff_ratio_original_q hm hmmax zero_lt_one hdim1 M
    hc0 htarget hweak1 hE hd hs
  have hbad : ∀ᶠ n in atTop,
      ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs) := by
    apply Eventually.of_forall
    intro n hn
    rcases (hM n).2.2.2.2.2.2.2.2.2.2 with hlo | hhi
    · exact (not_lt_of_ge hn.1) hlo
    · exact (not_lt_of_ge hn.2) hhi
  have hclSlack : cl < 2*(beta : ℝ)^2*Real.exp (-12*(beta : ℝ)^2) := by
    have hp : 0 < (beta : ℝ)^2*Real.exp (-12*(beta : ℝ)^2) :=
      mul_pos hTpos (Real.exp_pos _)
    linarith only [hclTemp, hp]
  have hcost :=
    ActualThetaZeroOverlapMinimum.eventually_high_only_first_child_sharp_failure_original_q
      hm (show 0 < m/10000 by positivity) (by linarith : m/10000 < 3*m)
      hcl hcu (by norm_num : (0 : ℝ) ≤ 2) zero_lt_one hTpos hc0 hc01
      (by linarith : (m/10000)/4 < 3*m-99*(m/10000))
      (by linarith : 100*(m/10000) < (1 : ℝ)/3+m)
      (by linarith : 0 < 9*m-298*(m/10000)) hclSlack hcuTemp
      dim1 hdim1 M hgap (hxs0.comp hshift.tendsto_atTop)
      hWallT htarget hweak1 hsTest hrTest hsCut hbad
  exact Hterminal m cl cu c0 ((beta : ℝ)^2/8) hm hmmax hcl hcu
    hclBound hcuBound hclTemp hcuTemp hc0 hc01 hbudget le_rfl
    dim1 hdim1 M hgap hWallT hunit htarget hweak1 hs0 hsCut
    (Eventually.of_forall (fun n => heps (shift n)))
    (Eventually.of_forall hdSmall) hcost

theorem exists_macro_weak_exclusion_high_branch_original_q
    {T m : ℝ} (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ cl cu : ℝ, 0 < cl → cl ≤ lower → upper ≤ cu →
      cl < T*Real.exp (-12*T) →
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu →
      ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
        (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 1 1 1 T),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      (∀ n, T/4 ≤ (Q n).data.epsilon) →
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
      (∀ n, eta ≤ (Q (phi n)).xs) →
      Tendsto (fun n => laplaceComparisonStrength (Q (phi n)).data.d
        (Q (phi n)).lam (Q (phi n)).xs/(Q (phi n)).xs^2) atTop (𝓝 0) → False := by
  obtain ⟨beta, hbeta, hTemp, rfl⟩ := temperature_root_original_q hT
  obtain ⟨lowerF, upperF, hlowerF, hupperF, Hterminal⟩ :=
    ActualThetaZeroOverlapMinimum.exists_high_gap_first_root_finite_contradiction_original_q
      hbeta hTemp
  obtain ⟨lowerM, upperM, hlowerM, hupperM, Hmacro⟩ :=
    ActualThetaZeroOverlapMinimum.theta_zero_macro_weak_high_gap_bad_forces_sharp_high_only_failure
      hbeta hTemp
  have hTpos : 0 < (beta : ℝ)^2 := zero_lt_one.trans hTemp
  obtain ⟨c0, hc0, hc01, hc0T, hbudget⟩ :=
    exists_uniform_large_epsilon_high_only_radius ((beta : ℝ)^2) (m/10000) hTpos
  refine ⟨min lowerF lowerM, max upperF upperM, lt_min hlowerF hlowerM,
    hupperF.trans_le (le_max_left _ _), ?_⟩
  intro cl cu hcl hclBound hcuBound hclTemp hcuTemp dim hdim Q hQ heps
    eta heta phi hphi hxs hweak
  have hclF : cl ≤ lowerF := hclBound.trans (min_le_left _ _)
  have hcuF : upperF ≤ cu := (le_max_left _ _).trans hcuBound
  have hclM : cl ≤ lowerM := hclBound.trans (min_le_right _ _)
  have hcuM : upperM ≤ cu := (le_max_right _ _).trans hcuBound
  have hcu : 0 < cu := hupperF.trans_le hcuF
  obtain ⟨N, hdSmall, hgap⟩ := retained_high_tail_original_q
    hTpos hm hmmax hc0 hc0T (fun n => dim (phi n))
    (hdim.tendsto_atTop.comp hphi.tendsto_atTop)
    (fun n => Q (phi n)) (fun n => hQ (phi n)) hweak (fun n => heps (phi n))
  let shift : ℕ → ℕ := fun n => n+N
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij N
  let dim1 : ℕ → ℕ := fun n => dim (phi (shift n))
  let M := fun n => Q (phi (shift n))
  have hdim1 : Tendsto dim1 atTop atTop :=
    hdim.tendsto_atTop.comp (hphi.tendsto_atTop.comp hshift.tendsto_atTop)
  have hM : ∀ n, RetainedBadQ ((beta : ℝ)^2) (dim1 n) (M n) :=
    fun n => hQ (phi (shift n))
  have hTfix : ∀ n, (M n).data.T = (beta : ℝ)^2 := fun n => (hM n).1
  have hE := Eventually.of_forall (f := atTop) (fun n => (hM n).2.1)
  have hd := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.1)
  have hs := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.1)
  have htarget := Eventually.of_forall (f := atTop) (fun n => (hM n).2.2.2.2.2.2.2.2.1)
  have hxsBand : ∀ n, (M n).xs ∈ Icc eta 1 :=
    fun n => ⟨hxs (shift n), (hM n).2.2.2.2.2.2.2.2.2.1⟩
  have hweak1 := hweak.comp hshift.tendsto_atTop
  have hs0 := (concrete_limits_original_q hm hmmax zero_lt_one hdim1 M hE hd hs).1
  have hsCut := child_cutoff_ratio_original_q hm hmmax zero_lt_one hdim1 M
    hc0 htarget hweak1 hE hd hs
  have hcost := Hmacro m (m/10000) cl cu 2 1 1 1 ((beta : ℝ)^2) c0
    hm (show 0 < m/10000 by positivity) zero_lt_one hc0 hc0T hclM hcuM
    dim1 hdim1 M eta heta hxsBand hTfix hs0 hweak1 hgap
    (fun n => (hM n).2.2.2.2.2.2.2.2.2.2)
  exact Hterminal m cl cu c0 ((beta : ℝ)^2/8) hm hmmax hcl hcu
    hclF hcuF hclTemp hcuTemp hc0 hc01 hbudget le_rfl
    dim1 hdim1 M hgap (Eventually.of_forall hTfix)
    (Eventually.of_forall (fun n => (hxsBand n).2)) htarget hweak1 hs0 hsCut
    (Eventually.of_forall (fun n => heps (phi (shift n))))
    (Eventually.of_forall hdSmall) hcost

end OAI.SKFluctuations.LaplaceWindowFormalization
