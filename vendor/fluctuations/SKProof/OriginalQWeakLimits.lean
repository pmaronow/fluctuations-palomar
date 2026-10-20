module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroChildCutoffInheritance
public import ComparisonActualHighWallThetaZeroSelectedOriginRateDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology NNReal

theorem temperature_root_original_q {T : ℝ} (hT : 1 < T) :
    ∃ beta : ℝ≥0, 0 < beta ∧ 1 < (beta : ℝ)^2 ∧ (beta : ℝ)^2 = T := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  refine ⟨⟨Real.sqrt T, Real.sqrt_nonneg T⟩, ?_, ?_, ?_⟩
  · exact Real.sqrt_pos.mpr hT0
  · change 1 < (Real.sqrt T)^2
    rw [Real.sq_sqrt hT0.le]
    exact hT
  · exact Real.sq_sqrt hT0.le

theorem concrete_limits_original_q
    {m cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300) (hC0 : 0 < C0)
    {dim : ℕ → ℕ} (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (hE : ∀ᶠ n in atTop, (Q n).data.E = wallHighError m (dim n+1))
    (hd : ∀ᶠ n in atTop, (Q n).data.d = wallHighD m (dim n+1))
    (hs : ∀ᶠ n in atTop, (Q n).data.s = wallHighMass m (dim n+1)) :
    Tendsto (fun n => (Q n).data.s) atTop (𝓝 0) ∧
    Tendsto (fun n => (Q n).data.d) atTop (𝓝 0) ∧
    Tendsto (fun n => (Q n).data.s /
      comparisonLowerScale (Q n).data.N (Q n).data.E (Q n).data.d) atTop (𝓝 0) ∧
    Tendsto (fun n => (Q n).data.s / (Q n).xs) atTop (𝓝 0) ∧
    Tendsto (fun n => (Q n).data.rmin / (Q n).xs) atTop (𝓝 0) := by
  have hdim1 : Tendsto (fun n => dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have HN : Tendsto (fun n => ((dim n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdim1
  have HDlim : Tendsto (fun n => (Q n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop
      (show 0 < (1 : ℝ)/6-15*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hd] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighD
    congr 1
    ring
  have HSlim : Tendsto (fun n => (Q n).data.s) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop
      (show 0 < (1 : ℝ)/6-5*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hs] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighMass
    congr 1
    ring
  have Hlower : Tendsto (fun n => (Q n).data.s /
      comparisonLowerScale (Q n).data.N (Q n).data.E (Q n).data.d)
      atTop (𝓝 0) := by
    apply ((concrete_wall_omission_ratio_tendsto_zero hm).comp hdim1).congr'
    filter_upwards [hE, hd, hs] with n hnE hnd hns
    simp only [Function.comp_apply, hnE, hnd, hns, ActualHighWallData.N]
  have Htest : Tendsto (fun n => (Q n).data.s / (Q n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => div_nonneg (Q n).data.hs.1.le (Q n).hxs.le)
      (fun n => div_le_div_of_nonneg_left (Q n).data.hs.1.le
        (comparisonLowerScale_pos (Q n).data.hN (Q n).data.hE (Q n).data.hd)
        (Q n).hscale) Hlower
  exact ⟨HSlim, HDlim, Hlower, Htest,
    ActualThetaZeroOverlapMinimum.theta_zero_rmin_over_selected_test_tendsto_zero_along_draft
      hm hC0 dim hdim Q⟩

theorem child_cutoff_ratio_original_q
    {m cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300) (hC0 : 0 < C0)
    {dim : ℕ → ℕ} (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (hc0 : 0 < c0)
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale (Q n).data.N (m/10000)
      (Q n).data.E (Q n).lam ≤ (Q n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
      (Q n).lam (Q n).xs / (Q n).xs^2) atTop (𝓝 0))
    (hE : ∀ᶠ n in atTop, (Q n).data.E = wallHighError m (dim n+1))
    (hd : ∀ᶠ n in atTop, (Q n).data.d = wallHighD m (dim n+1))
    (hs : ∀ᶠ n in atTop, (Q n).data.s = wallHighMass m (dim n+1)) :
    Tendsto (fun n => (Q n).data.s /
      actualChildCutoff (dim n+1) (m/10000) c0 (Q n).data.d (Q n).lam (Q n).xs)
      atTop (𝓝 0) := by
  exact theta_zero_omission_ratio_inherits_child_cutoff hm
    (show 0 < m/10000 by positivity) hC0 hc0
    (show (m/10000)/4 < 3*m-99*(m/10000) by linarith)
    dim hdim Q htarget hweak
    (concrete_limits_original_q hm hmmax hC0 hdim Q hE hd hs).2.2.1

end OAI.SKFluctuations.LaplaceWindowFormalization
