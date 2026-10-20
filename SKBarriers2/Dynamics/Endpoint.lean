module

public import SKBarriers2.Interfaces
public import SKBarriers2.Statement
public import OAI.Probability.SKBarriers.Dynamics.DynamicsMeasurable
public import SKOptimized.ContinuousTV
public import SKOptimized.DisorderConversion

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI.SK OAI.SK.Analytic

namespace SKBarriers2

private theorem packet_discreteKernel_eq {n : ℕ} (β : ℝ) (J : Disorder n)
    (k : ℕ) (x y : Config n) :
    SKOptimized.Model.discreteKernel β J k x y = discreteKernel β J k x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    change (∑ z, heatBath β J x z * SKOptimized.Model.discreteKernel β J k z y) =
      ∑ z, heatBath β J x z * discreteKernel β J k z y
    simp only [ih]

private theorem packet_continuousKernel_eq {n : ℕ} (β : ℝ) (J : Disorder n)
    (t : ℝ) (x y : Config n) :
    SKOptimized.Model.continuousKernel β J t x y = continuousKernel β J t x y := by
  unfold SKOptimized.Model.continuousKernel continuousKernel
  simp only [packet_discreteKernel_eq]

private theorem packet_discreteDistance_eq {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (k : ℕ) :
    SKOptimized.Model.discreteDistance β J x k = discreteDistance β J x k := by
  unfold SKOptimized.Model.discreteDistance discreteDistance
  simp only [packet_discreteKernel_eq]
  rfl

private theorem packet_continuousDistance_eq {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (t : ℝ) :
    SKOptimized.Model.continuousDistance β J x t = continuousDistance β J x t := by
  unfold SKOptimized.Model.continuousDistance continuousDistance
  simp only [packet_continuousKernel_eq]
  rfl

def discreteMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (τ : ℝ) (k : ℕ) : ℝ :=
  ∑ x, if discreteDistance β J x k ≤ τ then gibbs β J x else 0

def continuousMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (τ t : ℝ) : ℝ :=
  ∑ x, if continuousDistance β J x t ≤ τ then gibbs β J x else 0

def continuousBadMassAt (β τ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ J : Disorder n, (∑ x, if τ < continuousDistance β J x t then gibbs β J x else 0)
    ∂disorderLaw n

def discreteBadMassAt (β τ : ℝ) (n k : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x, if τ < discreteDistance β J x k then gibbs β J x else 0)
    ∂disorderLaw n

def clockAttemptCutoff (n : ℕ) (L : ℝ) : ℕ := ⌈(n : ℝ) ^ 2 * Real.exp L⌉₊

theorem clockAttemptCutoff_pos {n : ℕ} (hn : 0 < n) (L : ℝ) :
    0 < clockAttemptCutoff n L := by
  exact Nat.ceil_pos.mpr (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hn)) (Real.exp_pos L))

theorem clockAttemptCutoff_tail_le {n : ℕ} (hn : 0 < n) (L : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htL : t ≤ Real.exp L) :
    (∑' k : ℕ, if clockAttemptCutoff n L < k then clockWeight ((n : ℝ) * t) k else 0) ≤
      1 / (n : ℝ) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < (n : ℝ) ^ 2 * Real.exp L := by positivity
  calc
    _ ≤ ((n : ℝ) * t) / (clockAttemptCutoff n L : ℝ) :=
      clockWeight_tail_le (mul_nonneg hn'.le ht) (clockAttemptCutoff_pos hn L)
    _ ≤ ((n : ℝ) * Real.exp L) / (clockAttemptCutoff n L : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htL hn'.le) (by positivity)
    _ ≤ ((n : ℝ) * Real.exp L) / ((n : ℝ) ^ 2 * Real.exp L) :=
      div_le_div_of_nonneg_left (by positivity) hden (Nat.le_ceil _)
    _ = 1 / (n : ℝ) := by field_simp

theorem floor_exp_le_clockAttemptCutoff {n : ℕ} (hn : 0 < n) (L : ℝ) :
    ⌊Real.exp L⌋₊ ≤ clockAttemptCutoff n L := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  exact (Nat.floor_mono (le_mul_of_one_le_left (Real.exp_pos L).le hsq)).trans
    (Nat.floor_le_ceil _)

theorem discreteMixedMass_le_sign {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) {τ : ℝ} (hτ : τ < 1 / 2) (v : Config n → Config n) :
    discreteMixedMass β J τ k ≤
      (∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x) /
        ((1 / 2 : ℝ) - τ) := by
  apply (le_div_iff₀ (sub_pos.mpr hτ)).mpr
  have H := SKOptimized.Model.discrete_mixed_mass_times_gap hn β J k τ v
  simp only [SKOptimized.Model.finiteMixedMass, packet_discreteDistance_eq,
    packet_discreteKernel_eq] at H
  change ((1 / 2 : ℝ) - τ) * discreteMixedMass β J τ k ≤
    ∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x at H
  simpa only [mul_comm ((1 / 2 : ℝ) - τ)] using H

theorem continuousMixedMass_le_sign {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t τ : ℝ} (ht : 0 ≤ t) (hτ : τ < 1 / 2) (v : Config n → Config n) :
    continuousMixedMass β J τ t ≤
      (∑ x, gibbs β J x * ∑ y,
        if overlap (v x) y ≤ 0 then continuousKernel β J t x y else 0) /
        ((1 / 2 : ℝ) - τ) := by
  have H := SKOptimized.Model.continuous_above_mass_lower_bound hn β J ht τ
    (∑ x, gibbs β J x * ∑ y,
      if overlap (v x) y ≤ 0 then continuousKernel β J t x y else 0) hτ v (by simp only [packet_continuousKernel_eq]; exact le_rfl)
  simp only [SKOptimized.Model.finiteAboveMass, packet_continuousDistance_eq] at H
  have he := gibbs_predicate_mass_compl β J (fun x => continuousDistance β J x t ≤ τ)
  change 1 - _ ≤ (∑ x, if τ < continuousDistance β J x t then gibbs β J x else 0) at H
  simp only [not_le] at he
  rw [he] at H
  change 1 - _ ≤ 1 - continuousMixedMass β J τ t at H
  linarith only [H]

theorem mixedMass_bounds_of_crossing {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (L E : ℝ) (hE : 0 ≤ E) {τ : ℝ} (hτ : τ < 1 / 2)
    (v : Config n → Config n)
    (h : ∀ k ≤ clockAttemptCutoff n L,
      (∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x) ≤ E) :
    (∀ t : ℝ, 0 ≤ t → t ≤ Real.exp L →
      continuousMixedMass β J τ t ≤ (E + 1 / (n : ℝ)) / ((1 / 2 : ℝ) - τ)) ∧
    (∀ k : ℕ, k ≤ ⌊Real.exp L⌋₊ →
      discreteMixedMass β J τ k ≤ E / ((1 / 2 : ℝ) - τ)) := by
  constructor
  · intro t ht htL
    refine (continuousMixedMass_le_sign hn β J ht hτ v).trans ?_
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hτ).le
    exact (averaged_sign_clock_bound hn β J ht v _ hE h).trans
      (add_le_add le_rfl (clockAttemptCutoff_tail_le hn L ht htL))
  · intro k hk
    exact (discreteMixedMass_le_sign hn β J k hτ v).trans
      (div_le_div_of_nonneg_right (h k (hk.trans (floor_exp_le_clockAttemptCutoff hn L)))
        (sub_pos.mpr hτ).le)

private theorem continuousMixedMass_integrable (n : ℕ) (β τ t : ℝ) :
    Integrable (fun J : Disorder n => continuousMixedMass β J τ t) (disorderLaw n) := by
  exact integrable_gibbs_predicate_mass β _
    (fun x => measurableSet_le (measurable_continuousDistance β t x) measurable_const)

private theorem discreteMixedMass_integrable (n : ℕ) (β τ : ℝ) (k : ℕ) :
    Integrable (fun J : Disorder n => discreteMixedMass β J τ k) (disorderLaw n) := by
  exact integrable_gibbs_predicate_mass β _
    (fun x => measurableSet_le (continuous_discreteDistance β k x).measurable measurable_const)

theorem continuousBadMassAt_eq_one_sub (β τ : ℝ) (n : ℕ) (t : ℝ) :
    continuousBadMassAt β τ n t =
      1 - ∫ J, continuousMixedMass β J τ t ∂disorderLaw n := by
  have he (J : Disorder n) : (∑ x, if τ < continuousDistance β J x t then gibbs β J x else 0) =
      1 - continuousMixedMass β J τ t := by
    simpa only [not_le, continuousMixedMass] using
      gibbs_predicate_mass_compl β J (fun x => continuousDistance β J x t ≤ τ)
  unfold continuousBadMassAt
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (continuousMixedMass_integrable n β τ t)]
  simp

theorem discreteBadMassAt_eq_one_sub (β τ : ℝ) (n k : ℕ) :
    discreteBadMassAt β τ n k =
      1 - ∫ J, discreteMixedMass β J τ k ∂disorderLaw n := by
  have he (J : Disorder n) : (∑ x, if τ < discreteDistance β J x k then gibbs β J x else 0) =
      1 - discreteMixedMass β J τ k := by
    simpa only [not_le, discreteMixedMass] using
      gibbs_predicate_mass_compl β J (fun x => discreteDistance β J x k ≤ τ)
  unfold discreteBadMassAt
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (discreteMixedMass_integrable n β τ k)]
  simp

theorem main_of_quenched_mixed_bounds (β τ : ℝ) (t : ℕ → ℝ) (k : ℕ → ℕ)
    (C : (n : ℕ) → Set (Disorder n)) (hC : ∀ n, MeasurableSet (C n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ J ∈ C n,
      continuousMixedMass β J τ (t n) ≤ e n ∧ discreteMixedMass β J τ (k n) ≤ e n) :
    Tendsto (fun n => continuousBadMassAt β τ n (t n)) atTop (𝓝 1) ∧
      Tendsto (fun n => discreteBadMassAt β τ n (k n)) atTop (𝓝 1) := by
  have hcomp : Tendsto (fun n => (disorderLaw n).real (C n)ᶜ) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x := (1 : ℝ))).sub hC1
    simpa only [measureReal_compl (hC _), probReal_univ, sub_self] using H
  have general (f : (n : ℕ) → Disorder n → ℝ)
      (hf : ∀ n, AEStronglyMeasurable (f n) (disorderLaw n))
      (hprob : ∀ n J, f n J ∈ Icc (0 : ℝ) 1)
      (hgood : ∀ᶠ n : ℕ in atTop, ∀ J ∈ C n, f n J ≤ e n) :
      Tendsto (fun n => ∫ J, f n J ∂disorderLaw n) atTop (𝓝 0) := by
    exact SKOptimized.Disorder.annealed_bad_mass_tendsto_zero_of_eventual_bounds
      (fun n => inferInstance) hf hprob hC (Eventually.of_forall he) hgood
      (Eventually.of_forall (fun _ => le_rfl)) hcomp he0
  have HC : Tendsto (fun n => ∫ J, continuousMixedMass β J τ (t n) ∂disorderLaw n)
      atTop (𝓝 0) := by
    apply general _ (fun n => (continuousMixedMass_integrable n β τ (t n)).aestronglyMeasurable)
      (fun n J => ⟨gibbs_predicate_mass_nonneg β J _, gibbs_predicate_mass_le_one β J _⟩)
    filter_upwards [hbound] with n hn J hJ
    exact (hn J hJ).1
  have HD : Tendsto (fun n => ∫ J, discreteMixedMass β J τ (k n) ∂disorderLaw n)
      atTop (𝓝 0) := by
    apply general _ (fun n => (discreteMixedMass_integrable n β τ (k n)).aestronglyMeasurable)
      (fun n J => ⟨gibbs_predicate_mass_nonneg β J _, gibbs_predicate_mass_le_one β J _⟩)
    filter_upwards [hbound] with n hn J hJ
    exact (hn J hJ).2
  constructor
  · simpa only [← continuousBadMassAt_eq_one_sub, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub HC
  · simpa only [← discreteBadMassAt_eq_one_sub, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub HD

theorem main_of_uniform_quenched_mixed_bounds (β τ : ℝ) (L : ℕ → ℝ)
    (C : (n : ℕ) → Set (Disorder n)) (hC : ∀ n, MeasurableSet (C n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ J ∈ C n,
      (∀ t : ℝ, 0 ≤ t → t ≤ Real.exp (L n) → continuousMixedMass β J τ t ≤ e n) ∧
      (∀ k : ℕ, k ≤ ⌊Real.exp (L n)⌋₊ → discreteMixedMass β J τ k ≤ e n)) :
    ∀ (t : ℕ → ℝ) (k : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop, 0 ≤ t n ∧ t n ≤ Real.exp (L n) ∧ k n ≤ ⌊Real.exp (L n)⌋₊) →
      Tendsto (fun n => continuousBadMassAt β τ n (t n)) atTop (𝓝 1) ∧
        Tendsto (fun n => discreteBadMassAt β τ n (k n)) atTop (𝓝 1) := by
  intro t k htime
  apply main_of_quenched_mixed_bounds β τ t k C hC hC1 e he he0
  filter_upwards [hbound, htime] with n hn ht J hJ
  exact ⟨(hn J hJ).1 (t n) ht.1 ht.2.1, (hn J hJ).2 (k n) ht.2.2⟩

theorem main_of_quenched_crossing_bounds (β : ℝ) (L : ℕ → ℝ)
    (C : (n : ℕ) → Set (Disorder n)) (hC : ∀ n, MeasurableSet (C n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (hE0 : Tendsto E atTop (𝓝 0))
    (hcross : ∀ᶠ n : ℕ in atTop, ∀ J ∈ C n, ∃ v : Config n → Config n,
      ∀ k ≤ clockAttemptCutoff n (L n),
        (∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x) ≤ E n) :
    ∀ τ : ℝ, τ < 1 / 2 → ∀ (t : ℕ → ℝ) (k : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop, 0 ≤ t n ∧ t n ≤ Real.exp (L n) ∧ k n ≤ ⌊Real.exp (L n)⌋₊) →
      Tendsto (fun n => continuousBadMassAt β τ n (t n)) atTop (𝓝 1) ∧
        Tendsto (fun n => discreteBadMassAt β τ n (k n)) atTop (𝓝 1) := by
  intro τ hτ
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have herr : Tendsto (fun n => (E n + 1 / (n : ℝ)) / ((1 / 2 : ℝ) - τ))
      atTop (𝓝 0) := by
    simpa only [add_zero, zero_div] using (hE0.add hinv).div_const ((1 / 2 : ℝ) - τ)
  apply main_of_uniform_quenched_mixed_bounds β τ L C hC hC1
    (fun n => (E n + 1 / (n : ℝ)) / ((1 / 2 : ℝ) - τ))
    (fun n => div_nonneg (add_nonneg (hE n) (by positivity)) (sub_pos.mpr hτ).le) herr
  filter_upwards [hcross, eventually_gt_atTop (0 : ℕ)] with n hn hn0 J hJ
  obtain ⟨v, hv⟩ := hn J hJ
  have HB := mixedMass_bounds_of_crossing hn0 β J (L n) (E n) (hE n) hτ v hv
  refine ⟨HB.1, ?_⟩
  intro k hk
  exact (HB.2 k hk).trans (div_le_div_of_nonneg_right
    (le_add_of_nonneg_right (by positivity)) (sub_pos.mpr hτ).le)

theorem badMass_limits_of_quenched_mixed_bounds (β τ : ℝ) (L : ℕ → ℝ)
    (C : (n : ℕ) → Set (Disorder n)) (hC : ∀ n, MeasurableSet (C n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ J ∈ C n,
      (∀ t : ℝ, 0 ≤ t → t ≤ Real.exp (L n) → continuousMixedMass β J τ t ≤ e n) ∧
      (∀ k : ℕ, k ≤ ⌊Real.exp (L n)⌋₊ → discreteMixedMass β J τ k ≤ e n))
    (A κ : ℝ) (hscale : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ κ ≤ L n) :
    Tendsto (OAI.SK.Strengthened.continuousBadMass β A κ τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β A κ τ) atTop (𝓝 1) := by
  have htime : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.exp (A * (n : ℝ) ^ κ) ∧
      Real.exp (A * (n : ℝ) ^ κ) ≤ Real.exp (L n) ∧
      ⌊Real.exp (A * (n : ℝ) ^ κ)⌋₊ ≤ ⌊Real.exp (L n)⌋₊ := by
    filter_upwards [hscale] with n hn
    have hexp : Real.exp (A * (n : ℝ) ^ κ) ≤ Real.exp (L n) := Real.exp_le_exp.mpr hn
    exact ⟨(Real.exp_pos _).le, hexp, Nat.floor_mono hexp⟩
  exact main_of_uniform_quenched_mixed_bounds β τ L C hC hC1 e he he0 hbound
    (fun n => Real.exp (A * (n : ℝ) ^ κ))
    (fun n => ⌊Real.exp (A * (n : ℝ) ^ κ)⌋₊) htime

theorem badMass_limits_of_quenched_crossing_bounds (β : ℝ) (L : ℕ → ℝ)
    (C : (n : ℕ) → Set (Disorder n)) (hC : ∀ n, MeasurableSet (C n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (hE0 : Tendsto E atTop (𝓝 0))
    (hcross : ∀ᶠ n : ℕ in atTop, ∀ J ∈ C n, ∃ v : Config n → Config n,
      ∀ k ≤ clockAttemptCutoff n (L n),
        (∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x) ≤ E n) :
    ∀ τ : ℝ, τ < 1 / 2 → ∀ A κ : ℝ,
      (∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ κ ≤ L n) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β A κ τ) atTop (𝓝 1) ∧
        Tendsto (OAI.SK.Strengthened.discreteBadMass β A κ τ) atTop (𝓝 1) := by
  intro τ hτ A κ hscale
  have htime : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.exp (A * (n : ℝ) ^ κ) ∧
      Real.exp (A * (n : ℝ) ^ κ) ≤ Real.exp (L n) ∧
      ⌊Real.exp (A * (n : ℝ) ^ κ)⌋₊ ≤ ⌊Real.exp (L n)⌋₊ := by
    filter_upwards [hscale] with n hn
    have hexp : Real.exp (A * (n : ℝ) ^ κ) ≤ Real.exp (L n) := Real.exp_le_exp.mpr hn
    exact ⟨(Real.exp_pos _).le, hexp, Nat.floor_mono hexp⟩
  exact main_of_quenched_crossing_bounds β L C hC hC1 E hE hE0 hcross τ hτ
    (fun n => Real.exp (A * (n : ℝ) ^ κ))
    (fun n => ⌊Real.exp (A * (n : ℝ) ^ κ)⌋₊) htime

end SKBarriers2
