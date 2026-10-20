module

public import SKConstants.Completion.LJ.OriginalPredictable
public import SKConstants.ParisiFullPredictableExponential
public import SKConstants.ScalarObservationMaximal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def posteriorFieldSum (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (H : OriginalFieldCoefficient t) : ℕ → Ω → ℝ :=
  predictableGaussianSum (fun k => actualParisiMagnetizationIncrement W β (t k) (t (k + 1)))
    (originalFieldCoefficient W (actualParisiFullScalarDrift β) t H)

theorem measurable_posteriorFieldSum (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (posteriorFieldSum W β t H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.add ((measurable_originalFieldCoefficient W _ t H hH n).mul
      (measurable_actualParisiMagnetizationIncrement W β _ _))

theorem posteriorFieldSum_abs_le (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) (D : ℕ → ℝ)
    (hH : ∀ k p, |H k p| ≤ D k) (n : ℕ) (w : Ω) :
    |posteriorFieldSum W β t H n w| ≤ ∑ k ∈ Finset.range n, 2 * D k := by
  induction n with
  | zero => simp [posteriorFieldSum, predictableGaussianSum]
  | succ n ih =>
    rw [posteriorFieldSum, predictableGaussianSum, Finset.sum_range_succ]
    apply (abs_add_le _ _).trans (add_le_add ih ?_)
    rw [abs_mul]
    have hn := hH n (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t n) w)
    exact (mul_le_mul hn (actualParisiMagnetizationIncrement_abs_le W β _ _ w)
      (abs_nonneg _) ((abs_nonneg _).trans hn)).trans_eq (by ring)

theorem posteriorFieldSum_exponential (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t) (θ : ℝ) (n : ℕ) :
    (fun w => actualParisiPredictableExponential β t ht H θ n
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t n) w)) =ᵐ[W.law]
      (fun w => Real.exp (θ * posteriorFieldSum W β t H n w -
        θ ^ 2 * originalFieldVariation W (actualParisiFullScalarDrift β) t H n w / 2)) := by
  induction n with
  | zero => exact ae_of_all _ (fun w => by
      simp [actualParisiPredictableExponential, posteriorFieldSum, originalFieldVariation,
        predictableGaussianSum, predictableGaussianVariation])
  | succ n ih =>
    filter_upwards [ih, boundedDriftPastPath_restrict W (actualParisiFullScalarDrift β)
      (t n) (t (n + 1)) (ht (Nat.le_succ n)),
      actualParisiPastMagnetization_version W β (t n),
      actualParisiPastMagnetization_version W β (t (n + 1))] with w hi hr hm hn
    simp only [actualParisiPredictableExponential, hr, hi, hm, hn]
    rw [← Real.exp_add]
    congr 1
    simp only [posteriorFieldSum, predictableGaussianSum, originalFieldVariation,
      predictableGaussianVariation, originalFieldCoefficient, actualParisiMagnetizationIncrement,
      brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ n))]
    ring

theorem posteriorFieldSum_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k)) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hHD : ∀ k p, |H k p| ≤ D k) (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β) t H n w ≤ v)
    (θ : ℝ) :
    Integrable (fun w => Real.exp (θ * posteriorFieldSum W β t H n w)) W.law ∧
      mgf (posteriorFieldSum W β t H n) W.law θ ≤ Real.exp (θ ^ 2 * v / 2) := by
  let := W.isProbability
  let S := posteriorFieldSum W β t H n
  let V := originalFieldVariation W (actualParisiFullScalarDrift β) t H n
  have hm := measurable_posteriorFieldSum W β t H hH n
  have hbound (w : Ω) : Real.exp (θ * S w) ≤
      Real.exp (|θ| * ∑ k ∈ Finset.range n, 2 * D k) := by
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (posteriorFieldSum_abs_le W β t H D hHD n w) (abs_nonneg θ))
  have hi : Integrable (fun w => Real.exp (θ * S w)) W.law :=
    Integrable.of_bound (hm.const_mul θ).exp.aestronglyMeasurable _
      (ae_of_all _ (fun w => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound w))
  let E := fun w => Real.exp (θ * S w - θ ^ 2 * V w / 2)
  have hVm := aemeasurable_predictableGaussianVariation W.law (brownianMeshVariance t)
    (originalFieldCoefficient W (actualParisiFullScalarDrift β) t H)
    (fun k => (measurable_originalFieldCoefficient W _ t H hH k).aemeasurable) n
  have hiE : Integrable E W.law := hi.mono'
    (((hm.aemeasurable.const_mul θ).sub ((hVm.const_mul (θ ^ 2)).div_const 2)).exp.aestronglyMeasurable)
    (ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h0 := predictableGaussianVariation_nonneg (brownianMeshVariance t)
        (originalFieldCoefficient W (actualParisiFullScalarDrift β) t H) n w
      change 0 ≤ V w at h0
      nlinarith [mul_nonneg (sq_nonneg θ) h0]))
  have he := (integral_congr_ae (posteriorFieldSum_exponential W β t ht H θ n)).symm.trans_le
    (actualParisiPredictableExponential_integral_le_one W β hβ t ht H hH D hD hHD θ n)
  have hpoint : ∀ᵐ w ∂W.law,
      Real.exp (θ * S w) ≤ Real.exp (θ ^ 2 * v / 2) * E w := by
    filter_upwards [hv] with w hw
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change V w ≤ v at hw
    nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg θ)]
  refine ⟨hi, ?_⟩
  change (∫ w, Real.exp (θ * S w) ∂W.law) ≤ _
  apply (integral_mono_ae hi (hiE.const_mul _) hpoint).trans
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq (mul_one _)

def posteriorFieldPastSum (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (n : ℕ) (p : ScalarContinuousPath (t n)) : ℝ :=
  ∑ i : Fin n, H i (scalarContinuousPathRestrict (t i) (t n) (ht (by omega)) p) *
    (actualParisiPastMagnetization β (t (i + 1))
      (scalarContinuousPathRestrict (t (i + 1)) (t n) (ht (by omega)) p) -
      actualParisiPastMagnetization β (t i)
        (scalarContinuousPathRestrict (t i) (t n) (ht (by omega)) p))

theorem measurable_posteriorFieldPastSum (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (posteriorFieldPastSum β t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact ((hH i).comp (measurable_scalarContinuousPathRestrict _ _ _)).mul
    (((measurable_actualParisiPastMagnetization β _).comp
      (measurable_scalarContinuousPathRestrict _ _ _)).sub
      ((measurable_actualParisiPastMagnetization β _).comp (measurable_scalarContinuousPathRestrict _ _ _)))

theorem posteriorFieldPastSum_actual (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t) (n : ℕ) :
    (fun w => posteriorFieldPastSum β t ht H n
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t n) w)) =ᵐ[W.law]
      posteriorFieldSum W β t H n := by
  have hr : ∀ᵐ w ∂W.law, ∀ i : Fin (n + 1),
      scalarContinuousPathRestrict (t i) (t n) (ht (by omega))
        (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t n) w) =
          boundedDriftPastPath W (actualParisiFullScalarDrift β) (t i) w :=
    ae_all_iff.mpr (fun i => boundedDriftPastPath_restrict W _ _ _ (ht (by omega)))
  have hm : ∀ᵐ w ∂W.law, ∀ i : ℕ, actualParisiPastMagnetization β (t i)
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t i) w) =
        actualParisiMagnetizationObservable W β (t i) w :=
    ae_all_iff.mpr (fun i => actualParisiPastMagnetization_version W β (t i))
  filter_upwards [hr, hm] with w hwr hwm
  rw [posteriorFieldSum, predictableGaussianSum_eq_fin_sum]
  unfold posteriorFieldPastSum
  apply Finset.sum_congr rfl
  intro i _
  rw [hwr ⟨i, by omega⟩, hwr ⟨i + 1, by omega⟩, hwm, hwm]
  rfl

def posteriorFieldPastMax (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) : (n : ℕ) → ScalarContinuousPath (t n) → ℝ
  | 0, _ => 0
  | n + 1, p => max (posteriorFieldPastMax β t ht H n
      (scalarContinuousPathRestrict (t n) (t (n + 1)) (ht (Nat.le_succ n)) p))
      |posteriorFieldPastSum β t ht H (n + 1) p|

theorem measurable_posteriorFieldPastMax (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (posteriorFieldPastMax β t ht H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_scalarContinuousPathRestrict _ _ _)).max
      ((measurable_posteriorFieldPastSum β t ht H hH (n + 1)).abs)

theorem posteriorFieldPastMax_actual (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t) (n : ℕ) :
    (fun w => posteriorFieldPastMax β t ht H n
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t n) w)) =ᵐ[W.law]
      predictableGaussianRunningAbsMax
        (fun k => actualParisiMagnetizationIncrement W β (t k) (t (k + 1)))
        (originalFieldCoefficient W (actualParisiFullScalarDrift β) t H) n := by
  induction n with
  | zero => exact ae_of_all _ (fun _ => rfl)
  | succ n ih =>
    filter_upwards [ih, posteriorFieldPastSum_actual W β t ht H (n + 1),
      boundedDriftPastPath_restrict W (actualParisiFullScalarDrift β) (t n) (t (n + 1))
        (ht (Nat.le_succ n))] with w hi hs hr
    simp only [posteriorFieldPastMax, predictableGaussianRunningAbsMax, hr, hi, hs]
    rfl

def posteriorFieldFirstExit (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (a : ℝ) : OriginalFieldCoefficient t :=
  fun k p => if posteriorFieldPastMax β t ht H k p < a then H k p else 0

theorem measurable_posteriorFieldFirstExit (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (a : ℝ) (k : ℕ) :
    Measurable (posteriorFieldFirstExit β t ht H a k) :=
  Measurable.ite (measurableSet_lt (measurable_posteriorFieldPastMax β t ht H hH k) measurable_const)
    (hH k) measurable_const

theorem posteriorFieldFirstExit_actual (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t) (a : ℝ) :
    ∀ᵐ w ∂W.law, ∀ k,
      originalFieldCoefficient W (actualParisiFullScalarDrift β) t (posteriorFieldFirstExit β t ht H a) k w =
        predictableGaussianFirstExitCoefficient
          (fun i => actualParisiMagnetizationIncrement W β (t i) (t (i + 1)))
          (originalFieldCoefficient W (actualParisiFullScalarDrift β) t H) a k w := by
  have he := ae_all_iff.mpr (posteriorFieldPastMax_actual W β t ht H)
  filter_upwards [he] with w hw
  intro k
  dsimp only [originalFieldCoefficient, posteriorFieldFirstExit, predictableGaussianFirstExitCoefficient]
  rw [hw k]

theorem posteriorFieldSum_maximal_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k)) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hHD : ∀ k p, |H k p| ≤ D k) (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β) t H n w ≤ v)
    (hv0 : 0 < v) (a : ℝ) (ha : 0 < a) :
    W.law.real {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |posteriorFieldSum W β t H k w|} ≤
      2 * Real.exp (-(a ^ 2 / (2 * v))) := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let X := fun k => actualParisiMagnetizationIncrement W β (t k) (t (k + 1))
  let C := originalFieldCoefficient W b t H
  let G := posteriorFieldFirstExit β t ht H a
  have he := posteriorFieldFirstExit_actual W β t ht H a
  have hG (k : ℕ) (p : ScalarContinuousPath (t k)) : |G k p| ≤ D k := by
    dsimp only [G, posteriorFieldFirstExit]
    split_ifs
    · exact hHD k p
    · simpa using hD k
  have hvar : ∀ᵐ w ∂W.law, originalFieldVariation W b t G n w ≤ v := by
    filter_upwards [he, hv] with w hw hV
    have heq := predictableGaussianVariation_congr (brownianMeshVariance t)
      (originalFieldCoefficient W b t G) (predictableGaussianFirstExitCoefficient X C a) w hw n
    change predictableGaussianVariation (brownianMeshVariance t) _ n w ≤ v
    rw [heq]
    exact (predictableGaussianFirstExit_variation_le X C (brownianMeshVariance t) a n w).trans hV
  have htail := gaussian_mgf_two_sided_tail W.law (posteriorFieldSum W β t G n) v
    (fun θ => posteriorFieldSum_mgf W β hβ t ht G
      (measurable_posteriorFieldFirstExit β t ht H hH a) D hD hG n v hvar θ) hv0 a ha.le
  have hsubset : {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |posteriorFieldSum W β t H k w|} ≤ᵐ[W.law]
      {w | a ≤ |posteriorFieldSum W β t G n w|} := by
    filter_upwards [he] with w hw
    intro h
    have hc : a ≤ predictableGaussianRunningAbsMax X C n w :=
      (predictableGaussianRunningAbsMax_ge_iff X C n w a).mpr h
    have hs := (predictableGaussianFirstExit_sum_properties X C a ha n w).2 hc
    have heq := predictableGaussianSum_congr X (originalFieldCoefficient W b t G)
      (predictableGaussianFirstExitCoefficient X C a) w hw n
    change a ≤ |predictableGaussianSum X _ n w|
    rw [heq]
    exact hs
  apply le_trans ?_ htail
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)

theorem originalFieldVariation_le (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (C : ℝ) (hHC : ∀ k p, |H k p| ≤ C) (n : ℕ) (w : Ω) :
    originalFieldVariation W b t H n w ≤ C ^ 2 * ((t n : ℝ) - t 0) := by
  rw [originalFieldVariation, predictableGaussianVariation_eq_range_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, C ^ 2 * (brownianMeshVariance t k : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      have h := pow_le_pow_left₀ (abs_nonneg _) (hHC k (boundedDriftPastPath W b (t k) w)) 2
      simpa only [sq_abs, originalFieldCoefficient] using h
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ _))]
      exact Finset.sum_range_sub (fun k => (t k : ℝ)) n

theorem posteriorFieldSum_one (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (n : ℕ) (w : Ω) :
    posteriorFieldSum W β t (fun _ _ => 1) n w =
      actualParisiMagnetizationObservable W β (t n) w -
        actualParisiMagnetizationObservable W β (t 0) w := by
  rw [posteriorFieldSum, predictableGaussianSum_eq_range_sum]
  simp only [originalFieldCoefficient, one_mul, actualParisiMagnetizationIncrement]
  exact Finset.sum_range_sub (fun k => actualParisiMagnetizationObservable W β (t k) w) n

theorem actualPosterior_any_prefix_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (h : ℝ)
    (hh : (t n : ℝ) - t 0 ≤ h) (hh0 : 0 < h) (a : ℝ) (ha : 0 < a) :
    W.law.real {w | ∃ k : ℕ, k ≤ n ∧ a ≤
      |actualParisiMagnetizationObservable W β (t k) w -
        actualParisiMagnetizationObservable W β (t 0) w|} ≤
      2 * Real.exp (-(a ^ 2 / (2 * h))) := by
  have hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β)
      t (fun _ _ => 1) n w ≤ h := ae_of_all _ (fun w =>
    (originalFieldVariation_le W _ t ht (fun _ _ => 1) 1 (by intros; norm_num) n w).trans
      (by simpa only [one_pow, one_mul] using hh))
  have ht' := posteriorFieldSum_maximal_tail W β hβ t ht (fun _ _ => 1)
    (fun _ => measurable_const) (fun _ => 1) (by intros; norm_num) (by intros; norm_num)
    n h hv hh0 a ha
  simpa only [posteriorFieldSum_one] using ht'

end SKConstants.Completion.LJ
