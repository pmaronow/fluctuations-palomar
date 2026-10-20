module

public import SKConstants.Completion.S745.Geometry
public import SKConstants.Completion.LM4b.QueryPredictability
public import SKConstants.Completion.LJ.PosteriorTransforms

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S745
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def posteriorTransform (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (predictable : Bool) (n : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, c k * (if predictable then actualParisiFullPosteriorMean W β (t k) w else 1) *
    (actualParisiFullPosteriorMean W β (t (k + 1)) w - actualParisiFullPosteriorMean W β (t k) w)

theorem measurable_posteriorTransform (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (predictable : Bool) (n : ℕ) :
    Measurable (posteriorTransform W β t c predictable n) := by
  unfold posteriorTransform
  apply Finset.measurable_fun_sum
  intro k _
  have hm := measurable_actualParisiMagnetizationObservable W β
  cases predictable <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  · exact ((hm _).sub (hm _)).const_mul _
  · exact ((hm _).const_mul _).mul ((hm _).sub (hm _))

theorem posteriorTransform_subgaussian (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (predictable : Bool) (n : ℕ)
    (v : ℝ≥0) (hv : (∑ k ∈ Finset.range n, c k ^ 2 * (brownianMeshVariance t k : ℝ)) ≤ v) :
    HasSubgaussianMGF (posteriorTransform W β t c predictable n) v W.law := by
  let H : LJ.OriginalFieldCoefficient t := fun k p =>
    c k * (if predictable then actualParisiPastMagnetization β (t k) p else 1)
  have hH (k : ℕ) : Measurable (H k) := by
    dsimp only [H]
    cases predictable <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    · exact measurable_const
    · exact (measurable_actualParisiPastMagnetization β _).const_mul _
  have hHD (k : ℕ) (p : ScalarContinuousPath (t k)) : |H k p| ≤ |c k| := by
    dsimp only [H]
    rw [abs_mul]
    apply mul_le_of_le_one_right (abs_nonneg _)
    cases predictable
    · simp
    · exact actualParisiPastMagnetization_abs_le β _ _
  have hvar : ∀ᵐ w ∂W.law,
      LJ.originalFieldVariation W (actualParisiFullScalarDrift β) t H n w ≤ v := by
    apply ae_of_all
    intro w
    rw [LJ.originalFieldVariation, predictableGaussianVariation_eq_range_sum]
    apply le_trans (Finset.sum_le_sum (fun k _ => ?_)) hv
    apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
    have H := pow_le_pow_left₀ (abs_nonneg _)
      (hHD k (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w)) 2
    simpa only [sq_abs, LJ.originalFieldCoefficient] using H
  have he : LJ.posteriorFieldSum W β t H n =ᵐ[W.law]
      posteriorTransform W β t c predictable n := by
    have hm := ae_all_iff.mpr (fun k => actualParisiPastMagnetization_version W β (t k))
    filter_upwards [hm] with w hw
    rw [LJ.posteriorFieldSum, predictableGaussianSum_eq_range_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [LJ.originalFieldCoefficient, H, hw k, actualParisiMagnetizationIncrement]
    rfl
  have hs : HasSubgaussianMGF (LJ.posteriorFieldSum W β t H n) v W.law := by
    have H := fun θ => LJ.posteriorFieldSum_mgf W β hβ t ht H hH (fun k => |c k|)
      (fun k => abs_nonneg _) hHD n v hvar θ
    exact ⟨fun θ => (H θ).1, fun θ => by simpa only [mul_comm (θ ^ 2)] using (H θ).2⟩
  exact hs.congr he

theorem queryIncrement_indep_pairPast (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    IndepFun (fun u : Ω × A => (brownianFinitePath W (t n) u.1,
      brownianFinitePath Z (t n) u.2))
      (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t n)
      (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  let T := t n
  let Δ := t (n + 1) - t n
  have he : T + Δ = t (n + 1) := add_tsub_cancel_of_le (ht (Nat.le_succ n))
  have hi := (actualParisiQuery_future_indep_originalPast W Z β hβ T).symm.comp
    ((measurable_scalarPathFromPast T).prodMap (measurable_scalarPathFromPast T))
    (measurable_pi_apply Δ)
  apply hi.congr
  · filter_upwards [(measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
        (LM4b.brownianFinitePathFromPast_ae W T),
      (measurePreserving_snd (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
        (LM4b.brownianFinitePathFromPast_ae Z T)] with u huW huZ
    exact Prod.ext huW huZ
  · exact ae_of_all _ (fun u => by dsimp only [Function.comp_def]; rw [he]; rfl)

def queryTransformCoefficient (W : BrownianSystem Ω) (β : ℝ) (b : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (predictable : Bool) (k : ℕ) (u : Ω × A) : ℝ :=
  c k * (if predictable then actualParisiFullPosteriorMean W β (b k) u.1 else 1)

def queryTransform (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t b : ℕ → ℝ≥0) (c : ℕ → ℝ) (predictable : Bool) (n : ℕ) : Ω × A → ℝ :=
  predictableGaussianSum (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t)
    (queryTransformCoefficient W β b c predictable) n

theorem measurable_queryTransformCoefficient (W : BrownianSystem Ω) (β : ℝ)
    (b : ℕ → ℝ≥0) (c : ℕ → ℝ) (predictable : Bool) (k : ℕ) :
    Measurable (queryTransformCoefficient (A := A) W β b c predictable k) := by
  cases predictable
  · convert (measurable_const (a := c k) : Measurable (fun _ : Ω × A => c k)) using 1
    funext u
    exact mul_one _
  · exact ((measurable_actualParisiMagnetizationObservable W β _).comp measurable_fst).const_mul _

theorem measurable_queryTransform (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t b : ℕ → ℝ≥0) (c : ℕ → ℝ) (predictable : Bool) (n : ℕ) :
    Measurable (queryTransform W Z β hβ t b c predictable n) := by
  rw [queryTransform, funext (predictableGaussianSum_eq_range_sum _ _ n)]
  apply Finset.measurable_fun_sum
  intro k _
  exact (measurable_queryTransformCoefficient W β b c predictable k).mul
    (((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
      ((actualParisiQueryBrownianSystem W Z β hβ).measurable _))

theorem queryTransform_state_indep (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t b : ℕ → ℝ≥0) (ht : Monotone t)
    (hb : ∀ k, b k ≤ t k) (c : ℕ → ℝ) (predictable : Bool) (n : ℕ) :
    IndepFun (fun u => (queryTransform W Z β hβ t b c predictable n u,
      queryTransformCoefficient W β b c predictable n u,
      predictableGaussianVariation (brownianMeshVariance t)
        (queryTransformCoefficient W β b c predictable) n u))
      (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t n)
      (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  let C := fun k (p : ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) =>
    c k * (if predictable then LM4b.pastMagnetization β (t n) (b k) p.1 else 1)
  let B := fun k (p : ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) =>
    LM4b.pastQuery W β hβ (t n) (t k) p
  let Φ := fun p : ScalarContinuousPath (t n) × ScalarContinuousPath (t n) =>
    ((∑ k ∈ Finset.range n, C k p * (B (k + 1) p - B k p)), C n p,
      ∑ k ∈ Finset.range n, C k p ^ 2 * (brownianMeshVariance t k : ℝ))
  have hC (k : ℕ) : Measurable (C k) := by
    dsimp only [C]
    cases predictable <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    · exact measurable_const
    · exact ((LM4b.measurable_pastMagnetization β _ _).comp measurable_fst).const_mul _
  have hB (k : ℕ) : Measurable (B k) := LM4b.measurable_pastQuery W β hβ _ _
  have hΦ : Measurable Φ :=
    (Finset.measurable_fun_sum _ (fun k _ => (hC k).mul ((hB (k + 1)).sub (hB k)))).prodMk
      ((hC n).prodMk (Finset.measurable_fun_sum _ (fun k _ => ((hC k).pow_const 2).mul_const _)))
  have hi := (queryIncrement_indep_pairPast W Z β hβ t ht n).comp hΦ measurable_id
  apply hi.congr _ (ae_of_all _ (fun _ => rfl))
  filter_upwards [(measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
      (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) (t n)),
    scalarOrthogonalProcesses_finite_path_version W Z
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (t n)] with u huY huB
  have hc (k : ℕ) (hk : k ≤ n) :
      C k (brownianFinitePath W (t n) u.1, brownianFinitePath Z (t n) u.2) =
        queryTransformCoefficient W β b c predictable k u := by
    have hs : (b k : ℝ) ∈ Icc 0 (t n : ℝ) :=
      ⟨(b k).coe_nonneg, NNReal.coe_le_coe.mpr ((hb k).trans (ht hk))⟩
    have hy := huY ⟨b k, hs⟩
    change (scalarForwardPicardPath (actualParisiFullScalarDrift β) (t n)
      (0, brownianFinitePath W (t n) u.1)) ⟨b k, hs⟩ =
        actualParisiFullScalarProcess W β (b k) u.1 at hy
    cases predictable <;> simp only [C, queryTransformCoefficient, Bool.false_eq_true, ↓reduceIte, mul_one]
    simp only [LM4b.pastMagnetization, IccExtend, Function.comp_def, projIcc_of_mem _ hs]
    rw [hy]
    rfl
  have hq (k : ℕ) (hk : k ≤ n) :
      B k (brownianFinitePath W (t n) u.1, brownianFinitePath Z (t n) u.2) =
        (actualParisiQueryBrownianSystem W Z β hβ).B (t k) u := by
    have hs : (t k : ℝ) ∈ Icc 0 (t n : ℝ) :=
      ⟨(t k).coe_nonneg, NNReal.coe_le_coe.mpr (ht hk)⟩
    simp only [B, LM4b.pastQuery, IccExtend, Function.comp_def, projIcc_of_mem _ hs]
    exact (huB ⟨t k, hs⟩).1.symm
  change Φ _ = _
  unfold Φ queryTransform
  rw [predictableGaussianSum_eq_range_sum, predictableGaussianVariation_eq_range_sum]
  dsimp only [Function.comp_def, Prod.fst, Prod.snd]
  apply Prod.ext
  · dsimp only [Prod.fst]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hc k (Finset.mem_range.mp hk).le, hq k (Finset.mem_range.mp hk).le,
      hq (k + 1) (Finset.mem_range.mp hk)]
    rfl
  · apply Prod.ext
    · exact hc n le_rfl
    · dsimp only [Prod.snd]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hc k (Finset.mem_range.mp hk).le]

theorem queryTransform_subgaussian (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t b : ℕ → ℝ≥0) (ht : Monotone t)
    (hb : ∀ k, b k ≤ t k) (c : ℕ → ℝ) (predictable : Bool) (n : ℕ)
    (v : ℝ≥0) (hv : (∑ k ∈ Finset.range n, c k ^ 2 * (brownianMeshVariance t k : ℝ)) ≤ v) :
    HasSubgaussianMGF (queryTransform W Z β hβ t b c predictable n) v (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  have hcap : ∀ᵐ u ∂W.law.prod Z.law, predictableGaussianVariation (brownianMeshVariance t)
      (queryTransformCoefficient W β b c predictable) n u ≤ v := by
    apply ae_of_all
    intro u
    rw [predictableGaussianVariation_eq_range_sum]
    apply le_trans (Finset.sum_le_sum (fun k _ => ?_)) hv
    apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
    have hm : |queryTransformCoefficient W β b c predictable k u| ≤ |c k| := by
      rw [queryTransformCoefficient, abs_mul]
      apply mul_le_of_le_one_right (abs_nonneg _)
      cases predictable
      · simp
      · exact actualParisiMagnetizationObservable_abs_le W β _ _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  have H := fun θ => predictableGaussianSum_mgf_bound (W.law.prod Z.law)
    (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t)
    (queryTransformCoefficient W β b c predictable) (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_queryTransformCoefficient W β b c predictable k).aemeasurable)
    (queryTransform_state_indep W Z β hβ t b ht hb c predictable) θ n v hcap
  exact ⟨fun θ => (H θ).1, fun θ => by simpa only [queryTransform, mul_comm (θ ^ 2)] using (H θ).2⟩

end SKConstants.Completion.S745
