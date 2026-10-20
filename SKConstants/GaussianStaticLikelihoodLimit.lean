module
public import SKConstants.GaussianTwoDriverBrownian

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants

def staticGaussianBracket {A : Type*}
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0) :
    (n : ℕ) → A → GaussianHistory n → ℝ
  | 0, _, _ => 0
  | n + 1, a, p => staticGaussianBracket ξ h n a p.1 + (ξ n a p.1) ^ 2 * (h n : ℝ)

lemma staticGaussianExponential_square {A : Type*}
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (n : ℕ) (a : A) (p : GaussianHistory n) :
    staticPredictableGaussianExponential ξ h n a p ^ 2 =
      staticPredictableGaussianExponential (fun k a p => 2 * ξ k a p) h n a p *
        Real.exp (staticGaussianBracket ξ h n a p) := by
  induction n with
  | zero => simp [staticPredictableGaussianExponential, staticGaussianBracket]
  | succ n ih =>
    change (staticPredictableGaussianExponential ξ h n a p.1 *
      gaussianExponentialFactor (ξ n a p.1) (h n) p.2) ^ 2 =
      (staticPredictableGaussianExponential (fun k a p => 2 * ξ k a p) h n a p.1 *
        gaussianExponentialFactor (2 * ξ n a p.1) (h n) p.2) *
          Real.exp (staticGaussianBracket ξ h n a p.1 + (ξ n a p.1) ^ 2 * (h n : ℝ))
    rw [mul_pow, ih p.1, Real.exp_add]
    have hs (u y : ℝ) : gaussianExponentialFactor u (h n) y ^ 2 =
        gaussianExponentialFactor (2*u) (h n) y * Real.exp (u ^ 2 * (h n : ℝ)) := by
      simp only [gaussianExponentialFactor, pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hs]
    ring

lemma staticGaussianBracket_bound {A : Type*}
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (C : ℕ → ℝ) (hC : ∀ k a p, |ξ k a p| ≤ C k)
    (n : ℕ) (a : A) (p : GaussianHistory n) :
    staticGaussianBracket ξ h n a p ≤ ∑ j ∈ Finset.range n, (C j) ^ 2 * (h j : ℝ) := by
  induction n with
  | zero => simp [staticGaussianBracket]
  | succ n ih =>
    rw [staticGaussianBracket, Finset.sum_range_succ]
    apply add_le_add (ih p.1)
    apply mul_le_mul_of_nonneg_right _ (h n).coe_nonneg
    have hc := hC n a p.1
    nlinarith [abs_nonneg (ξ n a p.1), sq_abs (ξ n a p.1)]

theorem lintegral_staticGaussianExponential_sq_le {A : Type*} [MeasurableSpace A]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k))) (n : ℕ) (a : A) (V : ℝ)
    (hV : ∀ p, staticGaussianBracket ξ h n a p ≤ V) :
    ∫⁻ p, ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p ^ 2)
      ∂gaussianMeanHistoryLaw (fun _ => 0) h n ≤ ENNReal.ofReal (Real.exp V) := by
  have hm := staticPredictableGaussianExponential_measurable
    (fun k a p => 2 * ξ k a p) h (fun k => (hξ k).const_mul 2) n
  have hma : Measurable (fun p : GaussianHistory n => ENNReal.ofReal
      (staticPredictableGaussianExponential (fun k a p => 2 * ξ k a p) h n a p)) :=
    (hm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp V) * ENNReal.ofReal
        (staticPredictableGaussianExponential (fun k a p => 2 * ξ k a p) h n a p)
        ∂gaussianMeanHistoryLaw (fun _ => 0) h n := by
      apply lintegral_mono
      intro p
      change ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p ^ 2) ≤ _
      rw [staticGaussianExponential_square, mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]
      dsimp only
      gcongr
      exact hV p
    _ = _ := by
      rw [lintegral_const_mul _ hma,
        staticPredictableGaussianExponential_mean_one _ _ (fun k => (hξ k).const_mul 2) n a, mul_one]

def staticBrownianExponential {A Ω : Type*}
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) (ω : A × Ω) : ℝ :=
  staticPredictableGaussianExponential ξ (brownianMeshVariance t) n ω.1
    (brownianGaussianHistory D t n ω.2)

lemma measurable_staticBrownianExponential {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k)))
    (D : ℝ≥0 → Ω → ℝ) (hDm : ∀ s, Measurable (D s)) (t : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (staticBrownianExponential ξ D t n) :=
  (staticPredictableGaussianExponential_measurable ξ _ hξ n).comp
    (measurable_fst.prodMk ((measurable_brownianGaussianHistory D hDm t n).comp measurable_snd))

lemma staticBrownianExponential_conditional_mean_one {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k)))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (a : A) :
    ∫⁻ d, ENNReal.ofReal (staticBrownianExponential ξ D t n (a,d)) ∂Q = 1 := by
  have hm : Measurable (fun p : GaussianHistory n => ENNReal.ofReal
      (staticPredictableGaussianExponential ξ (brownianMeshVariance t) n a p)) :=
    ((staticPredictableGaussianExponential_measurable ξ _ hξ n).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  change (∫⁻ d, ENNReal.ofReal (staticPredictableGaussianExponential ξ _ n a
    (brownianGaussianHistory D t n d)) ∂Q) = 1
  rw [(brownianGaussianHistory_hasLaw hD t ht n).lintegral_comp hm.aemeasurable,
    ← gaussianMeanHistoryLaw_zero_eq]
  exact staticPredictableGaussianExponential_mean_one ξ _ hξ n a

lemma staticBrownianExponential_conditional_sq_le {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k)))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (a : A) (V : ℝ)
    (hV : ∀ p, staticGaussianBracket ξ (brownianMeshVariance t) n a p ≤ V) :
    ∫⁻ d, ENNReal.ofReal (staticBrownianExponential ξ D t n (a,d) ^ 2) ∂Q ≤
      ENNReal.ofReal (Real.exp V) := by
  have hm : Measurable (fun p : GaussianHistory n => ENNReal.ofReal
      (staticPredictableGaussianExponential ξ (brownianMeshVariance t) n a p ^ 2)) :=
    (((staticPredictableGaussianExponential_measurable ξ _ hξ n).comp
      (measurable_const.prodMk measurable_id)).pow_const 2).ennreal_ofReal
  change (∫⁻ d, ENNReal.ofReal (staticPredictableGaussianExponential ξ _ n a
    (brownianGaussianHistory D t n d) ^ 2) ∂Q) ≤ _
  rw [(brownianGaussianHistory_hasLaw hD t ht n).lintegral_comp hm.aemeasurable,
    ← gaussianMeanHistoryLaw_zero_eq]
  exact lintegral_staticGaussianExponential_sq_le ξ _ hξ n a V hV

theorem staticBrownianExponential_preserves_static_marginal {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k)))
    (D : ℝ≥0 → Ω → ℝ) (hDm : ∀ s, Measurable (D s)) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ((P.prod Q).withDensity (fun ω => ENNReal.ofReal (staticBrownianExponential ξ D t n ω))).map
      Prod.fst = P := by
  let f : A × Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (staticBrownianExponential ξ D t n ω)
  have hm : Measurable f := (measurable_staticBrownianExponential ξ hξ D hDm t n).ennreal_ofReal
  let κ : Kernel A Ω := (Kernel.const A Q).withDensity (fun a d => f (a,d))
  have hk : IsMarkovKernel κ := by
    constructor
    intro a
    constructor
    dsimp only [κ]
    rw [Kernel.withDensity_apply _ hm, Kernel.const_apply, withDensity_apply _
      MeasurableSet.univ, Measure.restrict_univ]
    exact staticBrownianExponential_conditional_mean_one Q ξ hξ D hD t ht n a
  let := hk
  have he : P ⊗ₘ κ = (P.prod Q).withDensity f := by
    dsimp only [κ]
    rw [Measure.compProd_withDensity hm, Measure.compProd_const]
  rw [← he]
  exact Measure.fst_compProd P κ

lemma integral_staticBrownianExponential {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k)))
    (D : ℝ≥0 → Ω → ℝ) (hDm : ∀ s, Measurable (D s)) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ∫ ω, staticBrownianExponential ξ D t n ω ∂P.prod Q = 1 := by
  have hm := measurable_staticBrownianExponential ξ hξ D hDm t n
  have hp (ω : A × Ω) : 0 ≤ staticBrownianExponential ξ D t n ω :=
    (staticPredictableGaussianExponential_pos _ _ _ _ _).le
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ hp)
      hm.aestronglyMeasurable,
    lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  simp_rw [staticBrownianExponential_conditional_mean_one Q ξ hξ D hD t ht n]
  simp

lemma eLpNorm_staticBrownianExponential_two_le {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k)))
    (D : ℝ≥0 → Ω → ℝ) (hDm : ∀ s, Measurable (D s)) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (V : ℝ)
    (hV : ∀ a p, staticGaussianBracket ξ (brownianMeshVariance t) n a p ≤ V) :
    eLpNorm (staticBrownianExponential ξ D t n) 2 (P.prod Q) ≤
      ENNReal.ofReal (Real.exp V) ^ (1 / (2 : ℝ)) := by
  have hm := measurable_staticBrownianExponential ξ hξ D hDm t n
  have hp (ω : A × Ω) : 0 ≤ staticBrownianExponential ξ D t n ω :=
    (staticPredictableGaussianExponential_pos _ _ _ _ _).le
  have hb : (∫⁻ ω, ENNReal.ofReal (staticBrownianExponential ξ D t n ω ^ 2) ∂P.prod Q) ≤
      ENNReal.ofReal (Real.exp V) := by
    rw [lintegral_prod _ (hm.pow_const 2).ennreal_ofReal.aemeasurable]
    calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (Real.exp V) ∂P := lintegral_mono
        (fun a => staticBrownianExponential_conditional_sq_le Q ξ hξ D hD t ht n a V (hV a))
      _ = _ := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [Real.enorm_eq_ofReal (hp _), ENNReal.rpow_two, ← ENNReal.ofReal_pow (hp _) 2]
  exact ENNReal.rpow_le_rpow hb (by norm_num)

theorem staticBrownian_density_limit {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hDm : ∀ s, Measurable (D s)) (hD : IsPreBrownianReal D Q)
    (N : ℕ → ℕ) (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j))
    (ξ : ℕ → (k : ℕ) → A → GaussianHistory k → ℝ)
    (hξ : ∀ j k, Measurable (Function.uncurry (ξ j k)))
    (Y : A × Ω → ℝ) (V : ℝ)
    (hV : ∀ j a p, staticGaussianBracket (ξ j) (brownianMeshVariance (t j)) (N j) a p ≤ V)
    (hlim : TendstoInMeasure (P.prod Q)
      (fun j => staticBrownianExponential (ξ j) D (t j) (N j)) atTop Y) :
    Integrable Y (P.prod Q) ∧ (∀ᵐ ω ∂P.prod Q, 0 ≤ Y ω) ∧
      (∫ ω, Y ω ∂P.prod Q = 1) ∧
      IsProbabilityMeasure ((P.prod Q).withDensity (fun ω => ENNReal.ofReal (Y ω))) ∧
      (((P.prod Q).withDensity (fun ω => ENNReal.ofReal (Y ω))).map Prod.fst = P) ∧
      Tendsto (fun j => eLpNorm (staticBrownianExponential (ξ j) D (t j) (N j) - Y) 1
        (P.prod Q)) atTop (𝓝 0) := by
  let X : ℕ → A × Ω → ℝ := fun j => staticBrownianExponential (ξ j) D (t j) (N j)
  let C : ℝ≥0 := ⟨(Real.exp V) ^ (1 / (2 : ℝ)), Real.rpow_nonneg (Real.exp_pos V).le _⟩
  have hm (j : ℕ) : Measurable (X j) :=
    measurable_staticBrownianExponential (ξ j) (hξ j) D hDm (t j) (N j)
  have hcap (j : ℕ) : eLpNorm (X j) 2 (P.prod Q) ≤ C := by
    have hb := eLpNorm_staticBrownianExponential_two_le P Q (ξ j) (hξ j)
      D hDm hD (t j) (ht j) (N j) V (hV j)
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (X j) 2 (P.prod Q) ≤ ENNReal.ofReal ((Real.exp V) ^ (1 / (2 : ℝ)))
    simpa only [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos V).le
      (by norm_num : 0 ≤ 1 / (2 : ℝ))] using hb
  have hp (j : ℕ) : ∀ᵐ ω ∂P.prod Q, 0 ≤ X j ω :=
    ae_of_all _ (fun ω => (staticPredictableGaussianExponential_pos _ _ _ _ _).le)
  have hr := probability_density_of_tendstoInMeasure_of_eLpNorm_two_le (P.prod Q) X Y
    (fun j => (hm j).aestronglyMeasurable) hp
    (fun j => integral_staticBrownianExponential P Q (ξ j) (hξ j) D hDm hD (t j) (ht j) (N j))
    C hcap hlim
  have hXi (j : ℕ) : Integrable (X j) (P.prod Q) :=
    memLp_one_iff_integrable.mp
      ((uniformIntegrable_of_eLpNorm_two_le (P.prod Q) X
        (fun j => (hm j).aestronglyMeasurable) C hcap).memLp j)
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ?_, hr.2.2.2.2⟩
  exact density_limit_preserves_marginal (P.prod Q) P Prod.fst measurable_fst X Y hXi hr.1
    hp hr.2.1
    (fun j => staticBrownianExponential_preserves_static_marginal P Q (ξ j) (hξ j)
      D hDm hD (t j) (ht j) (N j)) hr.2.2.2.2

end SKConstants
