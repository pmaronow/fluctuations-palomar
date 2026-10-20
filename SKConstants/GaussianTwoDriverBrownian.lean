module
public import SKConstants.GaussianTwoDriverLikelihoodLimit
public import SKConstants.BrownianGaussianHistory

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants

lemma measurePreserving_pairShuffle
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod
    ((measurePreserving_prodAssoc μB μC μD).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  convert h5.comp (h4.comp (h3.comp (h2.comp h1))) using 1
  rfl

def pairedGaussianHistoryJoin :
    (n : ℕ) → GaussianHistory n × GaussianHistory n → PairedGaussianHistory n
  | 0, _ => PUnit.unit
  | n + 1, p => (pairedGaussianHistoryJoin n (p.1.1,p.2.1),(p.1.2,p.2.2))

lemma measurable_pairedGaussianHistoryJoin (n : ℕ) :
    Measurable (pairedGaussianHistoryJoin n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (GaussianHistory n × ℝ) × (GaussianHistory n × ℝ) =>
      (pairedGaussianHistoryJoin n (p.1.1,p.2.1),(p.1.2,p.2.2)))
    exact (ih.comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
      (measurable_fst.snd.prodMk measurable_snd.snd)

lemma measurePreserving_pairedGaussianHistoryJoin (h : ℕ → ℝ≥0) (n : ℕ) :
    MeasurePreserving (pairedGaussianHistoryJoin n)
      ((gaussianHistoryLaw h n).prod (gaussianHistoryLaw h n))
      (pairedGaussianHistoryLaw h n) := by
  induction n with
  | zero =>
    refine ⟨measurable_pairedGaussianHistoryJoin 0, ?_⟩
    simp [gaussianHistoryLaw, pairedGaussianHistoryLaw, pairedGaussianHistoryJoin,
      Measure.dirac_prod_dirac]
  | succ n ih =>
    have hg := measurePreserving_pairShuffle (gaussianHistoryLaw h n) (gaussianReal 0 (h n))
      (gaussianHistoryLaw h n) (gaussianReal 0 (h n))
    have hj := ih.prod (MeasurePreserving.id ((gaussianReal 0 (h n)).prod (gaussianReal 0 (h n))))
    change MeasurePreserving _
      (((gaussianHistoryLaw h n).prod (gaussianReal 0 (h n))).prod
        ((gaussianHistoryLaw h n).prod (gaussianReal 0 (h n))))
      ((pairedGaussianHistoryLaw h n).prod ((gaussianReal 0 (h n)).prod (gaussianReal 0 (h n))))
    convert hj.comp hg using 1
    rfl

def pairedBrownianGaussianHistory {Ω Ω' : Type*}
    (B : ℝ≥0 → Ω → ℝ) (D : ℝ≥0 → Ω' → ℝ) (t : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω × Ω') : PairedGaussianHistory n :=
  pairedGaussianHistoryJoin n (brownianGaussianHistory B t n ω.1,
    brownianGaussianHistory D t n ω.2)

theorem pairedBrownianGaussianHistory_hasLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (D : ℝ≥0 → Ω' → ℝ)
    (hB : IsPreBrownianReal B P) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    HasLaw (pairedBrownianGaussianHistory B D t n)
      (pairedGaussianHistoryLaw (brownianMeshVariance t) n) (P.prod Q) := by
  have hb := brownianGaussianHistory_hasLaw hB t ht n
  have hd := brownianGaussianHistory_hasLaw hD t ht n
  have hf : HasLaw (Prod.fst : Ω × Ω' → Ω) P (P.prod Q) :=
    ⟨measurable_fst.aemeasurable, (measurePreserving_fst (μ := P) (ν := Q)).map_eq⟩
  have hg : HasLaw (Prod.snd : Ω × Ω' → Ω') Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable, (measurePreserving_snd (μ := P) (ν := Q)).map_eq⟩
  have hi := indepFun_prod₀ (μ := P) (ν := Q) hb.aemeasurable hd.aemeasurable
  have hh := hi.hasLaw_prod (hb.comp hf) (hd.comp hg)
  have hj : HasLaw (pairedGaussianHistoryJoin n)
      (pairedGaussianHistoryLaw (brownianMeshVariance t) n)
      ((gaussianHistoryLaw (brownianMeshVariance t) n).prod
        (gaussianHistoryLaw (brownianMeshVariance t) n)) :=
    ⟨(measurable_pairedGaussianHistoryJoin n).aemeasurable,
      (measurePreserving_pairedGaussianHistoryJoin (brownianMeshVariance t) n).map_eq⟩
  exact hj.comp hh

lemma measurable_brownianGaussianHistory {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hB : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (n : ℕ) : Measurable (brownianGaussianHistory B t n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.prodMk ((hB (t (n+1))).sub (hB (t n)))

lemma measurable_pairedBrownianGaussianHistory
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (B : ℝ≥0 → Ω → ℝ) (D : ℝ≥0 → Ω' → ℝ)
    (hB : ∀ s, Measurable (B s)) (hD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (n : ℕ) : Measurable (pairedBrownianGaussianHistory B D t n) :=
  (measurable_pairedGaussianHistoryJoin n).comp
    (((measurable_brownianGaussianHistory B hB t n).comp measurable_fst).prodMk
      ((measurable_brownianGaussianHistory D hD t n).comp measurable_snd))

def pairedBrownianDStaticCoefficient {Ω : Type*}
    (H : PairedGaussianCoefficient) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (k : ℕ) (a : Ω) (p : GaussianHistory k) : ℝ :=
  (H k (pairedGaussianHistoryJoin k (brownianGaussianHistory B t k a,p))).2

lemma measurable_pairedBrownianDStaticCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (H : PairedGaussianCoefficient) (hH : ∀ n, Measurable (H n))
    (B : ℝ≥0 → Ω → ℝ) (hB : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (k : ℕ) :
    Measurable (Function.uncurry (pairedBrownianDStaticCoefficient H B t k)) :=
  (hH k).snd.comp ((measurable_pairedGaussianHistoryJoin k).comp
    (((measurable_brownianGaussianHistory B hB t k).comp measurable_fst).prodMk measurable_snd))

lemma pairedBrownianDExponential_eq_static {Ω Ω' : Type*}
    (H : PairedGaussianCoefficient) (B : ℝ≥0 → Ω → ℝ) (D : ℝ≥0 → Ω' → ℝ)
    (t : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (n : ℕ) (a : Ω) (d : Ω') :
    pairedGaussianExponential (pairedGaussianDShare H) h n
      (pairedBrownianGaussianHistory B D t n (a,d)) =
      staticPredictableGaussianExponential (pairedBrownianDStaticCoefficient H B t) h n a
        (brownianGaussianHistory D t n d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pairedGaussianExponential (pairedGaussianDShare H) h n
      (pairedBrownianGaussianHistory B D t n (a,d)) *
        pairedGaussianStepFactor
          (0,(H n (pairedBrownianGaussianHistory B D t n (a,d))).2)
          (h n) (brownianMeshIncrement B t n a,brownianMeshIncrement D t n d) =
      staticPredictableGaussianExponential (pairedBrownianDStaticCoefficient H B t) h n a
        (brownianGaussianHistory D t n d) *
          gaussianExponentialFactor (pairedBrownianDStaticCoefficient H B t n a
            (brownianGaussianHistory D t n d)) (h n) (brownianMeshIncrement D t n d)
    rw [ih]
    simp only [pairedGaussianStepFactor, gaussianExponentialFactor, zero_mul,
      zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_self, Real.exp_zero, one_mul]
    rfl

lemma gaussianMeanHistoryLaw_zero_eq (h : ℕ → ℝ≥0) (n : ℕ) :
    gaussianMeanHistoryLaw (fun _ => 0) h n = gaussianHistoryLaw h n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gaussianMeanHistoryLaw, gaussianHistoryLaw, ih]

theorem pairedBrownianDExponential_conditional_mean_one
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (H : PairedGaussianCoefficient) (hH : ∀ n, Measurable (H n))
    (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ s, Measurable (B s))
    (D : ℝ≥0 → Ω' → ℝ) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (a : Ω) :
    ∫⁻ d, ENNReal.ofReal (pairedGaussianExponential (pairedGaussianDShare H)
      (brownianMeshVariance t) n (pairedBrownianGaussianHistory B D t n (a,d))) ∂Q = 1 := by
  simp_rw [pairedBrownianDExponential_eq_static]
  have hm : Measurable (fun p : GaussianHistory n => ENNReal.ofReal
      (staticPredictableGaussianExponential (pairedBrownianDStaticCoefficient H B t)
        (brownianMeshVariance t) n a p)) :=
    ((staticPredictableGaussianExponential_measurable _ _
      (measurable_pairedBrownianDStaticCoefficient H hH B hBm t) n).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [(brownianGaussianHistory_hasLaw hD t ht n).lintegral_comp hm.aemeasurable,
    ← gaussianMeanHistoryLaw_zero_eq]
  exact staticPredictableGaussianExponential_mean_one _ _
    (measurable_pairedBrownianDStaticCoefficient H hH B hBm t) n a

theorem pairedBrownianDExponential_preserves_static_marginal
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (H : PairedGaussianCoefficient) (hH : ∀ n, Measurable (H n))
    (B : ℝ≥0 → Ω → ℝ) (D : ℝ≥0 → Ω' → ℝ)
    (hBm : ∀ s, Measurable (B s)) (hDm : ∀ s, Measurable (D s))
    (hD : IsPreBrownianReal D Q) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ((P.prod Q).withDensity (fun ω => ENNReal.ofReal
      (pairedGaussianExponential (pairedGaussianDShare H) (brownianMeshVariance t) n
        (pairedBrownianGaussianHistory B D t n ω)))).map Prod.fst = P := by
  let f : Ω × Ω' → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (pairedGaussianExponential (pairedGaussianDShare H) (brownianMeshVariance t) n
      (pairedBrownianGaussianHistory B D t n ω))
  have hm : Measurable f :=
    ((measurable_pairedGaussianExponential _ (measurable_pairedGaussianDShare H hH)
      (brownianMeshVariance t) n).comp
        (measurable_pairedBrownianGaussianHistory B D hBm hDm t n)).ennreal_ofReal
  let κ : Kernel Ω Ω' := (Kernel.const Ω Q).withDensity (fun a d => f (a,d))
  have hk : IsMarkovKernel κ := by
    constructor
    intro a
    constructor
    dsimp only [κ]
    rw [Kernel.withDensity_apply _ hm, Kernel.const_apply, withDensity_apply _
      MeasurableSet.univ, Measure.restrict_univ]
    exact pairedBrownianDExponential_conditional_mean_one Q H hH B hBm D hD t ht n a
  let := hk
  have he : P ⊗ₘ κ = (P.prod Q).withDensity f := by
    dsimp only [κ]
    rw [Measure.compProd_withDensity hm, Measure.compProd_const]
  rw [← he]
  exact Measure.fst_compProd P κ

end SKConstants
