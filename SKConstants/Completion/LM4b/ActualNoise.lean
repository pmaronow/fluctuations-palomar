module

public import SKConstants.Completion.LM4b.ActualRowReference

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK LM4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualNoiseIncrement (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (j : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t j (u.1.2,u.2)

def actualNoiseCoefficient (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ)
    (j : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  c j * (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β (t j) u.1.2)

def actualNoise (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (k : ℕ) : (Bool × Ω) × A → ℝ :=
  predictableGaussianSum (actualNoiseIncrement W Z β hβ t) (actualNoiseCoefficient W β t c) k

def ActualQueryPredictableStateStatement
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) : Prop :=
  ∀ j, IndepFun (fun u => (actualNoise W Z β hβ t c j u,
    actualNoiseCoefficient W β t c j u,
    predictableGaussianVariation (brownianMeshVariance t) (actualNoiseCoefficient W β t c) j u))
      (actualNoiseIncrement W Z β hβ t j) (actualRowBaseLaw W Z)

theorem actualNoiseIncrement_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (j : ℕ) :
    HasLaw (actualNoiseIncrement W Z β hβ t j) (gaussianReal 0 (brownianMeshVariance t j))
      (actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  have hpair := ((measurePreserving_snd (μ:=scalarHiddenPriorBool 0) (ν:=W.law)).prod
    (MeasurePreserving.id Z.law)).hasLaw
  exact (brownianMeshIncrement_hasLaw
    (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal t ht j).comp hpair

theorem measurable_actualNoiseCoefficient (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (j : ℕ) :
    Measurable (actualNoiseCoefficient (A:=A) W β t c j) :=
  (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
    ((measurable_actualParisiMagnetizationObservable W β (t j)).comp
      (measurable_snd.comp measurable_fst))).const_mul _

theorem measurable_actualNoise (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (k : ℕ) :
    Measurable (actualNoise W Z β hβ t c k) := by
  rw [actualNoise]
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact ih.add ((measurable_actualNoiseCoefficient W β t c k).mul
      ((((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
        ((actualParisiQueryBrownianSystem W Z β hβ).measurable _)).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

theorem actualNoise_hasSubgaussianMGF_of_predictable
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ)
    (hpredictable : ActualQueryPredictableStateStatement W Z β hβ t c)
    (hbudget : ∑ j ∈ Finset.range k, (c j)^2 * (brownianMeshVariance t j : ℝ) ≤ 1) :
    HasSubgaussianMGF (actualNoise W Z β hβ t c k) 4 (actualRowBaseLaw W Z) := by
  have hm (j : ℕ) : AEMeasurable (actualNoiseCoefficient W β t c j) (actualRowBaseLaw W Z) :=
    (measurable_actualNoiseCoefficient W β t c j).aemeasurable
  have hcap (u : (Bool × Ω) × A) :
      predictableGaussianVariation (brownianMeshVariance t) (actualNoiseCoefficient W β t c) k u ≤ 4 := by
    rw [predictableGaussianVariation_eq_range_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range k, 4 * ((c j)^2 * (brownianMeshVariance t j : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        have hs : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
        have hb : |scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β (t j) u.1.2| ≤ 2 :=
          (abs_sub _ _).trans (by rw [hs]; linarith [actualParisiMagnetizationObservable_abs_le W β (t j) u.1.2])
        have hb2 : (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β (t j) u.1.2)^2 ≤ 4 := by
          simpa only [sq_abs, show (2:ℝ)^2=4 by norm_num] using
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        unfold actualNoiseCoefficient
        rw [mul_pow]
        nlinarith [mul_le_mul_of_nonneg_left hb2
          (mul_nonneg (sq_nonneg (c j)) (brownianMeshVariance t j).coe_nonneg)]
      _ = 4 * ∑ j ∈ Finset.range k, (c j)^2 * (brownianMeshVariance t j : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 := by linarith
  constructor
  · intro θ
    exact (predictableGaussianSum_mgf_bound _ _ _ _ (actualNoiseIncrement_hasLaw W Z β hβ t ht) hm
      hpredictable θ k 4 (ae_of_all _ hcap)).1
  · intro θ
    simpa only [NNReal.coe_ofNat, mul_comm (θ^2), actualNoise] using
      (predictableGaussianSum_mgf_bound _ _ _ _ (actualNoiseIncrement_hasLaw W Z β hβ t ht) hm
        hpredictable θ k 4 (ae_of_all _ hcap)).2

end SKConstants.Completion.LM4b
