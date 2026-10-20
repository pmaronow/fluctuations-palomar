module

public import SKConstants.Completion.SJ3.Versions
public import SKConstants.Completion.SJ3.PotentialIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ3
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance joint_W_isProbability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance joint_Z_isProbability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem meanSquare_linearCombination {U : Type*} [MeasurableSpace U] {μ : Measure U}
    {F G : ℕ → U → ℝ} {X Y : U → ℝ}
    (hF : ∀ l, MemLp (F l) 2 μ) (hG : ∀ l, MemLp (G l) 2 μ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hFlim : Tendsto (fun l => ∫ u, (F l u - X u) ^ 2 ∂μ) atTop (𝓝 0))
    (hGlim : Tendsto (fun l => ∫ u, (G l u - Y u) ^ 2 ∂μ) atTop (𝓝 0)) (a b : ℝ) :
    Tendsto (fun l => ∫ u, (a * F l u + b * G l u - (a * X u + b * Y u)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hFi (l : ℕ) : Integrable (fun u => (F l u - X u) ^ 2) μ := ((hF l).sub hX).integrable_sq
  have hGi (l : ℕ) : Integrable (fun u => (G l u - Y u) ^ 2) μ := ((hG l).sub hY).integrable_sq
  have hI (l : ℕ) : Integrable (fun u => (a * F l u + b * G l u - (a * X u + b * Y u)) ^ 2) μ :=
    ((((hF l).const_mul a).add ((hG l).const_mul b)).sub
      ((hX.const_mul a).add (hY.const_mul b))).integrable_sq
  apply squeeze_zero (fun l => integral_nonneg (fun _ => sq_nonneg _)) (fun l => ?_)
    (by simpa using (hFlim.const_mul (2 * a ^ 2)).add (hGlim.const_mul (2 * b ^ 2)))
  have hdom : Integrable (fun u => 2 * a ^ 2 * (F l u - X u) ^ 2 +
      2 * b ^ 2 * (G l u - Y u) ^ 2) μ :=
    ((hFi l).const_mul (2 * a ^ 2)).add ((hGi l).const_mul (2 * b ^ 2))
  have hh := integral_mono (hI l) hdom (fun u => by
    nlinarith [sq_nonneg (a * (F l u - X u) - b * (G l u - Y u))])
  simpa only [integral_add ((hFi l).const_mul (2 * a ^ 2)) ((hGi l).const_mul (2 * b ^ 2)),
    integral_const_mul] using hh

def queryRowLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β ((brownianDyadicGrid V).time l k)) *
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k) u.1.2) *
      ((actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l (k + 1)) (u.1.2, u.2) -
        (actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l k) (u.1.2, u.2))

theorem jointRowLeftSum_split (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) :
    jointRowLeftSum W Z β hβ V l u =
      β * potentialLeftSum W β V l u.1 + queryRowLeftSum W Z β hβ V l u := by
  simp only [jointRowLeftSum, potentialLeftSum, queryRowLeftSum,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem measurable_queryRowLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    Measurable (queryRowLeftSum W Z β hβ V l) := by
  have he : queryRowLeftSum W Z β hβ V l = fun u => jointRowLeftSum W Z β hβ V l u -
      β * potentialLeftSum W β V l u.1 := by
    funext u
    rw [jointRowLeftSum_split]
    ring
  rw [he]
  exact (measurable_jointRowLeftSum W Z β hβ V l).sub
    (((measurable_potentialLeftSum W β V l).comp measurable_fst).const_mul β)

def IsQueryRowIntegral (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (Q : (Bool × Ω) × A → ℝ) : Prop :=
  Measurable Q ∧ MemLp Q 2 (LM4.actualRowBaseLaw W Z) ∧
    (∀ l, Integrable (fun u => (queryRowLeftSum W Z β hβ V l u - Q u) ^ 2) (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, (queryRowLeftSum W Z β hβ V l u - Q u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0)

theorem potentialLeftSum_tendsto_L2_base (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∀ l, Integrable (fun u : (Bool × Ω) × A =>
      (potentialLeftSum W β V l u.1 - potentialIntegral W β hβ V u.1) ^ 2) (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u : (Bool × Ω) × A,
      (potentialLeftSum W β V l u.1 - potentialIntegral W β hβ V u.1) ^ 2
        ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  obtain ⟨hi, hl⟩ := potentialLeftSum_tendsto_L2 W β hβ V
  refine ⟨fun l => (hi l).comp_fst Z.law, ?_⟩
  have he (l : ℕ) : (∫ u : (Bool × Ω) × A,
      (potentialLeftSum W β V l u.1 - potentialIntegral W β hβ V u.1) ^ 2
        ∂LM4.actualRowBaseLaw W Z) =
      ∫ u, (potentialLeftSum W β V l u - potentialIntegral W β hβ V u) ^ 2
        ∂(scalarHiddenPriorBool 0).prod W.law := by
    simpa only [LM4.actualRowBaseLaw, probReal_univ, one_smul] using
      integral_fun_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
        (fun u => (potentialLeftSum W β V l u - potentialIntegral W β hβ V u) ^ 2)
  simp_rw [he]
  exact hl

theorem jointRowIntegral_of_query (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {Q : (Bool × Ω) × A → ℝ}
    (hQ : IsQueryRowIntegral W Z β hβ V Q) :
    IsJointRowIntegral W Z β hβ V (fun u => β * potentialIntegral W β hβ V u.1 + Q u) := by
  have hP : MemLp (fun u : (Bool × Ω) × A => potentialIntegral W β hβ V u.1)
      2 (LM4.actualRowBaseLaw W Z) := (potentialIntegral_memLp W β hβ V).comp_fst Z.law
  have hPs (l : ℕ) : MemLp (fun u : (Bool × Ω) × A => potentialLeftSum W β V l u.1)
      2 (LM4.actualRowBaseLaw W Z) := (potentialLeftSum_memLp W β hβ V l).comp_fst Z.law
  have hQs (l : ℕ) : MemLp (queryRowLeftSum W Z β hβ V l) 2 (LM4.actualRowBaseLaw W Z) := by
    have he : MemLp (fun u => queryRowLeftSum W Z β hβ V l u - Q u) 2 (LM4.actualRowBaseLaw W Z) :=
      (memLp_two_iff_integrable_sq (((measurable_queryRowLeftSum W Z β hβ V l).aemeasurable.sub
        hQ.2.1.aemeasurable).aestronglyMeasurable)).mpr (hQ.2.2.1 l)
    convert he.add hQ.2.1 using 1
    funext u
    simp only [Pi.add_apply, sub_add_cancel]
  have hT : MemLp (fun u : (Bool × Ω) × A => β * potentialIntegral W β hβ V u.1 + Q u)
      2 (LM4.actualRowBaseLaw W Z) := (hP.const_mul β).add hQ.2.1
  refine ⟨(((measurable_potentialIntegral W β hβ V).comp measurable_fst).const_mul β).add hQ.1,
    hT, ?_, ?_⟩
  · intro l
    simp only [jointRowLeftSum_split]
    exact ((((hPs l).const_mul β).add (hQs l)).sub hT).integrable_sq
  · have hh := meanSquare_linearCombination hPs hQs hP hQ.2.1
      (potentialLeftSum_tendsto_L2_base W Z β hβ V).2 hQ.2.2.2 β 1
    simpa only [jointRowLeftSum_split, one_mul] using hh

theorem queryRowIntegral_of_joint (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {Zv : (Bool × Ω) × A → ℝ}
    (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    IsQueryRowIntegral W Z β hβ V (fun u => Zv u - β * potentialIntegral W β hβ V u.1) := by
  have hP : MemLp (fun u : (Bool × Ω) × A => potentialIntegral W β hβ V u.1)
      2 (LM4.actualRowBaseLaw W Z) := (potentialIntegral_memLp W β hβ V).comp_fst Z.law
  have hPs (l : ℕ) : MemLp (fun u : (Bool × Ω) × A => potentialLeftSum W β V l u.1)
      2 (LM4.actualRowBaseLaw W Z) := (potentialLeftSum_memLp W β hβ V l).comp_fst Z.law
  have hS (l : ℕ) : MemLp (jointRowLeftSum W Z β hβ V l) 2 (LM4.actualRowBaseLaw W Z) := by
    have he : MemLp (fun u => jointRowLeftSum W Z β hβ V l u - Zv u) 2 (LM4.actualRowBaseLaw W Z) :=
      (memLp_two_iff_integrable_sq (((measurable_jointRowLeftSum W Z β hβ V l).aemeasurable.sub
        hZv.2.1.aemeasurable).aestronglyMeasurable)).mpr (hZv.2.2.1 l)
    convert he.add hZv.2.1 using 1
    funext u
    simp only [Pi.add_apply, sub_add_cancel]
  have hsub (l : ℕ) : queryRowLeftSum W Z β hβ V l = fun u =>
      jointRowLeftSum W Z β hβ V l u - β * potentialLeftSum W β V l u.1 := by
    funext u
    rw [jointRowLeftSum_split]
    ring
  have hQs (l : ℕ) : MemLp (queryRowLeftSum W Z β hβ V l) 2 (LM4.actualRowBaseLaw W Z) := by
    rw [hsub]
    exact (hS l).sub ((hPs l).const_mul β)
  have hT : MemLp (fun u : (Bool × Ω) × A => Zv u - β * potentialIntegral W β hβ V u.1)
      2 (LM4.actualRowBaseLaw W Z) := hZv.2.1.sub (hP.const_mul β)
  refine ⟨hZv.1.sub (((measurable_potentialIntegral W β hβ V).comp measurable_fst).const_mul β),
    hT, fun l => ((hQs l).sub hT).integrable_sq, ?_⟩
  have hh := meanSquare_linearCombination hS hPs hZv.2.1 hP hZv.2.2.2
    (potentialLeftSum_tendsto_L2_base W Z β hβ V).2 1 (-β)
  simpa only [hsub, one_mul, neg_mul, ← sub_eq_add_neg] using hh

theorem jointRowIntegral_exists_iff_query (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∃ Zv, IsJointRowIntegral W Z β hβ V Zv) ↔ ∃ Q, IsQueryRowIntegral W Z β hβ V Q := by
  constructor
  · rintro ⟨Zv, hZv⟩
    exact ⟨_, queryRowIntegral_of_joint W Z β hβ V hZv⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨_, jointRowIntegral_of_query W Z β hβ V hQ⟩

end SKConstants.Completion.SJ3
