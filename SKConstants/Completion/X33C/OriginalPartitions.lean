module

public import SKConstants.Completion.S71.CommonRefinement
public import SKConstants.Completion.LBase.CurvaturePast
public import SKConstants.Completion.X33C.IntegralRotation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X33C
open SKConstantsOAI.ZeroTemperatureSK S71.Mesh
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization

def rawPartitionSum {U Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient U) (t : ℕ → ℝ≥0) (N : ℕ) (u : U × Ω) : ℝ :=
  partitionSum (fun s => brownianContinuousCoefficient B H s u) (fun s => B s u.2) t N

theorem rawPartitionSum_difference_isometry {U Ω : Type*}
    [MeasurableSpace U] [MeasurableSpace Ω]
    (P : Measure U) [IsProbabilityMeasure P] (W : BrownianSystem Ω)
    (H : BrownianContinuousPastCoefficient U) (hmH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hs : Monotone s) (hM : 0 < M)
    (ht0 : t 0 = 0) (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V) :
    (∫ u, (rawPartitionSum W.B H t N u - rawPartitionSum W.B H s M u) ^ 2 ∂P.prod W.law) =
      ∑ k : Fin (N * M), (brownianMeshVariance (commonGrid t s N M V) k : ℝ) *
        ∫ u, (brownianContinuousCoefficient W.B H (commonLeft t N M V k) u -
          brownianContinuousCoefficient W.B H (commonOther t s N M V k) u) ^ 2 ∂P.prod W.law := by
  let := W.isProbability
  let c := commonGrid t s N M V
  let a := commonLeft t N M V
  let b := commonOther t s N M V
  let D : BrownianStaticPredictableCoefficient U c := fun k p =>
    H (a k) (p.1, brownianPastRestrict (commonLeft_le t s N M V k) p.2) -
      H (b k) (p.1, brownianPastRestrict (commonOther_le t s N M V k) p.2)
  have hmD (k : ℕ) : Measurable (D k) :=
    ((hmH _).comp (measurable_fst.prodMk
      ((measurable_brownianPastRestrict _).comp measurable_snd))).sub
      ((hmH _).comp (measurable_fst.prodMk
        ((measurable_brownianPastRestrict _).comp measurable_snd)))
  have hD (k : ℕ) (p : U × (Iic (c k) → ℝ)) : ‖D k p‖ ≤ 2 * C :=
    (norm_sub_le _ _).trans ((add_le_add (hC _ _) (hC _ _)).trans_eq (by ring))
  have he (u : U × Ω) :
      rawPartitionSum W.B H t N u - rawPartitionSum W.B H s M u =
        brownianStaticPredictableSum W.B c D (N * M) u := by
    rw [brownianStaticPredictableSum, predictableGaussianSum_eq_range_sum]
    exact partitionSum_difference _ _ t s N M V ht hs hM ht0 hs0 htN hsM
  simp_rw [he]
  have hi := integrable_brownianStaticCoefficient_sq_of_bounded P W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable c D hmD (2 * C) hD
  rw [(brownianStaticPredictableSum_L2_isometry P W.law W.B W.brownian.toIsPreBrownianReal
    W.measurable c (commonGrid_monotone t s N M V ht hs hM hs0 htN hsM) D hmD hi _).2.2,
    brownianStaticPredictableVariation, integral_predictableGaussianVariation _ _ _ hi]
  rfl

theorem rawPartitionSum_comparison_tendsto {U Ω : Type*}
    [MeasurableSpace U] [MeasurableSpace Ω]
    (P : Measure U) [IsProbabilityMeasure P] (W : BrownianSystem Ω)
    (H : BrownianContinuousPastCoefficient U) (hmH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod W.law,
      Continuous (fun s => brownianContinuousCoefficient W.B H s u))
    (V : ℝ≥0) (t s : ℕ → ℕ → ℝ≥0) (N M : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (hs : ∀ l, Monotone (s l)) (hM : ∀ l, 0 < M l)
    (ht0 : ∀ l, t l 0 = 0) (hs0 : ∀ l, s l 0 = 0)
    (htN : ∀ l, t l (N l) = V) (hsM : ∀ l, s l (M l) = V)
    (εt εs : ℕ → ℝ) (hεt : Tendsto εt atTop (𝓝 0)) (hεs : Tendsto εs atTop (𝓝 0))
    (htw : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ εt l)
    (hsw : ∀ l j, j < M l → (s l (j + 1) : ℝ) - s l j ≤ εs l) :
    Tendsto (fun l => ∫ u, (rawPartitionSum W.B H (t l) (N l) u -
      rawPartitionSum W.B H (s l) (M l) u) ^ 2 ∂P.prod W.law) atTop (𝓝 0) := by
  let := W.isProbability
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hV : 0 < (V : ℝ) + 1 := by positivity
  have hm (s : ℝ≥0) : AEStronglyMeasurable (brownianContinuousCoefficient W.B H s)
      (P.prod W.law) :=
    ((hmH s).comp (measurable_fst.prodMk
      ((Measurable.of_eval (fun t : Iic s => W.measurable t)).comp measurable_snd))).aestronglyMeasurable
  obtain ⟨η, hη, hsmall⟩ := expected_sq_difference_uniform_small_of_bounded (P.prod W.law)
    (brownianContinuousCoefficient W.B H) hm hc C (fun s u => hC s _) V
    (ε / ((V : ℝ) + 1)) (div_pos hε hV)
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    ((hεt.eventually (eventually_lt_nhds hη)).and (hεs.eventually (eventually_lt_nhds hη)))
  refine ⟨L, fun l hl => ?_⟩
  let c := commonGrid (t l) (s l) (N l) (M l) V
  have hcm : Monotone c := commonGrid_monotone _ _ _ _ _ (ht l) (hs l) (hM l)
    (hs0 l) (htN l) (hsM l)
  have henergy (k : Fin (N l * M l)) :
      (brownianMeshVariance c k : ℝ) *
        (∫ u, (brownianContinuousCoefficient W.B H (commonLeft (t l) (N l) (M l) V k) u -
          brownianContinuousCoefficient W.B H (commonOther (t l) (s l) (N l) (M l) V k) u) ^ 2
          ∂P.prod W.law) ≤
        (brownianMeshVariance c k : ℝ) * (ε / ((V : ℝ) + 1)) := by
    by_cases hz : (brownianMeshVariance c k : ℝ) = 0
    · simp only [hz, zero_mul, le_refl]
    · apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      have hactive : c k < c (k + 1) := by
        by_contra hn
        have he : c (k + 1) = c k := le_antisymm (le_of_not_gt hn) (hcm (Nat.le_succ _))
        exact hz (by simp only [brownianMeshVariance, he, tsub_self, NNReal.coe_zero])
      obtain ⟨ha, hb⟩ := commonTimes_le_horizon (t l) (s l) (N l) (M l) V (ht l)
        (hM l) (htN l) k k.isLt
      exact (hsmall _ ha _ hb (commonActive_close (t l) (s l) (N l) (M l) V
        (ht l) (hs l) (hM l) (hs0 l) (htN l) (hsM l) η
        (fun i hi => (htw l i hi).trans_lt (hL l hl).1)
        (fun j hj => (hsw l j hj).trans_lt (hL l hl).2) k k.isLt hactive)).le
  have hsum : (∑ k : Fin (N l * M l), (brownianMeshVariance c k : ℝ)) = V := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (brownianMeshVariance c k : ℝ))]
    simp_rw [brownianMeshVariance, NNReal.coe_sub (hcm (Nat.le_succ _))]
    rw [Finset.sum_range_sub (fun k => (c k : ℝ))]
    change (commonGrid _ _ _ _ _ _ : ℝ) - commonGrid _ _ _ _ _ _ = _
    rw [commonGrid_end, commonGrid_zero _ _ _ _ _ (hM l) (hs0 l) (ht0 l) (htN l)]
    simp only [NNReal.coe_zero, sub_zero]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  rw [rawPartitionSum_difference_isometry P W H hmH C hC (t l) (s l) (N l) (M l) V
    (ht l) (hs l) (hM l) (ht0 l) (hs0 l) (htN l) (hsM l)]
  calc
    _ ≤ ∑ k : Fin (N l * M l), (brownianMeshVariance c k : ℝ) *
        (ε / ((V : ℝ) + 1)) := Finset.sum_le_sum (fun k _ => henergy k)
    _ = (V : ℝ) * (ε / ((V : ℝ) + 1)) := by rw [← Finset.sum_mul, hsum]
    _ < ε := by rw [← mul_div_assoc]; exact (div_lt_iff₀ hV).mpr (by nlinarith)

def defectPastCoefficient (β : ℝ) : BrownianContinuousPastCoefficient Bool :=
  fun s u => scalarHiddenSign u.1 - actualParisiFullMagnetization β s
    (LBase.rawPastField (actualParisiFullScalarDrift β) s u.2)

theorem measurable_defectPastCoefficient (β : ℝ) (s : ℝ≥0) :
    Measurable (defectPastCoefficient β s) := by
  exact ((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub
    ((continuous_actualParisiFullMagnetization β).measurable.comp
      (measurable_const.prodMk ((LBase.measurable_rawPastField _ s).comp measurable_snd)))

theorem defectPastCoefficient_bound (β : ℝ) (s : ℝ≥0) (p : Bool × (Iic s → ℝ)) :
    ‖defectPastCoefficient β s p‖ ≤ 2 := by
  have hx : |scalarHiddenSign p.1| = 1 := by cases p.1 <;> norm_num [scalarHiddenSign]
  change |scalarHiddenSign p.1 - actualParisiFullMagnetization β s
    (LBase.rawPastField (actualParisiFullScalarDrift β) s p.2)| ≤ 2
  exact (abs_sub _ _).trans (by
    rw [hx]
    linarith [(actualParisiFullMagnetization_curvature_bounds β (s : ℝ)
      (LBase.rawPastField (actualParisiFullScalarDrift β) s p.2)).1])

theorem defectPastCoefficient_actual (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law, ∀ s : ℝ≥0,
      brownianContinuousCoefficient W.B (defectPastCoefficient β) s u =
        scalarHiddenSign u.1 - actualParisiFullPosteriorMean W β s u.2 := by
  let := W.isProbability
  filter_upwards [(measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).quasiMeasurePreserving.ae
    (LBase.rawPastField_actual W (actualParisiFullScalarDrift β))] with u hu
  intro s
  change scalarHiddenSign u.1 - actualParisiFullMagnetization β s
    (LBase.rawPastField (actualParisiFullScalarDrift β) s (fun t => W.B t.1 u.2)) = _
  rw [hu s]
  rfl

def originalPartitionSum {A : Type*} (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (N : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  partitionSum (fun s => scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2)
    (fun s => W.B s u.1.2) t N

theorem rawPartitionSum_actual (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law, ∀ t N,
      rawPartitionSum W.B (defectPastCoefficient β) t N u =
        originalPartitionSum W β t N (u, ()) := by
  filter_upwards [defectPastCoefficient_actual W β] with u hu
  intro t N
  unfold rawPartitionSum originalPartitionSum partitionSum
  simp_rw [hu]

theorem rawPartitionSum_memLp (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) :
    MemLp (rawPartitionSum W.B (defectPastCoefficient β) t N) 2
      ((scalarHiddenPriorBool 0).prod W.law) := by
  let := W.isProbability
  have h := memLp_brownianStaticPredictableSum (scalarHiddenPriorBool 0) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable t ht
    (brownianContinuousMeshCoefficient (defectPastCoefficient β) t)
    (fun k => measurable_defectPastCoefficient β (t k)) 2
    (fun k p => defectPastCoefficient_bound β (t k) p) N
  have he : rawPartitionSum W.B (defectPastCoefficient β) t N =
      brownianStaticPredictableSum W.B t
        (brownianContinuousMeshCoefficient (defectPastCoefficient β) t) N := by
    funext u
    rw [brownianStaticPredictableSum, predictableGaussianSum_eq_range_sum]
    rfl
  rw [he]
  exact h

theorem measurable_originalPartitionSum {A : Type*} [MeasurableSpace A]
    (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (N : ℕ) :
    Measurable (originalPartitionSum (A := A) W β t N) := by
  unfold originalPartitionSum partitionSum
  apply Finset.measurable_fun_sum
  intro k _
  exact (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
    ((measurable_actualParisiFullPosteriorMean W β _).comp (measurable_snd.comp measurable_fst))).mul
    (((W.measurable _).sub (W.measurable _)).comp (measurable_snd.comp measurable_fst))

theorem originalPartitionSum_memLp {A : Type*} [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) :
    MemLp (originalPartitionSum (A := A) W β t N) 2 (LM4.actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  have he := (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
    (ν := Z.law)).quasiMeasurePreserving.ae (rawPartitionSum_actual W β)
  exact ((rawPartitionSum_memLp W β t ht N).comp_fst Z.law).ae_eq
    (he.mono (fun u hu => hu t N))

theorem originalPartitionSum_comparison_tendsto {A : Type*} [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ)
    (V : ℝ≥0) (t s : ℕ → ℕ → ℝ≥0) (N M : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (hs : ∀ l, Monotone (s l)) (hM : ∀ l, 0 < M l)
    (ht0 : ∀ l, t l 0 = 0) (hs0 : ∀ l, s l 0 = 0)
    (htN : ∀ l, t l (N l) = V) (hsM : ∀ l, s l (M l) = V)
    (εt εs : ℕ → ℝ) (hεt : Tendsto εt atTop (𝓝 0)) (hεs : Tendsto εs atTop (𝓝 0))
    (htw : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ εt l)
    (hsw : ∀ l j, j < M l → (s l (j + 1) : ℝ) - s l j ≤ εs l) :
    Tendsto (fun l => ∫ u, (originalPartitionSum W β (t l) (N l) u -
      originalPartitionSum W β (s l) (M l) u) ^ 2 ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  have hc : ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law,
      Continuous (fun v => brownianContinuousCoefficient W.B (defectPastCoefficient β) v u) := by
    filter_upwards [defectPastCoefficient_actual W β,
      (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).quasiMeasurePreserving.ae
        (S33aB.posterior_continuous_ae W β)] with u hu hc
    convert continuous_const.sub hc using 1
    funext s
    exact hu s
  have h := rawPartitionSum_comparison_tendsto (scalarHiddenPriorBool 0) W
    (defectPastCoefficient β) (measurable_defectPastCoefficient β) 2
    (defectPastCoefficient_bound β) hc V t s N M ht hs hM ht0 hs0 htN hsM
    εt εs hεt hεs htw hsw
  have he (l : ℕ) :
      (∫ u, (originalPartitionSum W β (t l) (N l) u -
        originalPartitionSum W β (s l) (M l) u) ^ 2 ∂LM4.actualRowBaseLaw W Z) =
      ∫ u, (rawPartitionSum W.B (defectPastCoefficient β) (t l) (N l) u -
        rawPartitionSum W.B (defectPastCoefficient β) (s l) (M l) u) ^ 2
          ∂(scalarHiddenPriorBool 0).prod W.law := by
    calc
      _ = ∫ u : (Bool × Ω) × A,
          (rawPartitionSum W.B (defectPastCoefficient β) (t l) (N l) u.1 -
            rawPartitionSum W.B (defectPastCoefficient β) (s l) (M l) u.1) ^ 2
              ∂LM4.actualRowBaseLaw W Z := by
        apply integral_congr_ae
        filter_upwards [(measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
          (ν := Z.law)).quasiMeasurePreserving.ae (rawPartitionSum_actual W β)] with u hu
        rw [hu (t l) (N l), hu (s l) (M l)]
        rfl
      _ = _ := by
        simpa only [LM4.actualRowBaseLaw, probReal_univ, one_smul] using
          integral_fun_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
            (fun u => (rawPartitionSum W.B (defectPastCoefficient β) (t l) (N l) u -
              rawPartitionSum W.B (defectPastCoefficient β) (s l) (M l) u) ^ 2)
  simpa only [he] using h

end SKConstants.Completion.X33C
