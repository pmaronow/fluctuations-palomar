module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.LM4b.QueryPredictability

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S71.Query
open SKConstantsOAI.ZeroTemperatureSK LM4 LM4b

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance row_W_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance row_Z_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

def queryCoefficient (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0)
    (u : (Bool × Ω) × A) : ℝ :=
  Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) *
    (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2)

theorem measurable_queryCoefficient (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0) :
    Measurable (queryCoefficient (A := A) W β s) :=
  (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
    ((measurable_actualParisiMagnetizationObservable W β s).comp
      (measurable_snd.comp measurable_fst))).const_mul _

omit [MeasurableSpace A] in
theorem queryCoefficient_bound (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0)
    (u : (Bool × Ω) × A) : ‖queryCoefficient W β s u‖ ≤ 2 := by
  have hs : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
  have hm := actualParisiMagnetizationObservable_abs_le W β s u.1.2
  change |actualParisiFullPosteriorMean W β s u.1.2| ≤ 1 at hm
  have hr : Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) ≤ 1 :=
    (Real.sqrt_le_one).mpr (actualParisiFullSusceptibilitySquareExpected_bounds W β s).2
  rw [queryCoefficient, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs]
  exact (mul_le_mul hr ((abs_sub _ _).trans (by linarith)) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 2)

theorem queryCoefficient_continuous_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) : ∀ᵐ u ∂actualRowBaseLaw W Z,
      Continuous (fun s => queryCoefficient W β s u) := by
  have hp := (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))
  filter_upwards [hp.quasiMeasurePreserving.ae
    ((actualParisiFullScalarDrift β).solution_continuous_ae W)] with u hu
  change Continuous (fun s => actualParisiFullScalarProcess W β s u.1.2) at hu
  change Continuous (fun s : ℝ≥0 =>
    Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (s : ℝ)) *
      (scalarHiddenSign u.1.1 - actualParisiFullMagnetization β (s : ℝ)
        (actualParisiFullScalarProcess W β s u.1.2)))
  have hpair := NNReal.continuous_coe.prodMk hu
  have hm := (continuous_actualParisiFullMagnetization β).comp hpair
  have hr := ((continuous_actualParisiFullSusceptibilitySquareExpected W β).comp NNReal.continuous_coe).sqrt
  exact hr.mul (continuous_const.sub hm)

def pastCoefficient (W : BrownianSystem Ω) (β : ℝ) (T s : ℝ≥0)
    (p : Bool × (ScalarContinuousPath T × ScalarContinuousPath T)) : ℝ :=
  Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) *
    (scalarHiddenSign p.1 - pastMagnetization β T s p.2.1)

theorem measurable_pastCoefficient (W : BrownianSystem Ω) (β : ℝ) (T s : ℝ≥0) :
    Measurable (pastCoefficient W β T s) :=
  (((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub
    ((measurable_pastMagnetization β T s).comp (measurable_fst.comp measurable_snd))).const_mul _

theorem pastCoefficient_version (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (T : ℝ≥0) : ∀ᵐ u ∂actualRowBaseLaw W Z, ∀ s ≤ T,
      pastCoefficient W β T s
        (u.1.1, (brownianFinitePath W T u.1.2, brownianFinitePath Z T u.2)) =
      queryCoefficient W β s u := by
  have hp := (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))
  filter_upwards [hp.quasiMeasurePreserving.ae
    (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) T)] with u hu
  intro s hs
  have hmem : (s : ℝ) ∈ Icc 0 (T : ℝ) := ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩
  simp only [pastCoefficient, queryCoefficient, pastMagnetization, IccExtend,
    Function.comp_def, projIcc_of_mem _ hmem]
  have hy := hu ⟨s, hmem⟩
  change (scalarForwardPicardPath (actualParisiFullScalarDrift β) T
    (0, brownianFinitePath W T u.1.2)) ⟨s, hmem⟩ =
      actualParisiFullScalarProcess W β s u.1.2 at hy
  rw [hy]
  rfl

theorem queryState_indep (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (C : ℕ → (Bool × Ω) × A → ℝ)
    (hpast : ∀ n, ∃ H : ℕ → Bool ×
        (ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) → ℝ,
      (∀ j, Measurable (H j)) ∧
      ∀ᵐ u ∂actualRowBaseLaw W Z, ∀ j ≤ n,
        H j (u.1.1, (brownianFinitePath W (t n) u.1.2, brownianFinitePath Z (t n) u.2)) = C j u)
    (n : ℕ) :
    IndepFun (fun u => (predictableGaussianSum (actualNoiseIncrement W Z β hβ t) C n u,
      C n u, predictableGaussianVariation (brownianMeshVariance t) C n u))
      (actualNoiseIncrement W Z β hβ t n) (actualRowBaseLaw W Z) := by
  obtain ⟨H, hmH, hH⟩ := hpast n
  let F := fun p : Bool × (ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) =>
    ((∑ j ∈ Finset.range n, H j p *
      (pastQuery W β hβ (t n) (t (j+1)) p.2 - pastQuery W β hβ (t n) (t j) p.2)),
      H n p, ∑ j ∈ Finset.range n, (H j p)^2 * (brownianMeshVariance t j : ℝ))
  have hmB (j : ℕ) : Measurable (fun p : Bool ×
      (ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) =>
        pastQuery W β hβ (t n) (t j) p.2) :=
    (measurable_pastQuery W β hβ (t n) (t j)).comp measurable_snd
  have hmF : Measurable F :=
    (Finset.measurable_fun_sum _ (fun j _ => (hmH j).mul ((hmB (j+1)).sub (hmB j)))).prodMk
      ((hmH n).prodMk (Finset.measurable_fun_sum _ (fun j _ => ((hmH j).pow_const 2).mul_const _)))
  have hi := (actualQueryIncrement_indep_rowPast W Z β hβ t ht n).comp hmF measurable_id
  apply hi.congr _ (ae_of_all _ (fun _ => rfl))
  have hp := (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).prod
    (MeasurePreserving.id Z.law)
  filter_upwards [hH, hp.quasiMeasurePreserving.ae
    (scalarOrthogonalProcesses_finite_path_version W Z
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (t n))] with u huH huB
  have hB (j : ℕ) (hj : j ≤ n) :
      pastQuery W β hβ (t n) (t j) (brownianFinitePath W (t n) u.1.2,
        brownianFinitePath Z (t n) u.2) =
      (actualParisiQueryBrownianSystem W Z β hβ).B (t j) (u.1.2, u.2) := by
    have hs : (t j : ℝ) ∈ Icc 0 (t n : ℝ) :=
      ⟨(t j).coe_nonneg, NNReal.coe_le_coe.mpr (ht hj)⟩
    simp only [pastQuery, IccExtend, Function.comp_def, projIcc_of_mem _ hs]
    exact (huB ⟨t j, hs⟩).1.symm
  change F _ = _
  dsimp only [F]
  rw [predictableGaussianSum_eq_range_sum, predictableGaussianVariation_eq_range_sum]
  apply Prod.ext
  · dsimp only
    apply Finset.sum_congr rfl
    intro j hj
    rw [huH j (Finset.mem_range.mp hj).le, hB j (Finset.mem_range.mp hj).le,
      hB (j+1) (Finset.mem_range.mp hj)]
    rfl
  · apply Prod.ext
    · exact huH n le_rfl
    · dsimp only
      apply Finset.sum_congr rfl
      intro j hj
      rw [huH j (Finset.mem_range.mp hj).le]

theorem querySum_isometry (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (C : ℕ → (Bool × Ω) × A → ℝ) (hmC : ∀ j, Measurable (C j))
    (hiC : ∀ j, Integrable (fun u => (C j u)^2) (actualRowBaseLaw W Z))
    (hpast : ∀ n, ∃ H : ℕ → Bool ×
        (ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) → ℝ,
      (∀ j, Measurable (H j)) ∧
      ∀ᵐ u ∂actualRowBaseLaw W Z, ∀ j ≤ n,
        H j (u.1.1, (brownianFinitePath W (t n) u.1.2, brownianFinitePath Z (t n) u.2)) = C j u)
    (n : ℕ) :
    MemLp (predictableGaussianSum (actualNoiseIncrement W Z β hβ t) C n) 2 (actualRowBaseLaw W Z) ∧
    (∫ u, (predictableGaussianSum (actualNoiseIncrement W Z β hβ t) C n u)^2 ∂actualRowBaseLaw W Z) =
      ∑ j : Fin n, (brownianMeshVariance t j : ℝ) * ∫ u, (C j u)^2 ∂actualRowBaseLaw W Z := by
  have hi := predictableGaussianSum_L2_isometry (actualRowBaseLaw W Z) _ C (brownianMeshVariance t)
    (actualNoiseIncrement_hasLaw W Z β hβ t ht) (fun j => (hmC j).aemeasurable) hiC
    (queryState_indep W Z β hβ t ht C hpast) n
  refine ⟨?_, hi.2.2.trans (integral_predictableGaussianVariation _ _ _ hiC n)⟩
  apply (memLp_two_iff_integrable_sq ?_).mpr hi.1
  exact (aemeasurable_predictableGaussianSum _ _ _
    (fun j => (actualNoiseIncrement_hasLaw W Z β hβ t ht j).aemeasurable)
    (fun j => (hmC j).aemeasurable) n).aestronglyMeasurable

theorem queryRowLeftSum_memLp (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    MemLp (SJ3.queryRowLeftSum W Z β hβ V l) 2 (actualRowBaseLaw W Z) := by
  change MemLp (fun u => ∑ j ∈ Finset.range (2^l),
    queryCoefficient W β ((brownianDyadicGrid V).time l j) u *
      actualNoiseIncrement W Z β hβ ((brownianDyadicGrid V).time l) j u) 2 (actualRowBaseLaw W Z)
  apply memLp_finsetSum
  intro j _
  have hd : MemLp (actualNoiseIncrement W Z β hβ ((brownianDyadicGrid V).time l) j)
      2 (actualRowBaseLaw W Z) :=
    (actualNoiseIncrement_hasLaw W Z β hβ _ ((brownianDyadicGrid V).monotone l) j).memLp
      (memLp_id_gaussianReal 2)
  apply hd.of_le_mul (c := 2)
    (((measurable_queryCoefficient W β _).aestronglyMeasurable).mul hd.aestronglyMeasurable)
  apply ae_of_all
  intro u
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (queryCoefficient_bound W β _ u) (norm_nonneg _)

theorem queryDifference_isometry (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t s v : ℕ → ℝ≥0) (ht : Monotone t)
    (hs : ∀ j, s j ≤ t j) (hv : ∀ j, v j ≤ t j) (n : ℕ) :
    (∫ u, (predictableGaussianSum (actualNoiseIncrement W Z β hβ t)
      (fun j u => queryCoefficient W β (s j) u - queryCoefficient W β (v j) u) n u)^2
        ∂actualRowBaseLaw W Z) =
      ∑ j : Fin n, (brownianMeshVariance t j : ℝ) *
        ∫ u, (queryCoefficient W β (s j) u - queryCoefficient W β (v j) u)^2
          ∂actualRowBaseLaw W Z := by
  apply (querySum_isometry W Z β hβ t ht _
    (fun j => (measurable_queryCoefficient W β _).sub (measurable_queryCoefficient W β _))
    (fun j => ?_) (fun k => ?_) n).2
  · have hm : MemLp (fun u : (Bool × Ω) × A =>
        queryCoefficient W β (s j) u - queryCoefficient W β (v j) u) 2 (actualRowBaseLaw W Z) :=
      (memLp_const (4 : ℝ)).mono'
        (((measurable_queryCoefficient W β _).sub (measurable_queryCoefficient W β _)).aestronglyMeasurable)
        (ae_of_all _ (fun u => (norm_sub_le _ _).trans (by
          linarith [queryCoefficient_bound W β (s j) u, queryCoefficient_bound W β (v j) u])))
    exact hm.integrable_sq
  · refine ⟨fun j p => pastCoefficient W β (t k) (s j) p - pastCoefficient W β (t k) (v j) p,
      (fun j => (measurable_pastCoefficient W β _ _).sub (measurable_pastCoefficient W β _ _)), ?_⟩
    filter_upwards [pastCoefficient_version W Z β (t k)] with u hu
    intro j hj
    rw [hu (s j) ((hs j).trans (ht hj)), hu (v j) ((hv j).trans (ht hj))]
    rfl

end SKConstants.Completion.S71.Query
