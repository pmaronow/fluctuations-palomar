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

namespace SKConstants.Completion.S31
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

theorem queryRowLeftSum_refinement (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l d : ℕ) (u : (Bool × Ω) × A) :
    SJ3.queryRowLeftSum W Z β hβ V l u =
      ∑ i ∈ Finset.range (2^(l+d)),
        queryCoefficient W β ((brownianDyadicGrid V).time l (i/2^d)) u *
          actualNoiseIncrement W Z β hβ ((brownianDyadicGrid V).time (l+d)) i u := by
  let F := fun a => queryCoefficient W β ((brownianDyadicGrid V).time l a) u
  let M := fun i => (actualParisiQueryBrownianSystem W Z β hβ).B
    ((brownianDyadicGrid V).time (l+d) i) (u.1.2, u.2)
  calc
    _ = ∑ a ∈ Finset.range (2^l), F a * (M ((a+1)*2^d) - M (a*2^d)) := by
      simp only [F, M, ScalarDyadicNestedGrid.embed]
      rfl
    _ = ∑ i ∈ Finset.range ((2^l)*2^d), F (i/2^d) * (M (i+1) - M i) :=
      sum_weighted_refinement F M _ _ (by positivity)
    _ = _ := by rw [pow_add]; rfl

theorem queryRowLeftSum_difference_isometry (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (m l : ℕ) :
    (∫ u, (SJ3.queryRowLeftSum W Z β hβ V m u -
      SJ3.queryRowLeftSum W Z β hβ V l u)^2 ∂actualRowBaseLaw W Z) =
      ∑ i : Fin (2^(m+l)), (brownianMeshVariance ((brownianDyadicGrid V).time (m+l)) i : ℝ) *
        ∫ u, (queryCoefficient W β ((brownianDyadicGrid V).time m (i/2^l)) u -
          queryCoefficient W β ((brownianDyadicGrid V).time l (i/2^m)) u)^2 ∂actualRowBaseLaw W Z := by
  have he (u : (Bool × Ω) × A) :
      SJ3.queryRowLeftSum W Z β hβ V m u - SJ3.queryRowLeftSum W Z β hβ V l u =
        predictableGaussianSum (actualNoiseIncrement W Z β hβ ((brownianDyadicGrid V).time (m+l)))
          (fun i u => queryCoefficient W β ((brownianDyadicGrid V).time m (i/2^l)) u -
            queryCoefficient W β ((brownianDyadicGrid V).time l (i/2^m)) u) (2^(m+l)) u := by
    have hm := queryRowLeftSum_refinement W Z β hβ V m l u
    have hl := queryRowLeftSum_refinement W Z β hβ V l m u
    rw [Nat.add_comm l m] at hl
    rw [hm, hl, predictableGaussianSum_eq_range_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  exact queryDifference_isometry W Z β hβ _ _ _ ((brownianDyadicGrid V).monotone (m+l))
    (fun j => (brownianDyadicGrid V).left_le m l j)
    (fun j => by simpa only [Nat.add_comm l m] using (brownianDyadicGrid V).left_le l m j) _

theorem queryRowLeftSum_L2_cauchy (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N,
      (∫ u, (SJ3.queryRowLeftSum W Z β hβ V m u -
        SJ3.queryRowLeftSum W Z β hβ V l u)^2 ∂actualRowBaseLaw W Z) < ε := by
  intro ε hε
  have hV : 0 < (V : ℝ)+1 := by positivity
  obtain ⟨η, hη, hsmall⟩ := expected_sq_difference_uniform_small_of_bounded (actualRowBaseLaw W Z)
    (queryCoefficient W β) (fun s => (measurable_queryCoefficient W β s).aestronglyMeasurable)
    (queryCoefficient_continuous_ae W Z β) 2 (queryCoefficient_bound W β) V
    (ε / ((V : ℝ)+1)) (div_pos hε hV)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((brownianDyadicWidth_tendsto V).eventually (eventually_lt_nhds (half_pos hη)))
  refine ⟨N, fun m hm l hl => ?_⟩
  have henergy (i : Fin (2^(m+l))) :
      (∫ u, (queryCoefficient W β ((brownianDyadicGrid V).time m (i/2^l)) u -
        queryCoefficient W β ((brownianDyadicGrid V).time l (i/2^m)) u)^2 ∂actualRowBaseLaw W Z) ≤
          ε / ((V : ℝ)+1) := by
    let s := (brownianDyadicGrid V).time m (i/2^l)
    let t := (brownianDyadicGrid V).time l (i/2^m)
    let v := (brownianDyadicGrid V).time (m+l) i
    have hv : v ≤ V := by
      simpa only [brownianDyadicGrid_horizon] using
        (brownianDyadicGrid V).le_duration (k := 1) (by simpa only [one_mul] using i.isLt.le)
    have hs : s ≤ V := ((brownianDyadicGrid V).left_le m l i).trans hv
    have ht : t ≤ V := (show t ≤ v from by
      simpa only [Nat.add_comm l m] using (brownianDyadicGrid V).left_le l m i).trans hv
    have hvs : |(v : ℝ)-s| ≤ brownianDyadicWidth V m := brownianDyadicGrid_left_le V m l i
    have hvt : |(v : ℝ)-t| ≤ brownianDyadicWidth V l := by
      simpa only [Nat.add_comm l m] using brownianDyadicGrid_left_le V l m i
    have hst : |(s : ℝ)-t| < η := by
      have htri := abs_sub_le (s : ℝ) v t
      rw [abs_sub_comm (s : ℝ) v] at htri
      have hnm := hN m hm
      have hnl := hN l hl
      linarith
    exact (hsmall s hs t ht hst).le
  rw [queryRowLeftSum_difference_isometry]
  calc
    _ ≤ ∑ i : Fin (2^(m+l)),
        (brownianMeshVariance ((brownianDyadicGrid V).time (m+l)) i : ℝ) * (ε/((V : ℝ)+1)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (henergy i) (NNReal.coe_nonneg _))
    _ = (V : ℝ) * (ε/((V : ℝ)+1)) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        (brownianMeshVariance ((brownianDyadicGrid V).time (m+l)) i : ℝ))]
      simpa only [one_mul, brownianDyadicGrid_horizon] using (brownianDyadicGrid V).variance_sum 1 (m+l)
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hV).mpr
      nlinarith

theorem queryRowIntegral_exists (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∃ Q, SJ3.IsQueryRowIntegral W Z β hβ V Q := by
  let X := SJ3.queryRowLeftSum W Z β hβ V
  let μ := actualRowBaseLaw W Z
  have hmem (l : ℕ) : MemLp (X l) 2 μ := queryRowLeftSum_memLp W Z β hβ V l
  let F : ℕ → Lp ℝ 2 μ := fun l => (hmem l).toLp (X l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := queryRowLeftSum_L2_cauchy W Z β hβ V (ε^2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm l hl => ?_⟩
    have hd : dist (F m) (F l)^2 = ∫ u, (X m u-X l u)^2 ∂μ := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral (hmem m) (hmem l)
    have hb := hN m hm l hl
    change (∫ u, (X m u-X l u)^2 ∂μ) < ε^2 at hb
    rw [← hd] at hb
    nlinarith [dist_nonneg (x := F m) (y := F l)]
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hcauchy
  let Q := (Lp.memLp J).aestronglyMeasurable.mk (fun u => J u)
  have hJQ : (fun u => J u) =ᵐ[μ] Q := (Lp.memLp J).aestronglyMeasurable.ae_eq_mk
  refine ⟨Q, (Lp.memLp J).aestronglyMeasurable.measurable_mk,
    (Lp.memLp J).ae_eq hJQ, ?_, ?_⟩
  · intro l
    exact (((hmem l).sub (Lp.memLp J)).integrable_sq).congr
      (hJQ.mono (fun u hu => by
        change J u = Q u at hu
        dsimp only [X, Pi.sub_apply]
        rw [hu]))
  · have hn : Tendsto (fun l => ‖F l-J‖^2) atTop (𝓝 0) := by
      simpa using ((hJ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => J) atTop (𝓝 J))).norm).pow 2
    convert hn using 1
    funext l
    calc
      _ = ∫ u, (X l u-J u)^2 ∂μ := integral_congr_ae (hJQ.mono (fun u hu => by
        change J u = Q u at hu
        dsimp only [X, Pi.sub_apply]
        rw [hu]))
      _ = _ := (norm_toLp_sub_sq_eq_integral (hmem l) J).symm

theorem queryRowIntegralExists_holds : Blueprint5a.QueryRowIntegralExistsStatement := by
  intro Ω A _ _ W Z β hβ V
  exact queryRowIntegral_exists W Z β hβ V

theorem jointRowIntegral_exists (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∃ Zv, Blueprint4.IsJointRowIntegral W Z β hβ V Zv :=
  (SJ3.jointRowIntegral_exists_iff_query W Z β hβ V).mpr (queryRowIntegral_exists W Z β hβ V)

theorem queryRowIntegral_unique (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {Q R : (Bool × Ω) × A → ℝ}
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q) (hR : SJ3.IsQueryRowIntegral W Z β hβ V R) :
    Q =ᵐ[actualRowBaseLaw W Z] R :=
  SJ3.meanSquare_limit_unique (SJ3.measurable_queryRowLeftSum W Z β hβ V)
    hQ.2.1 hR.2.1 hQ.2.2.1 hQ.2.2.2 hR.2.2.2

theorem queryRowIntegral_unique_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {Q R : (Bool × Ω) × A → ℝ}
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q) (hR : SJ3.IsQueryRowIntegral W Z β hβ V R) :
    Q =ᵐ[actualParisiFullQuerySpinLaw W Z β V] R :=
  (SJ3.rowLinked_absolutelyContinuous W Z β V).ae_eq (queryRowIntegral_unique W Z β hβ V hQ hR)

end SKConstants.Completion.S31
