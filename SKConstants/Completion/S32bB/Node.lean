module

public import SKConstants.Completion.S32bB.Potential

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S32bB
open SKConstantsOAI.ZeroTemperatureSK Blueprint5a

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem supportPotential_lipschitz (β : ℝ) (hβ : 1 < β) :
    LipschitzWith 1 (parisiPhysicalValue β (parisiEquilibriumMeasure β)
      (parisiEquilibriumPhysicalEndpoint β)) := by
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have hv : (parisiEquilibriumPhysicalEndpoint β : ℝ) ∈ Icc (0 : ℝ) (β ^ 2) := by
    refine ⟨NNReal.coe_nonneg _, ?_⟩
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact (mul_le_mul_of_nonneg_left
      (parisiEquilibriumSupportEndpoint_spec β hβ).1.2.le (sq_nonneg β)).trans_eq (mul_one _)
  have hh := parisiPhysicalValue_spatial_derivatives β hb (parisiEquilibriumMeasure β) _ hv
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hh.1 x).differentiableAt)
  intro x
  rw [(hh.1 x).deriv]
  exact_mod_cast (hh.2.2 x).1

theorem memLp_comp_real_lipschitz {U : Type*} [MeasurableSpace U] (μ : Measure U)
    [IsFiniteMeasure μ] {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {Y : U → ℝ} (hY : MemLp Y 2 μ) : MemLp (fun u => f (Y u)) 2 μ := by
  apply ((hY.norm.const_mul (K : ℝ)).add (memLp_const |f 0|)).mono'
    (hf.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable)
  filter_upwards [] with u
  have hh := hf.norm_sub_le (Y u) 0
  simp only [Real.norm_eq_abs, sub_zero] at hh
  have ht := abs_add_le (f (Y u) - f 0) (f 0)
  rw [sub_add_cancel] at ht
  simp only [Real.norm_eq_abs, Pi.add_apply]
  linarith

theorem measurable_supportFieldLeftSum (W : BrownianSystem Ω) (β : ℝ) (l : ℕ) :
    Measurable (supportFieldLeftSum (A := A) W β l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact (((measurable_of_finite scalarHiddenSign).comp
    (measurable_fst.comp measurable_fst)).sub
      ((measurable_actualParisiFullPosteriorMean W β _).comp
        (measurable_snd.comp measurable_fst))).mul
          (((W.measurable _).sub (W.measurable _)).comp (measurable_snd.comp measurable_fst))

theorem measurable_supportFieldTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Measurable (supportFieldTarget (A := A) W β hβ) := by
  have hy : Measurable (fun u : Bool × Ω => actualParisiFullScalarProcess W β
      (parisiEquilibriumPhysicalEndpoint β) u.2) :=
    ((actualParisiFullScalarDrift β).solution_measurable W
      (parisiEquilibriumPhysicalEndpoint β)).comp measurable_snd
  have hU := (supportPotential_lipschitz β hβ).continuous.measurable.comp hy
  have hS := ((LJ.measurable_actualRowPotential W β
    (parisiEquilibriumPhysicalEndpoint β)).const_mul
      (β ^ 2 * actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β)))
  have hx : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_fst
  have hP : Measurable (LJ.supportPotentialPrimitive W β) :=
    (((hS.add (hx.mul hy)).sub hU).add_const _)
  exact (hP.sub ((SJ3.measurable_potentialIntegral W β hβ _).const_mul (β ^ 2))).comp measurable_fst

theorem supportFieldTarget_memLp_pair (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    MemLp (fun u : Bool × Ω => LJ.supportPotentialPrimitive W β u -
      β ^ 2 * SJ3.potentialIntegral W β hβ (parisiEquilibriumPhysicalEndpoint β) u)
      2 ((scalarHiddenPriorBool 0).prod W.law) := by
  let := W.isProbability
  let S := parisiEquilibriumPhysicalEndpoint β
  have hy : MemLp (fun u : Bool × Ω => actualParisiFullScalarProcess W β S u.2) 2
      ((scalarHiddenPriorBool 0).prod W.law) :=
    (solution_memLp W (actualParisiFullScalarDrift β) S 2 (by norm_num)).comp_snd _
  have hxy : MemLp (fun u : Bool × Ω => scalarHiddenSign u.1 *
      actualParisiFullScalarProcess W β S u.2) 2 ((scalarHiddenPriorBool 0).prod W.law) := by
    apply hy.norm.mono' (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul
      (((actualParisiFullScalarDrift β).solution_measurable W S).comp measurable_snd)).aestronglyMeasurable
    filter_upwards [] with u
    dsimp only [Pi.mul_apply, Function.comp_apply]
    simp only [Real.norm_eq_abs, abs_mul]
    have hs : |scalarHiddenSign u.1| = 1 := by cases u.1 <;> norm_num [scalarHiddenSign]
    rw [hs, one_mul]
    exact le_rfl
  have hU := memLp_comp_real_lipschitz _ (supportPotential_lipschitz β hβ) hy
  have hA : MemLp (LJ.actualRowPotential W β S) 2 ((scalarHiddenPriorBool 0).prod W.law) :=
    (memLp_const (2 : ℝ)).mono' (LJ.measurable_actualRowPotential W β S).aestronglyMeasurable
      (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using SJ3.actualRowPotential_bound W β S u))
  have hPrim := (((hA.const_mul (β ^ 2 * actualParisiFullSusceptibilityExpected W β S)).add
    hxy).sub hU).add (memLp_const (parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0))
  exact hPrim.sub ((SJ3.potentialIntegral_memLp W β hβ S).const_mul (β ^ 2))

theorem supportFieldTarget_memLp (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) : MemLp (supportFieldTarget W β hβ) 2 (LM4.actualRowBaseLaw W Z) := by
  let := Z.isProbability
  exact (supportFieldTarget_memLp_pair W β hβ).comp_fst Z.law

theorem supportFieldLeftSum_memLp (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (l : ℕ) : MemLp (supportFieldLeftSum W β l) 2 (LM4.actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  apply memLp_finsetSum
  intro k _
  have hb : MemLp (fun u : (Bool × Ω) × A =>
      W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1)) u.1.2 -
        W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2)
      2 (LM4.actualRowBaseLaw W Z) :=
    (((W.brownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_sub
      (s := (brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1))
      (t := (brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k)).memLp_two).comp_snd
        (scalarHiddenPriorBool 0)).comp_fst Z.law
  apply (hb.norm.const_mul 2).mono'
  · exact (((((measurable_of_finite scalarHiddenSign).comp
      (measurable_fst.comp measurable_fst)).sub
        ((measurable_actualParisiFullPosteriorMean W β _).comp
          (measurable_snd.comp measurable_fst))).mul
            (((W.measurable _).sub (W.measurable _)).comp
              (measurable_snd.comp measurable_fst))).aestronglyMeasurable)
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_mul]
    have hs : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
    have hm := abs_actualParisiFullPosteriorMean_le W β
      ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2
    have hcoef := (abs_sub _ _).trans (add_le_add (le_of_eq hs) hm)
    exact mul_le_mul_of_nonneg_right (by linarith : |scalarHiddenSign u.1.1 -
      actualParisiFullPosteriorMean W β
        ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2| ≤ 2)
      (abs_nonneg _)

theorem supportFieldIto_integrable (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (l : ℕ) :
    Integrable (fun u => (supportFieldLeftSum W β l u - supportFieldTarget W β hβ u) ^ 2)
      (LM4.actualRowBaseLaw W Z) :=
  ((supportFieldLeftSum_memLp W Z β l).sub (supportFieldTarget_memLp W Z β hβ)).integrable_sq

omit [MeasurableSpace A] in
theorem fullScalar_sde (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, ∀ V : ℝ≥0, actualParisiFullScalarProcess W β V w = W.B V w +
      ∫ s in (0 : ℝ)..(V : ℝ), (actualParisiFullScalarDrift β).f s.toNNReal
        (actualParisiFullScalarProcess W β s.toNNReal w) := by
  filter_upwards [W.driver_indistinguishable] with w hw V
  change (actualParisiFullScalarDrift β).solution W.driver V w = _
  rw [(actualParisiFullScalarDrift β).solution_eq _ W.driver_progressive, hw V]
  rfl

omit [MeasurableSpace A] in
theorem fullScalar_zero (W : BrownianSystem Ω) (β : ℝ) (w : Ω) :
    actualParisiFullScalarProcess W β 0 w = 0 :=
  (actualParisiFullScalarDrift β).solution_zero W w

omit [MeasurableSpace A] in
theorem supportFieldTarget_expansion (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (u : (Bool × Ω) × A) :
    supportFieldTarget W β hβ u =
      scalarHiddenSign u.1.1 * actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) u.1.2 -
        parisiPhysicalValue β (parisiEquilibriumMeasure β) (parisiEquilibriumPhysicalEndpoint β)
          (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) u.1.2) +
        parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 +
        β ^ 2 * actualParisiFullSusceptibilityExpected W β 0 * LJ.actualRowPotential W β 0 u.1 -
        β ^ 2 * ∫ t in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
          LJ.actualRowPotential W β t.toNNReal u.1 ∂(SJ3.negativeSusceptibility W β hβ).measure := by
  unfold supportFieldTarget LJ.supportPotentialPrimitive SJ3.potentialIntegral
  ring

omit [MeasurableSpace A] in
theorem supportFieldLeftSum_split (W : BrownianSystem Ω) (β : ℝ) (l : ℕ)
    (u : (Bool × Ω) × A) :
    supportFieldLeftSum W β l u =
      scalarHiddenSign u.1.1 *
        (W.B (parisiEquilibriumPhysicalEndpoint β) u.1.2 - W.B 0 u.1.2) -
      ∑ k ∈ Finset.range (2 ^ l),
        actualParisiFullPosteriorMean W β
          ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2 *
        (W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1)) u.1.2 -
          W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2) := by
  unfold supportFieldLeftSum
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k =>
      W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2) (2 ^ l)]
  simp only [dyadic_end, (brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).zero l]

omit [MeasurableSpace A] in
def originalQuadraticVariation (W : BrownianSystem Ω) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    (W.B ((brownianDyadicGrid V).time l (k + 1)) w -
      W.B ((brownianDyadicGrid V).time l k) w) ^ 2

omit [MeasurableSpace A] in
theorem originalQuadraticVariation_meanSquare_le (W : BrownianSystem Ω)
    (V : ℝ≥0) (l : ℕ) :
    (∫ u : Bool × Ω, (originalQuadraticVariation W V l u.2 - (V : ℝ)) ^ 2
      ∂(scalarHiddenPriorBool 0).prod W.law) ≤ 2 * brownianDyadicWidth V l * V := by
  let := W.isProbability
  let H : BrownianContinuousPastCoefficient Bool := fun _ _ => 1
  have he (j : ℕ) (u : Bool × Ω) : brownianStaticCenteredSquareSum W.B
      ((brownianDyadicGrid V).time j)
      (brownianContinuousMeshCoefficient H ((brownianDyadicGrid V).time j)) (1 * 2 ^ j) u =
        originalQuadraticVariation W V j u.2 - (V : ℝ) := by
    simp only [brownianStaticCenteredSquareSum, predictableGaussianCenteredSquareSum,
      predictableGaussianSum_eq_range_sum, brownianStaticCoefficient,
      brownianContinuousMeshCoefficient, H, one_mul, Finset.sum_sub_distrib]
    have hh := (brownianDyadicGrid V).variance_sum 1 j
    simp only [one_mul, brownianDyadicGrid_horizon] at hh
    rw [hh]
    rfl
  have hb := brownianCenteredSquare_refining_meanSquare_bound (scalarHiddenPriorBool 0) W.law
    W.B W.brownian.toIsPreBrownianReal W.measurable H (fun _ => measurable_const) 1
    (fun _ _ => by simp [H]) (brownianDyadicGrid V) 1 l (brownianDyadicWidth V l)
    (fun i _ => brownianDyadicGrid_width_le V l i)
  simp_rw [he] at hb
  simpa only [one_pow, mul_one, brownianDyadicGrid_horizon] using hb.2

omit [MeasurableSpace A] in
theorem originalQuadraticVariation_tendsto_L2 (W : BrownianSystem Ω) (V : ℝ≥0) :
    Tendsto (fun l => ∫ u : Bool × Ω,
      (originalQuadraticVariation W V l u.2 - (V : ℝ)) ^ 2
        ∂(scalarHiddenPriorBool 0).prod W.law) atTop (𝓝 0) := by
  apply squeeze_zero (fun l => integral_nonneg (fun _ => sq_nonneg _))
    (originalQuadraticVariation_meanSquare_le W V)
  simpa only [mul_zero, zero_mul] using
    ((brownianDyadicWidth_tendsto V).const_mul 2).mul_const (V : ℝ)

open ParisiFullSupport SKConstantsOAI.SK.Analytic

omit [MeasurableSpace A] in
theorem physicalPotential_eq_pre (β : ℝ) (hβ : 1 < β) {T : ℝ}
    (hQT : parisiEquilibriumSupportEndpoint β < T) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    physicalCDFPotential β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T t =
      parisiPhysicalValue β (parisiEquilibriumMeasure β) t := by
  have hb : 0 < β ^ 2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have htQ : (t : ℝ) / β ^ 2 ≤ parisiEquilibriumSupportEndpoint β := by
    apply (div_le_iff₀ hb).mpr
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ, mul_comm] using NNReal.coe_le_coe.mpr ht
  unfold physicalCDFPotential compactCDFValue parisiPhysicalValue
  rw [parisiCDFValue_eq_upstream,
    cdfStripTime_eq ⟨div_nonneg t.coe_nonneg hb.le, htQ.trans hQT.le⟩]

omit [MeasurableSpace A] in
theorem physicalPotential_deriv_eq_pre (β : ℝ) (hβ : 1 < β) {T : ℝ}
    (hQT : parisiEquilibriumSupportEndpoint β < T) (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    deriv (physicalCDFPotential β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T t) =
      actualParisiFullMagnetization β t := by
  change deriv (compactCDFValue β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T
    ((t : ℝ) / β ^ 2)) = _
  rw [compactCDFValue_deriv_eq β _
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) hT0]
  funext x
  simpa only [compactCDFJet, iteratedDeriv_zero] using
    (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le t ht x).symm

omit [MeasurableSpace A] in
theorem physicalPotential_second_deriv_eq_pre (β : ℝ) (hβ : 1 < β) {T : ℝ}
    (hQT : parisiEquilibriumSupportEndpoint β < T) (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    deriv (deriv (physicalCDFPotential β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T t)) =
      actualParisiFullCurvature β t := by
  rw [physicalPotential_deriv_eq_pre β hβ hQT hT0 hT1 t ht]
  funext x
  exact (actualParisiFullMagnetization_hasDerivAt β t x).deriv

omit [MeasurableSpace A] in
def supportSpatialRemainder (W : BrownianSystem Ω) (β : ℝ) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    let s := (brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k
    let t := (brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1)
    let y := actualParisiFullScalarProcess W β s w
    let d := actualParisiFullScalarProcess W β t w - y
    parisiPhysicalValue β (parisiEquilibriumMeasure β) s (y + d) -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) s y -
      actualParisiFullPosteriorMean W β s w * d - (1 / 2 : ℝ) * LJ.actualCurvature W β s w * d ^ 2

omit [MeasurableSpace A] in
theorem supportSpatialRemainder_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {T : ℝ} (hQT : parisiEquilibriumSupportEndpoint β < T) (hT0 : 0 ≤ T) (hT1 : T < 1)
    (l : ℕ) (w : Ω) : supportSpatialRemainder W β l w =
      spatialTaylorSum W (actualParisiFullScalarDrift β)
        (physicalCDFPotential β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T)
        (parisiEquilibriumPhysicalEndpoint β) l w := by
  unfold supportSpatialRemainder spatialTaylorSum
  apply Finset.sum_congr rfl
  intro k hk
  have ht := LM3.dyadic_time_le_horizon (parisiEquilibriumPhysicalEndpoint β) l k
    (Finset.mem_range.mp hk).le
  dsimp only
  rw [physicalPotential_second_deriv_eq_pre β hβ hQT hT0 hT1 _ ht,
    physicalPotential_deriv_eq_pre β hβ hQT hT0 hT1 _ ht,
    physicalPotential_eq_pre β hβ hQT _ ht]
  rfl

omit [MeasurableSpace A] in
theorem supportSpatialRemainder_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    (∀ l, Integrable (fun w => supportSpatialRemainder W β l w ^ 2) W.law) ∧
    Tendsto (fun l => ∫ w, supportSpatialRemainder W β l w ^ 2 ∂W.law) atTop (𝓝 0) := by
  let T := (parisiEquilibriumSupportEndpoint β + 1) / 2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0 ≤ T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T < 1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β < T := by dsimp [T]; linarith [hQ.2]
  have he : supportSpatialRemainder W β = fun l => spatialTaylorSum W (actualParisiFullScalarDrift β)
      (physicalCDFPotential β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T)
        (parisiEquilibriumPhysicalEndpoint β) l := by
    funext l w
    exact supportSpatialRemainder_eq W β hβ hQT hT0 hT1 l w
  rw [he]
  exact physicalPotential_spatialTaylor_tendsto_L2 W (actualParisiFullScalarDrift β) β
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1)
    (zero_lt_one.trans hβ).ne' hT0 hT1 _

omit [MeasurableSpace A] in
theorem originalCenteredSquare_isometry (W : BrownianSystem Ω) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ k, Measurable[Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable) (t k)] (H k))
    (hHsq : ∀ k, Integrable (fun w => H k w ^ 2) W.law) (n : ℕ) :
    Integrable (fun w => predictableGaussianCenteredSquareSum
      (brownianMeshIncrement W.B t) H (brownianMeshVariance t) n w ^ 2) W.law ∧
    (∫ w, predictableGaussianCenteredSquareSum (brownianMeshIncrement W.B t) H
      (brownianMeshVariance t) n w ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range n, 2 * (brownianMeshVariance t k : ℝ) ^ 2 * ∫ w, H k w ^ 2 ∂W.law := by
  let := W.isProbability
  let F := Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable)
  have hB (s : ℝ≥0) : Measurable[F s] (W.B s) :=
    (Filtration.stronglyAdapted_natural (fun r => (W.measurable r).stronglyMeasurable) s).measurable
  have hsum (j : ℕ) : Measurable[F (t j)]
      (predictableGaussianCenteredSquareSum (brownianMeshIncrement W.B t) H (brownianMeshVariance t) j) := by
    change Measurable[F (t j)] (fun w => predictableGaussianCenteredSquareSum
      (brownianMeshIncrement W.B t) H (brownianMeshVariance t) j w)
    simp only [predictableGaussianCenteredSquareSum, predictableGaussianSum_eq_range_sum]
    apply Finset.measurable_fun_sum
    intro k hk
    have hkj : k ≤ j := (Finset.mem_range.mp hk).le
    have hk1j : k + 1 ≤ j := Finset.mem_range.mp hk
    exact ((hH k).mono (F.mono (ht hkj)) le_rfl).mul
      (((((hB (t (k + 1))).mono (F.mono (ht hk1j)) le_rfl).sub
        ((hB (t k)).mono (F.mono (ht hkj)) le_rfl)).pow_const 2).sub_const _)
  apply predictableGaussianCenteredSquareSum_L2_isometry W.law _ H _
    (brownianMeshIncrement_hasLaw W.brownian.toIsPreBrownianReal t ht)
    (fun k => ((hH k).mono (F.le _) le_rfl).aemeasurable) hHsq
  intro j
  have hstate := (hsum j).prodMk (hH j)
  have he : t j + brownianMeshVariance t j = t (j + 1) := add_tsub_cancel_of_le (ht (by omega))
  have hi := (W.brownian.toIsPreBrownianReal.indepFun_shift (t j)).comp
    (measurable_pi_apply (brownianMeshVariance t j)) measurable_id
  change IndepFun (fun w => W.B (t j + brownianMeshVariance t j) w - W.B (t j) w)
    (fun w (s : Iic (t j)) => W.B s w) W.law at hi
  rw [he] at hi
  apply Indep.symm
  apply indep_of_indep_of_le hi le_rfl
  rw [← Filtration.natural_eq_comap W.B (fun r => (W.measurable r).stronglyMeasurable) (t j)]
  exact measurable_iff_comap_le.mp hstate

omit [MeasurableSpace A] in
def curvatureQuadraticError (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    LJ.actualCurvature W β ((brownianDyadicGrid V).time l k) w *
      ((W.B ((brownianDyadicGrid V).time l (k + 1)) w -
        W.B ((brownianDyadicGrid V).time l k) w) ^ 2 - brownianDyadicWidth V l)

omit [MeasurableSpace A] in
theorem curvatureQuadraticError_meanSquare_le (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    Integrable (fun w => curvatureQuadraticError W β V l w ^ 2) W.law ∧
    (∫ w, curvatureQuadraticError W β V l w ^ 2 ∂W.law) ≤ 2 * brownianDyadicWidth V l * V := by
  let := W.isProbability
  let t := (brownianDyadicGrid V).time l
  let H := fun k => LJ.actualCurvature W β (t k)
  have hH (k : ℕ) : Measurable[Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable) (t k)] (H k) := by
    change Measurable[Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable) (t k)]
      (fun w => actualParisiFullCurvature β (t k)
        ((actualParisiFullScalarDrift β).solution W.driver (t k) w))
    exact (actualParisiFullCurvature_lipschitz β (t k)).continuous.measurable.comp
      ((actualParisiFullScalarDrift β).solution_adapted W (t k))
  have hHi (k : ℕ) : Integrable (fun w => H k w ^ 2) W.law := by
    apply Integrable.of_bound ((LJ.measurable_actualCurvature W β (t k)).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with w
    have hh := LJ.actualCurvature_abs_le W β (t k) w
    simpa only [Real.norm_eq_abs, abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  have he : predictableGaussianCenteredSquareSum (brownianMeshIncrement W.B t) H
      (brownianMeshVariance t) (2 ^ l) = curvatureQuadraticError W β V l := by
    funext w
    simp only [predictableGaussianCenteredSquareSum, predictableGaussianSum_eq_range_sum,
      curvatureQuadraticError, brownianMeshIncrement, H, t]
    apply Finset.sum_congr rfl
    intro k _
    rw [brownianMeshVariance, NNReal.coe_sub ((brownianDyadicGrid V).monotone l (Nat.le_succ k)),
      dyadic_step_eq_width]
  have hiso := originalCenteredSquare_isometry W t ((brownianDyadicGrid V).monotone l) H hH hHi (2 ^ l)
  rw [he] at hiso
  refine ⟨hiso.1, ?_⟩
  rw [hiso.2]
  have hvar (k : ℕ) : (brownianMeshVariance t k : ℝ) = brownianDyadicWidth V l := by
    rw [brownianMeshVariance, NNReal.coe_sub ((brownianDyadicGrid V).monotone l (Nat.le_succ k))]
    exact dyadic_step_eq_width V l k
  calc
    _ ≤ ∑ k ∈ Finset.range (2 ^ l), 2 * brownianDyadicWidth V l ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [hvar]
      have hb : (∫ w, H k w ^ 2 ∂W.law) ≤ 1 := by
        have hh := integral_mono (hHi k) (integrable_const (1 : ℝ)) (fun w => by
          have hc := LJ.actualCurvature_abs_le W β (t k) w
          simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hc 2)
        simpa using hh
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * brownianDyadicWidth V l ^ 2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        brownianDyadicWidth]
      field_simp

omit [MeasurableSpace A] in
theorem curvatureQuadraticError_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    Tendsto (fun l => ∫ w, curvatureQuadraticError W β V l w ^ 2 ∂W.law) atTop (𝓝 0) := by
  exact squeeze_zero (fun l => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => (curvatureQuadraticError_meanSquare_le W β V l).2)
    (by simpa only [mul_zero, zero_mul] using
      ((brownianDyadicWidth_tendsto V).const_mul 2).mul_const (V : ℝ))

theorem supportSpatialRemainder_tendsto_L2_base (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) :
    (∀ l, Integrable (fun u : (Bool × Ω) × A => supportSpatialRemainder W β l u.1.2 ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u : (Bool × Ω) × A, supportSpatialRemainder W β l u.1.2 ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  obtain ⟨hi, ht⟩ := supportSpatialRemainder_tendsto_L2 W β hβ
  refine ⟨fun l => ((hi l).comp_snd (scalarHiddenPriorBool 0)).comp_fst Z.law, ?_⟩
  have he (l : ℕ) : (∫ u : (Bool × Ω) × A, supportSpatialRemainder W β l u.1.2 ^ 2
      ∂LM4.actualRowBaseLaw W Z) = ∫ w, supportSpatialRemainder W β l w ^ 2 ∂W.law := by
    calc
      _ = ∫ v : Bool × Ω, supportSpatialRemainder W β l v.2 ^ 2
          ∂(scalarHiddenPriorBool 0).prod W.law := by
        simpa only [LM4.actualRowBaseLaw, probReal_univ, one_smul] using
          integral_fun_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
            (fun v : Bool × Ω => supportSpatialRemainder W β l v.2 ^ 2)
      _ = _ := by
        simpa only [probReal_univ, one_smul] using
          integral_fun_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)
            (fun w => supportSpatialRemainder W β l w ^ 2)
  simp_rw [he]
  exact ht

theorem curvatureQuadraticError_tendsto_L2_base (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) :
    (∀ l, Integrable (fun u : (Bool × Ω) × A => curvatureQuadraticError W β V l u.1.2 ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u : (Bool × Ω) × A, curvatureQuadraticError W β V l u.1.2 ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  refine ⟨fun l => (((curvatureQuadraticError_meanSquare_le W β V l).1).comp_snd
    (scalarHiddenPriorBool 0)).comp_fst Z.law, ?_⟩
  have he (l : ℕ) : (∫ u : (Bool × Ω) × A, curvatureQuadraticError W β V l u.1.2 ^ 2
      ∂LM4.actualRowBaseLaw W Z) = ∫ w, curvatureQuadraticError W β V l w ^ 2 ∂W.law := by
    calc
      _ = ∫ v : Bool × Ω, curvatureQuadraticError W β V l v.2 ^ 2
          ∂(scalarHiddenPriorBool 0).prod W.law := by
        simpa only [LM4.actualRowBaseLaw, probReal_univ, one_smul] using
          integral_fun_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
            (fun v : Bool × Ω => curvatureQuadraticError W β V l v.2 ^ 2)
      _ = _ := by
        simpa only [probReal_univ, one_smul] using
          integral_fun_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)
            (fun w => curvatureQuadraticError W β V l w ^ 2)
  simp_rw [he]
  exact curvatureQuadraticError_tendsto_L2 W β V

end SKConstants.Completion.S32bB
