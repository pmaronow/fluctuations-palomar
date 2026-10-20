module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.FineInformation

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (row : ι → Ω → ℝ × ℝ)

@[expose] def spin (i : ι) (ω : Ω) : ℝ := (row i ω).1
@[expose] def gaussian (i : ι) (ω : Ω) : ℝ := (row i ω).2
@[expose] def meanSpin (i : ι) : ℝ := ∫ ω, spin row i ω ∂μ
@[expose] def mixedMean (i : ι) : ℝ := ∫ ω, spin row i ω * gaussian row i ω ∂μ

theorem mixed_third_moment
    (hm : ∀ i, Measurable (row i)) (hind : iIndepFun row μ)
    (hspin : ∀ i ω, spin row i ω ^ 2 = 1)
    (hcenter : ∀ i, ∫ ω, gaussian row i ω ∂μ = 0)
    (i j k : ι) :
    (∫ ω, spin row i ω * spin row j ω * gaussian row k ω ∂μ) =
      (if k = i then mixedMean μ row i * meanSpin μ row j else 0) +
      (if k = j then meanSpin μ row i * mixedMean μ row j else 0) -
      (if i = j ∧ k = i then 2 * meanSpin μ row i * mixedMean μ row i else 0) := by
  have hx (i : ι) : Measurable (spin row i) := (hm i).fst
  have hg (i : ι) : Measurable (gaussian row i) := (hm i).snd
  by_cases hij : i = j
  · subst j
    have hfun : (fun ω => spin row i ω * spin row i ω * gaussian row k ω) =
        gaussian row k := by
      funext ω
      rw [← pow_two, hspin]
      simp
    rw [hfun,hcenter]
    by_cases hki : k = i <;> simp [hki] <;> ring
  · by_cases hki : k = i
    · subst k
      have hpair := (hind.indepFun hij).comp
        (show Measurable (fun z : ℝ × ℝ => z.1 * z.2) from by fun_prop)
        measurable_fst
      have hfactor := hpair.integral_fun_mul_eq_mul_integral
        ((hx i).mul (hg i)).aestronglyMeasurable (hx j).aestronglyMeasurable
      change (∫ ω, (spin row i ω * gaussian row i ω) * spin row j ω ∂μ) =
        mixedMean μ row i * meanSpin μ row j at hfactor
      have hfun : (fun ω => spin row i ω * spin row j ω * gaussian row i ω) =
          (fun ω => (spin row i ω * gaussian row i ω) * spin row j ω) := by
        funext ω
        ring
      rw [hfun]
      change (∫ ω, (spin row i ω * gaussian row i ω) * spin row j ω ∂μ) = _
      rw [hfactor]
      simp [mixedMean, meanSpin, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        have hpair := (hind.indepFun hij).comp measurable_fst
          (show Measurable (fun z : ℝ × ℝ => z.1 * z.2) from by fun_prop)
        have hfactor := hpair.integral_fun_mul_eq_mul_integral
          (hx i).aestronglyMeasurable ((hx j).mul (hg j)).aestronglyMeasurable
        change (∫ ω, spin row i ω * (spin row j ω * gaussian row j ω) ∂μ) =
          meanSpin μ row i * mixedMean μ row j at hfactor
        have hfun : (fun ω => spin row i ω * spin row j ω * gaussian row j ω) =
            (fun ω => spin row i ω * (spin row j ω * gaussian row j ω)) := by
          funext ω
          ring
        rw [hfun,hfactor]
        simp [mixedMean, meanSpin, hij, Ne.symm hij]
      · have hpair := (hind.indepFun_prodMk hm i j k (Ne.symm hki) (Ne.symm hkj)).comp
          (show Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 * z.2.1) from
            by fun_prop) measurable_snd
        have hfactor := hpair.integral_fun_mul_eq_mul_integral
          ((hx i).mul (hx j)).aestronglyMeasurable (hg k).aestronglyMeasurable
        change (∫ ω, spin row i ω * spin row j ω * gaussian row k ω ∂μ) =
          (∫ ω, spin row i ω * spin row j ω ∂μ) *
            (∫ ω, gaussian row k ω ∂μ) at hfactor
        rw [hfactor,hcenter]
        simp [hki,hkj,hij]

theorem mixed_third_integrable
    (hm : ∀ i, Measurable (row i))
    (hspin : ∀ i ω, spin row i ω ^ 2 = 1)
    (hg : ∀ i, Integrable (gaussian row i) μ) (i j k : ι) :
    Integrable (fun ω => spin row i ω * spin row j ω * gaussian row k ω) μ := by
  apply (hg k).congr'
    (((hm i).fst.mul (hm j).fst).mul (hm k).snd).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have hi : ‖spin row i ω‖ = 1 := by
    rcases sq_eq_one_iff.mp (hspin i ω) with hi | hi <;> simp [hi]
  have hj : ‖spin row j ω‖ = 1 := by
    rcases sq_eq_one_iff.mp (hspin j ω) with hj | hj <;> simp [hj]
  change ‖gaussian row k ω‖ = ‖spin row i ω * spin row j ω * gaussian row k ω‖
  simp only [norm_mul, hi, hj, one_mul]

theorem oneQuery_contraction (u m zeta : ι → ℝ) (P : Matrix ι ι ℝ) :
    (∑ i, ∑ j, ∑ k, u i * P j k *
      ((if k = i then zeta i * m j else 0) +
        (if k = j then m i * zeta j else 0) -
        (if i = j ∧ k = i then 2 * m i * zeta i else 0))) =
      (∑ i, u i * zeta i * (∑ j, P j i * m j)) +
        (∑ i, u i * m i) * (∑ j, P j j * zeta j) -
        2 * (∑ i, u i * P i i * m i * zeta i) := by
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[expose] def oneQueryEnergy (N : ℝ) (u : ι → ℝ) (P : Matrix ι ι ℝ) (ω : Ω) : ℝ :=
  (N⁻¹) ^ 2 * ∑ i, ∑ j, ∑ k,
    u i * P j k * (spin row i ω * spin row j ω * gaussian row k ω)

omit [DecidableEq ι] [MeasurableSpace Ω] in
theorem oneQueryEnergy_eq_product (N : ℝ) (u : ι → ℝ) (P : Matrix ι ι ℝ) (ω : Ω) :
    oneQueryEnergy row N u P ω =
      (N⁻¹ * ∑ i, u i * spin row i ω) *
        (N⁻¹ * ∑ j, spin row j ω * (∑ k, P j k * gaussian row k ω)) := by
  unfold oneQueryEnergy
  rw [show (N⁻¹ * ∑ i, u i * spin row i ω) *
      (N⁻¹ * ∑ j, spin row j ω * (∑ k, P j k * gaussian row k ω)) =
      (N⁻¹) ^ 2 * ((∑ i, u i * spin row i ω) *
        (∑ j, spin row j ω * (∑ k, P j k * gaussian row k ω))) by ring]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem oneQuery_expectation
    (hm : ∀ i, Measurable (row i)) (hind : iIndepFun row μ)
    (hspin : ∀ i ω, spin row i ω ^ 2 = 1)
    (hcenter : ∀ i, ∫ ω, gaussian row i ω ∂μ = 0)
    (hg : ∀ i, Integrable (gaussian row i) μ)
    (N : ℝ) (u : ι → ℝ) (P : Matrix ι ι ℝ) :
    (∫ ω, oneQueryEnergy row N u P ω ∂μ) =
      (N⁻¹) ^ 2 *
        ((∑ i, u i * mixedMean μ row i * (∑ j, P j i * meanSpin μ row j)) +
          (∑ i, u i * meanSpin μ row i) * (∑ j, P j j * mixedMean μ row j) -
          2 * (∑ i, u i * P i i * meanSpin μ row i * mixedMean μ row i)) := by
  have hterm (i j k : ι) : Integrable (fun ω =>
      u i * P j k * (spin row i ω * spin row j ω * gaussian row k ω)) μ :=
    (mixed_third_integrable μ row hm hspin hg i j k).const_mul _
  unfold oneQueryEnergy
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _
    (fun j hj => integrable_finsetSum _ (fun k hk => hterm i j k)))]
  simp_rw [integral_finsetSum _ (fun j hj =>
    integrable_finsetSum _ (fun k hk => hterm _ j k))]
  simp_rw [integral_finsetSum _ (fun k hk => hterm _ _ k), integral_const_mul,
    mixed_third_moment μ row hm hind hspin hcenter]
  exact oneQuery_contraction u (meanSpin μ row) (mixedMean μ row) P

theorem oneQuery_expectation_of_mean_killed
    (hm : ∀ i, Measurable (row i)) (hind : iIndepFun row μ)
    (hspin : ∀ i ω, spin row i ω ^ 2 = 1)
    (hcenter : ∀ i, ∫ ω, gaussian row i ω ∂μ = 0)
    (hg : ∀ i, Integrable (gaussian row i) μ)
    (N : ℝ) (u : ι → ℝ) (P : Matrix ι ι ℝ)
    (hkilled : ∀ i, ∑ j, P j i * meanSpin μ row j = 0) :
    (∫ ω, oneQueryEnergy row N u P ω ∂μ) =
      (N⁻¹ * ∑ i, u i * meanSpin μ row i) *
        (N⁻¹ * ∑ j, P j j * mixedMean μ row j) -
      2 * (N⁻¹) ^ 2 * (∑ i, u i * P i i * meanSpin μ row i * mixedMean μ row i) := by
  rw [oneQuery_expectation μ row hm hind hspin hcenter hg]
  simp only [hkilled, mul_zero, Finset.sum_const_zero, zero_add]
  ring

@[expose] def pairedCoordinate (z : ℝ × Bool) : ℝ × ℝ :=
  (if z.2 then 1 else -1, z.1)

theorem pairedCoordinate_measurable : Measurable pairedCoordinate := by
  have hs : Measurable (fun b : Bool => if b then (1 : ℝ) else -1) :=
    measurable_of_finite _
  exact (hs.comp measurable_snd).prodMk measurable_fst

theorem product_mixed_third_moment
    (ν : ι → Measure (ℝ × Bool)) [∀ i, IsProbabilityMeasure (ν i)]
    (hcenter : ∀ i, ∫ z : ℝ × Bool, z.1 ∂ν i = 0) (i j k : ι) :
    (∫ ω : ι → ℝ × Bool,
      (pairedCoordinate (ω i)).1 * (pairedCoordinate (ω j)).1 * (ω k).1
        ∂Measure.pi ν) =
      (if k = i then
        (∫ z, (pairedCoordinate z).1 * z.1 ∂ν i) *
          (∫ z, (pairedCoordinate z).1 ∂ν j) else 0) +
      (if k = j then
        (∫ z, (pairedCoordinate z).1 ∂ν i) *
          (∫ z, (pairedCoordinate z).1 * z.1 ∂ν j) else 0) -
      (if i = j ∧ k = i then
        2 * (∫ z, (pairedCoordinate z).1 ∂ν i) *
          (∫ z, (pairedCoordinate z).1 * z.1 ∂ν i) else 0) := by
  let rows : ι → (ι → ℝ × Bool) → ℝ × ℝ := fun i ω => pairedCoordinate (ω i)
  have hm (i : ι) : Measurable (rows i) :=
    pairedCoordinate_measurable.comp (measurable_pi_apply i)
  have hind : iIndepFun rows (Measure.pi ν) :=
    iIndepFun_pi (fun _ => pairedCoordinate_measurable.aemeasurable)
  have hs (i : ι) (ω : ι → ℝ × Bool) : spin rows i ω ^ 2 = 1 := by
    change (if (ω i).2 then (1 : ℝ) else -1) ^ 2 = 1
    cases (ω i).2 <;> norm_num
  have hc (i : ι) : (∫ ω, gaussian rows i ω ∂Measure.pi ν) = 0 := by
    change (∫ ω : ι → ℝ × Bool, (ω i).1 ∂Measure.pi ν) = 0
    rw [integral_comp_eval measurable_fst.aestronglyMeasurable,hcenter]
  have hmarg (i : ι) : meanSpin (Measure.pi ν) rows i =
      ∫ z, (pairedCoordinate z).1 ∂ν i := by
    change (∫ ω : ι → ℝ × Bool, (pairedCoordinate (ω i)).1 ∂Measure.pi ν) = _
    exact integral_comp_eval (μ := ν) (i := i)
      pairedCoordinate_measurable.fst.aestronglyMeasurable
  have hcross (i : ι) : mixedMean (Measure.pi ν) rows i =
      ∫ z, (pairedCoordinate z).1 * z.1 ∂ν i := by
    change (∫ ω : ι → ℝ × Bool, (pairedCoordinate (ω i)).1 * (ω i).1 ∂Measure.pi ν) = _
    exact integral_comp_eval (μ := ν) (i := i)
      (pairedCoordinate_measurable.fst.mul measurable_fst).aestronglyMeasurable
  have h := mixed_third_moment (Measure.pi ν) rows hm hind hs hc i j k
  simp only [hmarg, hcross] at h
  simpa only [spin,gaussian,rows,pairedCoordinate] using h

variable {Seed : Type*} [MeasurableSpace Seed]

@[expose] def gaussianSeedLaw (η : ι → Measure Seed) : Measure (ι → ℝ × Seed) :=
  Measure.pi (fun i => (gaussianReal 0 1).prod (η i))

instance (η : ι → Measure Seed) [∀ i, IsProbabilityMeasure (η i)] :
    IsProbabilityMeasure (gaussianSeedLaw η) := by
  unfold gaussianSeedLaw
  infer_instance

@[expose] def gaussianSignRows (finalSign : ι → ℝ × Seed → Bool)
    (i : ι) (ω : ι → ℝ × Seed) : ℝ × ℝ :=
  (if finalSign i (ω i) then 1 else -1, (ω i).1)

theorem gaussianSignRows_measurable
    (finalSign : ι → ℝ × Seed → Bool) (hSign : ∀ i, Measurable (finalSign i)) (i : ι) :
    Measurable (gaussianSignRows finalSign i) := by
  have hs : Measurable (fun b : Bool => if b then (1 : ℝ) else -1) :=
    measurable_of_finite _
  exact ((hs.comp (hSign i)).prodMk measurable_fst).comp (measurable_pi_apply i)

theorem gaussianSignRows_independent (η : ι → Measure Seed)
    [∀ i, IsProbabilityMeasure (η i)] (finalSign : ι → ℝ × Seed → Bool)
    (hSign : ∀ i, Measurable (finalSign i)) :
    iIndepFun (gaussianSignRows finalSign) (gaussianSeedLaw η) := by
  have hs : Measurable (fun b : Bool => if b then (1 : ℝ) else -1) :=
    measurable_of_finite _
  exact iIndepFun_pi (fun i => ((hs.comp (hSign i)).prodMk measurable_fst).aemeasurable)

theorem gaussianSignRows_spin_square (finalSign : ι → ℝ × Seed → Bool)
    (i : ι) (ω : ι → ℝ × Seed) : spin (gaussianSignRows finalSign) i ω ^ 2 = 1 := by
  change (if finalSign i (ω i) then (1 : ℝ) else -1) ^ 2 = 1
  cases finalSign i (ω i) <;> norm_num

theorem gaussianSignRows_centered (η : ι → Measure Seed)
    [∀ i, IsProbabilityMeasure (η i)] (finalSign : ι → ℝ × Seed → Bool) (i : ι) :
    (∫ ω, gaussian (gaussianSignRows finalSign) i ω ∂gaussianSeedLaw η) = 0 := by
  change (∫ ω : ι → ℝ × Seed, (ω i).1
    ∂Measure.pi (fun j => (gaussianReal 0 1).prod (η j))) = 0
  rw [integral_comp_eval measurable_fst.aestronglyMeasurable]
  have hmap : ((gaussianReal 0 1).prod (η i)).map Prod.fst = gaussianReal 0 1 := by simp
  have h := integral_map (μ := (gaussianReal 0 1).prod (η i))
    measurable_fst.aemeasurable (measurable_id.aestronglyMeasurable :
      AEStronglyMeasurable (fun z : ℝ => z)
        (((gaussianReal 0 1).prod (η i)).map Prod.fst))
  rw [hmap] at h
  simp only [id_eq, integral_id_gaussianReal] at h
  exact h.symm

theorem gaussianSignRows_integrable (η : ι → Measure Seed)
    [∀ i, IsProbabilityMeasure (η i)] (finalSign : ι → ℝ × Seed → Bool) (i : ι) :
    Integrable (gaussian (gaussianSignRows finalSign) i) (gaussianSeedLaw η) := by
  have hmap : ((gaussianReal 0 1).prod (η i)).map Prod.fst = gaussianReal 0 1 := by simp
  have hG : Integrable (fun z : ℝ => z)
      (((gaussianReal 0 1).prod (η i)).map Prod.fst) := by
    rw [hmap]
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hg : Integrable (fun z : ℝ × Seed => z.1) ((gaussianReal 0 1).prod (η i)) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).1 hG
  change Integrable (fun ω : ι → ℝ × Seed => (ω i).1)
    (Measure.pi (fun j => (gaussianReal 0 1).prod (η j)))
  exact integrable_comp_eval (μ := fun j => (gaussianReal 0 1).prod (η j)) (i := i) hg

theorem gaussianSign_oneQuery_expectation (η : ι → Measure Seed)
    [∀ i, IsProbabilityMeasure (η i)] (finalSign : ι → ℝ × Seed → Bool)
    (hSign : ∀ i, Measurable (finalSign i)) (N : ℝ) (u : ι → ℝ) (P : Matrix ι ι ℝ)
    (hkilled : ∀ i, ∑ j, P j i * meanSpin (gaussianSeedLaw η) (gaussianSignRows finalSign) j = 0) :
    (∫ ω, oneQueryEnergy (gaussianSignRows finalSign) N u P ω ∂gaussianSeedLaw η) =
      (N⁻¹ * ∑ i, u i * meanSpin (gaussianSeedLaw η) (gaussianSignRows finalSign) i) *
        (N⁻¹ * ∑ j, P j j * mixedMean (gaussianSeedLaw η) (gaussianSignRows finalSign) j) -
      2 * (N⁻¹) ^ 2 * (∑ i, u i * P i i *
        meanSpin (gaussianSeedLaw η) (gaussianSignRows finalSign) i *
        mixedMean (gaussianSeedLaw η) (gaussianSignRows finalSign) i) := by
  exact oneQuery_expectation_of_mean_killed (gaussianSeedLaw η) (gaussianSignRows finalSign)
    (gaussianSignRows_measurable finalSign hSign)
    (gaussianSignRows_independent η finalSign hSign)
    (gaussianSignRows_spin_square finalSign)
    (gaussianSignRows_centered η finalSign)
    (gaussianSignRows_integrable η finalSign) N u P hkilled

end SKConstants.FineInformation
