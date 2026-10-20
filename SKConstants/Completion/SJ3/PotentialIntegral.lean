module

public import SKConstants.Completion.LJ.FiniteRow
public import SKConstants.Completion.LBase.FullProfiles
public import SKConstants.ScalarStieltjesRiemann
public import SKConstants.Completion.LM4b.ActualRowReference
public import SKConstants.Completion.LM3.RowScalarReduction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.SJ3
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization

theorem weightedIncrements_bound (w X : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ) (C P : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hw : ∀ i ≤ N, 0 ≤ w (a i) ∧ w (a i) ≤ P)
    (hmono : ∀ i < N, w (a (i + 1)) ≤ w (a i))
    (hX : ∀ i ≤ N, |X (a i)| ≤ C) :
    |∑ i ∈ Finset.range N, w (a i) * (X (a (i + 1)) - X (a i))| ≤ 3 * C * P := by
  rw [scalarStieltjes_discrete_parts]
  have hend : |w (a N) * X (a N) - w (a 0) * X (a 0)| ≤ 2 * C * P := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg (hw N le_rfl).1,
      abs_of_nonneg (hw 0 (Nat.zero_le N)).1]
    have h1 := mul_le_mul (hw N le_rfl).2 (hX N le_rfl) (abs_nonneg _) hP
    have h0 := mul_le_mul (hw 0 (Nat.zero_le N)).2 (hX 0 (Nat.zero_le N)) (abs_nonneg _) hP
    nlinarith
  have hsum : |∑ i ∈ Finset.range N, X (a (i + 1)) * (w (a (i + 1)) - w (a i))| ≤ C * P := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, |X (a (i + 1)) * (w (a (i + 1)) - w (a i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, C * (w (a i) - w (a (i + 1))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hm := hmono i (Finset.mem_range.mp hi)
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hm), neg_sub]
        exact mul_le_mul_of_nonneg_right (hX (i + 1) (Finset.mem_range.mp hi)) (sub_nonneg.mpr hm)
      _ = C * (w (a 0) - w (a N)) := by
        rw [← Finset.mul_sum]
        congr 1
        have he := Finset.sum_range_sub (fun i => w (a i)) N
        rw [Finset.sum_sub_distrib] at he ⊢
        linarith
      _ ≤ C * P := mul_le_mul_of_nonneg_left (by linarith [(hw 0 (Nat.zero_le N)).2, (hw N le_rfl).1]) hC
  exact (abs_sub _ _).trans (by linarith)

def negativeSusceptibility (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) : StieltjesFunction ℝ where
  toFun t := -actualParisiFullSusceptibilityExpected W β (t.toNNReal : ℝ)
  mono' := by
    intro s t hst
    exact neg_le_neg (LBase.actual_susceptibility_antitone W β hβ
      s.toNNReal.coe_nonneg t.toNNReal.coe_nonneg (Real.toNNReal_mono hst))
  right_continuous' := fun _ =>
    (((continuous_actualParisiFullSusceptibilityExpected W β).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).neg.continuousAt.continuousWithinAt)

theorem continuous_negativeSusceptibility (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Continuous (negativeSusceptibility W β hβ) :=
  ((continuous_actualParisiFullSusceptibilityExpected W β).comp
    (NNReal.continuous_coe.comp continuous_real_toNNReal)).neg

@[simp] theorem negativeSusceptibility_nnreal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) : negativeSusceptibility W β hβ t = -actualParisiFullSusceptibilityExpected W β t := by
  simp only [negativeSusceptibility, Real.toNNReal_coe]

@[simp] theorem negativeSusceptibility_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    negativeSusceptibility W β hβ 0 = -actualParisiFullSusceptibilityExpected W β 0 := by
  simp only [negativeSusceptibility, Real.toNNReal_zero, NNReal.coe_zero]

theorem actualRowPotential_bound (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) (u : Bool × Ω) :
    |LJ.actualRowPotential W β t u| ≤ 2 := by
  rw [LJ.actualRowPotential_eq_error]
  obtain ⟨h0, h4⟩ := actualParisiPinningError_mem_Icc W β t u
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem measurable_actualRowPotential_time (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (fun p : (Bool × Ω) × ℝ => LJ.actualRowPotential W β p.2.toNNReal p.1) := by
  have hy : Measurable (fun p : (Bool × Ω) × ℝ => actualParisiFullScalarProcess W β p.2.toNNReal p.1.2) := by
    have hm := LC1.measurable_fullScalar_real_shift W β 0
    simp only [zero_add] at hm
    simpa only [Function.comp_def] using hm.comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have ht : Measurable (fun p : (Bool × Ω) × ℝ => (p.2.toNNReal : ℝ)) :=
    measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_snd)
  have hm := (continuous_actualParisiFullMagnetization β).measurable.comp (ht.prodMk hy)
  have hs : Measurable (fun p : (Bool × Ω) × ℝ => scalarHiddenSign p.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  exact (hs.mul hm).sub ((hm.pow_const 2).div_const 2)

theorem actualRowPotential_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law,
      Continuous (fun t : ℝ => LJ.actualRowPotential W β t.toNNReal u) := by
  let := W.isProbability
  filter_upwards [(measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).quasiMeasurePreserving.ae
    ((actualParisiFullScalarDrift β).solution_continuous_ae W)] with u hu
  change Continuous (fun t => actualParisiFullScalarProcess W β t u.2) at hu
  have hy : Continuous (fun t : ℝ => actualParisiFullScalarProcess W β t.toNNReal u.2) :=
    hu.comp continuous_real_toNNReal
  have ht : Continuous (fun t : ℝ => (t.toNNReal : ℝ)) :=
    NNReal.continuous_coe.comp continuous_real_toNNReal
  have hm : Continuous (fun t : ℝ => actualParisiFullPosteriorMean W β t.toNNReal u.2) :=
    (continuous_actualParisiFullMagnetization β).comp (ht.prodMk hy)
  exact (continuous_const.mul hm).sub ((hm.pow 2).div_const 2)

def potentialLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) (u : Bool × Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k) *
      (LJ.actualRowPotential W β ((brownianDyadicGrid V).time l (k + 1)) u -
        LJ.actualRowPotential W β ((brownianDyadicGrid V).time l k) u)

def potentialIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (u : Bool × Ω) : ℝ :=
  actualParisiFullSusceptibilityExpected W β V * LJ.actualRowPotential W β V u -
    actualParisiFullSusceptibilityExpected W β 0 * LJ.actualRowPotential W β 0 u +
      ∫ t in (0 : ℝ)..(V : ℝ), LJ.actualRowPotential W β t.toNNReal u
        ∂(negativeSusceptibility W β hβ).measure

theorem measurable_potentialLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    Measurable (potentialLeftSum W β V l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact ((LJ.measurable_actualRowPotential W β _).sub (LJ.measurable_actualRowPotential W β _)).const_mul _

theorem potentialLeftSum_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (l : ℕ) (u : Bool × Ω) : |potentialLeftSum W β V l u| ≤ 6 := by
  have hh := weightedIncrements_bound (actualParisiFullSusceptibilityExpected W β)
    (fun t => LJ.actualRowPotential W β t.toNNReal u)
    (fun k => ((brownianDyadicGrid V).time l k : ℝ)) (2 ^ l) 2 1 (by norm_num) (by norm_num)
    (fun i _ => ⟨actualParisiFullSusceptibilityExpected_nonneg W β _, LBase.actual_susceptibility_le_one W β _⟩)
    (fun i _ => LBase.actual_susceptibility_antitone W β hβ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
      (NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l (Nat.le_succ i))))
    (fun i _ => actualRowPotential_bound W β _ u)
  simpa only [potentialLeftSum, Real.toNNReal_coe, show (3 : ℝ) * 2 * 1 = 6 by norm_num] using hh

theorem measurable_potentialIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    Measurable (potentialIntegral W β hβ V) := by
  have hm := (measurable_actualRowPotential_time W β).stronglyMeasurable.integral_prod_right'
    (ν := (negativeSusceptibility W β hβ).measure.restrict (Ioc (0 : ℝ) (V : ℝ)))
  change Measurable (fun u => _ - _ + ∫ t in (0 : ℝ)..(V : ℝ), _ ∂_)
  simp_rw [intervalIntegral.integral_of_le V.coe_nonneg]
  exact (((LJ.measurable_actualRowPotential W β V).const_mul _).sub
    ((LJ.measurable_actualRowPotential W β 0).const_mul _)).add hm.measurable

theorem potentialIntegral_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (u : Bool × Ω) : |potentialIntegral W β hβ V u| ≤ 6 := by
  let f := negativeSusceptibility W β hβ
  have hi : |∫ t in (0 : ℝ)..(V : ℝ), LJ.actualRowPotential W β t.toNNReal u ∂f.measure| ≤ 2 := by
    rw [intervalIntegral.integral_of_le V.coe_nonneg]
    have hh := norm_setIntegral_le_of_norm_le_const
      (μ := f.measure) (s := Ioc (0 : ℝ) (V : ℝ))
      (f := fun t => LJ.actualRowPotential W β t.toNNReal u)
      (by rw [f.measure_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun t _ => by simpa only [Real.norm_eq_abs] using actualRowPotential_bound W β t.toNNReal u)
    have hmass : f.measure.real (Ioc (0 : ℝ) (V : ℝ)) ≤ 1 := by
      rw [Measure.real, f.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono V.coe_nonneg))]
      simp only [f, negativeSusceptibility_nnreal, negativeSusceptibility_zero]
      linarith [LBase.actual_susceptibility_le_one W β 0, actualParisiFullSusceptibilityExpected_nonneg W β V]
    have hh' : |∫ t in Ioc (0 : ℝ) (V : ℝ), LJ.actualRowPotential W β t.toNNReal u ∂f.measure| ≤
        f.measure.real (Ioc (0 : ℝ) (V : ℝ)) * 2 := by
      simpa only [Real.norm_eq_abs, mul_comm] using hh
    exact hh'.trans (by linarith)
  have hb (t : ℝ≥0) : |actualParisiFullSusceptibilityExpected W β t * LJ.actualRowPotential W β t u| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (actualParisiFullSusceptibilityExpected_nonneg W β t)]
    exact (mul_le_mul (LBase.actual_susceptibility_le_one W β t) (actualRowPotential_bound W β t u)
      (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  exact (abs_add_le _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add (hb V) (hb 0))) hi).trans_eq (by norm_num))

theorem potentialLeftSum_memLp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (l : ℕ) :
    MemLp (potentialLeftSum W β V l) 2 ((scalarHiddenPriorBool 0).prod W.law) := by
  let := W.isProbability
  exact (memLp_const (6 : ℝ)).mono' (measurable_potentialLeftSum W β V l).aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using potentialLeftSum_bound W β hβ V l u))

theorem potentialIntegral_memLp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    MemLp (potentialIntegral W β hβ V) 2 ((scalarHiddenPriorBool 0).prod W.law) := by
  let := W.isProbability
  exact (memLp_const (6 : ℝ)).mono' (measurable_potentialIntegral W β hβ V).aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using potentialIntegral_bound W β hβ V u))

theorem potentialLeftSum_tendsto_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law,
      Tendsto (fun l => potentialLeftSum W β V l u) atTop (𝓝 (potentialIntegral W β hβ V u)) := by
  filter_upwards [actualRowPotential_continuous_ae W β] with u hu
  have hh := scalarStieltjes_left_sums_tendsto (negativeSusceptibility W β hβ)
    (fun t => LJ.actualRowPotential W β t.toNNReal u) hu V V.coe_nonneg
    (fun l k => ((brownianDyadicGrid V).time l k : ℝ)) (fun l => 2 ^ l) (brownianDyadicWidth V)
    (fun l => by simp [(brownianDyadicGrid V).zero l])
    (fun l => by simp [brownianDyadicGrid])
    (fun l i hi => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr (LM3.dyadic_time_le_horizon V l i hi)⟩)
    (fun l i _ => NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l (Nat.le_succ i)))
    (fun l i _ => brownianDyadicGrid_width_le V l i) (brownianDyadicWidth_tendsto V)
  have he : (fun l => ∑ k ∈ Finset.range (2 ^ l), negativeSusceptibility W β hβ
      ((brownianDyadicGrid V).time l k) *
        (LJ.actualRowPotential W β (((brownianDyadicGrid V).time l (k + 1) : ℝ).toNNReal) u -
          LJ.actualRowPotential W β (((brownianDyadicGrid V).time l k : ℝ).toNNReal) u)) =
      fun l => -potentialLeftSum W β V l u := by
    funext l
    simp only [potentialLeftSum, negativeSusceptibility_nnreal, Real.toNNReal_coe, neg_mul,
      Finset.sum_neg_distrib]
  rw [he] at hh
  simpa only [potentialIntegral, negativeSusceptibility_nnreal, negativeSusceptibility_zero, NNReal.coe_zero,
    Real.toNNReal_coe, Real.toNNReal_zero, neg_sub, neg_add_rev, neg_neg, neg_mul,
    sub_neg_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh.neg

theorem potentialLeftSum_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∀ l, Integrable (fun u => (potentialLeftSum W β V l u - potentialIntegral W β hβ V u) ^ 2)
      ((scalarHiddenPriorBool 0).prod W.law)) ∧
    Tendsto (fun l => ∫ u, (potentialLeftSum W β V l u - potentialIntegral W β hβ V u) ^ 2
      ∂(scalarHiddenPriorBool 0).prod W.law) atTop (𝓝 0) := by
  let := W.isProbability
  refine ⟨fun l => ((potentialLeftSum_memLp W β hβ V l).sub (potentialIntegral_memLp W β hβ V)).integrable_sq, ?_⟩
  have hh := tendsto_integral_of_dominated_convergence (μ := (scalarHiddenPriorBool 0).prod W.law)
    (f := fun _ : Bool × Ω => (0 : ℝ))
    (F := fun l u => (potentialLeftSum W β V l u - potentialIntegral W β hβ V u) ^ 2)
    (bound := fun _ => (144 : ℝ))
    (fun l => by simpa only [Pi.sub_apply] using (((measurable_potentialLeftSum W β V l).sub
      (measurable_potentialIntegral W β hβ V)).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun l => ae_of_all _ (fun u => ?_)) ?_
  · simpa only [integral_zero] using hh
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha := (abs_sub _ _).trans (add_le_add (potentialLeftSum_bound W β hβ V l u)
      (potentialIntegral_bound W β hβ V u))
    nlinarith [sq_abs (potentialLeftSum W β V l u - potentialIntegral W β hβ V u),
      abs_nonneg (potentialLeftSum W β V l u - potentialIntegral W β hβ V u)]
  · filter_upwards [potentialLeftSum_tendsto_ae W β hβ V] with u hu
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      (hu.sub_const (potentialIntegral W β hβ V u)).pow 2

end SKConstants.Completion.SJ3
