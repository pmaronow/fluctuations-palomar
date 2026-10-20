module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.ScalarProcessLogCosh
public import SKConstants.Completion.LQ.ActualProfileBounds
public import SKConstants.Upstream.OAI.Probability.SKSupport.Diffusion.BoundedDiffusionProperties
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S33aB
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem log_link_taylor_cell (b : Bool) (z y dM h : ℝ) :
    Real.log (1 + scalarHiddenSign b * Real.tanh y) -
        Real.log (1 + scalarHiddenSign b * Real.tanh z) -
        (scalarHiddenSign b - Real.tanh z) * dM +
        (scalarHiddenSign b - Real.tanh z) ^ 2 * h / 2 =
      (scalarHiddenSign b - Real.tanh z) * (y - z - dM - Real.tanh z * h) -
        scalarDefect z * ((y - z) ^ 2 - h) / 2 - scalarLogCoshTaylorResidual z y := by
  rw [LJ.log_sign_tanh_link b y, LJ.log_sign_tanh_link b z]
  have hs : scalarHiddenSign b ^ 2 = 1 := by cases b <;> norm_num [scalarHiddenSign]
  dsimp [scalarLogCoshTaylorResidual, scalarLogCosh, scalarDefect]
  linear_combination (h / 2) * hs

theorem posterior_eq_tanh (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (ht : parisiEquilibriumPhysicalEndpoint β ≤ t) (w : Ω) :
    actualParisiFullPosteriorMean W β t w =
      Real.tanh (actualParisiFullScalarProcess W β t w) := by
  have hv : β ^ 2 * parisiEquilibriumSupportEndpoint β ≤ (t : ℝ) := by
    rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact_mod_cast ht
  exact congrFun (actualParisiFullMagnetization_eq_tanh_after_support β hβ t hv) _

theorem log_link_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (ht : parisiEquilibriumPhysicalEndpoint β ≤ t) (u : Bool × Ω) :
    Real.log (actualParisiFullTerminalSpinDensity β W t u) =
      scalarHiddenSign u.1 * actualParisiFullScalarProcess W β t u.2 -
        scalarLogCosh (actualParisiFullScalarProcess W β t u.2) := by
  change Real.log (1 + scalarHiddenSign u.1 * actualParisiFullPosteriorMean W β t u.2) = _
  rw [posterior_eq_tanh W β hβ t ht]
  exact LJ.log_sign_tanh_link u.1 _

def logTaylorError (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  scalarLogCoshTaylorResidual (actualParisiFullScalarProcess W β s w)
    (actualParisiFullScalarProcess W β t w)

theorem logTaylorError_abs_le (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) :
    |logTaylorError W β s t w| ≤
      |actualParisiFullScalarProcess W β t w - actualParisiFullScalarProcess W β s w| ^ 3 / 3 :=
  scalarLogCosh_taylor_two_abs_le _ _

def driftError (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiFullScalarProcess W β t w - actualParisiFullScalarProcess W β s w -
    (W.B t w - W.B s w) - actualParisiFullPosteriorMean W β s w * ((t : ℝ) - s)

def quadraticError (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  scalarDefect (actualParisiFullScalarProcess W β s w) *
    ((actualParisiFullScalarProcess W β t w - actualParisiFullScalarProcess W β s w) ^ 2 -
      ((t : ℝ) - s)) / 2

def rotationError (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (u : (Bool × Ω) × A) : ℝ :=
  (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) *
    ((W.B t u.1.2 - W.B s u.1.2) - actualParisiQueryRho W β s *
      ((actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
        (actualParisiQueryBrownianSystem W Z β hβ).B s (u.1.2, u.2)) -
      actualParisiQuerySigma W β s *
      ((actualParisiAuxBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
        (actualParisiAuxBrownianSystem W Z β hβ).B s (u.1.2, u.2)))

def queryCell (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (u : (Bool × Ω) × A) : ℝ :=
  Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) *
    (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) *
    ((actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
      (actualParisiQueryBrownianSystem W Z β hβ).B s (u.1.2, u.2))

def dCell (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (u : (Bool × Ω) × A) : ℝ :=
  LM4b.actualRowDCoefficient W β s u *
    ((actualParisiAuxBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
      (actualParisiAuxBrownianSystem W Z β hβ).B s (u.1.2, u.2))

omit [MeasurableSpace A] in
theorem bracket_density_split (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (u : (Bool × Ω) × A) :
    LM4b.actualRowDCoefficient W β t u ^ 2 +
        β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β t *
          actualParisiPinningError W β t u.1 =
      actualParisiPinningError W β t u.1 := by
  rw [LM4b.actualRowDCoefficient_eq_defect W β hβ]
  change (actualParisiQuerySigma W β t *
    (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2)) ^ 2 +
      β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β t *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2) ^ 2 =
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2) ^ 2
  have hr := LQ.actual_rho_sq_eq W β hβ t t.coe_nonneg
  have hu := actualParisiQueryRhoSigma_unit W β hβ t
  rw [mul_pow, ← hr]
  linear_combination (scalarHiddenSign u.1.1 -
    actualParisiFullPosteriorMean W β t u.1.2) ^ 2 * hu

theorem compensated_cell_eq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0)
    (hs : parisiEquilibriumPhysicalEndpoint β ≤ s)
    (ht : parisiEquilibriumPhysicalEndpoint β ≤ t) (u : (Bool × Ω) × A) :
    Real.log (actualParisiFullTerminalSpinDensity β W t u.1) -
        Real.log (actualParisiFullTerminalSpinDensity β W s u.1) -
        dCell W Z β hβ s t u - β * queryCell W Z β hβ s t u +
        (LM4b.actualRowDCoefficient W β s u ^ 2 +
          β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β s *
            actualParisiPinningError W β s u.1) * ((t : ℝ) - s) / 2 =
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) *
          driftError W β s t u.1.2 - quadraticError W β s t u.1.2 -
        logTaylorError W β s t u.1.2 + rotationError W Z β hβ s t u := by
  rw [bracket_density_split W β hβ]
  have hr := LQ.actual_rho_eq W β hβ s s.coe_nonneg
  rw [log_link_eq W β hβ t ht, log_link_eq W β hβ s hs]
  rw [dCell, LM4b.actualRowDCoefficient_eq_defect W β hβ]
  dsimp [queryCell, driftError, quadraticError, logTaylorError, rotationError]
  have hcell := log_link_taylor_cell u.1.1
    (actualParisiFullScalarProcess W β s u.1.2)
    (actualParisiFullScalarProcess W β t u.1.2)
    (W.B t u.1.2 - W.B s u.1.2) ((t : ℝ) - s)
  rw [LJ.log_sign_tanh_link, LJ.log_sign_tanh_link] at hcell
  dsimp only [actualParisiPinningError]
  change _ = _
  simp only [show actualParisiMagnetizationObservable W β s u.1.2 =
    actualParisiFullPosteriorMean W β s u.1.2 from rfl,
    posterior_eq_tanh W β hβ s hs, hr]
  dsimp only [scalarLogCosh]
  linear_combination hcell

theorem compensated_telescope (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (N : ℕ)
    (ht : ∀ k ≤ N, parisiEquilibriumPhysicalEndpoint β ≤ t k)
    (u : (Bool × Ω) × A) :
    Real.log (actualParisiFullTerminalSpinDensity β W (t N) u.1) -
        Real.log (actualParisiFullTerminalSpinDensity β W (t 0) u.1) -
        (∑ k ∈ Finset.range N, dCell W Z β hβ (t k) (t (k + 1)) u) -
        β * (∑ k ∈ Finset.range N, queryCell W Z β hβ (t k) (t (k + 1)) u) +
        (∑ k ∈ Finset.range N,
          (LM4b.actualRowDCoefficient W β (t k) u ^ 2 +
            β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β (t k) *
              actualParisiPinningError W β (t k) u.1) *
              ((t (k + 1) : ℝ) - t k) / 2) =
      ∑ k ∈ Finset.range N,
        ((scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t k) u.1.2) *
          driftError W β (t k) (t (k + 1)) u.1.2 -
          quadraticError W β (t k) (t (k + 1)) u.1.2 -
          logTaylorError W β (t k) (t (k + 1)) u.1.2 +
          rotationError W Z β hβ (t k) (t (k + 1)) u) := by
  calc
    _ = ∑ k ∈ Finset.range N,
        (Real.log (actualParisiFullTerminalSpinDensity β W (t (k + 1)) u.1) -
          Real.log (actualParisiFullTerminalSpinDensity β W (t k) u.1) -
          dCell W Z β hβ (t k) (t (k + 1)) u -
          β * queryCell W Z β hβ (t k) (t (k + 1)) u +
          (LM4b.actualRowDCoefficient W β (t k) u ^ 2 +
            β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β (t k) *
              actualParisiPinningError W β (t k) u.1) *
              ((t (k + 1) : ℝ) - t k) / 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_range_sub (fun k =>
          Real.log (actualParisiFullTerminalSpinDensity β W (t k) u.1)) N,
        ← Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact compensated_cell_eq W Z β hβ _ _
        (ht k (Finset.mem_range.mp hk).le) (ht (k + 1) (Finset.mem_range.mp hk)) u

theorem dCell_dyadic_sum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) :
    (∑ k ∈ Finset.range (2 ^ l), dCell W Z β hβ
      ((brownianDyadicGrid V).time l k) ((brownianDyadicGrid V).time l (k + 1)) u) =
      LM4b.actualRowDLeftSum W Z β hβ V l u := rfl

theorem queryCell_dyadic_sum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) :
    (∑ k ∈ Finset.range (2 ^ l), queryCell W Z β hβ
      ((brownianDyadicGrid V).time l k) ((brownianDyadicGrid V).time l (k + 1)) u) =
      SJ3.queryRowLeftSum W Z β hβ V l u := rfl

def gaussianSixthMoment : ℝ := ∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1

theorem gaussianSixthMoment_nonneg : 0 ≤ gaussianSixthMoment :=
  integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 6)

theorem brownian_increment_sixth (W : BrownianSystem Ω) (s h : ℝ≥0) :
    (∫ w, |W.B (s + h) w - W.B s w| ^ 6 ∂W.law) =
      (h : ℝ) ^ 3 * gaussianSixthMoment := by
  have hl := W.brownian.toIsPreBrownianReal.hasLaw_sub (s + h) s
  have he := hl.integral_comp (WeakIto.gaussian_abs_pow_integrable 6 _).aestronglyMeasurable
  change (∫ w, |W.B (s + h) w - W.B s w| ^ 6 ∂W.law) = _ at he
  have hd : nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ) = h := by
    ext
    simp only [coe_nndist, Real.dist_eq, NNReal.coe_add, add_sub_cancel_left,
      abs_of_nonneg h.coe_nonneg]
  have heq := congrArg (fun v : ℝ≥0 => ∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 v) hd
  calc
    _ = ∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 h := he.trans heq
    _ = _ := by
      rw [WeakIto.gaussian_abs_pow]
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt h.coe_nonneg]
      rfl

theorem field_increment_sixth_le (W : BrownianSystem Ω) (β : ℝ) (s h : ℝ≥0) :
    Integrable (fun w => |actualParisiFullScalarProcess W β (s + h) w -
      actualParisiFullScalarProcess W β s w| ^ 6) W.law ∧
    (∫ w, |actualParisiFullScalarProcess W β (s + h) w -
      actualParisiFullScalarProcess W β s w| ^ 6 ∂W.law) ≤
      32 * ((h : ℝ) ^ 3 * gaussianSixthMoment + (h : ℝ) ^ 6) := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  have hm : Measurable (fun w => actualParisiFullScalarProcess W β (s + h) w -
      actualParisiFullScalarProcess W β s w) :=
    (b.solution_measurable W _).sub (b.solution_measurable W _)
  have hM : Integrable (fun w => |W.B (s + h) w - W.B s w| ^ 6) W.law :=
    (W.brownian.toIsPreBrownianReal.hasLaw_sub (s + h) s).integrable_comp
      (WeakIto.gaussian_abs_pow_integrable 6 _)
  have hu : Integrable (fun w => 32 * (|W.B (s + h) w - W.B s w| ^ 6 +
      (h : ℝ) ^ 6)) W.law := by
    simpa only [Pi.add_apply] using (hM.add (integrable_const ((h : ℝ) ^ 6))).const_mul 32
  have hb : ∀ᵐ w ∂W.law,
      |actualParisiFullScalarProcess W β (s + h) w - actualParisiFullScalarProcess W β s w| ^ 6 ≤
        32 * (|W.B (s + h) w - W.B s w| ^ 6 + (h : ℝ) ^ 6) := by
    filter_upwards [b.solution_increment W s h] with w hw
    change b.solution W.driver (s + h) w = _ at hw
    change |b.solution W.driver (s + h) w - b.solution W.driver s w| ^ 6 ≤ _
    rw [hw, add_assoc, add_sub_cancel_left]
    have hd : |b.displacement W s (s + h) w| ≤ (h : ℝ) := by
      simpa only [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg,
        show (b.bound : ℝ) = 1 from rfl, one_mul] using b.displacement_bound W s (s + h) w
    calc
      _ ≤ (|W.B (s + h) w - W.B s w| + |b.displacement W s (s + h) w|) ^ 6 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 6
      _ ≤ 32 * (|W.B (s + h) w - W.B s w| ^ 6 + |b.displacement W s (s + h) w| ^ 6) := by
        simpa only [show (2 : ℝ) ^ (6 - 1 : ℕ) = 32 from by norm_num] using add_pow_le (abs_nonneg (W.B (s + h) w - W.B s w))
          (abs_nonneg (b.displacement W s (s + h) w)) 6
      _ ≤ _ := by gcongr
  have hi : Integrable (fun w => |actualParisiFullScalarProcess W β (s + h) w -
      actualParisiFullScalarProcess W β s w| ^ 6) W.law := by
    apply hu.mono' (hm.norm.pow_const 6).aestronglyMeasurable
    filter_upwards [hb] with w hw
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hw
  refine ⟨hi, (integral_mono_ae hi hu hb).trans_eq ?_⟩
  rw [integral_const_mul, integral_add hM (integrable_const _),
    brownian_increment_sixth, integral_const, probReal_univ, one_smul]

attribute [local irreducible] actualParisiFullScalarDrift BrownianSystem.driver

theorem measurable_logTaylorError (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) :
    Measurable (logTaylorError W β s t) := by
  have hr : Continuous (fun p : ℝ × ℝ => scalarLogCoshTaylorResidual p.1 p.2) := by
    unfold scalarLogCoshTaylorResidual
    exact (((continuous_scalarLogCosh.comp continuous_snd).sub
      (continuous_scalarLogCosh.comp continuous_fst)).sub
      ((continuous_scalarTanh.comp continuous_fst).mul
        (continuous_snd.sub continuous_fst))).sub
      (((continuous_scalarDefect_actual.comp continuous_fst).mul
        ((continuous_snd.sub continuous_fst).pow 2)).div_const 2)
  change Measurable ((fun p : ℝ × ℝ => scalarLogCoshTaylorResidual p.1 p.2) ∘
    (fun w => ((actualParisiFullScalarDrift β).solution W.driver s w,
      (actualParisiFullScalarDrift β).solution W.driver t w)))
  apply hr.measurable.comp
  exact ((actualParisiFullScalarDrift β).solution_measurable W s).prodMk
    ((actualParisiFullScalarDrift β).solution_measurable W t)

theorem logTaylorError_square_le (W : BrownianSystem Ω) (β : ℝ) (s h : ℝ≥0) :
    Integrable (fun w => logTaylorError W β s (s + h) w ^ 2) W.law ∧
    (∫ w, logTaylorError W β s (s + h) w ^ 2 ∂W.law) ≤
      32 / 9 * ((h : ℝ) ^ 3 * gaussianSixthMoment + (h : ℝ) ^ 6) := by
  have hf := field_increment_sixth_le W β s h
  have hm := measurable_logTaylorError W β s (s + h)
  have hb (w : Ω) : logTaylorError W β s (s + h) w ^ 2 ≤
      |actualParisiFullScalarProcess W β (s + h) w - actualParisiFullScalarProcess W β s w| ^ 6 / 9 := by
    have ht := logTaylorError_abs_le W β s (s + h) w
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr ht
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (logTaylorError W β s (s + h) w)]
  have hi : Integrable (fun w => logTaylorError W β s (s + h) w ^ 2) W.law := by
    apply (hf.1.div_const 9).mono' (hm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hb w)
  refine ⟨hi, (integral_mono hi (hf.1.div_const 9) hb).trans ?_⟩
  rw [integral_div]
  nlinarith [hf.2]

def logTaylorUniformSum (W : BrownianSystem Ω) (β : ℝ) (s h : ℝ≥0) (N : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, logTaylorError W β (s + (k : ℝ≥0) * h)
    (s + ((k + 1 : ℕ) : ℝ≥0) * h) w

theorem logTaylorUniformSum_square_le (W : BrownianSystem Ω) (β : ℝ) (s h : ℝ≥0) (N : ℕ) :
    Integrable (fun w => logTaylorUniformSum W β s h N w ^ 2) W.law ∧
    (∫ w, logTaylorUniformSum W β s h N w ^ 2 ∂W.law) ≤
      (N : ℝ) ^ 2 * (32 / 9 * ((h : ℝ) ^ 3 * gaussianSixthMoment + (h : ℝ) ^ 6)) := by
  let R := fun (k : ℕ) => logTaylorError W β (s + (k : ℝ≥0) * h)
    (s + ((k + 1 : ℕ) : ℝ≥0) * h)
  have hR (k : ℕ) : Integrable (fun w => R k w ^ 2) W.law ∧
      (∫ w, R k w ^ 2 ∂W.law) ≤ 32 / 9 * ((h : ℝ) ^ 3 * gaussianSixthMoment + (h : ℝ) ^ 6) := by
    simpa only [R, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc] using
      logTaylorError_square_le W β (s + (k : ℝ≥0) * h) h
  have hmem (k : ℕ) : MemLp (R k) 2 W.law :=
    (memLp_two_iff_integrable_sq
      (measurable_logTaylorError W β _ _).aestronglyMeasurable).mpr (hR k).1
  have hi : Integrable (fun w => logTaylorUniformSum W β s h N w ^ 2) W.law :=
    (memLp_finsetSum (Finset.range N) (fun k _ => hmem k)).integrable_sq
  have hs : Integrable (fun w => (N : ℝ) * ∑ k ∈ Finset.range N, R k w ^ 2) W.law :=
    (integrable_finsetSum _ (fun k _ => (hR k).1)).const_mul _
  have hp (w : Ω) : logTaylorUniformSum W β s h N w ^ 2 ≤
      (N : ℝ) * ∑ k ∈ Finset.range N, R k w ^ 2 := by
    simpa only [logTaylorUniformSum, R, one_mul, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
      using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun _ => (1 : ℝ)) (fun k => R k w)
  refine ⟨hi, (integral_mono hi hs hp).trans ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => (hR k).1)]
  calc
    _ ≤ (N : ℝ) * ∑ _k ∈ Finset.range N,
        (32 / 9 * ((h : ℝ) ^ 3 * gaussianSixthMoment + (h : ℝ) ^ 6)) := by
      gcongr with k hk
      exact (hR k).2
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

def logTaylorDyadicSum (W : BrownianSystem Ω) (β : ℝ) (s T : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  logTaylorUniformSum W β s (T / (2 : ℝ≥0) ^ l) (2 ^ l) w

theorem logTaylorDyadicSum_eq (W : BrownianSystem Ω) (β : ℝ) (s T : ℝ≥0) (l : ℕ) (w : Ω) :
    logTaylorDyadicSum W β s T l w =
      ∑ k ∈ Finset.range (2 ^ l), logTaylorError W β
        (s + (brownianDyadicGrid T).time l k) (s + (brownianDyadicGrid T).time l (k + 1)) w := by
  unfold logTaylorDyadicSum logTaylorUniformSum
  apply Finset.sum_congr rfl
  intro k _
  congr 2 <;> simp only [brownianDyadicGrid] <;> ring

theorem logTaylorDyadicSum_square_le (W : BrownianSystem Ω) (β : ℝ) (s T : ℝ≥0) (l : ℕ) :
    Integrable (fun w => logTaylorDyadicSum W β s T l w ^ 2) W.law ∧
    (∫ w, logTaylorDyadicSum W β s T l w ^ 2 ∂W.law) ≤
      (32 / 9 * (gaussianSixthMoment + (T : ℝ) ^ 3) * (T : ℝ) ^ 3) / (2 : ℝ) ^ l := by
  have H := logTaylorUniformSum_square_le W β s (T / (2 : ℝ≥0) ^ l) (2 ^ l)
  refine ⟨H.1, H.2.trans ?_⟩
  simp only [Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  have hd : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
  have ht : (T : ℝ) / (2 : ℝ) ^ l ≤ (T : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [T.coe_nonneg]
  have hp : ((T : ℝ) / (2 : ℝ) ^ l) ^ 6 ≤
      ((T : ℝ) / (2 : ℝ) ^ l) ^ 3 * (T : ℝ) ^ 3 := by
    calc
      _ = ((T : ℝ) / (2 : ℝ) ^ l) ^ 3 * ((T : ℝ) / (2 : ℝ) ^ l) ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht 3) (by positivity)
  calc
    _ ≤ ((2 : ℝ) ^ l) ^ 2 * (32 / 9 *
        (((T : ℝ) / (2 : ℝ) ^ l) ^ 3 * gaussianSixthMoment +
          ((T : ℝ) / (2 : ℝ) ^ l) ^ 3 * (T : ℝ) ^ 3)) := by gcongr
    _ = _ := by field_simp

theorem logTaylorDyadicSum_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (s T : ℝ≥0) :
    Tendsto (fun l => ∫ w, logTaylorDyadicSum W β s T l w ^ 2 ∂W.law) atTop (𝓝 0) := by
  apply squeeze_zero (fun l => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => (logTaylorDyadicSum_square_le W β s T l).2)
  have h := (tendsto_const_nhds (x :=
      32 / 9 * (gaussianSixthMoment + (T : ℝ) ^ 3) * (T : ℝ) ^ 3)).mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  simpa only [div_eq_mul_inv, inv_pow, one_div, one_mul, mul_zero] using h

theorem row_projection_measurePreserving (W : BrownianSystem Ω) (Z : BrownianSystem A) :
    MeasurePreserving (fun u : (Bool × Ω) × A => u.1.2) (LM4.actualRowBaseLaw W Z) W.law := by
  let := W.isProbability
  let := Z.isProbability
  exact (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))

theorem logTaylorDyadicSum_tendsto_L2_base (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (s T : ℝ≥0) :
    (∀ l, Integrable (fun u : (Bool × Ω) × A => logTaylorDyadicSum W β s T l u.1.2 ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, logTaylorDyadicSum W β s T l u.1.2 ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  have hp := row_projection_measurePreserving W Z
  constructor
  · intro l
    exact hp.integrable_comp_of_integrable (logTaylorDyadicSum_square_le W β s T l).1
  · convert logTaylorDyadicSum_tendsto_L2 W β s T using 1
    funext l
    exact hp.hasLaw.integral_comp (logTaylorDyadicSum_square_le W β s T l).1.aestronglyMeasurable

theorem queryRowIntegral_unique (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {Q R : (Bool × Ω) × A → ℝ}
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q)
    (hR : SJ3.IsQueryRowIntegral W Z β hβ V R) :
    Q =ᵐ[LM4.actualRowBaseLaw W Z] R :=
  SJ3.meanSquare_limit_unique (SJ3.measurable_queryRowLeftSum W Z β hβ V)
    hQ.2.1 hR.2.1 hQ.2.2.1 hQ.2.2.2 hR.2.2.2

theorem postSupportInformationIto_at_support (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (J Q Qs : (Bool × Ω) × A → ℝ)
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) J)
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Q)
    (hQs : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Qs) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      rowInformationV W β (parisiEquilibriumPhysicalEndpoint β) J u -
        Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u.1) -
        β * (Q u - Qs u) =
      -(β ^ 2 / 2) * ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..
          (parisiEquilibriumPhysicalEndpoint β : ℝ),
        actualParisiFullSusceptibilitySquareExpected W β t * actualParisiPinningError W β t.toNNReal u.1 := by
  have hzero := SJ3.rowDIntegral_unique W Z β hβ _ hJ
    (SJ3.rowDIntegral_zero_pre W Z β hβ _ le_rfl)
  filter_upwards [hzero, queryRowIntegral_unique W Z β hβ _ hQ hQs] with u hu hq
  simp only [rowInformationV, LM4.actualRowInformation, LM4.rowInformation, LM4.actualRowLink,
    SJ3.rowDBracket_eq_zero_pre W β hβ _ le_rfl, hu, hq, sub_self, sub_zero,
    zero_div, add_zero, mul_zero, intervalIntegral.integral_same]

theorem posterior_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, Continuous (fun t : ℝ≥0 => actualParisiFullPosteriorMean W β t w) := by
  filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
  change Continuous ((fun p : ℝ × ℝ => actualParisiFullMagnetization β p.1 p.2) ∘
    (fun t : ℝ≥0 => ((t : ℝ), (actualParisiFullScalarDrift β).solution W.driver t w)))
  exact (continuous_actualParisiFullMagnetization β).comp (NNReal.continuous_coe.prodMk hw)

theorem post_bracket_split_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      LM4b.actualRowDBracket W β V u +
        β ^ 2 * (∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
          actualParisiFullSusceptibilitySquareExpected W β t *
            actualParisiPinningError W β t.toNNReal u.1) =
      ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
        actualParisiPinningError W β t.toNNReal u.1 := by
  have hc := (row_projection_measurePreserving W Z).quasiMeasurePreserving.ae
    (posterior_continuous_ae W β)
  filter_upwards [hc] with u hu
  let S := parisiEquilibriumPhysicalEndpoint β
  have hm : Continuous (fun t : ℝ => actualParisiFullPosteriorMean W β t.toNNReal u.1.2) :=
    hu.comp continuous_real_toNNReal
  have he : Continuous (fun t : ℝ => actualParisiPinningError W β t.toNNReal u.1) :=
    (continuous_const.sub hm).pow 2
  have hs : Continuous (fun t : ℝ => actualParisiQuerySigma W β (t.toNNReal : ℝ)) :=
    (continuous_actualParisiQuerySigma W β).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)
  have hd : Continuous (fun t : ℝ => LM4b.actualRowDCoefficient W β t.toNNReal u ^ 2) := by
    have hh : (fun t : ℝ => LM4b.actualRowDCoefficient W β t.toNNReal u ^ 2) =
        (fun t => (actualParisiQuerySigma W β (t.toNNReal : ℝ) *
          (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t.toNNReal u.1.2)) ^ 2) := by
      funext t
      rw [LM4b.actualRowDCoefficient_eq_defect W β hβ]
      rfl
    rw [hh]
    exact (hs.mul (continuous_const.sub hm)).pow 2
  have hr : Continuous (fun t : ℝ => actualParisiFullSusceptibilitySquareExpected W β t *
      actualParisiPinningError W β t.toNNReal u.1) :=
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).mul he
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hd.intervalIntegrable 0 S) (hd.intervalIntegrable S V)
  change LM4b.actualRowDBracket W β S u +
      (∫ t in (S : ℝ)..(V : ℝ), LM4b.actualRowDCoefficient W β t.toNNReal u ^ 2) =
      LM4b.actualRowDBracket W β V u at hadd
  rw [SJ3.rowDBracket_eq_zero_pre W β hβ S le_rfl, zero_add] at hadd
  rw [← hadd, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hd.intervalIntegrable S V) ((hr.const_mul _).intervalIntegrable S V)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := S.coe_nonneg.trans ((min_le_iff.mp ht.1).elim id
    (fun htV => (NNReal.coe_le_coe.mpr hV).trans htV))
  have hb := bracket_density_split W β hβ t.toNNReal u
  simpa only [Real.coe_toNNReal t ht0, mul_assoc] using hb

theorem field_increment_eq_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, ∀ s t : ℝ≥0,
      actualParisiFullScalarProcess W β t w - actualParisiFullScalarProcess W β s w =
        W.B t w - W.B s w + (actualParisiFullScalarDrift β).displacement W s t w := by
  filter_upwards [W.driver_indistinguishable] with w hw
  intro s t
  let b := actualParisiFullScalarDrift β
  change b.solution W.driver t w - b.solution W.driver s w = _
  rw [b.solution_eq _ W.driver_progressive, b.solution_eq _ W.driver_progressive, hw t, hw s]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (b.pathDrift_integrable W 0 s w) (b.pathDrift_integrable W s t w)
  change (∫ r in (0 : ℝ)..(s : ℝ), b.pathDrift W r w) + b.displacement W s t w =
    ∫ r in (0 : ℝ)..(t : ℝ), b.pathDrift W r w at hadd
  change _ = W.B t w - W.B s w + b.displacement W s t w
  dsimp only [BoundedLipschitzDrift.pathDrift] at hadd
  linarith

theorem driftError_eq_integral_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∀ᵐ w ∂W.law, ∀ s t : ℝ≥0, parisiEquilibriumPhysicalEndpoint β ≤ s → s ≤ t →
      driftError W β s t w = ∫ r in (s : ℝ)..(t : ℝ),
        actualParisiFullPosteriorMean W β r.toNNReal w - actualParisiFullPosteriorMean W β s w := by
  filter_upwards [field_increment_eq_ae W β, posterior_continuous_ae W β] with w hw hc
  intro s t hs hst
  have hm : Continuous (fun r : ℝ => actualParisiFullPosteriorMean W β r.toNNReal w) :=
    hc.comp continuous_real_toNNReal
  have hd : (actualParisiFullScalarDrift β).displacement W s t w =
      ∫ r in (s : ℝ)..(t : ℝ), actualParisiFullPosteriorMean W β r.toNNReal w := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_le_coe.mpr hst)] at hr
    have hr0 := s.coe_nonneg.trans hr.1
    have hSr : parisiEquilibriumPhysicalEndpoint β ≤ r.toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal r hr0]
      exact (NNReal.coe_le_coe.mpr hs).trans hr.1
    have hphys : β ^ 2 * parisiEquilibriumSupportEndpoint β ≤ (r.toNNReal : ℝ) := by
      rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
      exact_mod_cast hSr
    change (actualParisiFullScalarDrift β).f (r.toNNReal : ℝ)
      (actualParisiFullScalarProcess W β r.toNNReal w) = _
    rw [actualParisiFullScalarDrift_eq_tanh_after_support β hβ _ hphys]
    exact (posterior_eq_tanh W β hβ _ hSr w).symm
  rw [intervalIntegral.integral_sub (hm.intervalIntegrable s t) intervalIntegrable_const,
    intervalIntegral.integral_const]
  change _ = (∫ r in (s : ℝ)..(t : ℝ), actualParisiFullPosteriorMean W β r.toNNReal w) -
    ((t : ℝ) - s) * actualParisiFullPosteriorMean W β s w
  dsimp only [driftError]
  rw [hw s t, hd]
  ring

def weightedQuadratureError (f : ℝ → ℝ) (x : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (x - f (a k)) * ∫ r in a k..a (k + 1), f r - f (a k)

theorem weightedQuadratureError_abs_le (f : ℝ → ℝ) (x : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (ha : Monotone a) (η : ℝ)
    (hcap : ∀ k < N, |x - f (a k)| ≤ 2)
    (hmod : ∀ k < N, ∀ r ∈ Icc (a k) (a (k + 1)), |f r - f (a k)| ≤ η) :
    |weightedQuadratureError f x a N| ≤ 2 * η * (a N - a 0) := by
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        |(x - f (a k)) * ∫ r in a k..a (k + 1), f r - f (a k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, 2 * η * (a (k + 1) - a k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkk := ha (Nat.le_succ k)
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a k) (b := a (k + 1)) (f := fun r => f r - f (a k))
        (C := η) (fun r hr => by
          rw [uIoc_of_le hkk] at hr
          simpa only [Real.norm_eq_abs] using hmod k (Finset.mem_range.mp hk) r ⟨hr.1.le, hr.2⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hkk)] at hi
      rw [abs_mul]
      exact (mul_le_mul (hcap k (Finset.mem_range.mp hk)) hi (abs_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

theorem weightedQuadratureError_dyadic_tendsto (f : ℝ → ℝ) (hf : Continuous f)
    (hcap : ∀ r, |f r| ≤ 1) (b : Bool) (s T : ℝ≥0) :
    Tendsto (fun l => weightedQuadratureError f (scalarHiddenSign b)
      (fun k => ((s + (brownianDyadicGrid T).time l k : ℝ≥0) : ℝ)) (2 ^ l)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (2 * ((T : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨d, hd, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hf.continuousOn : ContinuousOn f (Icc (s : ℝ) (s + T : ℝ≥0)))) η hη
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    ((brownianDyadicWidth_tendsto T).eventually (eventually_lt_nhds hd))
  refine ⟨L, fun l hl => ?_⟩
  let a := fun k => ((s + (brownianDyadicGrid T).time l k : ℝ≥0) : ℝ)
  have ha : Monotone a := fun i j hij => by
    change (s : ℝ) + ((brownianDyadicGrid T).time l i : ℝ) ≤
      (s : ℝ) + ((brownianDyadicGrid T).time l j : ℝ)
    linarith [NNReal.coe_le_coe.mpr ((brownianDyadicGrid T).monotone l hij)]
  have hz : a 0 = (s : ℝ) := by simp [a]
  have hT : a (2 ^ l) = (s + T : ℝ≥0) := by simp [a, brownianDyadicGrid]
  have hmem (k : ℕ) (hk : k ≤ 2 ^ l) : a k ∈ Icc (s : ℝ) (s + T : ℝ≥0) := by
    constructor
    · rw [← hz]; exact ha (Nat.zero_le _)
    · rw [← hT]; exact ha hk
  have hwidth (k : ℕ) : a (k + 1) - a k = brownianDyadicWidth T l := by
    simp only [a, NNReal.coe_add, brownianDyadicGrid_time_coe, brownianDyadicWidth,
      Nat.cast_add, Nat.cast_one]
    ring
  have hbound := weightedQuadratureError_abs_le f (scalarHiddenSign b) a (2 ^ l) ha η
    (fun k _ => by
      have hx : |scalarHiddenSign b| = 1 := by cases b <;> norm_num [scalarHiddenSign]
      exact (abs_sub _ _).trans (by rw [hx]; linarith [hcap (a k)])) (fun k hk r hr => by
      have hkr : r ∈ Icc (s : ℝ) (s + T : ℝ≥0) :=
        ⟨(hmem k hk.le).1.trans hr.1, hr.2.trans (hmem (k + 1) hk).2⟩
      have hdr : dist (a k) r < d := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hr.1)]
        exact (sub_le_sub_right hr.2 _).trans_lt ((hwidth k).le.trans_lt (hL l hl))
      exact (show |f r - f (a k)| < η by
        simpa only [Real.dist_eq, abs_sub_comm] using hUC _ (hmem k hk.le) _ hkr hdr).le)
  rw [hz, hT, NNReal.coe_add, add_sub_cancel_left] at hbound
  rw [Real.dist_eq, sub_zero]
  apply hbound.trans_lt
  dsimp [η]
  calc
    _ = ε * (T : ℝ) / ((T : ℝ) + 1) := by field_simp
    _ < ε := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) + 1)).mpr
      nlinarith

theorem measurable_driftError (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) :
    Measurable (driftError W β s t) := by
  have hY (v : ℝ≥0) : Measurable (actualParisiFullScalarProcess W β v) :=
    (actualParisiFullScalarDrift β).solution_measurable W v
  exact (((hY t).sub (hY s)).sub ((W.measurable t).sub (W.measurable s))).sub
    ((measurable_actualParisiFullPosteriorMean W β s).mul_const _)

def driftDyadicSum (W : BrownianSystem Ω) (β : ℝ) (s T : ℝ≥0) (l : ℕ)
    (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β
      (s + (brownianDyadicGrid T).time l k) u.1.2) *
    driftError W β (s + (brownianDyadicGrid T).time l k)
      (s + (brownianDyadicGrid T).time l (k + 1)) u.1.2

theorem measurable_driftDyadicSum (W : BrownianSystem Ω) (β : ℝ) (s T : ℝ≥0) (l : ℕ) :
    Measurable (driftDyadicSum (A := A) W β s T l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
    ((measurable_actualParisiFullPosteriorMean W β _).comp (measurable_snd.comp measurable_fst))).mul
    ((measurable_driftError W β _ _).comp (measurable_snd.comp measurable_fst))

theorem driftDyadicSum_tendsto_L2_base (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (s T : ℝ≥0) (hs : parisiEquilibriumPhysicalEndpoint β ≤ s) :
    (∀ l, Integrable (fun u => driftDyadicSum W β s T l u ^ 2) (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, driftDyadicSum W β s T l u ^ 2 ∂LM4.actualRowBaseLaw W Z)
      atTop (𝓝 0) := by
  have hp := row_projection_measurePreserving W Z
  have hpath : ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      (∀ l, |driftDyadicSum W β s T l u| ≤ 4 * (T : ℝ)) ∧
        Tendsto (fun l => driftDyadicSum W β s T l u) atTop (𝓝 0) := by
    filter_upwards [hp.quasiMeasurePreserving.ae (driftError_eq_integral_ae W β hβ),
      hp.quasiMeasurePreserving.ae (posterior_continuous_ae W β)] with u hu hc
    let f := fun r : ℝ => actualParisiFullPosteriorMean W β r.toNNReal u.1.2
    have hf : Continuous f := hc.comp continuous_real_toNNReal
    have hf1 : ∀ r, |f r| ≤ 1 := fun r => abs_actualParisiFullPosteriorMean_le W β _ _
    have heq (l : ℕ) : driftDyadicSum W β s T l u =
        weightedQuadratureError f (scalarHiddenSign u.1.1)
          (fun k => ((s + (brownianDyadicGrid T).time l k : ℝ≥0) : ℝ)) (2 ^ l) := by
      unfold driftDyadicSum weightedQuadratureError
      apply Finset.sum_congr rfl
      intro k _
      have hsk : parisiEquilibriumPhysicalEndpoint β ≤ s + (brownianDyadicGrid T).time l k :=
        hs.trans (le_add_of_nonneg_right (by positivity))
      have hkk : s + (brownianDyadicGrid T).time l k ≤
          s + (brownianDyadicGrid T).time l (k + 1) := by
        gcongr
        exact (brownianDyadicGrid T).monotone l (Nat.le_succ k)
      rw [hu _ _ hsk hkk]
      simp only [f, Real.toNNReal_coe]
    constructor
    · intro l
      rw [heq l]
      have hsign : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
      have ha : Monotone (fun k => ((s + (brownianDyadicGrid T).time l k : ℝ≥0) : ℝ)) := by
        intro i j hij
        simp only [NNReal.coe_add]
        linarith [NNReal.coe_le_coe.mpr ((brownianDyadicGrid T).monotone l hij)]
      have hb := weightedQuadratureError_abs_le f (scalarHiddenSign u.1.1) _ (2 ^ l) ha 2
        (fun k _ => (abs_sub _ _).trans (by rw [hsign]; linarith [hf1 ((s + (brownianDyadicGrid T).time l k : ℝ≥0) : ℝ)]))
        (fun k _ r _ => (abs_sub _ _).trans (by linarith [hf1 r, hf1 ((s + (brownianDyadicGrid T).time l k : ℝ≥0) : ℝ)]))
      norm_num [brownianDyadicGrid] at hb ⊢
      exact hb
    · simpa only [heq] using weightedQuadratureError_dyadic_tendsto f hf hf1 u.1.1 s T
  have hdom (l : ℕ) : ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      ‖driftDyadicSum W β s T l u ^ 2‖ ≤ (4 * (T : ℝ)) ^ 2 := by
    filter_upwards [hpath] with u hu
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hu.1 l) 2
  have hi (l : ℕ) : Integrable (fun u => driftDyadicSum W β s T l u ^ 2)
      (LM4.actualRowBaseLaw W Z) :=
    (integrable_const _).mono' (measurable_driftDyadicSum W β s T l |>.pow_const 2).aestronglyMeasurable (hdom l)
  refine ⟨hi, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := LM4.actualRowBaseLaw W Z)
    (bound := fun _ => (4 * (T : ℝ)) ^ 2)
    (fun l => (measurable_driftDyadicSum W β s T l |>.pow_const 2).aestronglyMeasurable)
    (integrable_const _) hdom (by
      filter_upwards [hpath] with u hu
      simpa using hu.2.pow 2)
  simpa using ht

end SKConstants.Completion.S33aB
