module

public import SKConstants.Completion.X73A.Posterior

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X73A
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type} [MeasurableSpace Ω]

def posteriorSquareCompensator (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  ∫ r in (s : ℝ)..(t : ℝ), LJ.actualCurvature W β r.toNNReal w ^ 2

theorem measurable_posteriorSquareCompensator (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) :
    Measurable (posteriorSquareCompensator W β s t) :=
  SKConstantsOAI.ZeroTemperatureSK.WeakIto.measurable_time_integral
    ((LC1.measurable_actualFullCurvature_process_real W β).pow_const 2) _ _

theorem posteriorSquareCompensator_abs_le (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (w : Ω) :
    |posteriorSquareCompensator W β s t w| ≤ (t : ℝ) - s := by
  have h := S73.quadraticIntegral_abs_le (fun _ => 1)
    (fun r => LJ.actualCurvature W β r.toNNReal w) s t (NNReal.coe_le_coe.mpr hst)
    (by simp) (fun r => LJ.actualCurvature_abs_le W β _ w)
  simpa only [one_mul, abs_one, intervalIntegral.integral_const, smul_eq_mul, mul_one,
    posteriorSquareCompensator] using h

def compensatedPosteriorSquare (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiMagnetizationIncrement W β s t w ^ 2 - posteriorSquareCompensator W β s t w

theorem measurable_compensatedPosteriorSquare (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) :
    Measurable (compensatedPosteriorSquare W β s t) :=
  ((measurable_actualParisiMagnetizationIncrement W β s t).pow_const 2).sub
    (measurable_posteriorSquareCompensator W β s t)

theorem compensatedPosteriorSquare_abs_le (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (w : Ω) :
    |compensatedPosteriorSquare W β s t w| ≤ 4 + ((t : ℝ) - s) := by
  apply (abs_sub _ _).trans
  have hd := actualParisiMagnetizationIncrement_abs_le W β s t w
  have hsq : |actualParisiMagnetizationIncrement W β s t w ^ 2| ≤ 4 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (actualParisiMagnetizationIncrement W β s t w)]
  exact add_le_add hsq (posteriorSquareCompensator_abs_le W β s t hst w)

theorem compensatedPosteriorSquare_memLp (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (p : ℝ≥0∞) :
    MemLp (compensatedPosteriorSquare W β s t) p W.law := by
  let := W.isProbability
  exact memLp_of_abs_le W.law _ (measurable_compensatedPosteriorSquare W β s t)
    _ (compensatedPosteriorSquare_abs_le W β s t hst) p

theorem compensatedPosteriorSquare_past_test (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) (F : ScalarContinuousPath s → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
      compensatedPosteriorSquare W β s t w ∂W.law) = 0 := by
  let := W.isProbability
  let f := fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w)
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W _ s)
  have hinc : MemLp (fun w => actualParisiMagnetizationIncrement W β s t w ^ 2) 2 W.law :=
    memLp_of_abs_le W.law _ ((measurable_actualParisiMagnetizationIncrement W β s t).pow_const 2)
      4 (fun w => by
        rw [abs_pow]
        have hh := actualParisiMagnetizationIncrement_abs_le W β s t w
        nlinarith [abs_nonneg (actualParisiMagnetizationIncrement W β s t w)]) 2
  have hbr : MemLp (posteriorSquareCompensator W β s t) 2 W.law :=
    memLp_of_abs_le W.law _ (measurable_posteriorSquareCompensator W β s t) _
      (posteriorSquareCompensator_abs_le W β s t hst) 2
  have hi := integral_sub
    ((memLp_bounded_mul hinc f hf C (fun _ => hC _)).integrable (by norm_num))
    ((memLp_bounded_mul hbr f hf C (fun _ => hC _)).integrable (by norm_num))
  have hs := posteriorIncrement_secondMoment_past_test W β hβ s (t - s) F hF C hC
  rw [add_tsub_cancel_of_le hst] at hs
  have hswap := LC1.bounded_signed_interval_expectation_swap W.law s t f hf C (fun _ => hC _)
    (fun r w => LJ.actualCurvature W β r.toNNReal w ^ 2)
    ((LC1.measurable_actualFullCurvature_process_real W β).pow_const 2) 1 (fun r w => by
      change |LJ.actualCurvature W β r.toNNReal w ^ 2| ≤ (1 : ℝ)
      rw [abs_pow]
      have hh := LJ.actualCurvature_abs_le W β r.toNNReal w
      nlinarith [abs_nonneg (LJ.actualCurvature W β r.toNNReal w)])
  change (∫ w, f w * (actualParisiMagnetizationIncrement W β s t w ^ 2 -
    posteriorSquareCompensator W β s t w) ∂W.law) = 0
  simp_rw [mul_sub]
  rw [hi, hs]
  exact sub_eq_zero.mpr hswap.symm

theorem compensatedPosteriorSquare_secondMoment_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, compensatedPosteriorSquare W β s t w ^ 2 ∂W.law) ≤
      (96 * Real.exp (1 / 2) + 2) * ((t : ℝ) - s) ^ 2 := by
  let := W.isProbability
  have h4 := (memLp_of_abs_le W.law _
    ((measurable_actualParisiMagnetizationIncrement W β s t).pow_const 2) 4
    (fun w => by
      rw [abs_pow]
      have hh := actualParisiMagnetizationIncrement_abs_le W β s t w
      nlinarith [abs_nonneg (actualParisiMagnetizationIncrement W β s t w)]) 2).integrable_sq
  simp only [← pow_mul, show 2 * 2 = 4 from rfl] at h4
  have hb (w : Ω) : posteriorSquareCompensator W β s t w ^ 2 ≤ ((t : ℝ) - s) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (posteriorSquareCompensator_abs_le W β s t hst w) 2
  have hi := integral_mono (compensatedPosteriorSquare_memLp W β s t hst 2).integrable_sq
    ((h4.const_mul 2).add (integrable_const (2 * ((t : ℝ) - s) ^ 2))) (fun w => by
      change (compensatedPosteriorSquare W β s t w) ^ 2 ≤
        2 * actualParisiMagnetizationIncrement W β s t w ^ 4 + 2 * ((t : ℝ) - s) ^ 2
      dsimp only [compensatedPosteriorSquare]
      nlinarith [sq_nonneg (actualParisiMagnetizationIncrement W β s t w ^ 2 +
        posteriorSquareCompensator W β s t w), hb w])
  simp only [integral_add (h4.const_mul 2) (integrable_const _), Pi.add_apply,
    integral_const_mul, integral_const, probReal_univ, one_smul] at hi
  nlinarith [S73.posteriorIncrement_fourth_moment_le W β hβ s t hst]

def pastCompensatedPosteriorSquare (β : ℝ) (s t T : ℝ≥0) (hsT : s ≤ T) (htT : t ≤ T)
    (p : ScalarContinuousPath T) : ℝ :=
  (actualParisiFullMagnetization β t (p ⟨t, t.coe_nonneg, htT⟩) -
    actualParisiFullMagnetization β s (p ⟨s, s.coe_nonneg, hsT⟩)) ^ 2 -
      ∫ r in (s : ℝ)..(t : ℝ),
        actualParisiFullCurvature β r.toNNReal (IccExtend T.coe_nonneg p r) ^ 2

theorem measurable_pastCompensatedPosteriorSquare (β : ℝ) (s t T : ℝ≥0)
    (hsT : s ≤ T) (htT : t ≤ T) :
    Measurable (pastCompensatedPosteriorSquare β s t T hsT htT) := by
  have hm (u : ℝ≥0) (hu : u ≤ T) : Measurable (fun p : ScalarContinuousPath T =>
      actualParisiFullMagnetization β u (p ⟨u, u.coe_nonneg, hu⟩)) :=
    (((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable).comp (ContinuousMap.measurable_eval _)
  have ha : Measurable (fun q : ℝ × ScalarContinuousPath T =>
      actualParisiFullCurvature β q.1.toNNReal (IccExtend T.coe_nonneg q.2 q.1) ^ 2) := by
    exact (((continuous_actualParisiFullCurvature β).comp
      (((continuous_subtype_val.comp continuous_real_toNNReal).comp continuous_fst).prodMk
        (LC1.continuous_finitePath_extend T |>.comp (continuous_snd.prodMk continuous_fst)))).pow 2).measurable
  exact (((hm t htT).sub (hm s hsT)).pow_const 2).sub
    (SKConstantsOAI.ZeroTemperatureSK.WeakIto.measurable_time_integral ha s t)

theorem pastCompensatedPosteriorSquare_abs_le (β : ℝ) (s t T : ℝ≥0)
    (hst : s ≤ t) (hsT : s ≤ T) (htT : t ≤ T) (p : ScalarContinuousPath T) :
    |pastCompensatedPosteriorSquare β s t T hsT htT p| ≤ 4 + ((t : ℝ) - s) := by
  have hm : |actualParisiFullMagnetization β t (p ⟨t, t.coe_nonneg, htT⟩) -
      actualParisiFullMagnetization β s (p ⟨s, s.coe_nonneg, hsT⟩)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith
      [(actualParisiFullMagnetization_curvature_bounds β t (p ⟨t, t.coe_nonneg, htT⟩)).1,
       (actualParisiFullMagnetization_curvature_bounds β s (p ⟨s, s.coe_nonneg, hsT⟩)).1])
  have hb := S73.quadraticIntegral_abs_le (fun _ => 1)
    (fun r => actualParisiFullCurvature β r.toNNReal (IccExtend T.coe_nonneg p r)) s t
    (NNReal.coe_le_coe.mpr hst)
    (by simp)
    (fun r => actualParisiFullCurvature_abs_le_one β _ _)
  simp only [one_mul, abs_one, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hb
  apply (abs_sub _ _).trans
  apply add_le_add _ hb
  rw [abs_pow]
  nlinarith [abs_nonneg (actualParisiFullMagnetization β t (p ⟨t, t.coe_nonneg, htT⟩) -
    actualParisiFullMagnetization β s (p ⟨s, s.coe_nonneg, hsT⟩))]

theorem pastCompensatedPosteriorSquare_actual (W : BrownianSystem Ω) (β : ℝ)
    (s t T : ℝ≥0) (hst : s ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    (fun w => pastCompensatedPosteriorSquare β s t T hsT htT
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) T w)) =ᵐ[W.law]
        compensatedPosteriorSquare W β s t := by
  filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) T] with w hp
  unfold pastCompensatedPosteriorSquare compensatedPosteriorSquare
    actualParisiMagnetizationIncrement actualParisiMagnetizationObservable posteriorSquareCompensator
  rw [hp, hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr hst)] at hr
  have hr0 : 0 ≤ r := s.coe_nonneg.trans hr.1
  have hrT : r ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hr0, hr.2.trans (NNReal.coe_le_coe.mpr htT)⟩
  change actualParisiFullCurvature β r.toNNReal
    (boundedDriftPastPath W (actualParisiFullScalarDrift β) T w
      (projIcc 0 (T : ℝ) T.coe_nonneg r)) ^ 2 = _
  rw [projIcc_of_mem _ hrT, hp]
  change actualParisiFullCurvature β r.toNNReal
    ((actualParisiFullScalarDrift β).solution W.driver ⟨r, hr0⟩ w) ^ 2 =
      actualParisiFullCurvature β r.toNNReal
        ((actualParisiFullScalarDrift β).solution W.driver r.toNNReal w) ^ 2
  rw [show (⟨r, hr0⟩ : ℝ≥0) = r.toNNReal from
    NNReal.coe_injective (Real.coe_toNNReal r hr0).symm]

theorem compensatedPosteriorSquare_disjoint_cross (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a s t u : ℝ≥0) (has : a ≤ s) (hst : s ≤ t) (htu : t ≤ u) :
    (∫ w, compensatedPosteriorSquare W β a s w * compensatedPosteriorSquare W β t u w ∂W.law) = 0 := by
  let F := pastCompensatedPosteriorSquare β a s t (has.trans hst) hst
  have hF := measurable_pastCompensatedPosteriorSquare β a s t (has.trans hst) hst
  have hb : 0 ≤ 4 + ((s : ℝ) - a) := by
    have hh := NNReal.coe_le_coe.mpr has
    linarith
  have hz := compensatedPosteriorSquare_past_test W β hβ t u htu F hF
    ⟨4 + ((s : ℝ) - a), hb⟩
    (pastCompensatedPosteriorSquare_abs_le β a s t has (has.trans hst) hst)
  refine (integral_congr_ae ?_).trans hz
  filter_upwards [pastCompensatedPosteriorSquare_actual W β a s t has (has.trans hst) hst] with w hw
  change F (boundedDriftPastPath W (actualParisiFullScalarDrift β) t w) = _ at hw
  rw [hw]

theorem integral_sq_sum_orthogonal (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hcross : ∀ i j, i < j → (∫ w, X i w * X j w ∂μ) = 0) (c : ℕ → ℝ) (n : ℕ) :
    (∫ w, (∑ i ∈ Finset.range n, c i * X i w) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range n, c i ^ 2 * ∫ w, X i w ^ 2 ∂μ := by
  classical
  have hc (i j : ℕ) : (∫ w, X i w * X j w ∂μ) =
      if i = j then ∫ w, X i w ^ 2 ∂μ else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, pow_two]
    rw [ite_eq_right hij]
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hcross i j hij
    · simpa only [mul_comm] using hcross j i hji
  have hi (i j : ℕ) : Integrable (fun w => c i * c j * (X i w * X j w)) μ :=
    ((hX i).integrable_mul (hX j)).const_mul _
  have he (w : Ω) : (∑ i ∈ Finset.range n, c i * X i w) ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, c i * c j * (X i w * X j w) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, hc]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hi, ite_eq_left]
  ring

theorem compensatedPosteriorSquare_sum_secondMoment_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ)
    (n : ℕ) (C h : ℝ) (_hC : 0 ≤ C) (hc : ∀ i < n, |c i| ≤ C)
    (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ h) :
    (∫ w, (∑ i ∈ Finset.range n, c i *
      compensatedPosteriorSquare W β (t i) (t (i + 1)) w) ^ 2 ∂W.law) ≤
      (96 * Real.exp (1 / 2) + 2) * C ^ 2 * h * ((t n : ℝ) - t 0) := by
  let X := fun i => compensatedPosteriorSquare W β (t i) (t (i + 1))
  let V : ℝ := 96 * Real.exp (1 / 2) + 2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hx (i : ℕ) : MemLp (X i) 2 W.law :=
    compensatedPosteriorSquare_memLp W β _ _ (ht (Nat.le_succ i)) 2
  have hcross (i j : ℕ) (hij : i < j) : (∫ w, X i w * X j w ∂W.law) = 0 :=
    compensatedPosteriorSquare_disjoint_cross W β hβ _ _ _ _
      (ht (Nat.le_succ i)) (ht (by omega)) (ht (Nat.le_succ j))
  rw [integral_sq_sum_orthogonal W.law X hx hcross c n]
  calc
    _ ≤ ∑ i ∈ Finset.range n, c i ^ 2 * (V * ((t (i + 1) : ℝ) - t i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (compensatedPosteriorSquare_secondMoment_le W β hβ _ _ (ht (Nat.le_succ i))) (sq_nonneg _)
    _ = V * ∑ i ∈ Finset.range n, c i ^ 2 * ((t (i + 1) : ℝ) - t i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ V * ∑ i ∈ Finset.range n, C ^ 2 * h * ((t (i + 1) : ℝ) - t i) := by
      apply mul_le_mul_of_nonneg_left _ hV
      apply Finset.sum_le_sum
      intro i hi
      have hin := Finset.mem_range.mp hi
      have hd : 0 ≤ (t (i + 1) : ℝ) - t i :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ i)))
      have hcsq : c i ^ 2 ≤ C ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc i hin) 2
      calc
        _ ≤ C ^ 2 * ((t (i + 1) : ℝ) - t i) ^ 2 :=
          mul_le_mul_of_nonneg_right hcsq (sq_nonneg _)
        _ ≤ C ^ 2 * (h * ((t (i + 1) : ℝ) - t i)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right (hmesh i hin) hd])
            (sq_nonneg C)
        _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => (t i : ℝ))]
      dsimp [V]
      ring

end SKConstants.Completion.X73A
