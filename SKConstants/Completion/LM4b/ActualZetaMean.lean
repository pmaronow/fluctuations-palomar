module

public import SKConstants.Completion.LM4b.ZetaAlgebra
public import SKConstants.Completion.LC1.QuerySpinMoments

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology

namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK LC1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem actualPastMagnetization_brownian_moment_zero
    (W : BrownianSystem Ω) (β : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w, actualParisiMagnetizationObservable W β S w * (W.B T w - W.B S w) ∂W.law) = 0 := by
  let F : ScalarContinuousPath S → ℝ := fun p => actualParisiFullMagnetization β S
    (p ⟨S,S.coe_nonneg,le_rfl⟩)
  have hF : Measurable F := ((continuous_actualParisiFullMagnetization β).comp
    (continuous_const.prodMk continuous_id)).measurable.comp (ContinuousMap.measurable_eval _)
  have hi := (brownian_future_indep_boundedDriftPastPath W (actualParisiFullScalarDrift β) S).symm.comp
    hF (measurable_pi_apply (T-S))
  have hver : (fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w)) =ᵐ[W.law]
      actualParisiMagnetizationObservable W β S := by
    filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) S] with w hw
    dsimp [F, actualParisiMagnetizationObservable]
    rw [hw]
    rfl
  have he : S + (T-S) = T := add_tsub_cancel_of_le hST
  have hi' : IndepFun (actualParisiMagnetizationObservable W β S)
      (fun w => W.B T w-W.B S w) W.law := by
    simpa only [Function.comp_def, he] using hi.congr hver (ae_of_all _ (fun _ => rfl))
  calc
    _ = (∫ w, actualParisiMagnetizationObservable W β S w ∂W.law) *
        (∫ w, W.B T w-W.B S w ∂W.law) := by
      simpa only [Pi.mul_apply] using hi'.integral_mul_eq_mul_integral
        (measurable_actualParisiMagnetizationObservable W β S).aestronglyMeasurable
        ((W.measurable T).sub (W.measurable S)).aestronglyMeasurable
    _ = 0 := by rw [integral_sub (W.brownian.integrable_eval T) (W.brownian.integrable_eval S),
      W.brownian.integral_eval, W.brownian.integral_eval, sub_self, mul_zero]

theorem actualPastMagnetization_stieltjes_moment_zero
    (W : BrownianSystem Ω) (β : ℝ) (f : StieltjesFunction ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w, actualParisiMagnetizationObservable W β S w *
      (scalarGlobalStieltjesWeightedProcess f W.driver T w -
        scalarGlobalStieltjesWeightedProcess f W.driver S w) ∂W.law) = 0 := by
  have hh := bounded_brownian_stieltjes_increment_integral W f S T hST
    (actualParisiMagnetizationObservable W β S)
    (measurable_actualParisiMagnetizationObservable W β S) 1
    (actualParisiMagnetizationObservable_abs_le W β S)
  have hz (R : ℝ≥0) (hSR : S ≤ R) :
      (∫ w, actualParisiMagnetizationObservable W β S w *
        (W.driver R w-W.driver S w) ∂W.law) = 0 := by
    refine (integral_congr_ae ?_).trans (actualPastMagnetization_brownian_moment_zero W β S R hSR)
    filter_upwards [W.driver_indistinguishable] with w hw
    rw [hw,hw]
  rw [hz T hST, mul_zero] at hh
  have hi : (∫ r in (S:ℝ)..(T:ℝ), (∫ w, actualParisiMagnetizationObservable W β S w *
      (W.driver r.toNNReal w-W.driver S w) ∂W.law) ∂f.measure) = 0 := by
    calc
      _ = ∫ _r in (S:ℝ)..(T:ℝ), (0:ℝ) ∂f.measure := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hr
        apply hz
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ (S.coe_nonneg.trans hr.1)]
        exact hr.1
      _ = 0 := by simp
  simpa only [hi, sub_zero] using hh

theorem actualPastMagnetization_query_moment_zero
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ u : Ω × A, actualParisiMagnetizationObservable W β S u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B T u -
        (actualParisiQueryBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law) = 0 := by
  let := W.isProbability
  let := Z.isProbability
  let f := actualParisiNegativeRhoStieltjes W β hβ
  let g := actualParisiSigmaStieltjes W β hβ
  let M := actualParisiMagnetizationObservable W β S
  let X : Ω → ℝ := fun w => scalarGlobalStieltjesWeightedProcess f W.driver T w -
    scalarGlobalStieltjesWeightedProcess f W.driver S w
  let Y : A → ℝ := fun z => scalarGlobalStieltjesWeightedProcess g Z.driver T z -
    scalarGlobalStieltjesWeightedProcess g Z.driver S z
  have hiX := (bounded_brownian_stieltjes_integrable W f S T hST M
    (measurable_actualParisiMagnetizationObservable W β S) 1
    (actualParisiMagnetizationObservable_abs_le W β S)).2
  have hiY : Integrable Y Z.law := by
    simpa only [one_mul] using (bounded_brownian_stieltjes_integrable Z g S T hST
      (fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)).2
  have he (u : Ω × A) : M u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B T u -
        (actualParisiQueryBrownianSystem W Z β hβ).B S u) =
      -(M u.1 * X u.1) + M u.1 * Y u.2 := by
    change M u.1 * ((-_+_)-(-_+_)) = _
    dsimp [X,Y]
    ring
  change (∫ u : Ω × A, M u.1 *
    ((actualParisiQueryBrownianSystem W Z β hβ).B T u -
      (actualParisiQueryBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law) = 0
  simp_rw [he]
  have h1 : (∫ u : Ω × A, -(M u.1 * X u.1) ∂W.law.prod Z.law) = 0 := by
    rw [integral_neg]
    have hh : (∫ u : Ω × A, M u.1 * X u.1 ∂W.law.prod Z.law) =
        ∫ w, M w * X w ∂W.law := by
      simpa only [probReal_univ, one_smul] using
        integral_fun_fst (μ:=W.law) (ν:=Z.law) (fun w => M w * X w)
    rw [hh, actualPastMagnetization_stieltjes_moment_zero W β f S T hST, neg_zero]
  have h2 : (∫ u : Ω × A, M u.1 * Y u.2 ∂W.law.prod Z.law) = 0 := by
    rw [integral_prod_mul, brownianStieltjes_increment_mean_zero Z g S T hST, mul_zero]
  have hh := integral_add (f:=fun u : Ω × A => -(M u.1 * X u.1))
    (g:=fun u : Ω × A => M u.1 * Y u.2) (hiX.comp_fst Z.law).neg
      ((integrable_actualParisiMagnetizationObservable W β S).mul_prod hiY)
  exact hh.trans (by rw [h1,h2]; ring)

def actualRowPotential (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0)
    (u : (Bool × Ω) × A) : ℝ :=
  rowPotential (scalarHiddenSign u.1.1) (actualParisiMagnetizationObservable W β S u.1.2)

theorem measurable_actualRowPotential (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) :
    Measurable (actualRowPotential (A := A) W β S) := by
  have hm : Measurable (fun u : (Bool × Ω) × A => actualParisiMagnetizationObservable W β S u.1.2) :=
    (measurable_actualParisiMagnetizationObservable W β S).comp (measurable_snd.comp measurable_fst)
  have hs : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  exact (hs.mul hm).sub ((hm.pow_const 2).div_const 2)

omit [MeasurableSpace A] in
theorem actualRowPotential_abs_le (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (u : (Bool × Ω) × A) :
    |actualRowPotential W β S u| ≤ 3/2 := by
  apply rowPotential_abs_le _ (actualParisiMagnetizationObservable_abs_le W β S u.1.2)
  cases u.1.1 <;> norm_num [scalarHiddenSign]

theorem actualRowPotential_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (S H : ℝ≥0) (hSH : S ≤ H) :
    (∫ u, actualRowPotential W β S u ∂actualParisiFullQuerySpinLaw W Z β H) =
      actualParisiFullOverlap W β S / 2 := by
  let ν := actualParisiFullQuerySpinLaw W Z β H
  let M := actualParisiMagnetizationObservable W β S
  have hM := measurable_actualParisiMagnetizationObservable W β S
  have hM2 : Integrable (fun u => M u^2) W.law := by
    simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β S S
  have hSq : (∫ u, M u.1.2^2 ∂ν) = actualParisiFullOverlap W β S :=
    (actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).integral_comp (hM.pow_const 2).aestronglyMeasurable
  have hSpin : (∫ u : (Bool × Ω) × A, scalarHiddenSign u.1.1 * M u.1.2 ∂ν) =
      actualParisiFullOverlap W β S := by
    have hh := actualQuerySpinLaw_sign_test_integrable W Z β H
      (fun u : Ω × A => M u.1) (hM.comp measurable_fst)
      ((integrable_actualParisiMagnetizationObservable W β S).comp_fst Z.law)
    rw [hh]
    have he := integral_fun_fst (μ:=W.law) (ν:=Z.law)
      (fun w => actualParisiMagnetizationObservable W β H w * M w)
    simp only [probReal_univ, one_smul] at he
    exact he.trans (by simpa only [M,actualParisiFullOverlap,actualParisiMagnetizationObservable,mul_comm] using actualParisiMagnetization_crossMoment W β hβ S H hSH)
  have hiSpin : Integrable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1 * M u.1.2) ν := by
    apply Integrable.of_bound
      ((((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).mul
        (hM.comp (measurable_snd.comp measurable_fst))).aestronglyMeasurable) 1
    exact ae_of_all _ (fun u => by
      change |scalarHiddenSign u.1.1 * M u.1.2| ≤ 1
      rw [abs_mul]
      have hs : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
      rw [hs,one_mul]
      exact actualParisiMagnetizationObservable_abs_le W β S u.1.2)
  change (∫ u, scalarHiddenSign u.1.1 * M u.1.2 - M u.1.2^2/2 ∂ν) = _
  have hiSq : Integrable (fun u : (Bool × Ω) × A => M u.1.2^2/2) ν :=
    ((actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).integrable_comp hM2).div_const 2
  calc
    _ = (∫ u : (Bool × Ω) × A, scalarHiddenSign u.1.1 * M u.1.2 ∂ν) -
        (∫ u : (Bool × Ω) × A, M u.1.2^2/2 ∂ν) := integral_sub hiSpin hiSq
    _ = actualParisiFullOverlap W β S - actualParisiFullOverlap W β S / 2 := by
      rw [integral_div, hSpin, hSq]
    _ = _ := by ring

def actualRowQueryIncrement (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (u : (Bool × Ω) × A) : ℝ :=
  (actualParisiQueryBrownianSystem W Z β hβ).B T (u.1.2,u.2) -
    (actualParisiQueryBrownianSystem W Z β hβ).B S (u.1.2,u.2)

def actualQueryCellMean (W : BrownianSystem Ω) (β : ℝ) (S T : ℝ≥0) : ℝ :=
  ∫ r in (S:ℝ)..(T:ℝ), actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r

theorem actualRowQueryDefect_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u, (scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β S u.1.2) *
      actualRowQueryIncrement W Z β hβ S T u ∂actualParisiFullQuerySpinLaw W Z β H) =
      actualQueryCellMean W β S T := by
  let ν := actualParisiFullQuerySpinLaw W Z β H
  let Q := actualParisiQueryBrownianSystem W Z β hβ
  let F : Ω × A → ℝ := fun u => Q.B T u - Q.B S u
  have hFi : Integrable F (W.law.prod Z.law) :=
    (Q.brownian.integrable_eval T).sub (Q.brownian.integrable_eval S)
  have hFm : Measurable F := (Q.measurable T).sub (Q.measurable S)
  have hIi : Integrable (fun u : (Bool × Ω) × A => F (u.1.2,u.2)) ν :=
    (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integrable_comp hFi
  have hmi : AEStronglyMeasurable
      (fun u : (Bool × Ω) × A => actualParisiMagnetizationObservable W β S u.1.2) ν :=
    ((measurable_actualParisiMagnetizationObservable W β S).comp
      (measurable_snd.comp measurable_fst)).aestronglyMeasurable
  have hsi : AEStronglyMeasurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) ν :=
    ((measurable_of_finite scalarHiddenSign).comp
      (measurable_fst.comp measurable_fst)).aestronglyMeasurable
  have hI1 : Integrable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1 * F (u.1.2,u.2)) ν :=
    hIi.bdd_mul (c:=1) hsi (ae_of_all _ (fun u => by cases u.1.1 <;> norm_num [scalarHiddenSign]))
  have hI2 : Integrable (fun u : (Bool × Ω) × A =>
      actualParisiMagnetizationObservable W β S u.1.2 * F (u.1.2,u.2)) ν :=
    hIi.bdd_mul (c:=1) hmi (ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs]
      exact actualParisiMagnetizationObservable_abs_le W β S u.1.2))
  change (∫ u, (scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β S u.1.2) *
    F (u.1.2,u.2) ∂ν) = _
  simp only [sub_mul]
  rw [integral_sub hI1 hI2]
  have hs := actualQuerySpinLaw_query_spin_moment W Z β hβ S T H hST hTH
  simp only [mul_comm] at hs
  rw [hs]
  have hz : (∫ u : (Bool × Ω) × A,
      actualParisiMagnetizationObservable W β S u.1.2 * F (u.1.2,u.2) ∂ν) = 0 := by
    have hh := (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp
      (((measurable_actualParisiMagnetizationObservable W β S).comp measurable_fst).mul hFm).aestronglyMeasurable
    exact hh.trans (actualPastMagnetization_query_moment_zero W Z β hβ S T hST)
  rw [hz, sub_zero]
  simp only [actualQueryCellMean, mul_comm]

theorem integrable_actualRowQueryDefect (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0) :
    Integrable (fun u => (scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β S u.1.2) *
      actualRowQueryIncrement W Z β hβ S T u) (actualParisiFullQuerySpinLaw W Z β H) := by
  have hI := (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integrable_comp
    (((actualParisiQueryBrownianSystem W Z β hβ).brownian.integrable_eval T).sub
      ((actualParisiQueryBrownianSystem W Z β hβ).brownian.integrable_eval S))
  have hm : Measurable (fun u : (Bool × Ω) × A =>
      scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β S u.1.2) :=
    ((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_actualParisiMagnetizationObservable W β S).comp (measurable_snd.comp measurable_fst))
  apply hI.bdd_mul (c:=2) hm.aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs]
  have hs : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
  exact (abs_sub _ _).trans (by rw [hs]; linarith [actualParisiMagnetizationObservable_abs_le W β S u.1.2])

def actualZeta (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (w c : ℕ → ℝ) (k : ℕ) (e : ℝ) (u : (Bool × Ω) × A) : ℝ :=
  (∑ j ∈ Finset.range k, w j * (actualRowPotential W β (t (j+1)) u - actualRowPotential W β (t j) u)) +
    (∑ j ∈ Finset.range k, c j *
      ((scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β (t (j+1)) u.1.2) *
        actualRowQueryIncrement W Z β hβ (t (j+1)) (t (j+2)) u)) - e/2

theorem actualZeta_mean_formula (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (w c : ℕ → ℝ)
    (k : ℕ) (e : ℝ) (H : ℝ≥0) (hH : t (k+1) ≤ H) :
    (∫ u, actualZeta W Z β hβ t w c k e u ∂actualParisiFullQuerySpinLaw W Z β H) =
      (∑ j ∈ Finset.range k, w j * (actualParisiFullOverlap W β (t (j+1)) -
        actualParisiFullOverlap W β (t j))/2) +
        (∑ j ∈ Finset.range k, c j * actualQueryCellMean W β (t (j+1)) (t (j+2))) - e/2 := by
  let ν := actualParisiFullQuerySpinLaw W Z β H
  have hpot (S : ℝ≥0) : Integrable (actualRowPotential W β S) ν :=
    Integrable.of_bound (measurable_actualRowPotential W β S).aestronglyMeasurable (3/2)
      (ae_of_all _ (fun u => by rw [Real.norm_eq_abs]; exact actualRowPotential_abs_le W β S u))
  have hI (j : ℕ) : Integrable
      (fun u => w j * (actualRowPotential W β (t (j+1)) u - actualRowPotential W β (t j) u)) ν :=
    ((hpot _).sub (hpot _)).const_mul _
  have hN (j : ℕ) : Integrable (fun u => c j *
      ((scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β (t (j+1)) u.1.2) *
        actualRowQueryIncrement W Z β hβ (t (j+1)) (t (j+2)) u)) ν :=
    (integrable_actualRowQueryDefect W Z β hβ _ _ H).const_mul _
  have hIntA := integrable_finsetSum (Finset.range k) (fun j _ => hI j)
  have hIntN := integrable_finsetSum (Finset.range k) (fun j _ => hN j)
  unfold actualZeta
  rw [integral_sub (f:=fun u =>
    (∑ j ∈ Finset.range k, w j * (actualRowPotential W β (t (j+1)) u - actualRowPotential W β (t j) u)) +
    (∑ j ∈ Finset.range k, c j * ((scalarHiddenSign u.1.1-actualParisiMagnetizationObservable W β (t (j+1)) u.1.2) *
      actualRowQueryIncrement W Z β hβ (t (j+1)) (t (j+2)) u))) (g:=fun _ => e/2)
    (hIntA.add hIntN) (integrable_const _), integral_add hIntA hIntN]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_finsetSum _ (fun j _ => hI j), integral_finsetSum _ (fun j _ => hN j)]
  congr 2
  · apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have hjH : t (j+1) ≤ H := (ht (by omega : j+1 ≤ k+1)).trans hH
    rw [integral_const_mul, integral_sub (hpot _) (hpot _),
      actualRowPotential_mean W Z β hβ _ H hjH,
      actualRowPotential_mean W Z β hβ _ H ((ht (Nat.le_succ j)).trans hjH)]
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, actualRowQueryDefect_mean W Z β hβ _ _ H
      (ht (by omega : j+1 ≤ j+2)) ((ht (by have := Finset.mem_range.mp hj; omega : j+2 ≤ k+1)).trans hH)]

theorem actualZeta_mean_of_coefficient_identities
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (w c b s : ℕ → ℝ) (k : ℕ)
    (hw : ∀ j < k, w j * (actualParisiFullOverlap W β (t (j+1)) - actualParisiFullOverlap W β (t j)) = b j*s j)
    (hc : ∀ j < k, c j * actualQueryCellMean W β (t (j+1)) (t (j+2)) = b j*s j)
    (H : ℝ≥0) (hH : t (k+1) ≤ H) :
    (∫ u, actualZeta W Z β hβ t w c k (∑ j ∈ Finset.range k, b j*s j) u
      ∂actualParisiFullQuerySpinLaw W Z β H) = ∑ j ∈ Finset.range k, b j*s j := by
  rw [actualZeta_mean_formula W Z β hβ t ht w c k _ H hH]
  have ha : (∑ j ∈ Finset.range k, w j * (actualParisiFullOverlap W β (t (j+1)) -
      actualParisiFullOverlap W β (t j))/2) = (∑ j ∈ Finset.range k,b j*s j)/2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj => congrArg (fun a : ℝ => a/2) (hw j (Finset.mem_range.mp hj)))
  have hb : (∑ j ∈ Finset.range k, c j * actualQueryCellMean W β (t (j+1)) (t (j+2))) =
      ∑ j ∈ Finset.range k,b j*s j := Finset.sum_congr rfl (fun j hj => hc j (Finset.mem_range.mp hj))
  rw [ha,hb]
  ring

def actualCoarseScale (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  actualParisiPosteriorIntervalScale W β (t j) (t (j+1))

def actualCoarseSpinMean (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  actualQueryCellMean W β (t (j+1)) (t (j+2)) / Real.sqrt ((t (j+2):ℝ)-(t (j+1):ℝ))

def actualCoarseWeight (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  actualCoarseSpinMean W β t j / actualCoarseScale W β t j

def actualCoarseNoiseWeight (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  actualCoarseScale W β t j / Real.sqrt ((t (j+2):ℝ)-(t (j+1):ℝ))

def actualCoarseEnergy (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, actualCoarseSpinMean W β t j * actualCoarseScale W β t j

theorem actualCoarseZeta_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (k : ℕ) (H : ℝ≥0) (hH : t (k+1) ≤ H) :
    (∫ u, actualZeta W Z β hβ t (actualCoarseWeight W β t) (actualCoarseNoiseWeight W β t)
      k (actualCoarseEnergy W β t k) u ∂actualParisiFullQuerySpinLaw W Z β H) =
      actualCoarseEnergy W β t k := by
  apply actualZeta_mean_of_coefficient_identities W Z β hβ t ht.monotone _ _ _ _ k _ _ H hH
  · intro j _
    have hs := actualParisiPosteriorIntervalScale_sq W β hβ (t j) (t (j+1)) (ht (Nat.lt_succ_self j))
    have hsp : 0 < actualCoarseScale W β t j :=
      NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ (t j) (t (j+1)) (ht (Nat.lt_succ_self j)))
    change actualCoarseWeight W β t j * _ = _
    rw [actualCoarseWeight, ← hs]
    change (actualCoarseSpinMean W β t j / actualCoarseScale W β t j) *
      (actualCoarseScale W β t j)^2 = _
    field_simp
  · intro j _
    unfold actualCoarseNoiseWeight actualCoarseSpinMean
    ring

end SKConstants.Completion.LM4b
