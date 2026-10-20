module

public import SKConstants.Completion.N13bc.PaddedHalf
public import SKConstants.Completion.N13bc.PaddedCross
public import SKConstants.Completion.N13bc.EmpiricalBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK LW Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def paddedSevenRow
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r) :
    SevenIndex r → ((Bool × Ω) × A) → EuclideanSpace ℝ (Fin (2^r)) :=
  sevenFeatures r (fun u => liftMatrix h (posteriorGramError W β t k u))
    (fun u => liftMatrix h (crossError W Z β hβ t V k u))
    (liftVector h (posteriorWeight W β t k)) (liftVector h (queryWeight W β t k))
    (fun u => liftVector h (scalarHiddenSign u.1.1 • posteriorRow W β t k u - posteriorWeight W β t k))
    (fun u => liftVector h (scalarHiddenSign u.1.1 • queryRow W Z β hβ t k u - queryWeight W β t k))

theorem measurable_paddedSevenRow
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r) (i : SevenIndex r) :
    Measurable (paddedSevenRow W Z β hβ t V k r h i) := by
  have hT := measurable_posteriorRow (A := A) W β t k
  have hG := measurable_queryRow W Z β hβ t k
  have hX : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  have hE : Measurable (posteriorGramError (A := A) W β t k) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (((EuclideanSpace.proj i).measurable.comp hT).mul
      ((EuclideanSpace.proj j).measurable.comp hT)).sub measurable_const
  have hH : Measurable (crossError W Z β hβ t V k) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (((EuclideanSpace.proj i).measurable.comp hT).mul
      ((EuclideanSpace.proj j).measurable.comp hG)).sub measurable_const
  exact measurable_sevenFeatures r _ _ _ _ _ _ (measurable_liftMatrix h _ hE)
    (measurable_liftMatrix h _ hH)
    (measurable_liftVector h _ ((hX.smul hT).sub measurable_const))
    (measurable_liftVector h _ ((hX.smul hG).sub measurable_const)) i

theorem projection_lift_eq_zero_of_duration
    (t : ℕ → ℝ≥0) (ht : StrictMono t) {k m : ℕ} (h : k ≤ m)
    (J : Finset (Fin m)) (hd : (∑ j ∈ J, paddedDuration t h j) = 0)
    (w : EuclideanSpace ℝ (Fin k)) : coordinateProjection J (liftVector h w) = 0 := by
  ext j
  by_cases hj : j ∈ J
  · by_cases hk : j.val < k
    · have hpos : 0 < paddedDuration t h j := by
        dsimp [paddedDuration, liftVector]
        rw [if_pos hk]
        exact sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _)))
      have H := Finset.single_le_sum (fun i _ => paddedDuration_nonneg t ht.monotone h i) hj
      rw [hd] at H
      exact False.elim ((not_le_of_gt hpos) H)
    · simp [coordinateProjection_apply, hj, liftVector_dummy h w j (not_lt.mp hk)]
  · simp [coordinateProjection_apply, hj]

theorem paddedSevenRow_zero
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    (i : SevenIndex r) (hi : sevenDuration r (paddedDuration t h) i = 0)
    (u : (Bool × Ω) × A) : paddedSevenRow W Z β hβ t V k r h i u = 0 := by
  cases i with
  | inl j => simp [sevenDuration] at hi
  | inr p =>
    rcases p with ⟨j,I⟩
    have hs := projection_lift_eq_zero_of_duration t ht h (dyadicIntervalSets r I) hi
      (posteriorWeight W β t k)
    have hb := projection_lift_eq_zero_of_duration t ht h (dyadicIntervalSets r I) hi
      (queryWeight W β t k)
    fin_cases j <;> simp [paddedSevenRow, sevenFeatures, hs, hb]

theorem actualPaddedSevenRowMGF_of_weight_bound
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    (hV : t (k+1) ≤ V) {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hWeight : ∀ j : Fin k, |queryWeight W β t k j / posteriorWeight W β t k j| ≤ B) :
    ∀ i (a : EuclideanSpace ℝ (Fin (2^r))), ‖a‖ ≤ 1 →
      LocalQuadraticMGF (fun u => ⟪normalizedRow (paddedSevenRow W Z β hβ t V k r h i)
        (sevenDuration r (paddedDuration t h) i) u,a⟫_ℝ)
        (linkedScalarLaw W Z β V) (weightedProducerVariance B R r)
        (weightedProducerRadius B R r) := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hV0 : t k ≤ V := (ht.monotone (Nat.le_succ _)).trans hV
  intro i a ha
  cases i with
  | inl j =>
    have H (query : Bool) := localMGF_into_weighted_budget hB hR r
      (actual_spin_row_localMGF W Z β hβ t ht k V hV (restrictVector h a)
        ((restrictVector_norm_le h a).trans ha) hR hProxy query)
    fin_cases j
    · simpa [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow,
        liftVector_inner] using H false
    · simpa [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow,
        liftVector_inner] using H true
  | inr p =>
    rcases p with ⟨j,I⟩
    by_cases hz : nodeDuration r (paddedDuration t h) I = 0
    · simpa [sevenDuration, hz, normalizedRow] using
        (localMGF_zero (μ := linkedScalarLaw W Z β V)
          (weightedProducerParameters_pos hB0 hR r).1.le)
    have hd : 0 < nodeDuration r (paddedDuration t h) I :=
      lt_of_le_of_ne (nodeDuration_nonneg r _ (paddedDuration_nonneg t ht.monotone h) I) (Ne.symm hz)
    have hs (j : Fin k) : |posteriorWeight W β t k j / posteriorWeight W β t k j| ≤ B := by
      have hj : posteriorWeight W β t k j ≠ 0 :=
        (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ
          (t j) (t (j+1)) (ht (Nat.lt_succ_self _)))).ne'
      simpa only [div_self hj, abs_one] using hB
    have hHalf (w : EuclideanSpace ℝ (Fin k))
        (hw : ∀ j, |w j / posteriorWeight W β t k j| ≤ B) (tr : Bool) :=
      actual_padded_halfUpper_duration_localMGF W Z β hβ t ht V k r h hV0 a ha w
        (dyadicIntervalSets r I) hB0 hR hProxy hw hd tr
    have hCross (tr : Bool) := localMGF_into_weighted_budget hB hR r
      (actual_padded_cross_duration_localMGF W Z β hβ t ht V k r h hV0 a ha I hd hR hProxy tr)
    fin_cases j
    · have H := hHalf (posteriorWeight W β t k) hs false
      convert H using 1
      funext u
      simp [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow, nodeDuration,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hHalf (posteriorWeight W β t k) hs true
      convert H using 1
      funext u
      simp [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow, nodeDuration,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hHalf (queryWeight W β t k) hWeight false
      convert H using 1
      funext u
      simp [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow, nodeDuration,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hCross false
      convert H using 1
      funext u
      simp [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hCross true
      convert H using 1
      funext u
      simp [paddedSevenRow, sevenFeatures, sevenDuration, normalizedRow,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]

theorem actual_padded_seven_simultaneous_tail_explicit
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    (hV : t (k+1) ≤ V) {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hWeight : ∀ j : Fin k, |queryWeight W β t k j / posteriorWeight W β t k j| ≤ B)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    (linkedScalarRowsLaw W Z β V n).real
      {ω | ∃ i : SevenIndex r, 2*η*Real.sqrt (sevenDuration r (paddedDuration t h) i) <
        ‖rowAverage (paddedSevenRow W Z β hβ t V k r h i) ω‖} ≤
      2*(10*(2 : ℝ)^r-3)*(5 : ℝ)^(2^r)*Real.exp (-(n : ℝ)*
        min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
          (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R)))) := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hp := weightedProducer_le_explicit hB0 hR r
  have hRows := actualPaddedSevenRowMGF_of_weight_bound W Z β hβ t ht V k r h hV hB hR hProxy hWeight
  have H := iid_duration_family_tail (linkedScalarLaw W Z β V) hn
    (paddedSevenRow W Z β hβ t V k r h) (measurable_paddedSevenRow W Z β hβ t V k r h)
    (sevenDuration r (paddedDuration t h))
    (sevenDuration_nonneg r _ (paddedDuration_nonneg t ht.monotone h))
    (paddedSevenRow_zero W Z β hβ t ht V k r h)
    (by unfold explicitSevenVariance; positivity [Real.log_pos (by linarith : 1 < 2+R)])
    (by unfold explicitSevenRadius; positivity [Real.log_pos (by linarith : 1 < 2+R)]) hη
    (fun i a ha => localMGF_mono (hRows i a ha) hp.1 hp.2)
  rw [card_SevenIndex] at H
  convert H using 1
  · rfl
  · unfold explicitSevenVariance explicitSevenRadius
    congr 4 <;> field_simp <;> ring

end SKConstants.Completion.N13bc
