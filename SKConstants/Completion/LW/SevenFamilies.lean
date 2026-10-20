module

public import SKConstants.Completion.LW.LinkedScalarRows
public import SKConstants.Completion.LW.DurationConcentration
public import SKConstants.SubGaussianProductsSecondMoment

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal InnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK

abbrev SevenIndex (r : ℕ) := Fin 2 ⊕ (Fin 5 × DyadicCore.Interval r)

theorem card_dyadicInterval_add_one (r : ℕ) :
    Fintype.card (DyadicCore.Interval r) + 1 = 2 * 2^r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change Fintype.card (Unit ⊕ (DyadicCore.Interval r ⊕ DyadicCore.Interval r)) + 1 = _
    simp only [Fintype.card_sum, Fintype.card_unit, pow_succ]
    omega

theorem card_SevenIndex (r : ℕ) :
    (Fintype.card (SevenIndex r) : ℝ) = 10*(2 : ℝ)^r - 3 := by
  have H := card_dyadicInterval_add_one r
  have HR : (Fintype.card (DyadicCore.Interval r) : ℝ) + 1 = 2*(2 : ℝ)^r := by
    exact_mod_cast H
  simp only [SevenIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

def sevenDuration (r : ℕ) (h : Fin (2^r) → ℝ) : SevenIndex r → ℝ
  | .inl _ => 1
  | .inr p => nodeDuration r h p.2

theorem sevenDuration_nonneg (r : ℕ) (h : Fin (2^r) → ℝ) (hh : ∀ j, 0 ≤ h j)
    (i : SevenIndex r) : 0 ≤ sevenDuration r h i := by
  cases i with
  | inl _ => exact zero_le_one
  | inr p => exact nodeDuration_nonneg r h hh p.2

theorem sum_sevenDuration (r : ℕ) (h : Fin (2^r) → ℝ) :
    (∑ i : SevenIndex r, sevenDuration r h i) =
      2 + 5*(r+1 : ℝ)*(∑ j, h j) := by
  simp only [SevenIndex, Fintype.sum_sum_type, Fintype.sum_prod_type, sevenDuration,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sum_nodeDuration]
  ring

theorem iid_seven_duration_total_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (U : SevenIndex r → Ω → EuclideanSpace ℝ (Fin (2^r)))
    (hU : ∀ j, Measurable (U j))
    (h : Fin (2^r) → ℝ) (hh : ∀ j, 0 ≤ h j)
    (hzero : ∀ j, sevenDuration r h j = 0 → ∀ ω, U j ω = 0)
    {v radius η : ℝ} (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η)
    (hRows : ∀ j (a : EuclideanSpace ℝ (Fin (2^r))), ‖a‖ ≤ 1 →
      Concentration.LocalQuadraticMGF
        (fun ω => ⟪normalizedRow (U j) (sevenDuration r h j) ω,a⟫_ℝ) μ v radius) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | 4*η^2 * (2 + 5*(r+1 : ℝ)*∑ j, h j) <
        ∑ j : SevenIndex r, ‖rowAverage (U j) ω‖^2} ≤
      2 * (10*(2 : ℝ)^r-3) * (5 : ℝ)^(2^r) * Real.exp (-(n : ℝ) *
        min (η^2/(4*v)) (radius*η/2)) := by
  simpa only [sum_sevenDuration, card_SevenIndex] using
    iid_duration_total_tail μ hn U hU (sevenDuration r h)
      (sevenDuration_nonneg r h hh) hzero hv hr hη hRows

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def posteriorGramError (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (k : ℕ) (u : (Bool × Ω) × A) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => posteriorRow W β t k u i * posteriorRow W β t k u j - if i=j then 1 else 0

def crossError (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (V : ℝ≥0) (k : ℕ) (u : (Bool × Ω) × A) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => posteriorRow W β t k u i * queryRow W Z β hβ t k u j -
    ∫ v, posteriorRow W β t k v i * queryRow W Z β hβ t k v j ∂linkedScalarLaw W Z β V

def sevenRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (V : ℝ≥0) (r : ℕ) (i : SevenIndex r)
    (u : (Bool × Ω) × A) : EuclideanSpace ℝ (Fin (2^r)) :=
  match i with
  | .inl j => if j=0 then
      scalarHiddenSign u.1.1 • posteriorRow W β t (2^r) u - posteriorWeight W β t (2^r)
    else scalarHiddenSign u.1.1 • queryRow W Z β hβ t (2^r) u - queryWeight W β t (2^r)
  | .inr (j,I) =>
    let L := halfUpperTruncation (posteriorGramError W β t (2^r) u)
    let H := crossError W Z β hβ t V (2^r) u
    let s := coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r))
    let b := coordinateProjection (dyadicIntervalSets r I) (queryWeight W β t (2^r))
    if j=0 then Matrix.toEuclideanCLM (𝕜 := ℝ) L s
    else if j=1 then Matrix.toEuclideanCLM (𝕜 := ℝ) L.transpose s
    else if j=2 then Matrix.toEuclideanCLM (𝕜 := ℝ) L b
    else if j=3 then Matrix.toEuclideanCLM (𝕜 := ℝ) H s
    else Matrix.toEuclideanCLM (𝕜 := ℝ) H.transpose s

theorem measurable_sevenRow (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (V : ℝ≥0) (r : ℕ) (i : SevenIndex r) :
    Measurable (sevenRow W Z β hβ t V r i) := by
  have hT := measurable_posteriorRow (A := A) W β t (2^r)
  have hG := measurable_queryRow W Z β hβ t (2^r)
  have hX : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  have hMV (M : (Bool × Ω) × A → Matrix (Fin (2^r)) (Fin (2^r)) ℝ)
      (hm : Measurable M) (c : EuclideanSpace ℝ (Fin (2^r))) :
      Measurable (fun u => Matrix.toEuclideanCLM (𝕜 := ℝ) (M u) c) := by
    change Measurable (fun u => Matrix.toEuclideanCLM (𝕜 := ℝ) (M u) (WithLp.toLp 2 c.ofLp))
    simp_rw [Matrix.toEuclideanCLM_toLp]
    apply (WithLp.measurable_toLp 2 _).comp
    apply Measurable.of_eval
    intro i
    change Measurable (fun u => ∑ j, M u i j * c j)
    apply Finset.measurable_fun_sum
    intro j _
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)).mul_const _
  cases i with
  | inl j =>
    change Measurable (fun u : (Bool × Ω) × A => if j=0 then
      scalarHiddenSign u.1.1 • posteriorRow W β t (2^r) u - posteriorWeight W β t (2^r)
      else scalarHiddenSign u.1.1 • queryRow W Z β hβ t (2^r) u - queryWeight W β t (2^r))
    split_ifs <;> fun_prop
  | inr p =>
    rcases p with ⟨j,I⟩
    have hE : Measurable (posteriorGramError (A := A) W β t (2^r)) := by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      exact (((EuclideanSpace.proj i).measurable.comp hT).mul
        ((EuclideanSpace.proj j).measurable.comp hT)).sub measurable_const
    have hH : Measurable (crossError W Z β hβ t V (2^r)) := by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      exact (((EuclideanSpace.proj i).measurable.comp hT).mul
        ((EuclideanSpace.proj j).measurable.comp hG)).sub measurable_const
    have hL : Measurable (fun u : (Bool × Ω) × A =>
        halfUpperTruncation (posteriorGramError W β t (2^r) u)) :=
      (halfUpperCLM r).continuous.measurable.comp hE
    have hLt : Measurable (fun u : (Bool × Ω) × A =>
        (halfUpperTruncation (posteriorGramError W β t (2^r) u)).transpose) := by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hL)
    have hHt : Measurable (fun u : (Bool × Ω) × A =>
        (crossError W Z β hβ t V (2^r) u).transpose) := by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hH)
    change Measurable (fun u : (Bool × Ω) × A =>
      if j=0 then Matrix.toEuclideanCLM (𝕜 := ℝ)
        (halfUpperTruncation (posteriorGramError W β t (2^r) u))
        (coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r)))
      else if j=1 then Matrix.toEuclideanCLM (𝕜 := ℝ)
        (halfUpperTruncation (posteriorGramError W β t (2^r) u)).transpose
        (coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r)))
      else if j=2 then Matrix.toEuclideanCLM (𝕜 := ℝ)
        (halfUpperTruncation (posteriorGramError W β t (2^r) u))
        (coordinateProjection (dyadicIntervalSets r I) (queryWeight W β t (2^r)))
      else if j=3 then Matrix.toEuclideanCLM (𝕜 := ℝ) (crossError W Z β hβ t V (2^r) u)
        (coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r)))
      else Matrix.toEuclideanCLM (𝕜 := ℝ) (crossError W Z β hβ t V (2^r) u).transpose
        (coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r))))
    split_ifs
    · exact hMV _ hL _
    · exact hMV _ hLt _
    · exact hMV _ hL _
    · exact hMV _ hH _
    · exact hMV _ hHt _

def ActualSevenRowMGFStatement (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (V : ℝ≥0) (r : ℕ)
    (v radius : ℝ) : Prop :=
  ∀ i (a : EuclideanSpace ℝ (Fin (2^r))), ‖a‖ ≤ 1 →
    Concentration.LocalQuadraticMGF
      (fun u => ⟪normalizedRow (sevenRow W Z β hβ t V r i)
        (sevenDuration r (fun j => previousDuration t j) i) u,a⟫_ℝ)
      (linkedScalarLaw W Z β V) v radius

theorem actual_seven_duration_total_tail
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ)
    {n : ℕ} (hn : 0 < n) {v radius η : ℝ}
    (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η)
    (hRows : ActualSevenRowMGFStatement W Z β hβ t V r v radius) :
    (linkedScalarRowsLaw W Z β V n).real
      {ω | 4*η^2 * (2 + 5*(r+1 : ℝ)*∑ j : Fin (2^r), previousDuration t j) <
        ∑ i : SevenIndex r, ‖rowAverage (sevenRow W Z β hβ t V r i) ω‖^2} ≤
      2 * (10*(2 : ℝ)^r-3) * (5 : ℝ)^(2^r) * Real.exp (-(n : ℝ) *
        min (η^2/(4*v)) (radius*η/2)) := by
  apply iid_seven_duration_total_tail (linkedScalarLaw W Z β V) hn r
    (sevenRow W Z β hβ t V r) (measurable_sevenRow W Z β hβ t V r)
    (fun j => previousDuration t j)
  · intro j
    exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _)))
  · intro i hi u
    have hpos : 0 < sevenDuration r (fun j => previousDuration t j) i := by
      cases i with
      | inl j => exact zero_lt_one
      | inr p =>
        apply Finset.sum_pos
        · intro j _
          exact sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _)))
        · exact dyadicIntervalSets_nonempty r p.2
    exact False.elim ((ne_of_gt hpos) hi)
  · exact hv
  · exact hr
  · exact hη
  · exact hRows

end SKConstants.Completion.LW
