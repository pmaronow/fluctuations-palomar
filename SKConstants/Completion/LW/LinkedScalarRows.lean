module

public import SKConstants.ParisiFullMixedRowCovariance
public import SKConstants.Completion.LC1.QuerySpinMoments
public import SKConstants.Completion.LC1.UpperBlock
public import SKConstants.Completion.LW.DurationBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK LQ

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

abbrev linkedScalarLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) : Measure ((Bool × Ω) × A) :=
  actualParisiFullQuerySpinLaw W Z β V

theorem linkedScalarLaw_eq_withDensity (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) :
    linkedScalarLaw W Z β V =
      (((scalarHiddenPriorBool 0).prod W.law).prod Z.law).withDensity
        (fun u => ENNReal.ofReal
          (1 + scalarHiddenSign u.1.1 * actualParisiFullPosteriorMean W β V u.1.2)) := by
  letI := W.isProbability
  letI := Z.isProbability
  unfold linkedScalarLaw actualParisiFullQuerySpinLaw actualParisiFullTerminalSpinLaw
  rw [prod_withDensity_left
    (measurable_actualParisiFullTerminalSpinDensity β W V).ennreal_ofReal]
  rfl

theorem linkedScalarLaw_drivers_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) :
    HasLaw (fun u : (Bool × Ω) × A => (u.1.2,u.2))
      (W.law.prod Z.law) (linkedScalarLaw W Z β V) :=
  actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β V

abbrev linkedScalarRowsLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) (n : ℕ) : Measure (Fin n → (Bool × Ω) × A) :=
  actualParisiFullMixedRowsLaw W Z β V n

theorem linkedScalarRowsLaw_independent {E : Type*} [MeasurableSpace E]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (V : ℝ≥0) (n : ℕ)
    (f : (Bool × Ω) × A → E) (hf : Measurable f) :
    iIndepFun (fun i : Fin n => fun ω => f (ω i)) (linkedScalarRowsLaw W Z β V n) :=
  iIndepFun_pi (fun _ => hf.aemeasurable)

theorem linkedScalarRowsLaw_drivers_hasLaw
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (V : ℝ≥0) (n : ℕ) :
    HasLaw (fun ω : Fin n → (Bool × Ω) × A => fun i => ((ω i).1.2,(ω i).2))
      (Measure.pi (fun _ : Fin n => W.law.prod Z.law))
      (linkedScalarRowsLaw W Z β V n) := by
  letI := W.isProbability
  letI := Z.isProbability
  exact (measurePreserving_pi (fun _ : Fin n => linkedScalarLaw W Z β V)
    (fun _ => W.law.prod Z.law) (fun _ =>
      ⟨(measurable_snd.comp measurable_fst).prodMk measurable_snd,
        (linkedScalarLaw_drivers_hasLaw W Z β V).map_eq⟩)).hasLaw

def posteriorRow (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (k : ℕ)
    (u : (Bool × Ω) × A) : EuclideanSpace ℝ (Fin k) :=
  actualParisiNormalizedPosteriorRow W β t k u.1.2

def queryRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (k : ℕ) (u : (Bool × Ω) × A) : EuclideanSpace ℝ (Fin k) :=
  scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B
    (fun j => t (j+1)) (u.1.2,u.2)

theorem measurable_posteriorRow (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (k : ℕ) : Measurable (posteriorRow (A := A) W β t k) :=
  (measurable_actualParisiNormalizedPosteriorRow W β t k).comp
    (measurable_snd.comp measurable_fst)

theorem measurable_queryRow (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (k : ℕ) :
    Measurable (queryRow W Z β hβ t k) :=
  (measurable_scalarNormalizedBrownianRow
    (actualParisiQueryBrownianSystem W Z β hβ).B
    (actualParisiQueryBrownianSystem W Z β hβ).measurable (fun j => t (j+1))).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

def previousDuration (t : ℕ → ℝ≥0) (j : ℕ) : ℝ := (t (j+1) : ℝ) - t j

theorem sum_previousDuration (t : ℕ → ℝ≥0) (k : ℕ) :
    (∑ j : Fin k, previousDuration t j) = (t k : ℝ) - t 0 := by
  have H (m : ℕ) : (∑ j ∈ Finset.range m, previousDuration t j) = (t m : ℝ)-t 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [previousDuration]; ring
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ j ∈ Finset.range k, previousDuration t j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, dite_true]
    _ = _ := H k

def posteriorWeight (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (k : ℕ) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => (actualParisiPosteriorIntervalScale W β (t j) (t (j+1)) : ℝ))

def queryWeight (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (k : ℕ) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j =>
    (∫ v in (t (j+1) : ℝ)..(t (j+2) : ℝ),
      actualParisiQueryRho W β v * actualParisiFullSusceptibilityExpected W β v) /
        Real.sqrt (previousDuration t (j+1)))

theorem posteriorWeight_eq_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (j : Fin k) :
    posteriorWeight W β t k j = posteriorScale
      (actualParisiFullSusceptibilitySquareExpected W β) (t j) (t (j+1)) :=
  actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _ (ht (Nat.lt_succ_self _))

theorem queryWeight_div_posteriorWeight_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (j : Fin k) {κ : ℝ}
    (hratio : previousDuration t (j+1) / previousDuration t j ≤ κ) :
    |queryWeight W β t k j| / posteriorWeight W β t k j ≤ Real.sqrt κ := by
  have heq : queryWeight W β t k j = LQ.queryMean
      (fun v => actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v)
      (t (j+1) : ℝ) (t (j+2) : ℝ) := by
    change (∫ v in (t (j+1) : ℝ)..(t (j+2) : ℝ),
        actualParisiQueryRho W β v * actualParisiFullSusceptibilityExpected W β v) /
        Real.sqrt (previousDuration t (j+1)) = _
    unfold LQ.queryMean previousDuration
    congr 1
    apply intervalIntegral.integral_congr
    intro v _
    exact mul_comm _ _
  rw [heq, posteriorWeight_eq_integral W β hβ t ht]
  apply actual_adjacent_query_weight_le_of_ratio W β hβ (t j).coe_nonneg
    (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _)))
    (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _)))
  exact hratio

theorem posteriorRow_spin_moment (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (k : ℕ) (j : Fin k) (V : ℝ≥0) (hV : t (j+1) ≤ V) :
    (∫ u, posteriorRow W β t k u j * scalarHiddenSign u.1.1
      ∂linkedScalarLaw W Z β V) = posteriorWeight W β t k j := by
  have hm : Measurable (fun u : Bool × Ω =>
      (actualParisiMagnetizationIncrement W β (t j) (t (j+1)) u.2 /
        (actualParisiPosteriorIntervalScale W β (t j) (t (j+1)) : ℝ)) *
        scalarHiddenSign u.1) := by
    have h1 := measurable_actualParisiMagnetizationIncrement W β (t j) (t (j+1))
    have h2 := measurable_of_finite scalarHiddenSign
    fun_prop
  exact ((actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).integral_comp
    hm.aestronglyMeasurable).trans
      (actualParisiFullTerminalSpinLaw_normalized_increment_spin_moment W β hβ
        (t j) (t (j+1)) V (ht (Nat.lt_succ_self _)) hV)

theorem queryRow_spin_moment (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (k : ℕ) (j : Fin k) (V : ℝ≥0) (hV : t (j+2) ≤ V) :
    (∫ u, queryRow W Z β hβ t k u j * scalarHiddenSign u.1.1
      ∂linkedScalarLaw W Z β V) = queryWeight W β t k j := by
  simpa only [queryRow, queryWeight, previousDuration, Nat.add_assoc] using
    LC1.actualQuerySpinLaw_normalized_query_spin_moment
      W Z β hβ (fun i => t (i+1)) k j V (ht (by omega)) (by simpa [Nat.add_assoc] using hV)

theorem posterior_query_upper_moment (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (k : ℕ) (V : ℝ≥0) (i j : Fin k) (hij : i ≤ j) :
    (∫ u, posteriorRow W β t k u i * queryRow W Z β hβ t k u j
      ∂linkedScalarLaw W Z β V) = 0 :=
  LC1.actualQuerySpinLaw_shifted_upper_block W Z β hβ t ht k V i j hij

end SKConstants.Completion.LW
