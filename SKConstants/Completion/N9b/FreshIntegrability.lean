module

public import SKConstants.Completion.N9.FrozenQuery
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 M1
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem measurable_freshRowDrivers_param (a h f : ℝ≥0)
    (B D : Ξ → ScalarContinuousPath a) (z : Ξ → ℝ × FreshRowSeed h f)
    (hB : Measurable B) (hD : Measurable D) (hz : Measurable z) :
    Measurable (fun p => freshRowDrivers a h f (B p) (D p) (z p)) := by
  apply Measurable.prodMk
  · exact (measurable_scalarConcatPath a (h+f)).comp
      (hB.prodMk ((measurable_scalarConcatPath h f).comp
        (((measurable_scalarQueryBridgeComplete h).comp
          (hz.fst.prodMk hz.snd.fst)).prodMk hz.snd.snd.fst)))
  · exact (measurable_scalarConcatPath a (h+f)).comp
      (hD.prodMk hz.snd.snd.snd.fst)

theorem measurable_freshRowTerminalField_param (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0)
    (B D : Ξ → ScalarContinuousPath a) (z : Ξ → ℝ × FreshRowSeed h f)
    (hB : Measurable B) (hD : Measurable D) (hz : Measurable z) :
    Measurable (fun p => freshRowTerminalField W β hβ a h f (B p) (D p) (z p)) := by
  exact (ContinuousMap.measurable_eval _).comp
    ((measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
      (measurable_const.prodMk (measurable_freshRowDrivers_param a h f B D z hB hD hz)))

theorem measurable_freshRowSign_param (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0)
    (B D : Ξ → ScalarContinuousPath a) (z : Ξ → ℝ × FreshRowSeed h f)
    (hB : Measurable B) (hD : Measurable D) (hz : Measurable z) :
    Measurable (fun p => freshRowSign W β hβ a h f (B p) (D p) (z p)) := by
  have hm : Measurable (fun p => actualParisiFullMagnetization β (a+(h+f))
      (freshRowTerminalField W β hβ a h f (B p) (D p) (z p))) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
        (measurable_freshRowTerminalField_param W β hβ a h f B D z hB hD hz)
  exact Measurable.ite (measurableSet_le hz.snd.snd.snd.snd
    ((measurable_const.add hm).div_const 2)) measurable_const measurable_const

theorem measurable_fixedPastPosterior_param (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a : ℝ≥0) (B D : Ξ → ScalarContinuousPath a)
    (hB : Measurable B) (hD : Measurable D) :
    Measurable (fun p => fixedPastPosterior W β hβ a (B p) (D p)) := by
  exact ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
    ((ContinuousMap.measurable_eval _).comp
      ((measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
        (measurable_const.prodMk (hB.prodMk hD))))

theorem remainingProjection_entry_abs_le_one {m n : ℕ}
    (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i=j then 1 else 0) (i j : Fin n) :
    |remainingProjection F i j| ≤ 1 := by
  let P := remainingProjection F
  have hsym (k l : Fin n) : P k l = P l k := by
    dsimp [P, remainingProjection]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hsq : (∑ k, P i k^2) = P i i := by
    have he := congrArg (fun A => A i i) (remainingProjection_idempotent F hF)
    change (∑ k, P i k*P k i) = P i i at he
    simpa only [← hsym i, ← pow_two] using he
  have hle : (P i j)^2 ≤ 1 :=
    ((Finset.single_le_sum (fun k _ => sq_nonneg (P i k)) (Finset.mem_univ j)).trans_eq hsq).trans
      (remainingProjection_diagonal_bounds F hF i).2
  change |P i j| ≤ 1
  nlinarith [sq_abs (P i j), abs_nonneg (P i j)]

theorem normalizedQuery_entry_abs_le_sqrt {m n : ℕ} (N : ℝ)
    (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i=j then 1 else 0) (i : Fin n) :
    |normalizedQuery N (F 0) i| ≤ Real.sqrt N := by
  have hrow : (∑ k, F 0 k^2) = 1 := by
    simpa only [dot, ite_true, ← pow_two] using hF 0 0
  have hs : (F 0 i)^2 ≤ 1 :=
    (Finset.single_le_sum (fun k _ => sq_nonneg (F 0 k)) (Finset.mem_univ i)).trans_eq hrow
  have habs : |F 0 i| ≤ 1 := by nlinarith [sq_abs (F 0 i), abs_nonneg (F 0 i)]
  simpa only [normalizedQuery, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg N), mul_one] using
    mul_le_mul_of_nonneg_left habs (Real.sqrt_nonneg N)

theorem frozenQuery_integrable_prod (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (μ : Measure Ξ) [IsFiniteMeasure μ]
    (a h f : ℝ≥0) (n m : ℕ) (s : ℝ)
    (E : Ξ → Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Ξ → Fin n → ℝ)
    (B D : Ξ → Fin n → ScalarContinuousPath a)
    (hE : ∀ p i j, dot (E p i) (E p j) = if i=j then 1 else 0)
    (hEm : Measurable E) (hm₀ : Measurable m₀) (hB : Measurable B) (hD : Measurable D) :
    Integrable (fun z : Ξ × (Fin n → ℝ × FreshRowSeed h f) =>
      let t := frozenQueryTarget W β hβ a s (m₀ z.1) (B z.1) (D z.1)
      let row := gaussianSignRows
        (fun i => freshRowSign W β hβ a h f (B z.1 i) (D z.1 i))
      oneQueryEnergy row n (normalizedQuery n (paperFrame (E z.1) t 0))
        (remainingProjection (paperFrame (E z.1) t)) z.2) (μ.prod (freshRowsLaw W h f n)) := by
  let : IsProbabilityMeasure (freshRowsLaw W h f n) := freshRowsLaw_probability W h f n
  let T := fun p => frozenQueryTarget W β hβ a s (m₀ p) (B p) (D p)
  let F := fun p => paperFrame (E p) (T p)
  let U := fun p => normalizedQuery n (F p 0)
  let P := fun p => remainingProjection (F p)
  let X := fun (z : Ξ × (Fin n → ℝ × FreshRowSeed h f)) i =>
    if freshRowSign W β hβ a h f (B z.1 i) (D z.1 i) (z.2 i) then (1 : ℝ) else -1
  have hTm (i : Fin n) : Measurable (fun p => T p i) :=
    ((measurable_fixedPastPosterior_param W β hβ a
      (fun p => B p i) (fun p => D p i)
      ((measurable_pi_apply i).comp hB) ((measurable_pi_apply i).comp hD)).sub
        ((measurable_pi_apply i).comp hm₀)).div_const s
  have hFm (i j) : Measurable (fun p => F p i j) :=
    paperFrame_measurable E T
      (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hEm)) hTm i j
  have hUm (i) : Measurable (fun p => U p i) := (hFm 0 i).const_mul _
  have hPm (i j) : Measurable (fun p => P p i j) := by
    dsimp [P, remainingProjection, Matrix.mul_apply, Matrix.transpose_apply, tailRows]
    fun_prop
  have hXm (i : Fin n) : Measurable (fun z => X z i) := by
    exact (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      (measurable_freshRowSign_param W β hβ a h f
        (fun z : Ξ × (Fin n → ℝ × FreshRowSeed h f) => B z.1 i)
        (fun z => D z.1 i) (fun z => z.2 i)
        (((measurable_pi_apply i).comp hB).comp measurable_fst)
        (((measurable_pi_apply i).comp hD).comp measurable_fst)
        ((measurable_pi_apply i).comp measurable_snd))
  have hXnorm (z : Ξ × (Fin n → ℝ × FreshRowSeed h f)) i : ‖X z i‖ = 1 := by
    dsimp [X]
    split <;> norm_num
  have hg (i : Fin n) : Integrable
      (fun z : Ξ × (Fin n → ℝ × FreshRowSeed h f) => (z.2 i).1)
        (μ.prod (freshRowsLaw W h f n)) :=
    (gaussianSignRows_integrable (fun _ : Fin n => freshRowSeedLaw W h f)
      (fun _ _ => false) i).comp_snd μ
  have hterm (i j k : Fin n) : Integrable
      (fun z : Ξ × (Fin n → ℝ × FreshRowSeed h f) =>
        U z.1 i * P z.1 j k * (X z i * X z j * (z.2 k).1))
          (μ.prod (freshRowsLaw W h f n)) := by
    have hb : Integrable (fun z : Ξ × (Fin n → ℝ × FreshRowSeed h f) =>
        (U z.1 i * P z.1 j k * (X z i * X z j)) * (z.2 k).1)
          (μ.prod (freshRowsLaw W h f n)) := by
      apply (hg k).bdd_mul
        ((((hUm i).comp measurable_fst).mul ((hPm j k).comp measurable_fst)).mul
          ((hXm i).mul (hXm j))).aestronglyMeasurable
        (c := Real.sqrt n)
      apply ae_of_all
      intro z
      change ‖U z.1 i * P z.1 j k * (X z i * X z j)‖ ≤ Real.sqrt n
      rw [norm_mul, norm_mul, norm_mul, hXnorm z i, hXnorm z j, one_mul, mul_one]
      exact (mul_le_mul (normalizedQuery_entry_abs_le_sqrt n (F z.1)
        (paperFrame_orthogonal _ _ (hE z.1)) i)
        (remainingProjection_entry_abs_le_one (F z.1)
          (paperFrame_orthogonal _ _ (hE z.1)) j k)
        (abs_nonneg _) (Real.sqrt_nonneg _)).trans_eq (mul_one _)
    convert hb using 1
    ext z
    ring
  exact (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => hterm i j k)))).const_mul (((n : ℝ)⁻¹)^2)

theorem frozenQueryExpectation_integrable (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (μ : Measure Ξ) [IsFiniteMeasure μ]
    (a h f : ℝ≥0) (n m : ℕ) (s : ℝ)
    (E : Ξ → Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Ξ → Fin n → ℝ)
    (B D : Ξ → Fin n → ScalarContinuousPath a)
    (hE : ∀ p i j, dot (E p i) (E p j) = if i=j then 1 else 0)
    (hEm : Measurable E) (hm₀ : Measurable m₀) (hB : Measurable B) (hD : Measurable D) :
    Integrable (fun p => frozenQueryExpectation W β hβ a h f s
      (E p) (m₀ p) (B p) (D p)) μ := by
  let : IsProbabilityMeasure (freshRowsLaw W h f n) := freshRowsLaw_probability W h f n
  exact (frozenQuery_integrable_prod W β hβ μ a h f n m s E m₀ B D hE hEm hm₀ hB hD).integral_prod_left

end SKConstants.Completion.N9b
