module

public import SKConstants.ParisiFiniteCDFBridge
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
public import SKConstants.Upstream.OAI.Probability.SKSupport.Foundations.SmoothingStep
public import SKConstants.Upstream.OAI.Probability.SKSupport.Control.CoefficientApprox

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def dyadicCDFMesh (n : ℕ) (t : ℝ≥0) : ℝ≥0 := t / (2 : ℝ≥0) ^ n

theorem dyadicIntervals_length (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    (dyadicIntervals α n s t).length = 2 ^ n := by
  induction n generalizing s t with
  | zero => simp [dyadicIntervals]
  | succ n ih =>
    simp only [dyadicIntervals, List.length_append, ih, pow_succ]
    omega

theorem dyadicIntervals_uniform_duration (α : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (t : ℝ≥0) {p : ℝ × ℝ≥0} (hp : p ∈ dyadicIntervals α n s t) :
    p.2 = dyadicCDFMesh n t := by
  induction n generalizing s t with
  | zero =>
    have hp' : p = (α s, t) := by simpa only [dyadicIntervals, List.mem_singleton] using hp
    simp [hp', dyadicCDFMesh]
  | succ n ih =>
    have he : dyadicCDFMesh n (t / 2) = dyadicCDFMesh (n + 1) t := by
      simp only [dyadicCDFMesh, pow_succ, div_div]
      rw [mul_comm]
    simp only [dyadicIntervals, List.mem_append] at hp
    exact (hp.elim (ih s (t / 2)) (ih (s + (t : ℝ) / 2) (t / 2))).trans he

def dyadicCDFCoefficient (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  if hk : k < (dyadicIntervals α n s t).length then
    Real.toNNReal (((dyadicIntervals α n s t).get ⟨k, hk⟩).1) else 0

lemma dyadicCDFCoefficient_le_one {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0) (k : ℕ) :
    (dyadicCDFCoefficient α n s t k : ℝ) ≤ 1 := by
  unfold dyadicCDFCoefficient
  split_ifs with hk
  · rw [Real.coe_toNNReal _
      (dyadicIntervals_mass_bounds hα n s t (List.get_mem _ ⟨k, hk⟩)).1]
    exact (dyadicIntervals_mass_bounds hα n s t (List.get_mem _ ⟨k, hk⟩)).2
  · simp

lemma finiteCoeff_le_one {c : ℕ → ℝ≥0} (hc : ∀ k, (c k : ℝ) ≤ 1)
    (h : ℝ≥0) (N k : ℕ) (r : ℝ) : finiteCoeff c h N k r ≤ 1 := by
  induction N generalizing k r with
  | zero => simp [finiteCoeff]
  | succ N ih =>
    simp only [finiteCoeff]
    split_ifs
    · exact hc k
    · exact ih (k + 1) (r - h)

theorem dyadicScalar_eq_finiteValue_zero {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (β : ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    dyadicScalar β α n s t scalarSpinTerminal =
      finiteValue (dyadicCDFCoefficient α n s t)
        (Real.toNNReal (β ^ 2) * dyadicCDFMesh n t) (softAbs 1) (2 ^ n) 0 0 := by
  let l := dyadicIntervals α n s t
  let c := dyadicCDFCoefficient α n s t
  have hlist : List.ofFn (fun i : Fin l.length => ((c i : ℝ), dyadicCDFMesh n t)) = l := by
    calc
      _ = List.ofFn (fun i : Fin l.length => l.get i) := by
        congr 1
        funext i
        apply Prod.ext
        · change (dyadicCDFCoefficient α n s t i : ℝ) =
            ((dyadicIntervals α n s t).get i).1
          rw [dyadicCDFCoefficient, dite_eq_left i.isLt, Real.coe_toNNReal _
            (dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i)).1]
        · exact (dyadicIntervals_uniform_duration α n s t (List.get_mem _ i)).symm
      _ = l := List.ofFn_get l
  have hterminal : scalarSpinTerminal = softAbs 1 := by
    funext x
    simp [scalarSpinTerminal, softAbs]
  rw [finiteValue_zero (regularDatum_softAbs (by norm_num : (1 : ℝ) ≠ 0))
    (softAbs_lipschitz (by norm_num : (1 : ℝ) ≠ 0))]
  have H := scalarTimeChain_uniform_eq_cascade
    (regularDatum_softAbs (by norm_num : (1 : ℝ) ≠ 0))
    (softAbs_lipschitz (by norm_num : (1 : ℝ) ≠ 0)) β c (dyadicCDFMesh n t) l.length 0
  simp only [Nat.zero_add] at H
  rw [hlist] at H
  simpa only [l, c, dyadicScalar, hterminal, dyadicIntervals_length] using H

theorem dyadicScalar_uniform_higher_derivative_bounds {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) {β : ℝ} (hβ : β ≠ 0)
    (s : ℝ) (t : ℝ≥0) (ht : 0 < (t : ℝ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
      |iteratedDeriv (m + 2) (dyadicScalar β α n s t scalarSpinTerminal) x| ≤ C := by
  let δ := β ^ 2 * (t : ℝ) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos (sq_pos_of_ne_zero hβ) ht) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := finiteGradient_uniform_smoothing (m + 1) 1 (by norm_num) δ hδ
  refine ⟨C, hC, ?_⟩
  intro n x
  let c := dyadicCDFCoefficient α n s t
  let h := Real.toNNReal (β ^ 2) * dyadicCDFMesh n t
  have hh : ((2 ^ n : ℕ) : ℝ) * h = β ^ 2 * (t : ℝ) := by
    simp only [h, dyadicCDFMesh, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat,
      Real.coe_toNNReal _ (sq_nonneg β), Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    <;> ring
  have HH := hbound (softAbs 1) (regularDatum_softAbs (by norm_num : (1 : ℝ) ≠ 0))
    (softAbs_lipschitz (by norm_num : (1 : ℝ) ≠ 0)) c h (2 ^ n) 0 0 le_rfl
    (by rw [hh]; dsimp [δ]; linarith [mul_pos (sq_pos_of_ne_zero hβ) ht])
    (fun r _ => finiteCoeff_le_one (dyadicCDFCoefficient_le_one hα n s t) h (2 ^ n) 0 r)
    (m + 1) le_rfl 0 ⟨le_rfl, le_rfl⟩ x
  rw [dyadicScalar_eq_finiteValue_zero hα β n s t]
  simpa only [iteratedDeriv_succ'] using HH

theorem scalarCDFValue_contDiff_and_higher_derivative_limit {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {β : ℝ} (hβ : β ≠ 0) (s : ℝ) (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ht1 : t ≤ 1) :
    ContDiff ℝ ∞ (scalarCDFValue β α s t) ∧
      ∀ m : ℕ, TendstoUniformly
        (fun n => iteratedDeriv m (dyadicScalar β α n s t scalarSpinTerminal))
        (iteratedDeriv m (scalarCDFValue β α s t)) atTop := by
  apply smooth_limit_of_uniform_derivative_bounds
  · intro n
    rw [dyadicScalar_eq_finiteValue_zero hα β n s t]
    exact (finiteValue_regular (regularDatum_softAbs (by norm_num : (1 : ℝ) ≠ 0))
      (softAbs_lipschitz (by norm_num : (1 : ℝ) ≠ 0)) _ _ _ _ _).smooth
  · exact dyadicScalar_uniform_higher_derivative_bounds hα hβ s t ht
  · exact dyadicScalar_value_uniform β hα hmono s t ht1

end SKConstants.ParisiFullSupport
