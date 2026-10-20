module

public import SKConstants.FiniteContradiction
public import Mathlib.Probability.Independence.Basic

public section
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory

namespace SKConstants

theorem probability_finite_endpoint_mass {V Ω : Type*}
    [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : V → ℝ) (X : Ω → V) (A : Finset V) (hX : Measurable X)
    (hmarg : ∀ u, μ.real {ω | X ω = u} = q u) :
    μ.real (X ⁻¹' (A : Set V)) = ∑ u ∈ A, q u := by
  calc
    μ.real (X ⁻¹' (A : Set V)) = ∑ u ∈ A, μ.real (X ⁻¹' {u}) :=
      (sum_measureReal_preimage_singleton A
        (fun u _ ↦ (measurableSet_singleton u).preimage hX)).symm
    _ = ∑ u ∈ A, q u := by
      apply Finset.sum_congr rfl
      intro u _
      simpa only [Set.preimage, Set.mem_singleton_iff] using hmarg u

theorem probability_independent_finite_endpoint_rectangle {V Ω : Type*}
    [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : V → ℝ) (X Y : Ω → V) (A B : Finset V)
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y μ)
    (hXmarg : ∀ u, μ.real {ω | X ω = u} = q u)
    (hYmarg : ∀ v, μ.real {ω | Y ω = v} = q v) :
    μ.real {ω | X ω ∈ A ∧ Y ω ∈ B} =
      (∑ u ∈ A, q u) * (∑ v ∈ B, q v) := by
  have h := hind.measure_inter_preimage_eq_mul (A : Set V) (B : Set V)
    A.measurableSet B.measurableSet
  calc
    μ.real {ω | X ω ∈ A ∧ Y ω ∈ B} =
        μ.real (X ⁻¹' (A : Set V) ∩ Y ⁻¹' (B : Set V)) := rfl
    _ = μ.real (X ⁻¹' (A : Set V)) * μ.real (Y ⁻¹' (B : Set V)) := by
      simpa only [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
    _ = (∑ u ∈ A, q u) * (∑ v ∈ B, q v) := by
      rw [probability_finite_endpoint_mass μ q X A hX hXmarg,
        probability_finite_endpoint_mass μ q Y B hY hYmarg]

theorem probability_finiteKL_balanced_endpoint_crossing {V Ω : Type*}
    [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : V → ℝ) (X Y : Ω → V) (A : Finset V) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y μ)
    (hXmarg : ∀ u, μ.real {ω | X ω = u} = q u)
    (hYmarg : ∀ v, μ.real {ω | Y ω = v} = q v) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤
      μ.real {ω | X ω ∈ A ∧ Y ω ∉ A} := by
  have h₁ := finiteKL_uniform_coverage p q A K alpha hp hq hp_sum hq_sum
    hKL hAlpha hA
  have h₂ := finiteKL_uniform_coverage p q Aᶜ K alpha hp hq hp_sum hq_sum
    hKL hAlpha hAc
  have hprod := mul_le_mul h₁ h₂ (Real.exp_pos _).le
    (Finset.sum_nonneg (fun u _ ↦ (hq u).le))
  have hexp : Real.exp (-2 * (K + Real.log 2) / alpha) =
      Real.exp (-(K + Real.log 2) / alpha) *
        Real.exp (-(K + Real.log 2) / alpha) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hrect := probability_independent_finite_endpoint_rectangle μ q X Y A Aᶜ
    hX hY hind hXmarg hYmarg
  simpa only [Finset.mem_compl] using hprod.trans_eq hrect.symm

theorem probability_balanced_coarse_avoidance_bad_mass {V Ω : Type*}
    [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : SimpleGraph V) (p q : V → ℝ) (A : Finset V)
    (f : Ω → ℕ → V) (coarse : Ω → ℕ → Prop) (good : Set Ω)
    (N R : ℕ) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hX : Measurable (fun ω ↦ f ω 0)) (hY : Measurable (fun ω ↦ f ω N))
    (hind : IndepFun (fun ω ↦ f ω 0) (fun ω ↦ f ω N) μ)
    (hXmarg : ∀ u, μ.real {ω | f ω 0 = u} = q u)
    (hYmarg : ∀ v, μ.real {ω | f ω N = v} = q v)
    (hgood : MeasurableSet good)
    (hsteps : ∀ ω ∈ good, ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω ∈ good, ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω ∈ good, ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set V) R) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤ μ.real goodᶜ ∧
    μ.real good ≤ 1 - Real.exp (-2 * (K + Real.log 2) / alpha) := by
  have hcross := probability_finiteKL_balanced_endpoint_crossing μ p q
    (fun ω ↦ f ω 0) (fun ω ↦ f ω N) A K alpha hp hq hp_sum hq_sum
    hKL hAlpha hA hAc hX hY hind hXmarg hYmarg
  have hbad := finite_crossing_implies_bad G (A : Set V) f coarse
    (fun ω ↦ ω ∈ good) N R hsteps hcoarse havoid
  have hmass : Real.exp (-2 * (K + Real.log 2) / alpha) ≤ μ.real goodᶜ :=
    hcross.trans (measureReal_mono hbad)
  refine ⟨hmass, ?_⟩
  rw [measureReal_compl hgood] at hmass
  have huniv : μ.real Set.univ = 1 := by simp [Measure.real]
  rw [huniv] at hmass
  linarith

theorem probability_balanced_coarse_avoidance_contradiction {V Ω : Type*}
    [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : SimpleGraph V) (p q : V → ℝ) (A : Finset V)
    (f : Ω → ℕ → V) (coarse : Ω → ℕ → Prop) (good : Set Ω)
    (N R : ℕ) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hX : Measurable (fun ω ↦ f ω 0)) (hY : Measurable (fun ω ↦ f ω N))
    (hind : IndepFun (fun ω ↦ f ω 0) (fun ω ↦ f ω N) μ)
    (hXmarg : ∀ u, μ.real {ω | f ω 0 = u} = q u)
    (hYmarg : ∀ v, μ.real {ω | f ω N = v} = q v)
    (hgood : MeasurableSet good)
    (hsteps : ∀ ω ∈ good, ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω ∈ good, ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω ∈ good, ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set V) R)
    (hsmall : μ.real goodᶜ < Real.exp (-2 * (K + Real.log 2) / alpha)) : False := by
  have h := (probability_balanced_coarse_avoidance_bad_mass μ G p q A f
    coarse good N R K alpha hp hq hp_sum hq_sum hKL hAlpha hA hAc
    hX hY hind hXmarg hYmarg hgood hsteps hcoarse havoid).1
  exact (not_lt_of_ge h) hsmall

theorem probability_finiteGibbs_balanced_coarse_avoidance_bad_mass {n : ℕ}
    [MeasurableSpace (Spin n)] [MeasurableSingletonClass (Spin n)]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (G : SimpleGraph (Spin n)) (q : Spin n → ℝ) (A : Finset (Spin n))
    (f : Ω → ℕ → Spin n) (coarse : Ω → ℕ → Prop) (good : Set Ω)
    (N R : ℕ) (K alpha : ℝ)
    (hq : ∀ u, 0 < q u) (hq_sum : ∑ u, q u = 1)
    (hKL : finiteKL (gibbsProbability beta W) q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, gibbsProbability beta W u)
    (hAc : alpha ≤ ∑ u ∈ Aᶜ, gibbsProbability beta W u)
    (hX : Measurable (fun ω ↦ f ω 0)) (hY : Measurable (fun ω ↦ f ω N))
    (hind : IndepFun (fun ω ↦ f ω 0) (fun ω ↦ f ω N) μ)
    (hXmarg : ∀ u, μ.real {ω | f ω 0 = u} = q u)
    (hYmarg : ∀ v, μ.real {ω | f ω N = v} = q v)
    (hgood : MeasurableSet good)
    (hsteps : ∀ ω ∈ good, ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω ∈ good, ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω ∈ good, ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set (Spin n)) R) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤ μ.real goodᶜ ∧
    μ.real good ≤ 1 - Real.exp (-2 * (K + Real.log 2) / alpha) := by
  exact probability_balanced_coarse_avoidance_bad_mass μ G
    (gibbsProbability beta W) q A f coarse good N R K alpha
    (gibbsProbability_pos beta W) hq (gibbsProbability_sum beta W) hq_sum
    hKL hAlpha hA hAc hX hY hind hXmarg hYmarg hgood hsteps hcoarse havoid

end SKConstants
