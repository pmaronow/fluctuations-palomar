module

public import SKConstants.Completion.LW.DurationBounds
public import SKConstants.Completion.LW.VectorConcentration

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW

def rowAverage {Ω : Type*} {n d : ℕ} (U : Ω → EuclideanSpace ℝ (Fin d))
    (ω : Fin n → Ω) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i : Fin n, U (ω i)

def normalizedRow {Ω : Type*} {d : ℕ} (U : Ω → EuclideanSpace ℝ (Fin d))
    (duration : ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  (Real.sqrt duration)⁻¹ • U ω

theorem iid_duration_vector_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} (hn : 0 < n)
    (U : Ω → EuclideanSpace ℝ (Fin d)) (hU : Measurable U)
    {duration v radius η : ℝ} (hd : 0 ≤ duration)
    (hzero : duration = 0 → ∀ ω, U ω = 0)
    (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η)
    (hRows : ∀ a : EuclideanSpace ℝ (Fin d), ‖a‖ ≤ 1 →
      Concentration.LocalQuadraticMGF (fun ω => ⟪normalizedRow U duration ω,a⟫_ℝ)
        μ v radius) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | 2*η*Real.sqrt duration < ‖rowAverage U ω‖} ≤
        2 * (5 : ℝ)^d * Real.exp (-(n : ℝ) *
          min (η^2/(4*v)) (radius*η/2)) := by
  by_cases hz : duration = 0
  · have he : {ω : Fin n → Ω | 2*η*Real.sqrt duration < ‖rowAverage U ω‖} = ∅ := by
      ext ω
      simp [hz, rowAverage, hzero hz]
    rw [he, measureReal_empty]
    positivity
  have hs : 0 < Real.sqrt duration := Real.sqrt_pos.mpr (lt_of_le_of_ne hd (Ne.symm hz))
  have hm : Measurable (normalizedRow U duration) := by
    exact hU.const_smul ((Real.sqrt duration)⁻¹)
  have H := iid_vector_average_tail μ hn (normalizedRow U duration) hm hv hr hη hRows
  have heq (ω : Fin n → Ω) :
      rowAverage (normalizedRow U duration) ω = (Real.sqrt duration)⁻¹ • rowAverage U ω := by
    unfold rowAverage normalizedRow
    rw [← Finset.smul_sum, smul_comm]
  have hsub : {ω : Fin n → Ω | 2*η*Real.sqrt duration < ‖rowAverage U ω‖} ⊆
      {ω | 2*η < ‖rowAverage (normalizedRow U duration) ω‖} := by
    intro ω hω
    change 2*η*Real.sqrt duration < ‖rowAverage U ω‖ at hω
    change 2*η < ‖rowAverage (normalizedRow U duration) ω‖
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, ← div_eq_inv_mul]
    exact (lt_div_iff₀ hs).mpr hω
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans H

theorem iid_duration_family_tail {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} (hn : 0 < n)
    (U : J → Ω → EuclideanSpace ℝ (Fin d)) (hU : ∀ j, Measurable (U j))
    (duration : J → ℝ) (hd : ∀ j, 0 ≤ duration j)
    (hzero : ∀ j, duration j = 0 → ∀ ω, U j ω = 0)
    {v radius η : ℝ} (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η)
    (hRows : ∀ j (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      Concentration.LocalQuadraticMGF
        (fun ω => ⟪normalizedRow (U j) (duration j) ω,a⟫_ℝ) μ v radius) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | ∃ j, 2*η*Real.sqrt (duration j) < ‖rowAverage (U j) ω‖} ≤
        2 * (Fintype.card J : ℝ) * (5 : ℝ)^d * Real.exp (-(n : ℝ) *
          min (η^2/(4*v)) (radius*η/2)) := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let E (j : J) : Set (Fin n → Ω) :=
    {ω | 2*η*Real.sqrt (duration j) < ‖rowAverage (U j) ω‖}
  have hevent : {ω | ∃ j, 2*η*Real.sqrt (duration j) < ‖rowAverage (U j) ω‖} =
      ⋃ j ∈ (Finset.univ : Finset J), E j := by ext ω; simp [E]
  rw [hevent]
  calc
    P.real (⋃ j ∈ (Finset.univ : Finset J), E j) ≤ ∑ j : J, P.real (E j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j : J, 2 * (5 : ℝ)^d * Real.exp (-(n : ℝ) *
        min (η^2/(4*v)) (radius*η/2)) := Finset.sum_le_sum (fun j _ =>
          iid_duration_vector_tail μ hn (U j) (hU j) (hd j) (hzero j) hv hr hη (hRows j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem duration_family_square_bound {J : Type*} [Fintype J]
    (z duration : J → ℝ) (hd : ∀ j, 0 ≤ duration j) {η : ℝ}
    (hz0 : ∀ j, 0 ≤ z j)
    (hz : ∀ j, z j ≤ 2*η*Real.sqrt (duration j)) :
    (∑ j, z j^2) ≤ 4*η^2 * ∑ j, duration j := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ (2*η*Real.sqrt (duration j))^2 :=
      pow_le_pow_left₀ (hz0 j) (hz j) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (hd j)]; ring

theorem iid_duration_total_tail {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} (hn : 0 < n)
    (U : J → Ω → EuclideanSpace ℝ (Fin d)) (hU : ∀ j, Measurable (U j))
    (duration : J → ℝ) (hd : ∀ j, 0 ≤ duration j)
    (hzero : ∀ j, duration j = 0 → ∀ ω, U j ω = 0)
    {v radius η : ℝ} (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η)
    (hRows : ∀ j (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      Concentration.LocalQuadraticMGF
        (fun ω => ⟪normalizedRow (U j) (duration j) ω,a⟫_ℝ) μ v radius) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | 4*η^2 * ∑ j, duration j < ∑ j, ‖rowAverage (U j) ω‖^2} ≤
        2 * (Fintype.card J : ℝ) * (5 : ℝ)^d * Real.exp (-(n : ℝ) *
          min (η^2/(4*v)) (radius*η/2)) := by
  have hsub : {ω : Fin n → Ω |
      4*η^2 * ∑ j, duration j < ∑ j, ‖rowAverage (U j) ω‖^2} ⊆
      {ω | ∃ j, 2*η*Real.sqrt (duration j) < ‖rowAverage (U j) ω‖} := by
    intro ω hω
    by_contra H
    change ¬ ∃ j, 2*η*Real.sqrt (duration j) < ‖rowAverage (U j) ω‖ at H
    have H' (j : J) : ‖rowAverage (U j) ω‖ ≤ 2*η*Real.sqrt (duration j) :=
      le_of_not_gt (fun hj => H ⟨j,hj⟩)
    exact (not_lt_of_ge (duration_family_square_bound
      (fun j => ‖rowAverage (U j) ω‖) duration hd (fun _ => norm_nonneg _) H')) hω
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (iid_duration_family_tail μ hn U hU duration hd hzero hv hr hη hRows)

end SKConstants.Completion.LW
