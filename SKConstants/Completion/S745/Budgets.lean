module

public import SKConstants.Completion.S745.Geometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S745
open SKConstantsOAI.ZeroTemperatureSK Blueprint5a Blueprint4
variable {Ω : Type*} [MeasurableSpace Ω]

def coarseCoefficient (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K l j i : ℕ) : ℝ :=
  β * actualParisiFullSusceptibilityExpected W β (refinedGrid δ l j i) -
    LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j

def queryCoefficient (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (l j i : ℕ) : ℝ :=
  Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (refinedGrid δ l j i)) -
    LJ.residualCoarseB W β (Blueprint5a.mesh δ) j

theorem susceptibility_oscillation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {a b s v : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hs : s ∈ Icc a b) (hv : v ∈ Icc a b) :
    |actualParisiFullSusceptibilityExpected W β s -
      actualParisiFullSusceptibilityExpected W β v| ≤
        (b - a) * actualParisiFullSusceptibilityExpected W β a := by
  let p := actualParisiFullSusceptibilityExpected W β
  have hp0 : 0 ≤ p a := actualParisiFullSusceptibilityExpected_nonneg W β a
  have hexp := NScalar.susceptibility_exp_comparison W β hβ a b ha hab
  have hlow : (1 - (b - a)) * p a ≤ p b := by
    have H := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-(b - a))).le
    rw [← mul_assoc, ← Real.exp_add] at H
    have he : -(b - a) + (b - a) = 0 := by ring
    rw [he, Real.exp_zero, one_mul] at H
    exact (mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-(b - a))] :
      1 - (b - a) ≤ Real.exp (-(b - a))) hp0).trans H
  have hmono := LBase.actual_susceptibility_antitone W β hβ
  have hsa := hmono ha (ha.trans hs.1) hs.1
  have hsb := hmono (ha.trans hs.1) (ha.trans hab) hs.2
  have hva := hmono ha (ha.trans hv.1) hv.1
  have hvb := hmono (ha.trans hv.1) (ha.trans hab) hv.2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coarse_squareBudget_le (h2 : CoarseCoefficientBudgetStatement)
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K → ∀ l,
      squareBudget δ K l (coarseCoefficient W β δ K l) ≤ C * δ := by
  obtain ⟨C, hC, hbudget⟩ := h2 W β hβ
  let A := Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)
  have hA : 0 < A := Real.exp_pos _
  have hb : 0 < β := zero_lt_one.trans hβ
  refine ⟨2 * C + 16 * β ^ 2 * A, by positivity, ?_⟩
  intro δ K hm l
  have hδ := hm.1
  have hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1 :=
    fun j hj => hm.2.2.1 j (by omega)
  have hcount := growingQuery_finite_count_bound δ hδ (K + 1) hsmall
  have hcell (j : ℕ) (hj : j < K + 1) :
      (∑ i ∈ Finset.range (2 ^ l), coarseCoefficient W β δ K l j i ^ 2 *
        ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)) ≤
      2 * (∫ v in (Blueprint5a.mesh δ j : ℝ)..(Blueprint5a.mesh δ (j + 1) : ℝ),
        (β * actualParisiFullSusceptibilityExpected W β v -
          LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j) ^ 2) +
        2 * β ^ 2 * A * (δ : ℝ) ^ 2 := by
    let p := actualParisiFullSusceptibilityExpected W β
    let h : ℝ := growingQueryDuration δ j
    let a : ℝ := Blueprint5a.mesh δ j
    let D : ℝ := β * h * p a
    have hh0 : 0 ≤ h := (growingQueryDuration δ j).coe_nonneg
    have hh1 : h ≤ 1 := by exact_mod_cast hsmall j hj
    have hp0 : 0 ≤ p a := actualParisiFullSusceptibilityExpected_nonneg W β a
    have hos (i : ℕ) (hi : i < 2 ^ l) (v : ℝ)
        (hv : v ∈ Icc (refinedGrid δ l j 0 : ℝ) (refinedGrid δ l j (2 ^ l) : ℝ)) :
        |(β * p (refinedGrid δ l j i) - LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j) -
          (β * p v - LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j)| ≤ D := by
      have hs := refinedGrid_mem δ l j i hi.le
      simp only [refinedGrid, LJ3.growingLagDyadicTime_zero, LJ3.growingLagDyadicTime_end] at hv
      have H := susceptibility_oscillation W β hβ (growingQueryTime δ j).coe_nonneg
        (NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j)))
        (show (refinedGrid δ l j i : ℝ) ∈ Icc (growingQueryTime δ j : ℝ)
          (growingQueryTime δ (j + 1) : ℝ) from ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩) hv
      rw [growingQueryTime_sub] at H
      rw [show (β * p (refinedGrid δ l j i) - LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j) -
          (β * p v - LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j) =
          β * (p (refinedGrid δ l j i) - p v) by ring, abs_mul, abs_of_pos hb]
      exact (mul_le_mul_of_nonneg_left H hb.le).trans_eq (by dsimp [D]; ring)
    have H := sampled_square_le (refinedGrid δ l j) (LJ3.growingLagDyadicTime_monotone δ l j)
      (2 ^ l) (fun v => β * p v - LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j)
      (((continuous_actualParisiFullSusceptibilityExpected W β).const_mul β).sub continuous_const)
      D hos
    simp only [refinedGrid, LJ3.growingLagDyadicTime_zero, LJ3.growingLagDyadicTime_end,
      growingQueryTime_sub] at H
    have hpr := actualParisiFullSusceptibilityExpected_sq_le_squareExpected W β a
    have hr := LQ.mesh_profile_square_le (actualParisiFullSusceptibilitySquareExpected W β)
      A δ j (LQ.actual_square_profile_tail W β hβ a (growingQueryTime δ j).coe_nonneg)
    have hpp : p a ^ 2 * h ^ 2 * h ≤ A * (δ : ℝ) ^ 2 := by
      calc
        _ ≤ p a ^ 2 * h ^ 2 := mul_le_of_le_one_right (by positivity) hh1
        _ ≤ actualParisiFullSusceptibilitySquareExpected W β a * h ^ 2 :=
          mul_le_mul_of_nonneg_right hpr (sq_nonneg _)
        _ ≤ _ := hr
    have herr : 2 * D ^ 2 * h ≤ 2 * β ^ 2 * A * (δ : ℝ) ^ 2 := by
      have H := mul_le_mul_of_nonneg_left hpp (show 0 ≤ 2 * β ^ 2 by positivity)
      dsimp only [D] at *
      nlinarith only [H]
    exact H.trans (add_le_add le_rfl herr)
  have HI := (hbudget δ K hm).1
  change (∑ j ∈ Finset.range (K + 1), _) ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        (2 * (∫ v in (Blueprint5a.mesh δ j : ℝ)..(Blueprint5a.mesh δ (j + 1) : ℝ),
          (β * actualParisiFullSusceptibilityExpected W β v -
            LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j) ^ 2) +
          2 * β ^ 2 * A * (δ : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _ = 2 * (∑ j ∈ Finset.range (K + 1),
        ∫ v in (Blueprint5a.mesh δ j : ℝ)..(Blueprint5a.mesh δ (j + 1) : ℝ),
          (β * actualParisiFullSusceptibilityExpected W β v -
            LJ.residualCoarseA W β (Blueprint5a.mesh δ) K j) ^ 2) +
          (2 * β ^ 2 * A * δ) * ((K + 1 : ℕ) * (δ : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      ring
    _ ≤ 2 * (C * δ) + (2 * β ^ 2 * A * δ) * 8 :=
      add_le_add (by linarith) (mul_le_mul_of_nonneg_left hcount (by positivity))
    _ = _ := by ring

theorem query_squareBudget_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (hm : LagMesh β δ K) :
    squareBudget δ K l (queryCoefficient W β δ l) ≤
      (1 + 8 * (33 / 8 : ℝ) ^ 2 *
        Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)) * δ := by
  let C := (33 / 8 : ℝ) ^ 2 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)
  have hC : 0 ≤ C := by positivity
  have hδ := hm.1
  have hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1 :=
    fun j hj => hm.2.2.1 j (by omega)
  have haux : (∑ i ∈ Finset.range (2 ^ l), queryCoefficient W β δ l 0 i ^ 2 *
      ((refinedGrid δ l 0 (i + 1) : ℝ) - refinedGrid δ l 0 i)) ≤ δ := by
    calc
      _ ≤ ∑ i ∈ Finset.range (2 ^ l),
          ((refinedGrid δ l 0 (i + 1) : ℝ) - refinedGrid δ l 0 i) := by
        apply Finset.sum_le_sum
        intro i _
        have H := (actualParisiFullSusceptibilitySquareExpected_bounds W β (refinedGrid δ l 0 i)).2
        simpa only [queryCoefficient, LJ.residualCoarseB, ↓reduceIte, sub_zero,
          Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β _).1, one_mul] using
          mul_le_mul_of_nonneg_right H (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
            (LJ3.growingLagDyadicTime_monotone δ l 0 (Nat.le_succ i))))
      _ = δ := by rw [refinedGrid_duration_sum]; exact LQ.meshDuration_zero δ
  have hcell (j : ℕ) (hj : j < K) :
      (∑ i ∈ Finset.range (2 ^ l), queryCoefficient W β δ l (j + 1) i ^ 2 *
        ((refinedGrid δ l (j + 1) (i + 1) : ℝ) - refinedGrid δ l (j + 1) i)) ≤ C * (δ : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (2 ^ l), C * (δ : ℝ) ^ 2 *
          ((refinedGrid δ l (j + 1) (i + 1) : ℝ) - refinedGrid δ l (j + 1) i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hv := refinedGrid_mem δ l (j + 1) i (Finset.mem_range.mp hi).le
        exact mul_le_mul_of_nonneg_right
          (SJ7.growing_residualCoarseB_sq_le W β hβ δ hδ j (hsmall j (by omega))
            (show (refinedGrid δ l (j + 1) i : ℝ) ∈ Icc (growingQueryTime δ (j + 1) : ℝ)
              (growingQueryTime δ (j + 2) : ℝ) from ⟨by exact_mod_cast hv.1, by exact_mod_cast hv.2⟩))
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
            (LJ3.growingLagDyadicTime_monotone δ l (j + 1) (Nat.le_succ i))))
      _ = C * (δ : ℝ) ^ 2 * growingQueryDuration δ (j + 1) := by
        rw [← Finset.mul_sum, refinedGrid_duration_sum]
      _ ≤ C * (δ : ℝ) ^ 2 :=
        mul_le_of_le_one_right (by positivity) (by exact_mod_cast hsmall (j + 1) (by omega))
  have hcount := growingQuery_finite_count_bound δ hδ (K + 1) hsmall
  have hK : (K : ℝ) * δ ≤ 8 := by
    have H := mul_le_mul_of_nonneg_right (show (K : ℝ) ≤ (K + 1 : ℕ) by exact_mod_cast Nat.le_succ K) δ.coe_nonneg
    exact H.trans hcount
  change (∑ j ∈ Finset.range (K + 1), _) ≤ _
  rw [Finset.sum_range_succ']
  have H := Finset.sum_le_sum (s := Finset.range K) (fun j hj => hcell j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at H
  have H' := mul_le_mul_of_nonneg_left hK (show 0 ≤ C * δ by positivity)
  dsimp only [C] at *
  nlinarith only [H, H', haux]

end SKConstants.Completion.S745
