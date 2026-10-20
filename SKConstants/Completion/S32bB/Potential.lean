module

public import SKConstants.Completion.S32bB.Discrete

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace SKConstants.Completion.S32bB
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic ParisiFullSupport

variable {Ω : Type*} [MeasurableSpace Ω]

theorem physicalPotential_third_bound (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ C : ℝ≥0, ∀ v x, |iteratedDeriv 3 (physicalCDFPotential β α T v) x| ≤ C := by
  obtain ⟨C, hC⟩ := (compactCDFGradient_family β α ha h1 hβ hT0 hT1).bounds 2
  refine ⟨C, fun v x => ?_⟩
  change |iteratedDeriv (2 + 1) (compactCDFValue β α T (v / β ^ 2)) x| ≤ C
  rw [iteratedDeriv_succ', compactCDFValue_deriv_eq β α ha hT0]
  exact hC _ x

theorem physicalPotential_spatialTaylor_tendsto_L2 (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (V : ℝ≥0) :
    (∀ l, Integrable (fun w =>
      spatialTaylorSum W b (physicalCDFPotential β α T) V l w ^ 2) W.law) ∧
    Tendsto (fun l => ∫ w,
      spatialTaylorSum W b (physicalCDFPotential β α T) V l w ^ 2 ∂W.law) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := physicalPotential_third_bound β α ha h1 hβ hT0 hT1
  have hF (v : ℝ) : ContDiff ℝ 3 (physicalCDFPotential β α T v) :=
    (compactCDFValue_smooth β α ha hβ hT0 hT1 (v / β ^ 2)).of_le (by simp)
  exact ⟨fun l => (spatialTaylorSum_memLp W b _ hF C hC V l).integrable_sq,
    spatialTaylorSum_tendsto_L2 W b _ hF C hC V⟩

theorem physicalPotential_discrete_telescope (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT1 : T < 1) (V : ℝ≥0) (hV : (V : ℝ) ≤ β ^ 2 * T) (l : ℕ) (w : Ω) :
    physicalCDFPotential β α T V (b.solution W.driver V w) -
        physicalCDFPotential β α T 0 (b.solution W.driver 0 w) =
      (∑ k ∈ Finset.range (2 ^ l),
        let s := (brownianDyadicGrid V).time l k
        let t := (brownianDyadicGrid V).time l (k + 1)
        deriv (physicalCDFPotential β α T s) (b.solution W.driver s w) *
          (b.solution W.driver t w - b.solution W.driver s w)) +
      (1 / 2 : ℝ) * (∑ k ∈ Finset.range (2 ^ l),
        let s := (brownianDyadicGrid V).time l k
        let t := (brownianDyadicGrid V).time l (k + 1)
        deriv (deriv (physicalCDFPotential β α T s)) (b.solution W.driver s w) *
          (b.solution W.driver t w - b.solution W.driver s w) ^ 2) +
      spatialTaylorSum W b (physicalCDFPotential β α T) V l w +
      (∑ k ∈ Finset.range (2 ^ l),
        ∫ r in ((brownianDyadicGrid V).time l k : ℝ)..
          ((brownianDyadicGrid V).time l (k + 1) : ℝ),
          physicalCDFPotentialRate β α T r
            (b.solution W.driver ((brownianDyadicGrid V).time l (k + 1)) w)) := by
  let a := (brownianDyadicGrid V).time l
  let Y := fun k => b.solution W.driver (a k) w
  let F := physicalCDFPotential β α T
  have hstep (k : ℕ) (hk : k < 2 ^ l) :
      F (a (k + 1)) (Y (k + 1)) - F (a k) (Y (k + 1)) =
        ∫ r in (a k : ℝ)..(a (k + 1) : ℝ),
          physicalCDFPotentialRate β α T r (Y (k + 1)) := by
    apply physicalCDFPotential_integral_rate β α ha h1 hβ hT1
      (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l (Nat.le_succ k)))
    exact (NNReal.coe_le_coe.mpr (LM3.dyadic_time_le_horizon V l (k + 1) (by omega))).trans hV
  have htel := Finset.sum_range_sub (fun k => F (a k) (Y k)) (2 ^ l)
  have htotal :
      (∑ k ∈ Finset.range (2 ^ l),
        (F (a (k + 1)) (Y (k + 1)) - F (a k) (Y k))) =
        (∑ k ∈ Finset.range (2 ^ l), deriv (F (a k)) (Y k) * (Y (k + 1) - Y k)) +
        (1 / 2 : ℝ) * (∑ k ∈ Finset.range (2 ^ l),
          deriv (deriv (F (a k))) (Y k) * (Y (k + 1) - Y k) ^ 2) +
        spatialTaylorSum W b F V l w +
        (∑ k ∈ Finset.range (2 ^ l), ∫ r in (a k : ℝ)..(a (k + 1) : ℝ),
          physicalCDFPotentialRate β α T r (Y (k + 1))) := by
    simp only [spatialTaylorSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := hstep k (Finset.mem_range.mp hk)
    dsimp only [Y, a] at *
    rw [← hh]
    rw [show b.solution W.driver ((brownianDyadicGrid V).time l k) w +
        (b.solution W.driver ((brownianDyadicGrid V).time l (k + 1)) w -
          b.solution W.driver ((brownianDyadicGrid V).time l k) w) =
        b.solution W.driver ((brownianDyadicGrid V).time l (k + 1)) w by ring]
    ring
  rw [htel] at htotal
  simpa only [a, Y, F, dyadic_end, (brownianDyadicGrid V).zero l, NNReal.coe_zero] using htotal

end SKConstants.Completion.S32bB
