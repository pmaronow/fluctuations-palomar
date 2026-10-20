module

public import SKConstants.Completion.NL1.Coefficients
public import SKConstants.Completion.NL1.GaussianMGF
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal Topology

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 LC5 LGram N13A LM5

theorem sharpLinearEnergy_deterministic_holds
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hc : CoarseExponents4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ y : SharpInput p n, sharpRows W β hβ p n y ∈ gramGood W β hβ p n →
        |sharpQueryEnergy W β hβ p n y - linearEnergy W β hβ (sharpRows W β hβ p n y)| ≤
          200 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ) *
            weightedSq W β hβ (sharpRows W β hβ p n y) ∧
        discardedVariance (sharpRows W β hβ p n y) ≤
          C / n * ((n : ℝ)^(-p.a) + weightedSq W β hβ (sharpRows W β hβ p n y) +
            (n : ℝ)^(-p.b)) := by
  let A := Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)
  let B := (LBase.terminalTailConstant β)^2 * Real.exp 1
  let C := A + 180 + B
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha1 : p.a < 1 := by
    have hfp : 0 < p.f := lt_trans hc.1 hc.2.1
    linarith [hf.2.1]
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  filter_upwards [N13d.coarse_previous_time_eventually β p.a p.b hc.1 hc.2.2.1.le ha1,
    N13d.coarse_previous_susceptibility_square_eventually W β hβ p.a p.b
      hc.1 hc.2.2.1.le ha1] with n hn hp
  intro y hy
  have he := sharpEnergy_and_variance W β hβ p n (by omega) hn.2.1 y hy
  refine ⟨he.1, he.2.trans ?_⟩
  have hQ := weightedSq_nonneg W β hβ (sharpRows W β hβ p n y)
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmesh : (coarseMesh p n : ℝ) = (n : ℝ)^(-p.a) := paperGrowingQueryMeshSize_coe p.a n
  rw [hmesh]
  have hsum : A * (n : ℝ)^(-p.a) + 180 * weightedSq W β hβ (sharpRows W β hβ p n y) +
      (actualParisiFullSusceptibilityExpected W β
        (growingQueryTime (coarseMesh p n) (coarseCount p n)))^2 ≤
      C * ((n : ℝ)^(-p.a) + weightedSq W β hβ (sharpRows W β hβ p n y) + (n : ℝ)^(-p.b)) := by
    calc
      _ ≤ A * (n : ℝ)^(-p.a) + 180 * weightedSq W β hβ (sharpRows W β hβ p n y) +
          B * (n : ℝ)^(-p.b) := by
        have hp' : (actualParisiFullSusceptibilityExpected W β
            (growingQueryTime (coarseMesh p n) (coarseCount p n)))^2 ≤ B * (n : ℝ)^(-p.b) := hp
        linarith
      _ ≤ _ := by
        dsimp only [C]
        nlinarith [Real.rpow_pos_of_pos hN (-p.a), Real.rpow_pos_of_pos hN (-p.b),
          mul_nonneg hA.le hQ, mul_nonneg hB hQ,
          mul_nonneg hB (Real.rpow_pos_of_pos hN (-p.a)).le,
          mul_nonneg hA.le (Real.rpow_pos_of_pos hN (-p.b)).le]
  calc
    _ ≤ (n : ℝ)⁻¹ * (C * ((n : ℝ)^(-p.a) +
        weightedSq W β hβ (sharpRows W β hβ p n y) + (n : ℝ)^(-p.b))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem sharpLinearEnergy_holds : N13A.SharpLinearEnergyStatement := by
  intro Ω _ W β hβ p hf hc
  obtain ⟨C, hC, he⟩ := sharpLinearEnergy_deterministic_holds W β hβ p hf hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  exact ⟨hn, fun S hS hSG θ => sharpDiscarded_mgf_on_rows W β hβ p n hn0 S hS hSG θ⟩

end SKConstants.Completion.NL1
