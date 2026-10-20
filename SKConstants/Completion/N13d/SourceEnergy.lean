module

public import SKConstants.Completion.N13d.LinearEnergy
public import SKConstants.Completion.N13d.SourceCompletion
public import SKConstants.Completion.LM5.WholeGramEnergy
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open NormedSpace InnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal

namespace SKConstants.Completion.N13d
open GaussianProposal LC5 LGram N13e LM5

theorem paperSpinCoefficients_eq_coordinates {Past : Type*}
    (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) :
    WithLp.toLp 2 (paperSpinCoefficients r K N target update a z x) =
      familyCoordinates (fun j => WithLp.toLp 2
        (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j))
        ((Real.sqrt N)⁻¹ • WithLp.toLp 2 x) := by
  have hroot : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hscalar : N⁻¹*Real.sqrt N = (Real.sqrt N)⁻¹ := by
    apply (mul_right_cancel₀ hroot)
    rw [mul_assoc, Real.mul_self_sqrt hN.le, inv_mul_cancel₀ hN.ne', inv_mul_cancel₀ hroot]
  ext j
  change N⁻¹*(x ⬝ᵥ paperQueryDirectionTrace r (r+K) N target update K (a,1) z j) =
    inner (𝕜 := ℝ) (WithLp.toLp 2
      (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j))
      ((Real.sqrt N)⁻¹ • WithLp.toLp 2 x)
  rw [LC5.paperQueryDirectionTrace_scale r (r+K) N target update K (a,1) z j,
    dotProduct_smul, real_inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, smul_eq_mul]
  change N⁻¹*(Real.sqrt N*(x ⬝ᵥ _)) = (Real.sqrt N)⁻¹*(x ⬝ᵥ _)
  rw [← mul_assoc, hscalar]

theorem actualPaper_query_energy_weighted_estimate {Past : Type*}
    (r K R m : ℕ) (hdim : K+m=2^R) (N ε : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (s b : EuclideanSpace ℝ (Fin K)) (H0 : Matrix (Fin K) (Fin K) ℝ) :
    let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j)
    let g := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (fun i => paperEndpointTrace (r+K) K z j (.inl i))
    let x0 := (Real.sqrt N)⁻¹ • WithLp.toLp 2 x
    let Q := sevenErrorSumDim R (K+m) hdim
      (padMatrix m (familyGram T-1) 0) (padMatrix m (familyCross T g-H0) 0)
      (padVector m s) (padVector m (familyCoordinates T x0-s))
      (padVector m b) (padVector m (familyCoordinates g x0-b))
    0 ≤ ε → 16*((R+1:ℕ):ℝ)^2*ε ≤ 1 → ‖familyGram T-1‖ ≤ ε →
    (∀ i j, i ≤ j → H0 i j = 0) → ‖familyCross T g-H0‖ ≤ ε →
    ‖WithLp.toLp 2 (paperSpinCoefficients r K N target update a z x)-s‖ ≤ 6*Real.sqrt Q ∧
      |paperQueryEnergy r (r+K) N target update K (a,1) z x-inner (𝕜 := ℝ) s b-
        energyLinearPart (familyGram T-1) (familyCross T g-H0)
          s (familyCoordinates T x0-s) b (familyCoordinates g x0-b)| ≤
        200*((R+1:ℕ):ℝ)*Q := by
  dsimp only
  intro hε hsmall hEA hH0 hEH
  let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
    (paperTargetTrace r (r+K) target update K (a,1) z j)
  let U := fun j => WithLp.toLp 2
    (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
  have hd : 1 ≤ ((R+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hGram : ‖familyGram T-1‖ ≤ (3/4:ℝ) := hEA.trans (by
    have hm := mul_le_mul_of_nonneg_right
      (show (1:ℝ) ≤ ((R+1:ℕ):ℝ)^2 by nlinarith) hε
    nlinarith)
  have hU : U = gramSchmidtNormed ℝ T := funext fun j =>
    actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z (Real.sqrt N)⁻¹
      (inv_pos.mpr (Real.sqrt_pos.mpr hN)) hGram j
  rw [paperSpinCoefficients_eq_coordinates r K N hN target update a z x,
    paperQueryEnergy_eq_projected r K N hN]
  change ‖familyCoordinates U _-s‖ ≤ _ ∧ |projectedQueryEnergy U _ _-_-_| ≤ _
  rw [hU]
  exact projectedQueryEnergy_weighted_estimate_padded R K m hdim ε T _ _ s b H0
    hε hsmall hEA hH0 hEH

open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def growingSevenErrorSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K R m : ℕ) (hdim : K+m=2^R)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : ℝ :=
  let T := growingSourceTargetFamily W β hβ δ r K u.2
  let g := growingSourceQueryFamily δ r K u.2
  let x := growingSourceSpinVector δ r K u
  let s := growingS W β hβ δ K
  let b := populationQuerySpin W W β hβ (growingQueryTime δ)
    (fun j => growingQueryTime δ (j+1)) K (growingQueryTime δ (K+1))
  let H0 := populationCross W W β hβ (growingQueryTime δ)
    (fun j => growingQueryTime δ (j+1)) K (growingQueryTime δ (K+1))
  sevenErrorSumDim R (K+m) hdim
    (padMatrix m (familyGram T-1) 0) (padMatrix m (familyCross T g-H0) 0)
    (padVector m s) (padVector m (familyCoordinates T x-s))
    (padVector m b) (padVector m (familyCoordinates g x-b))

theorem growingCoefficients_eq_source (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    growingCoefficients W β hβ δ r K (growingSourceCompact δ r K u).1 =
      WithLp.toLp 2 (paperSpinCoefficients r K (r+K:ℕ)
        (M1.Target W β hβ δ r K) (M1.Update δ r K) (M1.Initial δ r K u.2)
        (M1.Original δ r K u.2) (signSpin u.1)) := by
  apply congrArg (WithLp.toLp 2)
  exact (paperSpinCoefficients_factors_visible r K (r+K:ℕ)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingUpdate_blind δ r K)
    (M1.Initial δ r K u.2) (M1.Original δ r K u.2) (signSpin u.1)).symm

theorem growingSource_query_energy_weighted_estimate
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K R m : ℕ) (hdim : K+m=2^R) (hN : 0 < r+K) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hu : u ∈ sourceWholeGramEvent W β hβ δ r K ε) :
    ‖growingCoefficients W β hβ δ r K (growingSourceCompact δ r K u).1-
        growingS W β hβ δ K‖ ≤ 6*Real.sqrt (growingSevenErrorSum W β hβ δ r K R m hdim u) ∧
      |paperQueryEnergy r (r+K) (r+K:ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
          (M1.Initial δ r K u.2,1) (M1.Original δ r K u.2) (signSpin u.1) -
        inner (𝕜 := ℝ) (growingS W β hβ δ K)
          (populationQuerySpin W W β hβ (growingQueryTime δ)
            (fun j => growingQueryTime δ (j+1)) K (growingQueryTime δ (K+1))) -
        sourceEnergyLinearPart W β hβ δ r K u| ≤
        200*((R+1:ℕ):ℝ)*growingSevenErrorSum W β hβ δ r K R m hdim u := by
  have h := actualSource_good_blocks W β hβ δ hδ r K ε u hu
  rw [growingCoefficients_eq_source W β hβ δ r K u]
  exact actualPaper_query_energy_weighted_estimate r K R m hdim (r+K:ℕ) ε
    (Nat.cast_pos.mpr hN) (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (M1.Initial δ r K u.2) (M1.Original δ r K u.2) (signSpin u.1)
    (growingS W β hβ δ K) _ _ hε hsmall h.1
    (populationCross_shifted_upper W W β hβ _ (growingQueryTime_strictMono δ hδ).monotone K _)
    h.2.1

theorem sevenErrorSumDim_nonneg (R n : ℕ) (hdim : n=2^R)
    (EA EH : Matrix (Fin n) (Fin n) ℝ) (s eq b ev : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sevenErrorSumDim R n hdim EA EH s eq b ev := by
  subst n
  dsimp [sevenErrorSumDim, sevenErrorSum]
  positivity

theorem growingSevenErrorSum_nonneg (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K R m : ℕ) (hdim : K+m=2^R)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    0 ≤ growingSevenErrorSum W β hβ δ r K R m hdim u :=
  sevenErrorSumDim_nonneg R (K+m) hdim _ _ _ _ _ _

theorem growingSource_completionVariance_le_weighted
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K R m : ℕ) (hdim : K+m=2^R) (hN : 0 < r+K) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime δ K)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hu : u ∈ sourceWholeGramEvent W β hβ δ r K ε) :
    completionVariance (r+K:ℕ)
      (fun j => growingCoefficients W β hβ δ r K (growingSourceCompact δ r K u).1 j)
      (growingResidual W β hβ δ r K (growingSourceCompact δ r K u).1) ≤
      ((r+K:ℕ):ℝ)⁻¹ * (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)*(δ : ℝ) +
        180*growingSevenErrorSum W β hβ δ r K R m hdim u +
        (actualParisiFullSusceptibilityExpected W β (growingQueryTime δ K))^2) := by
  let Q := growingSevenErrorSum W β hβ δ r K R m hdim u
  have hQ : 0 ≤ Q := growingSevenErrorSum_nonneg W β hβ δ r K R m hdim u
  have hcoeff := (growingSource_query_energy_weighted_estimate W β hβ δ hδ
    r K R m hdim hN ε hε hsmall u hu).1
  have h := growingSource_completionVariance_sharp_le W β hβ δ hδ r K hN
    (6*Real.sqrt Q) (by positivity) hpost (growingSourceCompact δ r K u).1 hcoeff
  calc
    _ ≤ growingVarianceBudget W β δ r K (6*Real.sqrt Q) := h
    _ = _ := by
      unfold growingVarianceBudget
      rw [mul_pow, Real.sq_sqrt hQ]
      dsimp [Q]
      ring

theorem growingSource_gram_weighted_discarded_tail
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K R m : ℕ) (hdim : K+m=2^R) (hN : 0 < r+K) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime δ K)
    (B v : ℝ) (hB : 0 ≤ B) (hv : 0 < v) :
    (M1.SourceLinkedLaw W β hβ δ r K).real {u |
      u ∈ sourceWholeGramEvent W β hβ δ r K ε ∧
      growingSevenErrorSum W β hβ δ r K R m hdim u ≤ B^2 ∧
      v ≤ |growingSourceDiscardedEnergy W β hβ δ r K u|} ≤
      2*Real.exp (-v^2/(2*growingVarianceBudget W β δ r K (6*B))) := by
  have hsub : {u | u ∈ sourceWholeGramEvent W β hβ δ r K ε ∧
      growingSevenErrorSum W β hβ δ r K R m hdim u ≤ B^2 ∧
      v ≤ |growingSourceDiscardedEnergy W β hβ δ r K u|} ⊆
      {u | (growingSourceCompact δ r K u).1 ∈ growingCoefficientEvent W β hβ δ r K (6*B) ∧
        v ≤ |growingSourceDiscardedEnergy W β hβ δ r K u|} := by
    intro u hu
    refine ⟨?_, hu.2.2⟩
    exact (growingSource_query_energy_weighted_estimate W β hβ δ hδ
      r K R m hdim hN ε hε hsmall u hu.1).1.trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hB,hu.2.1⟩) (by norm_num))
  exact (measureReal_mono hsub).trans
    (growingSourceDiscardedEnergy_tail_on W β hβ δ hδ r K hN (6*B)
      (by positivity) hpost v hv)

end SKConstants.Completion.N13d
