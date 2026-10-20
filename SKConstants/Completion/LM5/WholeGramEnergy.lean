module

public import SKConstants.Completion.LM5.GrowingLinkedEnergy
public import SKConstants.Completion.LC1.UpperBlock
public import SKConstants.ParisiFullMixedRows
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
open scoped BigOperators Matrix Matrix.Norms.L2Operator RealInnerProductSpace NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def growingPopulationTargetQuery (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => ∫ u, actualParisiNormalizedPosteriorRow W β (growingQueryTime δ) K u.1.2 i *
    scalarNormalizedBrownianRow (d := K) (actualParisiQueryBrownianSystem W Z β hβ).B
      (fun k => growingQueryTime δ (k+1)) (u.1.2,u.2) j
    ∂actualParisiFullQuerySpinLaw W Z β (M1.Horizon δ K)

def growingPopulationTargetSpin (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (δ : ℝ≥0) (K : ℕ) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (fun i => ∫ u, actualParisiNormalizedPosteriorRow W β (growingQueryTime δ) K u.1.2 i *
    scalarHiddenSign u.1.1 ∂actualParisiFullQuerySpinLaw W Z β (M1.Horizon δ K))

def growingPopulationQuerySpin (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (fun j => ∫ u,
    scalarNormalizedBrownianRow (d := K) (actualParisiQueryBrownianSystem W Z β hβ).B
      (fun k => growingQueryTime δ (k+1)) (u.1.2,u.2) j * scalarHiddenSign u.1.1
    ∂actualParisiFullQuerySpinLaw W Z β (M1.Horizon δ K))

theorem growingPopulationTargetQuery_strictLower (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) :
    ∀ i j : Fin K, i ≤ j → growingPopulationTargetQuery W Z β hβ δ K i j = 0 :=
  LC1.actualQuerySpinLaw_shifted_upper_block W Z β hβ (growingQueryTime δ)
    (growingQueryTime_strictMono δ hδ).monotone K (M1.Horizon δ K)

def growingSourceTargetFamily (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (z : M1.SourceInput δ r K) : Fin K → EuclideanSpace ℝ (Fin (r+K)) :=
  fun j => (Real.sqrt (r+K : ℕ))⁻¹ • WithLp.toLp 2
    (paperTargetTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
      (growingInitial δ r K z.1,1) (M1.Original δ r K z) j)

def growingSourceQueryFamily (δ : ℝ≥0) (r K : ℕ) (z : M1.SourceInput δ r K) :
    Fin K → EuclideanSpace ℝ (Fin (r+K)) :=
  fun j => (Real.sqrt (r+K : ℕ))⁻¹ • WithLp.toLp 2
    (fun i => paperEndpointTrace (r+K) K (M1.Original δ r K z) j (.inl i))

def growingSourceSpinVector (δ : ℝ≥0) (r K : ℕ)
    (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : EuclideanSpace ℝ (Fin (r+K)) :=
  (Real.sqrt (r+K : ℕ))⁻¹ • WithLp.toLp 2 (signSpin z.1)

def growingSourceWholeRow (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (i : Fin (r+K)) : Fin (K+(K+1)) → ℝ :=
  Fin.append
    (fun j => paperTargetTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
      (growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) j i)
    (Fin.append (fun j => paperEndpointTrace (r+K) K (M1.Original δ r K z.2) j (.inl i))
      (fun _ : Fin 1 => signSpin z.1 i))

def growingPopulationWholeGram (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) :
    Matrix (Fin (K+(K+1))) (Fin (K+(K+1))) ℝ :=
  fun i j => ∫ u, actualParisiFullMixedRow W Z β hβ (growingQueryTime δ)
    (fun k => growingQueryTime δ (k+1)) K u i *
    actualParisiFullMixedRow W Z β hβ (growingQueryTime δ)
      (fun k => growingQueryTime δ (k+1)) K u j
    ∂actualParisiFullQuerySpinLaw W Z β (M1.Horizon δ K)

def growingSourceWholeGramError (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ)
    (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    Matrix (Fin (K+(K+1))) (Fin (K+(K+1))) ℝ :=
  Matrix.of (fun j k => ((r+K : ℕ) : ℝ)⁻¹ * ∑ i,
    growingSourceWholeRow W β hβ δ r K z i j * growingSourceWholeRow W β hβ δ r K z i k) -
      growingPopulationWholeGram W Z β hβ δ K

def growingSourceWholeGramEvent (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (η : ℝ) :
    Set ((Fin (r+K) → Bool) × M1.SourceInput δ r K) :=
  {z | ‖growingSourceWholeGramError W Z β hβ δ r K z‖ ≤ η}

def GrowingWholeGramEnergyInputsStatement (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (η : ℝ) : Prop :=
  ∀ z ∈ growingSourceWholeGramEvent W Z β hβ δ r K η,
    ‖familyGram (growingSourceTargetFamily W β hβ δ r K z.2)-1‖ ≤ η ∧
    ‖familyCross (growingSourceTargetFamily W β hβ δ r K z.2)
      (growingSourceQueryFamily δ r K z.2)-growingPopulationTargetQuery W Z β hβ δ K‖ ≤ η ∧
    ‖familyCoordinates (growingSourceTargetFamily W β hβ δ r K z.2)
      (growingSourceSpinVector δ r K z)-growingPopulationTargetSpin W Z β δ K‖ ≤ η ∧
    ‖familyCoordinates (growingSourceQueryFamily δ r K z.2)
      (growingSourceSpinVector δ r K z)-growingPopulationQuerySpin W Z β hβ δ K‖ ≤ η ∧
    ‖growingPopulationTargetSpin W Z β δ K‖ ≤ 1 ∧
    ‖growingPopulationQuerySpin W Z β hβ δ K‖ ≤ 1

theorem growingSource_query_energy_on_wholeGram (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K R m : ℕ) (hN : 0 < r+K) (hdim : K+m=2^R) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : 16*((R+1 : ℕ) : ℝ)^2*η ≤ 1)
    (hGram : GrowingWholeGramEnergyInputsStatement W Z β hβ δ r K η)
    (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hz : z ∈ growingSourceWholeGramEvent W Z β hβ δ r K η) :
    |paperQueryEnergy r (r+K) (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
      (growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) (signSpin z.1) -
      inner (𝕜 := ℝ) (growingPopulationTargetSpin W Z β δ K)
        (growingPopulationQuerySpin W Z β hβ δ K)| ≤ queryError R η := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  obtain ⟨hEA,hEH,heq,hev,hs,hb⟩ := hGram z hz
  exact actualPaper_query_energy_operator_error r K R m hdim (r+K : ℕ) η hp
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K z.2.1)
    (M1.Original δ r K z.2) (signSpin z.1)
    (growingPopulationTargetSpin W Z β δ K) (growingPopulationQuerySpin W Z β hβ δ K)
    (growingPopulationTargetQuery W Z β hβ δ K) hη hsmall hEA
    (growingPopulationTargetQuery_strictLower W Z β hβ δ hδ K) hEH heq hev hs hb

end SKConstants.Completion.LM5
