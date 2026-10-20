module

public import SKConstants.Completion.LGram.IIDEvent
public import SKConstants.Completion.LGram.PopulationNorms
public import SKConstants.Completion.LGram.SevenErrors
public import SKConstants.Completion.LC0.SourceReplay
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def paperRows {Past : Type*} (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (l : Fin (r+K)) : EuclideanSpace ℝ (Fin (K+(K+1))) :=
  WithLp.toLp 2 (Fin.append (fun j => paperTargetTrace r (r+K) target update K (a,1) z j l)
    (Fin.append (fun j => paperEndpointTrace (r+K) K z j (.inl l)) (fun _ : Fin 1 => x l)))

theorem paperRows_good_blocks {Past : Type*} (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (P : Matrix (Fin (K+(K+1))) (Fin (K+(K+1))) ℝ)
    (hP : P.submatrix (posteriorIndex K) (posteriorIndex K) = 1) (η : ℝ)
    (hz : paperRows r K target update a z x ∈ rowGramEvent P (r+K) η) :
    let N : ℝ := (r+K:ℕ)
    let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (a,1) z j)
    let G := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2 (fun l => paperEndpointTrace (r+K) K z j (.inl l))
    let x0 := (Real.sqrt N)⁻¹ • WithLp.toLp 2 x
    ‖familyGram T-1‖ ≤ η ∧
      ‖familyCross T G-P.submatrix (posteriorIndex K) (queryIndex K)‖ ≤ η ∧
      ‖familyCoordinates T x0-WithLp.toLp 2 (fun i => P (posteriorIndex K i) (spinIndex K))‖ ≤ η ∧
      ‖familyCoordinates G x0-WithLp.toLp 2 (fun i => P (queryIndex K i) (spinIndex K))‖ ≤ η := by
  have h := rowGramEvent_blocks P _ _ (posteriorIndex_injective K) (queryIndex_injective K)
    (spinIndex K) _ η hz hP
  simpa only [sampleColumn, paperRows, posteriorIndex, queryIndex, spinIndex,
    Fin.append_left, Fin.append_right] using h

variable {Ω : Type*} [MeasurableSpace Ω]

def literalSourceRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    Fin (r+K) → EuclideanSpace ℝ (Fin (K+(K+1))) :=
  paperRows r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (M1.Initial δ r K u.2) (M1.Original δ r K u.2) (fun i => scalarHiddenSign (u.1 i))

def SourceMixedRowsLawStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Prop :=
  HasLaw (literalSourceRows W β hβ δ r K)
    (mixedVectorRowsLaw W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
      K (growingQueryTime δ (K+1)) (r+K))
    (M1.SourceLinkedLaw W β hβ δ r K)

def sourceWholeGramEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (η : ℝ) : Set ((Fin (r+K) → Bool) × M1.SourceInput δ r K) :=
  (literalSourceRows W β hβ δ r K) ⁻¹'
    rowGramEvent (mixedPopulation W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))) (r+K) η

theorem actualSource_wholeGram_compl_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hN : 0 < r+K) (η : ℝ) (hη : 0 < η)
    (hrow : SourceMixedRowsLawStatement W β hβ δ r K) :
    (M1.SourceLinkedLaw W β hβ δ r K).real (sourceWholeGramEvent W β hβ δ r K η)ᶜ ≤
      gramTailBudget (r+K) (K+(K+1)) (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ K)) η := by
  have he := hrow.measureReal_eq
    (measurableSet_rowGramEvent (mixedPopulation W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))) (r+K) η).compl
  change (M1.SourceLinkedLaw W β hβ δ r K).real (sourceWholeGramEvent W β hβ δ r K η)ᶜ = _ at he
  rw [he]
  exact growingMixedRows_wholeGram_compl_le W W β hβ δ hδ K hN η hη

theorem actualSource_good_blocks (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (η : ℝ)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hu : u ∈ sourceWholeGramEvent W β hβ δ r K η) :
    let a := M1.Initial δ r K u.2
    let z := M1.Original δ r K u.2
    let target := M1.Target W β hβ δ r K
    let update := M1.Update δ r K
    let N : ℝ := (r+K:ℕ)
    let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2 (paperTargetTrace r (r+K) target update K (a,1) z j)
    let G := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2 (fun l => paperEndpointTrace (r+K) K z j (.inl l))
    let x0 := (Real.sqrt N)⁻¹ • WithLp.toLp 2 (fun i => scalarHiddenSign (u.1 i))
    ‖familyGram T-1‖ ≤ η ∧
      ‖familyCross T G-populationCross W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))‖ ≤ η ∧
      ‖familyCoordinates T x0-populationTargetSpin W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))‖ ≤ η ∧
      ‖familyCoordinates G x0-populationQuerySpin W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))‖ ≤ η :=
  paperRows_good_blocks r K _ _ _ _ _ _
    (mixedPopulation_target_block W W β hβ _ (growingQueryTime_strictMono δ hδ) _ _ _) η hu

theorem actualSource_query_energy_operator_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K R m : ℕ) (hdim : K+m=2^R)
    (hN : 0 < r+K) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : 16 * ((R+1:ℕ):ℝ)^2 * η ≤ 1)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hu : u ∈ sourceWholeGramEvent W β hβ δ r K η) :
    |paperQueryEnergy r (r+K) (r+K:ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (M1.Initial δ r K u.2,1) (M1.Original δ r K u.2) (fun i => scalarHiddenSign (u.1 i)) -
      inner (𝕜 := ℝ)
        (populationTargetSpin W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
          K (growingQueryTime δ (K+1)))
        (populationQuerySpin W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
          K (growingQueryTime δ (K+1)))| ≤ queryError R η := by
  have h := actualSource_good_blocks W β hβ δ hδ r K η u hu
  exact LC5.actualPaper_query_energy_operator_error r K R m hdim (r+K:ℕ) η
    (Nat.cast_pos.mpr hN) _ _ _ _ _ _ _ _ hη hsmall h.1
    (populationCross_shifted_upper W W β hβ _ (growingQueryTime_strictMono δ hδ).monotone K _)
    h.2.1 h.2.2.1 h.2.2.2
    (populationTargetSpin_norm_le_one W W β hβ _ (growingQueryTime_strictMono δ hδ) _ K _)
    (populationQuerySpin_norm_le_one W W β hβ _ _
      ((growingQueryTime_strictMono δ hδ).comp (fun _ _ h => Nat.add_lt_add_right h 1)) K _)

theorem actualSource_sevenErrorSum_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K R m : ℕ) (hdim : K+m=2^R)
    (η : ℝ) (hη : 0 ≤ η)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hu : u ∈ sourceWholeGramEvent W β hβ δ r K η) :
    let N : ℝ := (r+K:ℕ)
    let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (M1.Initial δ r K u.2,1) (M1.Original δ r K u.2) j)
    let G := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (fun l => paperEndpointTrace (r+K) K (M1.Original δ r K u.2) j (.inl l))
    let x := (Real.sqrt N)⁻¹ • WithLp.toLp 2 (fun i => scalarHiddenSign (u.1 i))
    let s := populationTargetSpin W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
      K (growingQueryTime δ (K+1))
    let b := populationQuerySpin W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
      K (growingQueryTime δ (K+1))
    let H0 := populationCross W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
      K (growingQueryTime δ (K+1))
    sevenErrorSumDim R (K+m) hdim (padMatrix m (familyGram T-1) 0)
      (padMatrix m (familyCross T G-H0) 0) (padVector m s)
      (padVector m (familyCoordinates T x-s)) (padVector m b)
      (padVector m (familyCoordinates G x-b)) ≤ 7*((R+1:ℕ):ℝ)^3*η^2 := by
  have h := actualSource_good_blocks W β hβ δ hδ r K η u hu
  exact sevenErrorSum_padded_le_of_operator_errors R K m hdim η _ _ _ _ _ _ hη
    h.1 h.2.1 h.2.2.1 h.2.2.2
    (populationTargetSpin_norm_le_one W W β hβ _ (growingQueryTime_strictMono δ hδ) _ K _)
    (populationQuerySpin_norm_le_one W W β hβ _ _
      ((growingQueryTime_strictMono δ hδ).comp (fun _ _ h => Nat.add_lt_add_right h 1)) K _)

end SKConstants.Completion.LGram
