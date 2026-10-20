module

public import SKConstants.Completion.LGram.Population
public import SKConstants.Completion.LQ.GrowingMeshGeometry
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK LC5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {N : ℕ}

def mixedRowsArray (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t g : ℕ → ℝ≥0) (k : ℕ) (w : Fin N → (Bool × Ω) × A) :
    Fin N → EuclideanSpace ℝ (Fin (k+(k+1))) :=
  fun i => actualParisiFullMixedRows W Z β hβ t g k i w

theorem measurable_mixedRowsArray (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t g : ℕ → ℝ≥0) (k : ℕ) :
    Measurable (mixedRowsArray (N:=N) W Z β hβ t g k) :=
  Measurable.of_eval (fun i => measurable_actualParisiFullMixedRows W Z β hβ t g k i)

def mixedVectorRowsLaw (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) (N : ℕ) :=
  (actualParisiFullMixedRowsLaw W Z β H N).map (mixedRowsArray W Z β hβ t g k)

theorem mixedRows_centeredCovariance_eq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0)
    (hN : 0 < N) (w : Fin N → (Bool × Ω) × A) :
    Concentration.centeredEmpiricalCovariance (actualParisiFullMixedRowsLaw W Z β H N)
      (actualParisiFullMixedRows W Z β hβ t g k) w =
    empiricalGram (mixedRowsArray W Z β hβ t g k w)-mixedPopulation W Z β hβ t g k H := by
  apply centeredEmpiricalCovariance_eq_empirical_sub_population _ _ _ hN
  intro l i j
  have hm : Measurable (fun u => actualParisiFullMixedRow W Z β hβ t g k u i *
      actualParisiFullMixedRow W Z β hβ t g k u j) := by
    exact ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp
      (measurable_actualParisiFullMixedRow W Z β hβ t g k))).mul
      ((measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp
        (measurable_actualParisiFullMixedRow W Z β hβ t g k)))
  exact (measurePreserving_eval (fun _ : Fin N => actualParisiFullQuerySpinLaw W Z β H) l).hasLaw.integral_comp
    hm.aestronglyMeasurable

theorem mixedRows_rowGramEvent_compl_le (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0)
    (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (actualParisiFullMixedRowsLaw W Z β H N).real
      {w | mixedRowsArray W Z β hβ t g k w ∉ rowGramEvent (mixedPopulation W Z β hβ t g k H) N η} ≤
      gramTailBudget N (k+(k+1)) (actualParisiFullMixedRowMGFProxy W β (t k)) η := by
  have h := mixedRows_wholeGramEvent_compl_le W Z β hβ t ht k g hg H hN η hη
  simpa only [wholeGramEvent, rowGramEvent,
    mixedRows_centeredCovariance_eq W Z β hβ t g k H hN, Set.compl_ofPred,
    Set.mem_ofPred_eq] using h

theorem mixedVectorRows_rowGramEvent_compl_le (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0)
    (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (mixedVectorRowsLaw W Z β hβ t g k H N).real
      (rowGramEvent (mixedPopulation W Z β hβ t g k H) N η)ᶜ ≤
      gramTailBudget N (k+(k+1)) (actualParisiFullMixedRowMGFProxy W β (t k)) η := by
  rw [mixedVectorRowsLaw, map_measureReal_apply
    (measurable_mixedRowsArray W Z β hβ t g k) (measurableSet_rowGramEvent _ _ _).compl]
  exact mixedRows_rowGramEvent_compl_le W Z β hβ t ht k g hg H hN η hη

theorem mixedRows_good_blocks (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0)
    (w : Fin N → (Bool × Ω) × A) (η : ℝ)
    (hw : mixedRowsArray W Z β hβ t g k w ∈ rowGramEvent (mixedPopulation W Z β hβ t g k H) N η) :
    let z := mixedRowsArray W Z β hβ t g k w
    let T := fun i => sampleColumn z (posteriorIndex k i)
    let G := fun i => sampleColumn z (queryIndex k i)
    let x := sampleColumn z (spinIndex k)
    ‖familyGram T-1‖ ≤ η ∧ ‖familyCross T G-populationCross W Z β hβ t g k H‖ ≤ η ∧
      ‖familyCoordinates T x-populationTargetSpin W Z β hβ t g k H‖ ≤ η ∧
      ‖familyCoordinates G x-populationQuerySpin W Z β hβ t g k H‖ ≤ η :=
  rowGramEvent_blocks _ _ _ (posteriorIndex_injective k) (queryIndex_injective k) _ _ _ hw
    (mixedPopulation_target_block W Z β hβ t ht g k H)

theorem growingMixedRows_wholeGram_compl_le (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (mixedVectorRowsLaw W Z β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
      k (growingQueryTime δ (k+1)) N).real
      (rowGramEvent (mixedPopulation W Z β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) k (growingQueryTime δ (k+1))) N η)ᶜ ≤
      gramTailBudget N (k+(k+1)) (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ k)) η :=
  mixedVectorRows_rowGramEvent_compl_le W Z β hβ _ (growingQueryTime_strictMono δ hδ) k _
    ((growingQueryTime_strictMono δ hδ).comp (fun _ _ h => Nat.add_lt_add_right h 1)) _ hN η hη

end SKConstants.Completion.LGram
