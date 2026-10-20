module

public import SKProof.OriginalQGateAssembly
public import SKProof.RegularBaseEq7

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal

namespace OriginalQLocalSharpReductionDraft

structure StoppingGateOnly {n : ℕ} {delta : ℝ}
    (a : ActualHighWallData n delta) (m cl cu : ℝ) : Prop where
  stopping : ∀ lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2),
    (n : ℝ)^(10*delta)*a.E < 2*lam →
    comparisonConditionalScale a.N delta a.E lam < 1 →
    StopsSelectedBadAtStrength a m cl cu lam

end OriginalQLocalSharpReductionDraft

open OriginalQLocalSharpReductionDraft

def ActualOriginalQStoppingInputs : Prop :=
  ∀ beta : ℝ, 1 < beta →
    ∀ m : ℝ, 0 < m → m < 1 / 300 →
      ∃ cl cu : ℝ, 0 < cl ∧ cl ≤ 1 ∧ 1 ≤ cu ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ hp : ActualConcreteHighWallNumeric m n,
          ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) (beta^2),
          ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
            StoppingGateOnly
              (actualConcreteHighWallData (beta^2) m n hp epsilon 0
                hepsilon heps0 (by norm_num)) m cl cu

theorem actualOriginalQStoppingRegularInputs_of_stopping :
    ActualOriginalQStoppingInputs → ActualOriginalQStoppingRegularInputs := by
  intro H beta hbeta m hm hmmax
  obtain ⟨cl, cu, hcl, hcl1, hcu1, Hstopping⟩ := H beta hbeta m hm hmmax
  have Hregular := RegularEq7.eventually_regularGate
    (C0 := 1) (D := 1) (Bclock := beta^2)
    hm hmmax hcl (lt_of_lt_of_le zero_lt_one hcu1) (by norm_num)
  refine ⟨cl, cu, hcl, hcl1, hcu1, ?_⟩
  apply (Hstopping.and Hregular).mono
  intro n hn hp epsilon hepsilon heps0
  let a := actualConcreteHighWallData (beta^2) m n hp epsilon 0
    hepsilon heps0 (by norm_num)
  have hstopping : StoppingGateOnly a m cl cu := hn.1 hp epsilon hepsilon heps0
  refine ⟨hstopping.stopping, ?_⟩
  apply hn.2 a rfl rfl rfl
  · exact hp.hd1
  · exact hp.hupper
  · simpa only [a, actualConcreteHighWallData, ActualHighWallData.N, one_mul]
      using hp.hlower
  · exact le_rfl

theorem main_fluctuation_statement_of_stopping :
    ActualOriginalQStoppingInputs → OAI.SKFluctuations.MainFluctuationStatement := by
  intro H
  exact main_fluctuation_statement_of_stopping_regular
    (actualOriginalQStoppingRegularInputs_of_stopping H)

end OAI.SKFluctuations.LaplaceWindowFormalization

