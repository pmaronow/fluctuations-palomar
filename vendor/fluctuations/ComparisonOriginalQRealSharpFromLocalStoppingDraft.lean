module

public import ComparisonOriginalQPointwiseSharpFromLocalStoppingDraft
public import ComparisonFinalWallFromOriginalQSharpDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy OriginalQLocalSharpReductionDraft PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

def ActualOriginalQLocalStoppingInputs : Prop :=
  ∀ beta : ℝ, 1 < beta →
    ∀ m : ℝ, 0 < m → m < 1 / 300 →
      ∃ cl cu : ℝ, 0 < cl ∧ cl ≤ 1 ∧ 1 ≤ cu ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ hp : ActualConcreteHighWallNumeric m n,
          ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) (beta^2),
          ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
            LocalStoppingGates
              (actualConcreteHighWallData (beta^2) m n hp epsilon 0
                hepsilon heps0 (by norm_num)) m cl cu

theorem actual_remaining_original_q_sharp_of_local_stopping_inputs
    (Hlocal : ActualOriginalQLocalStoppingInputs) :
    ActualRemainingOriginalQSharpCost := by
  intro beta hbeta m hm hmmax
  obtain ⟨cl,cu,hcl,hcl1,hcu1,H⟩ := Hlocal beta hbeta m hm hmmax
  filter_upwards [eventually_concrete_sharp_of_all_original_density
    (T := beta^2) hm,H] with n hnSharp hnLocal
  intro hp epsilon hepsilon heps0
  let a := actualConcreteHighWallData (beta^2) m n hp epsilon 0
    hepsilon heps0 (by norm_num)
  apply hnSharp hp epsilon hepsilon heps0
  apply all_original_density_of_local_stopping_gates a
    (show 0 ≤ m/10000 by positivity) hcl1 hcu1
  · intro lam hlam
    exact (concrete_original_q_selected_origin_gates hm
      (by have hn := hp.hn; omega) a rfl rfl rfl
      ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).1
  · intro lam hlam
    exact (concrete_original_q_selected_origin_gates hm
      (by have hn := hp.hn; omega) a rfl rfl rfl
      ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).2
  · simpa only [a,actualConcreteHighWallData,ActualHighWallData.N] using hp.hupper
  · simpa only [a,actualConcreteHighWallData,ActualHighWallData.N] using hp.hlower
  · exact hnLocal hp epsilon hepsilon heps0

theorem main_fluctuation_statement_of_original_q_local_stopping_inputs
    (Hlocal : ActualOriginalQLocalStoppingInputs) :
    MainFluctuationStatement := by
  exact main_fluctuation_statement_of_original_q_sharp_cost
    (actual_remaining_original_q_sharp_of_local_stopping_inputs Hlocal)

end OAI.SKFluctuations.LaplaceWindowFormalization
