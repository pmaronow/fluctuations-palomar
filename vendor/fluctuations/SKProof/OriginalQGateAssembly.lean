module

public import ComparisonOriginalQRealSharpFromLocalStoppingDraft
public import SKProof.MacroInnerFamilyProbe

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal

namespace OriginalQLocalSharpReductionDraft

theorem eventually_macroGate_of_eq3 {m delta C0 D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ActualHighWallData n delta,
      a.d ≤ D → Real.sqrt a.N*a.E ≤ a.d^2 →
      a.N^(-(2 : ℝ)/3+m)*a.d ≤ C0*a.E → a.T ≤ Bclock →
      ∀ (lam : ℝ) (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2)),
        (n : ℝ)^(10*delta)*a.E < 2*lam →
        1 ≤ comparisonConditionalScale a.N delta a.E lam →
        ∀ alpha : a.Profile, GlobalSweepMinimum a lam hlam alpha →
          a.thetaZeroOriginalSweepDensity lam alpha ≤ (n : ℝ)^(10*delta)*a.E := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (MacroInnerFamilyProbe.eventually_macro_gate_producer
      (D := D) (Bclock := Bclock) hm hdelta hroom hC0)
  filter_upwards [eventually_ge_atTop (N+1)] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  simpa only [ActualHighWallData.N, GlobalSweepMinimum] using hN k (by omega)

structure StoppingRegularGates {n : ℕ} {delta : ℝ}
    (a : ActualHighWallData n delta) (m cl cu : ℝ) : Prop where
  stopping : ∀ lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2),
    (n : ℝ)^(10*delta)*a.E < 2*lam →
    comparisonConditionalScale a.N delta a.E lam < 1 →
    StopsSelectedBadAtStrength a m cl cu lam
  regular : ∀ (lam : ℝ)
    (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2)),
    (n : ℝ)^(10*delta)*a.E < 2*lam →
    comparisonConditionalScale a.N delta a.E lam < 1 →
    ∀ alpha : a.Profile, GlobalSweepMinimum a lam hlam alpha →
    BaseRegular a cl cu lam alpha →
    a.thetaZeroOriginalSweepDensity lam alpha ≤ (n : ℝ)^(10*delta)*a.E

end OriginalQLocalSharpReductionDraft

open OriginalQLocalSharpReductionDraft

def ActualOriginalQStoppingRegularInputs : Prop :=
  ∀ beta : ℝ, 1 < beta →
    ∀ m : ℝ, 0 < m → m < 1 / 300 →
      ∃ cl cu : ℝ, 0 < cl ∧ cl ≤ 1 ∧ 1 ≤ cu ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ hp : ActualConcreteHighWallNumeric m n,
          ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) (beta^2),
          ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
            StoppingRegularGates
              (actualConcreteHighWallData (beta^2) m n hp epsilon 0
                hepsilon heps0 (by norm_num)) m cl cu

theorem actualOriginalQLocalStoppingInputs_of_stoppingRegular :
    ActualOriginalQStoppingRegularInputs → ActualOriginalQLocalStoppingInputs := by
  intro H beta hbeta m hm hmmax
  obtain ⟨cl, cu, hcl, hcl1, hcu1, Hlocal⟩ := H beta hbeta m hm hmmax
  have Hmacro := eventually_macroGate_of_eq3
    (delta := m/10000) (C0 := 1) (D := 1) (Bclock := beta^2)
    hm (by positivity) (by linarith) (by norm_num)
  refine ⟨cl, cu, hcl, hcl1, hcu1, ?_⟩
  apply (Hlocal.and Hmacro).mono
  intro n hn hp epsilon hepsilon heps0
  let a := actualConcreteHighWallData (beta^2) m n hp epsilon 0
    hepsilon heps0 (by norm_num)
  have hlocal : StoppingRegularGates a m cl cu := hn.1 hp epsilon hepsilon heps0
  refine ⟨hlocal.stopping, hlocal.regular, ?_⟩
  apply hn.2 a
  · exact hp.hd1
  · exact hp.hupper
  · simpa only [a, actualConcreteHighWallData, ActualHighWallData.N, one_mul]
      using hp.hlower
  · exact le_rfl

theorem main_fluctuation_statement_of_stopping_regular :
    ActualOriginalQStoppingRegularInputs → OAI.SKFluctuations.MainFluctuationStatement := by
  intro H
  exact main_fluctuation_statement_of_original_q_local_stopping_inputs
    (actualOriginalQLocalStoppingInputs_of_stoppingRegular H)

end OAI.SKFluctuations.LaplaceWindowFormalization

