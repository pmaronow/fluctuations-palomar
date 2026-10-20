module

public import SKConstants.Completion.N13d.SourcePowerTail
public import SKConstants.Completion.Blueprint.AssemblyFine
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace SKConstants.Completion.N13d
open SKConstantsOAI.ZeroTemperatureSK Blueprint LBase

theorem coarse_previous_time_lower (a b : ℝ) (hb : 0 < b) (hab : b/4 ≤ a)
    (n : ℕ) (hn : 2 ≤ n) (hq : queryCount a b n+1=stopIndex a b n) :
    b*Real.log (n:ℝ)-1 ≤
      (growingQueryTime (meshSize a n) (queryCount a b n) : ℝ) := by
  have hV := (horizon_bounds a b hb hab n hn hq).1
  have hcell := duration_bound a b hb n hn hq (queryCount a b n) le_rfl
  have hpow : (n:ℝ)^(b/4-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith)
  change b*Real.log (n:ℝ) ≤
    (growingQueryTime (meshSize a n) (queryCount a b n+1) : ℝ) at hV
  rw [growingQueryTime_succ, NNReal.coe_add] at hV
  linarith

theorem coarse_previous_time_eventually (β a b : ℝ)
    (hb : 0 < b) (hab : b/4 ≤ a) (ha1 : a < 1) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime (meshSize a n) (queryCount a b n) ∧
      b*Real.log (n:ℝ)-1 ≤
        (growingQueryTime (meshSize a n) (queryCount a b n) : ℝ) := by
  have hlog : ∀ᶠ n : ℕ in atTop,
      ((parisiEquilibriumPhysicalEndpoint β : ℝ)+1)/b ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [schedule_eventually a b hb hab ha1, hlog] with n hn hl
  have hp := coarse_previous_time_lower a b hb hab n hn.1 hn.2.1
  refine ⟨hn.1, ?_, hp⟩
  apply NNReal.coe_le_coe.mp
  have hh := (div_le_iff₀ hb).mp hl
  nlinarith

theorem coarse_previous_susceptibility_square_eventually
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a b : ℝ) (hb : 0 < b) (hab : b/4 ≤ a) (ha1 : a < 1) :
    ∀ᶠ n : ℕ in atTop,
      (actualParisiFullSusceptibilityExpected W β
        (growingQueryTime (meshSize a n) (queryCount a b n)))^2 ≤
      (terminalTailConstant β)^2*Real.exp 1*(n:ℝ)^(-b) := by
  filter_upwards [coarse_previous_time_eventually β a b hb hab ha1] with n hn
  simpa only [neg_neg] using actual_susceptibility_square_shift_log_bound W β hβ (-1) b _ n
    (by omega) (growingQueryTime (meshSize a n) (queryCount a b n)).coe_nonneg
    (by linarith [hn.2.2])

end SKConstants.Completion.N13d
