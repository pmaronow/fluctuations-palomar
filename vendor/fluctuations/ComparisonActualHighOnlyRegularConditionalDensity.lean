module

public import ComparisonActualHighOnlyConditionalFinitePhysicalBudget
public import ComparisonActualHighOnlyConditionalErrorExhaustion
public import ComparisonActualHighOnlyConditionalFloorError
public import ComparisonActualHighOnlyConditionalErrorDecomposition
public import ComparisonActualHighOnlyConditionalCostAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 22000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem eventually_actual_regular_conditional_density_at_raw_order_high_only
    (ell:ℕ) (hell:2 < ell)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hclcu:cl ≤ cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d ≤ 1 → a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
      a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      a.data.originalSweepDensity a.lam a.alpha ≤ a.data.N^(10*delta)*a.data.E := by
  have HB:=eventually_actual_conditional_finite_physical_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HF:=eventually_actual_conditional_floor_error_high_only Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=conditionalFinitePhysicalCoefficient D
  have hC4:4 ≤ C:=conditionalFinitePhysicalCoefficient_ge_four D
  have hC:0 ≤ C:=by linarith only [hC4]
  have HS:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (comparison_conditional_full_error_absorption_high_only hC hdelta)
  have H8:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (8:ℝ)
  filter_upwards [HB,HF,HS,H8,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnB hnF hnS hn8 hnScalar
  intro a hd1 hs hsxs hxs hclock
  have hN:1 ≤ a.data.N:=by exact_mod_cast Nat.succ_pos n
  have hE:=a.data.hE
  have hNpos:=a.data.hN
  have hscalar:=hnScalar a hd1
  by_cases hy:a.xs+1 ≤ a.data.N
  · obtain ⟨P⟩:=a.exists_potential_high_only hs
    have Hfinite:=hnB a hs hsxs hd1 hxs hy P hclock
    have Hnonpos:=P.nonpositive_error_le_of_finite_budgets_high_only (Ioo (0:ℝ) 1) measurableSet_Ioo Hfinite
    have Heq:=a.error_mask_eq_open_radius_high_only (P.negativeSet∪P.contactSet)
    rw [←Heq] at Hnonpos
    have Hfloor:=hnF a hd1 hs hsxs hxs P
    have Htotal:=P.original_error_eq_nonpositive_add_positive_high_only
    have Hfull:(∫u in 0..1,a.comparisonErrorDensity u) ≤
        4*(a.data.N^(3*delta)*a.data.E)+C*Real.log a.data.N*(a.data.N^(7*delta)*a.data.E)+
          a.data.N^(2*delta)*a.data.E:=by
      rw [Htotal]
      linarith only [Hnonpos,Hfloor]
    have H3:=mul_le_mul_of_nonneg_right hC4
      (show 0 ≤ a.data.N^(3*delta)*a.data.E by positivity)
    have H2:=mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith only [hC4])
      (show 0 ≤ a.data.N^(2*delta)*a.data.E by positivity)
    have H7:=mul_nonneg hC (show 0 ≤ a.data.N^(7*delta)*a.data.E by positivity)
    have Hwide:(∫u in 0..1,a.comparisonErrorDensity u) ≤
        C*(1+Real.log a.data.N)*a.data.N^(7*delta)*a.data.E+
          C*a.data.N^(3*delta)*a.data.E+C*a.data.N^(2*delta)*a.data.E:=by
      nlinarith only [Hfull,H3,H2,H7]
    rw [a.original_sweep_density_eq_error_integral]
    exact Hwide.trans (hnS a.data.E hE.le)
  · have hlarge:a.data.N ≤ comparisonConditionalScale a.data.N delta a.data.E a.lam+1:=by
      rw [←hxs];exact (lt_of_not_ge hy).le
    have HL:=a.data.original_sweep_density_large_conditional_scale a.alpha a.hlam a.hld
      (by simpa only [Function.comp_apply] using hn8) hscalar.1 hlarge
    exact HL.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 10*delta by linarith)) hE.le)

theorem eventually_actual_regular_conditional_density_with_order_high_only
    (ell:ℕ) (hell:2 < ell+1)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hclcu:cl ≤ cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/(ell:ℝ) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d ≤ 1 → a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
      a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      a.data.originalSweepDensity a.lam a.alpha ≤ a.data.N^(10*delta)*a.data.E := by
  exact eventually_actual_regular_conditional_density_at_raw_order_high_only (ell+1) hell
    hm hdelta hroom hcl hcu hclcu hAz hC0 hCt (by
      simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using horder)

theorem eventually_actual_regular_conditional_density_high_only
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hclcu:cl ≤ cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d ≤ 1 → a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
      a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      a.data.originalSweepDensity a.lam a.alpha ≤ a.data.N^(10*delta)*a.data.E := by
  obtain ⟨ell,hell⟩:=exists_nat_gt (max 3 (1+(delta+2)/delta))
  have hell2:2 < ell:=by
    have H:(3:ℝ) < ell:=(le_max_left _ _).trans_lt hell
    exact_mod_cast (lt_trans (by norm_num : (2:ℝ) < 3) H)
  have hden:0 < (ell:ℝ)-1:=by
    have H:(2:ℝ) < ell:=by exact_mod_cast hell2
    linarith only [H]
  have horder:(delta+2)/((ell:ℝ)-1) ≤ delta:=by
    apply (div_le_iff₀ hden).mpr
    have H:(delta+2)/delta < (ell:ℝ)-1:=by linarith only [(le_max_right _ _).trans_lt hell]
    have HH:delta+2 < ((ell:ℝ)-1)*delta:=(div_lt_iff₀ hdelta).mp H
    nlinarith only [HH]
  exact eventually_actual_regular_conditional_density_at_raw_order_high_only ell hell2
    hm hdelta hroom hcl hcu hclcu hAz hC0 hCt horder

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
