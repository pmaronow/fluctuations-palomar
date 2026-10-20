module

public import QuantitativePaper.AbsoluteComparisonEnergyBudget
public import QuantitativePaper.UniformScalarRootTrialLemma

@[expose] public section

/-! Literal main Proposition 5.5 for the actual finite SK model. One
positive clipping window and one constant work for every temperature
above beta0 and every positive finite dimension. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 2400000

theorem absolute_selfconsistent_comparison (β₀ : ℝ) (hβ₀ : 1<β₀) :
    ∃L C : ℝ,0<L ∧ L ≤ 1 ∧ L ≤ β₀/2 ∧ 0<C ∧
      ∀n : ℕ,0<n→∀β : ℝ,β₀ ≤ β→∀lam∈Ioc (0:ℝ) L,
        0 ≤ energyComparisonError n β lam ∧
          energyComparisonError n β lam ≤ C*
            ((n:ℝ)^(-2/3:ℝ)+(n:ℝ)^(-3/4:ℝ)*lam^(-1/2:ℝ)+
              Real.log (2+(n:ℝ))/((n:ℝ)*lam)) := by
  obtain ⟨T,k,Cs,C1,L,hT,hk,hCs,hC1,hL,hL1,hLβ,hLT,hAll⟩:=uniform_scalar_root_trial β₀ hβ₀
  let A:=absoluteComparisonQuarterConstant
  let B:=absoluteComparisonThirdConstant T k Cs
  let D:=absoluteComparisonBudgetConstant
  let Cbudget:=absoluteComparisonIntegrationConstant A B D
  have hc:=absoluteComparison_rate_constants_pos T k Cs
  have hCb : 0<Cbudget:=absoluteComparisonIntegrationConstant_pos A B D hc.1.le hc.2.1.le hc.2.2.le
  refine ⟨L,absoluteComparisonAbsorptionConstant Cbudget quantitativeParisiConstant C1,
    hL,hL1,hLβ,absoluteComparisonAbsorptionConstant_pos _ _ _ hCb.le
      quantitativeParisiConstant_pos.le (zero_le_one.trans hC1),?_⟩
  intro n hn β hb lam hlam
  have hβ : 1 ≤ β:=hβ₀.le.trans hb
  have hβp : 0<β:=by linarith
  have hlam1 : lam∈Ioc (0:ℝ) 1:=⟨hlam.1,hlam.2.trans hL1⟩
  have hlamβ : lam ≤ β/2:=by linarith [hlam.2.trans hLβ]
  have hprior:=absolute_comparison_prior n hn β lam hβp hlam.1 hlamβ
  let base:=FRSB.parisiMinimizer β 0
  have hbase : IsParisiMinimizer β 0 base:=FRSB.parisiMinimizer_minimal β 0
  obtain ⟨hs,hν,hcdf,htrial,hdensity,hzero,hval,hcost⟩:=
    (hAll β hb base hbase).2.2.2.2 lam ⟨hlam.1.le,hlam.2⟩
  have hbudget:=absolute_energy_comparison_budget T k Cs hT hk (zero_le_one.trans hCs)
    n hn (scalarClippedTrialMeasure (lam/β) hs base) β lam C1 hβ hlam1 hlamβ
    (zero_le_one.trans hC1) hν htrial (by simpa only [Measure.restrict_smul] using hdensity) hzero hcost
  refine ⟨hprior.1,?_⟩
  apply absoluteComparison_absorb (n:ℝ) lam (energyComparisonError n β lam)
    Cbudget quantitativeParisiConstant C1 (Nat.cast_pos.mpr hn) hlam.1 hlam1.2 hprior.1
    hCb.le quantitativeParisiConstant_pos.le (zero_le_one.trans hC1)
  · convert hprior.2 using 1 <;> norm_num
  · convert hbudget using 1 <;> norm_num

end QuantitativePaper
