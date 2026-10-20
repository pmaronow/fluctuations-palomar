module

public import QuantitativePaper.AbsoluteComparisonOptimizedDefect
public import QuantitativePaper.AbsoluteComparisonIntegratedBudget
public import QuantitativePaper.AbsoluteComparisonIntegratedConstant
public import QuantitativePaper.AbsoluteComparisonPrior

@[expose] public section

/-! Integrating the true optimized replica defect gives the actual finite
model budget, including its self-consistent clipped-trial error. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 2400000

theorem absolute_energy_comparison_budget (T k Cs : ℝ)
    (hT : T∈Ioc (0:ℝ) (1/4)) (hk : 0<k) (hCs : 0 ≤ Cs)
    (n : ℕ) (hn : 0<n) (ν : ParisiMeasure) (β lam C1 : ℝ)
    (hβ : 1 ≤ β) (hlam : lam∈Ioc (0:ℝ) 1) (hlamβ : lam ≤ β/2) (hC1 : 0 ≤ C1)
    (hν : ν∈scalarFloor (lam/β))
    (htrial : ∀y∈Icc (0:ℝ) T,k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0:ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0:ℝ) T))
    (hzero : 0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0)
    (hcost : parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ≤ C1*lam^5) :
    energyComparisonError n β lam ≤
      absoluteComparisonIntegrationConstant absoluteComparisonQuarterConstant
        (absoluteComparisonThirdConstant T k Cs) absoluteComparisonBudgetConstant*
      ((n:ℝ)^(-2/3:ℝ)+(n:ℝ)^(-3/4:ℝ)*lam^(-1/2:ℝ)+Real.log (2+(n:ℝ))/((n:ℝ)*lam)+
        ((n:ℝ)^(-2/3:ℝ)*lam^(-1/3:ℝ))*(energyComparisonError n β lam+C1*lam^5)^(1/11:ℝ)) := by
  have hβp : 0<β:=by linarith
  have hlt : lam<β:=by linarith
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr hlt⟩
  have hprior:=absolute_comparison_prior n hn β lam hβp hlam.1 hlamβ
  let η:=energyComparisonError n β lam+C1*lam^5
  have hη : 0 ≤ η:=add_nonneg hprior.1 (mul_nonneg hC1 (pow_nonneg hlam.1.le _))
  have hN : 1 ≤ (n:ℝ):=by exact_mod_cast hn
  have hc:=absoluteComparison_rate_constants_pos T k Cs
  have henv:=vectorInterpolationMinimum_integral n hn β (lam/β) hs hβp.ne'
  have heq : 4*energyComparisonError n β lam=
      ∫t in (0:ℝ)..1,β*optimizedVectorInterpolationDefect n β (lam/β) t:=by
    rw [energyComparisonError_eq_fractional_gap n β lam hβp.ne',henv.2,
      intervalIntegral.integral_const_mul]
    field_simp [hβp.ne']
    <;> ring
  have hbd:=absolute_optimized_defect_ae T k Cs hT hk hCs n hn ν β lam C1 hβ hlam hlt hC1
    hν htrial hdensity hzero hcost
  have hb : ∀ᵐt∂volume.restrict (Ioo (0:ℝ) 1),
      β*optimizedVectorInterpolationDefect n β (lam/β) t ≤
        min (1/((n:ℝ)*(1-t)*lam)) (2*((n:ℝ)*(1-t))^(-(1/2:ℝ)))+
          absoluteComparisonQuarterConstant*((n:ℝ)*(1-t))^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+
          absoluteComparisonThirdConstant T k Cs*(n:ℝ)^(-(2/3:ℝ))*(1-t)^(-(65/66:ℝ))*
            (absoluteComparisonBudgetConstant+lam^(-(1/3:ℝ))*η^(1/11:ℝ)):=by
    convert hbd using 1 <;> norm_num [absoluteComparisonDefectMajorant,η]
  have hint:=absolute_comparison_integrated_budget (n:ℝ) lam η
    absoluteComparisonQuarterConstant (absoluteComparisonThirdConstant T k Cs) absoluteComparisonBudgetConstant
    hN hlam.1 hη hc.1.le hc.2.1.le hc.2.2.le
    (fun t=>β*optimizedVectorInterpolationDefect n β (lam/β) t) (henv.1.const_mul β) hb
  rw [←heq] at hint
  apply absoluteComparison_integrated_budget (n:ℝ) lam (energyComparisonError n β lam) η
    absoluteComparisonQuarterConstant (absoluteComparisonThirdConstant T k Cs) absoluteComparisonBudgetConstant
    hN hlam.1 hprior.1 hη hc.1.le hc.2.1.le hc.2.2.le
  convert hint using 1 <;> norm_num

end QuantitativePaper
