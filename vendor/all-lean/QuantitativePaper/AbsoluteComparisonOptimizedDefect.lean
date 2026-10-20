module

public import QuantitativePaper.AbsoluteComparisonDefectBound
public import QuantitativePaper.AbsoluteComparisonTrialBudget

@[expose] public section

/-! Genuine optimized defect control, obtained from attained minima and
the physical endpoint trial budget, without a measurable minimizer selector. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 2200000

def absoluteComparisonDefectMajorant (T k Cs : ℝ) (n : ℕ) (lam η t : ℝ) : ℝ :=
  min (1/((n:ℝ)*(1-t)*lam)) (2*((n:ℝ)*(1-t))^(-1/2:ℝ))+
  absoluteComparisonQuarterConstant*((n:ℝ)*(1-t))^(-3/4:ℝ)*lam^(-1/2:ℝ)+
  absoluteComparisonThirdConstant T k Cs*(n:ℝ)^(-2/3:ℝ)*(1-t)^(-65/66:ℝ)*
    (absoluteComparisonBudgetConstant+lam^(-1/3:ℝ)*η^(1/11:ℝ))

theorem absolute_optimized_defect_point (T k Cs : ℝ)
    (hT : T∈Ioc (0:ℝ) (1/4)) (hk : 0<k) (hCs : 0 ≤ Cs)
    (n : ℕ) (hn : 0<n) (ν : ParisiMeasure) (β lam C1 : ℝ)
    (hβ : 1 ≤ β) (hlam : lam∈Ioc (0:ℝ) 1) (hlamβ : lam<β) (hC1 : 0 ≤ C1)
    (hν : ν∈scalarFloor (lam/β))
    (htrial : ∀y∈Icc (0:ℝ) T,k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0:ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0:ℝ) T))
    (hzero : 0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0)
    (hcost : parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ≤ C1*lam^5)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β (lam/β)) t) :
    β*optimizedVectorInterpolationDefect n β (lam/β) t ≤
      absoluteComparisonDefectMajorant T k Cs n lam (energyComparisonError n β lam+C1*lam^5) t := by
  have hβp : 0<β:=by linarith
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr hlamβ⟩
  let μ:=vectorMeasureMinimizer n hn β t (lam/β) ht.2.le hs.2.le
  have hμ:=vectorMeasureMinimizer_mem n hn β t (lam/β) ht.2.le hs.2.le
  have hminV : ∀ρ∈scalarFloor (lam/β), vectorMeasureFunctional n μ β t (lam/β) ≤
      vectorMeasureFunctional n ρ β t (lam/β):=
    vectorMeasureMinimizer_minimal n hn β t (lam/β) ht.2.le hs.2.le
  have hmin : ∀ρ∈scalarFloor (lam/β), responseEnergyFunctional n μ β t lam ≤
      responseEnergyFunctional n ρ β t lam:=fun ρ hρ=>div_le_div_of_nonneg_right (hminV ρ hρ) hβp.le
  have hbudget:=absolute_trial_budget hn μ ν β lam t C1 hβp hs ⟨ht.1.le,ht.2.le⟩
    hμ hν hminV hzero hcost
  have he : 0 ≤ energyComparisonError n β lam:=by
    rw [energyComparisonError_eq_fractional_gap n β lam hβp.ne']
    exact div_nonneg (constrainedParisiValue_sub_completedFractionalPressure_nonneg n hn β (lam/β) hs hβp.ne') hβp.le
  have hη : 0 ≤ energyComparisonError n β lam+C1*lam^5:=add_nonneg he (mul_nonneg hC1 (pow_nonneg hlam.1.le _))
  have hclock : 1-(1-t)=t:=by ring
  have hb:=absolute_refined_defect_bound T k Cs hT hk hCs hn μ ν β lam (1-t)
    (energyComparisonError n β lam+C1*lam^5) hβ hlam hlamβ ⟨sub_pos.mpr ht.2,by linarith [ht.1]⟩
    hη hμ hν (by simpa only [hclock] using hmin) (by simpa only [hclock] using hbudget)
    htrial hdensity
  simp only [hclock] at hb
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn μ β (lam/β) hs hμ hβp.ne' t ht hminV hf]
  exact hb

theorem absolute_optimized_defect_ae (T k Cs : ℝ)
    (hT : T∈Ioc (0:ℝ) (1/4)) (hk : 0<k) (hCs : 0 ≤ Cs)
    (n : ℕ) (hn : 0<n) (ν : ParisiMeasure) (β lam C1 : ℝ)
    (hβ : 1 ≤ β) (hlam : lam∈Ioc (0:ℝ) 1) (hlamβ : lam<β) (hC1 : 0 ≤ C1)
    (hν : ν∈scalarFloor (lam/β))
    (htrial : ∀y∈Icc (0:ℝ) T,k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0:ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0:ℝ) T))
    (hzero : 0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0)
    (hcost : parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ≤ C1*lam^5) :
    ∀ᵐt∂volume.restrict (Ioo (0:ℝ) 1), β*optimizedVectorInterpolationDefect n β (lam/β) t ≤
      absoluteComparisonDefectMajorant T k Cs n lam (energyComparisonError n β lam+C1*lam^5) t := by
  have hβp : 0<β:=by linarith
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr hlamβ⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [vectorInterpolationMinimum_ae_differentiable n hn β (lam/β) hs hβp.ne'] with t hd
  intro ht
  exact absolute_optimized_defect_point T k Cs hT hk hCs n hn ν β lam C1 hβ hlam hlamβ hC1
    hν htrial hdensity hzero hcost t ht (hd ⟨ht.1.le,ht.2.le⟩)

end QuantitativePaper
