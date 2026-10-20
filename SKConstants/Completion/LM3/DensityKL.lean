module
public import SKConstants.Completion.LC4a.ReplayKL

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3

theorem klDiv_positive_densities_ae {U : Type*} [MeasurableSpace U]
    (R : Measure U) [IsProbabilityMeasure R] (f g : U → ℝ)
    (hf : AEMeasurable f R) (hg : AEMeasurable g R)
    (hfpos : ∀ u, 0 < f u) (hgpos : ∀ u, 0 < g u)
    [IsProbabilityMeasure (R.withDensity (fun u => ENNReal.ofReal (f u)))]
    [IsProbabilityMeasure (R.withDensity (fun u => ENNReal.ofReal (g u)))]
    (hint : Integrable (fun u => Real.log (f u) - Real.log (g u))
      (R.withDensity (fun u => ENNReal.ofReal (f u)))) :
    klDiv (R.withDensity (fun u => ENNReal.ofReal (f u)))
      (R.withDensity (fun u => ENNReal.ofReal (g u))) =
      ENNReal.ofReal (∫ u, Real.log (f u) - Real.log (g u)
        ∂(R.withDensity (fun u => ENNReal.ofReal (f u)))) := by
  let L := R.withDensity (fun u => ENNReal.ofReal (f u))
  let P := R.withDensity (fun u => ENNReal.ofReal (g u))
  have hLR : L ≪ R := withDensity_absolutelyContinuous _ _
  have hRP : R ≪ P := withDensity_absolutelyContinuous' hg.ennreal_ofReal
    (ae_of_all _ (fun u => ENNReal.ofReal_ne_zero_iff.mpr (hgpos u)))
  have hac : L ≪ P := hLR.trans hRP
  have hRN := Measure.rnDeriv_withDensity_right L R hg.ennreal_ofReal
    (ae_of_all _ (fun u => ENNReal.ofReal_ne_zero_iff.mpr (hgpos u)))
    (ae_of_all _ (fun u => ENNReal.ofReal_ne_top))
  have hRF := Measure.rnDeriv_withDensity₀ R hf.ennreal_ofReal
  have hllr : llr L P =ᵐ[L] fun u => Real.log (f u) - Real.log (g u) := by
    filter_upwards [hRN.filter_mono hLR.ae_le, hRF.filter_mono hLR.ae_le] with u hu huf
    change (L.rnDeriv P) u = (ENNReal.ofReal (g u))⁻¹ * (L.rnDeriv R) u at hu
    change (L.rnDeriv R) u = ENNReal.ofReal (f u) at huf
    change Real.log ((L.rnDeriv P) u).toReal = _
    rw [hu, huf]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (hgpos u).le, ENNReal.toReal_ofReal (hfpos u).le]
    rw [Real.log_mul (inv_ne_zero (hgpos u).ne') (hfpos u).ne', Real.log_inv]
    ring
  rw [klDiv_of_ac_of_integrable hac (hint.congr hllr.symm), integral_congr_ae hllr]
  simp [L, P]

end SKConstants.Completion.LM3
