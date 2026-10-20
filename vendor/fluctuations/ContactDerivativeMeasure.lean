module

public import FiniteContactTraceBudget
public import ComparisonContactIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

def contactDerivativeMeasure (S : ℝ→ℝ) (a b F : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity (fun r=>ENNReal.ofReal (deriv S r/F))

theorem monotoneOn_deriv_ae_nonneg {S : ℝ→ℝ} {a b : ℝ}
    (hS : MonotoneOn S (Icc a b)) : ∀ᵐ r,r∈Icc a b→0 ≤ deriv S r := by
  filter_upwards [volume.ae_ne a,volume.ae_ne b] with r hra hrb hr
  have hn : Icc a b∈𝓝 r := Icc_mem_nhds
    (lt_of_le_of_ne hr.1 hra.symm) (lt_of_le_of_ne hr.2 hrb)
  rw [←derivWithin_of_mem_nhds (f:=S) hn]
  exact hS.derivWithin_nonneg

theorem contactDerivativeMeasure_isFinite {S : ℝ→ℝ} {a b F : ℝ}
    (hab : a ≤ b) (hS : MonotoneOn S (Icc a b))
    (hAC : AbsolutelyContinuousOnInterval S a b) (hF : 0 < F) :
    IsFiniteMeasure (contactDerivativeMeasure S a b F) := by
  apply isFiniteMeasure_withDensity
  have hi : IntegrableOn (fun r=>deriv S r/F) (Icc a b) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hAC.intervalIntegrable_deriv).div_const F
  have hn : 0 ≤ᵐ[volume.restrict (Icc a b)] (fun r=>deriv S r/F) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (monotoneOn_deriv_ae_nonneg hS)] with r hr hdr
    exact div_nonneg (hdr hr) hF.le
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hn).mpr hi

theorem contactDerivativeMeasure_interval {S : ℝ→ℝ} {a b F p q : ℝ}
    (hab : a ≤ b) (hS : MonotoneOn S (Icc a b))
    (hAC : AbsolutelyContinuousOnInterval S a b) (hF : 0 < F)
    (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    contactDerivativeMeasure S a b F (Ioo p q)=ENNReal.ofReal ((S q-S p)/F) := by
  have hsub : Ioo p q⊆Icc a b := fun r hr=>⟨hap.trans hr.1.le,hr.2.le.trans hqb⟩
  have hsubcc : Icc p q⊆Icc a b := Icc_subset_Icc hap hqb
  have hlocal : AbsolutelyContinuousOnInterval S p q :=
    hAC.mono (by simpa only [uIcc_of_le hab,uIcc_of_le hpq] using hsubcc)
  have hicc : IntegrableOn (fun r=>deriv S r/F) (Icc p q) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mp hlocal.intervalIntegrable_deriv).div_const F
  have hi : IntegrableOn (fun r=>deriv S r/F) (Ioo p q) := hicc.mono_set Ioo_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo p q)] (fun r=>deriv S r/F) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (monotoneOn_deriv_ae_nonneg hS)] with r hr hdr
    exact div_nonneg (hdr (hsub hr)) hF.le
  rw [contactDerivativeMeasure,withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict_of_subset hsub,←ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_div]
  congr 1
  congr 1
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hpq]
  exact hlocal.integral_deriv_eq_sub

theorem contactDerivativeMeasure_weight_integrable {S weight : ℝ→ℝ} {a b F : ℝ}
    (hS : MonotoneOn S (Icc a b)) (hF : 0 < F)
    {A : Set ℝ} (hA : MeasurableSet A) (hsub : A⊆Icc a b)
    (hi : IntegrableOn (fun r=>weight r*deriv S r) A) :
    IntegrableOn weight A (contactDerivativeMeasure S a b F) := by
  change Integrable weight ((contactDerivativeMeasure S a b F).restrict A)
  rw [contactDerivativeMeasure,restrict_withDensity hA,
    Measure.restrict_restrict_of_subset hsub]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (((stronglyMeasurable_deriv S).measurable.div_const F).ennreal_ofReal.aemeasurable)
    (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))).mpr
  have hn : ∀ᵐ r∂volume.restrict A,0 ≤ deriv S r/F := by
    filter_upwards [ae_restrict_mem hA,
      ae_restrict_of_ae (monotoneOn_deriv_ae_nonneg hS)] with r hr hdr
    exact div_nonneg (hdr (hsub hr)) hF.le
  apply (hi.div_const F).congr
  filter_upwards [hn] with r hr
  rw [ENNReal.toReal_ofReal hr,smul_eq_mul]
  ring

theorem contactDerivativeMeasure_weight_integral {S weight : ℝ→ℝ} {a b F : ℝ}
    (hS : MonotoneOn S (Icc a b)) (hF : 0 < F)
    {A : Set ℝ} (hA : MeasurableSet A) (hsub : A⊆Icc a b) :
    (∫r in A,weight r∂contactDerivativeMeasure S a b F)=
      (∫r in A,weight r*deriv S r)/F := by
  rw [contactDerivativeMeasure,restrict_withDensity hA,
    Measure.restrict_restrict_of_subset hsub,
    integral_withDensity_eq_integral_toReal_smul
      (((stronglyMeasurable_deriv S).measurable.div_const F).ennreal_ofReal)
      (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hA,
    ae_restrict_of_ae (monotoneOn_deriv_ae_nonneg hS)] with r hr hdr
  rw [ENNReal.toReal_ofReal (div_nonneg (hdr (hsub hr)) hF.le),smul_eq_mul]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
