module

public import ComparisonShiftedNativeThermalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem massSlice_profile_mem {lo hi r : ℝ}
    (hlo : lo∈Icc m.u0 1) (hhi : hi∈Icc m.u0 1)
    (hr : r∈m.massSlice lo hi) : m.alpha.val.val r∈Ioo lo hi := by
  have hlR:=m.R_bounds lo
  have hrR:=m.R_bounds hi
  have hrI : r∈Icc m.rmin 1:=⟨hlR.1.trans hr.1.le,hr.2.le.trans hrR.2⟩
  have hs:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
  have hlow:=hs hlR hrI hr.1
  have hhigh:=hs hrI hrR hr.2
  rw [m.R_spec hlo] at hlow
  rw [m.R_spec hhi] at hhigh
  exact ⟨hlow,hhigh⟩

theorem inverse_slice_mass {lo hi : ℝ} (hlo : lo∈Icc m.rmin 1)
    (hhi : hi∈Icc m.rmin 1) (hlh : lo≤hi) :
    (∫r in Ioo lo hi,deriv m.alpha.val.val r)=m.alpha.val.val hi-m.alpha.val.val lo := by
  have hsub : uIcc lo hi⊆Icc m.rmin 1:=by
    rw [uIcc_of_le hlh]
    exact Icc_subset_Icc hlo.1 hhi.2
  have hac : AbsolutelyContinuousOnInterval m.alpha.val.val lo hi:=
    ((inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property).mono hsub).absolutelyContinuousOnInterval
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlh]
  exact hac.integral_deriv_eq_sub

theorem massSlice_mass {lo hi : ℝ} (hlo : lo∈Icc m.u0 1)
    (hhi : hi∈Icc m.u0 1) (hlh : lo≤hi) :
    (∫r in m.massSlice lo hi,deriv m.alpha.val.val r)=hi-lo := by
  rw [massSlice,m.inverse_slice_mass (m.R_bounds lo) (m.R_bounds hi) (m.R_monotone hlh),
    m.R_spec hlo,m.R_spec hhi]

theorem inverse_derivative_unit_mass :
    IntegrableOn (deriv m.alpha.val.val) (Icc m.rmin 1) ∧
    (∫r in Icc m.rmin 1,deriv m.alpha.val.val r)=1-m.u0 := by
  have hac : AbsolutelyContinuousOnInterval m.alpha.val.val m.rmin 1:=
    ((inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property).mono
      (by rw [uIcc_of_le m.hr])).absolutelyContinuousOnInterval
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le m.hr).mp hac.intervalIntegrable_deriv,?_⟩
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le m.hr,
    hac.integral_deriv_eq_sub,m.alpha.property.1,m.alpha.property.2.1]

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
