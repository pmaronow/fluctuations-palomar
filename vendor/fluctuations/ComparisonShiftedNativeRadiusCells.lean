module

public import ComparisonShiftedNativeRadiusDefectLimit
public import ComparisonNativeRadiusCellLengths

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem high_radius_le_quantile_iff {r u : ℝ} (hr : r∈Ioo m.rmin 1)
    (hu : u∈Icc (0:ℝ) 1) : r ≤ m.R u ↔ m.alpha.val.val r ≤ u := by
  constructor
  · intro H
    have high : m.u0 ≤ u:=by
      by_contra HH
      rw [m.R_before (le_of_not_ge HH)] at H
      exact hr.1.not_ge H
    have HA:=m.alpha.val.property.2 H
    rw [m.R_spec ⟨high,hu.2⟩] at HA
    exact HA
  · intro H
    have HR:=m.R_monotone H
    rw [m.R_inverse (Ioo_subset_Icc_self hr)] at HR
    exact HR

theorem high_radius_cell_mem {r u v : ℝ} (hr : r∈Ioo m.rmin 1)
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) :
    m.alpha.val.val r∈Ioc u v ↔ r∈Ioc (m.R u) (m.R v) := by
  have HU:=m.high_radius_le_quantile_iff hr hu
  have HV:=m.high_radius_le_quantile_iff hr hv
  constructor
  · intro H
    exact ⟨lt_of_not_ge (fun HH=>H.1.not_ge (HU.mp HH)),HV.mpr H.2⟩
  · intro H
    exact ⟨lt_of_not_ge (fun HH=>H.1.not_ge (HU.mpr HH)),HV.mp H.2⟩

theorem mass_radius_substitution_zero_low (F : ℝ→ℝ)
    (hFi : IntervalIntegrable F volume 0 1)
    (hzero : ∀u∈Ioo (0:ℝ) m.u0,F u=0) :
    (∫u in (0:ℝ)..1,F u)=∫r in Icc m.rmin 1,deriv m.alpha.val.val r*F (m.alpha.val.val r) := by
  have hlow : (∫u in (0:ℝ)..m.u0,F u)=0:=by
    rw [intervalIntegral.integral_congr_Ioo_of_le m.hu.1 hzero]
    simp
  have hi0 : IntervalIntegrable F volume 0 m.u0:=hFi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.1]
    exact Icc_subset_Icc le_rfl m.hu.2)
  have hi1 : IntervalIntegrable F volume m.u0 1:=hFi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.2]
    exact Icc_subset_Icc m.hu.1 le_rfl)
  rw [←intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hlow,zero_add,m.mass_radius_substitution]

theorem radiusMassWeight_cell_average_eq_radius_length
    {a z x kmin u v : ℝ} (ha : m.rmin < a) (_hz : z ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (hx : 0 < x) (hkmin : 0 < kmin) (hfloor : ∀r∈A,kmin ≤ m.k r)
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u < v) :
    MassCellAveraging.average (comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin) u v=
      volume.real (A∩Ioc (m.R u) (m.R v))/(x*(v-u)) := by
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  let F:=(Ioc u v).indicator f
  have hFi : IntervalIntegrable F volume 0 1:=by
    have hf:=comparisonRadiusMassWeight_memLp_two m.R m.alpha.val.val m.R_monotone.measurable hA hx hkmin
    have hi:=(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
    exact ⟨hi.1.indicator measurableSet_Ioc,hi.2.indicator measurableSet_Ioc⟩
  have Hlow : ∀t∈Ioo (0:ℝ) m.u0,F t=0:=by
    intro t ht
    have HR:=m.R_before ht.2.le
    have Hnot:m.rmin∉A:=fun H=>not_le_of_gt ha (hAD H).1.le
    by_cases HC:t∈Ioc u v <;> simp [F,HC,f,comparisonRadiusMassWeight,HR,Hnot]
  have HP:=m.radiusMassWeight_linear_pullback hx hkmin hfloor
  have Hcell : (∫t in u..v,f t)=volume.real (A∩Ioc (m.R u) (m.R v))*(1/x):=by
    have HE : (∫t in u..v,f t)=∫t in (0:ℝ)..1,F t:=by
      rw [intervalIntegral.integral_of_le huv.le,intervalIntegral.integral_of_le zero_le_one,
        setIntegral_indicator measurableSet_Ioc,inter_eq_right.mpr (Ioc_subset_Ioc hu.1 hv.2)]
    rw [HE,m.mass_radius_substitution_zero_low F hFi Hlow]
    have HE' : (∫r in Icc m.rmin 1,deriv m.alpha.val.val r*F (m.alpha.val.val r))=
        ∫r in Icc m.rmin 1,(A∩Ioc (m.R u) (m.R v)).indicator (fun _ : ℝ=>1/x) r:=by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc,HP,
        ae_restrict_of_ae (volume.ae_ne m.rmin),ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
        with r hr hp hr0 hr1
      have hro:r∈Ioo m.rmin 1:=⟨lt_of_le_of_ne hr.1 hr0.symm,lt_of_le_of_ne hr.2 hr1⟩
      have HC:=m.high_radius_cell_mem hro hu hv
      by_cases hcell:m.alpha.val.val r∈Ioc u v
      · rw [show F (m.alpha.val.val r)=f (m.alpha.val.val r) from indicator_of_mem hcell f]
        by_cases HA:r∈A <;>
          simpa only [f,indicator_apply,mem_inter_iff,HA,HC.mp hcell,and_true,ite_true,ite_false] using hp
      · rw [show F (m.alpha.val.val r)=0 from indicator_of_notMem hcell f,mul_zero]
        exact (indicator_of_notMem (show r∉A∩Ioc (m.R u) (m.R v) from
          fun H=>hcell (HC.mpr H.2)) (fun _ : ℝ=>1/x)).symm
    rw [HE',integral_indicator_const _ (hA.inter measurableSet_Ioc),measureReal_restrict_apply
      (hA.inter measurableSet_Ioc),inter_eq_left.mpr (by
        intro r hr
        exact ⟨(m.R_bounds u).1.trans hr.2.1.le,hr.2.2.trans (m.R_bounds v).2⟩),smul_eq_mul]
  unfold MassCellAveraging.average
  rw [Hcell]
  field_simp [hx.ne',(sub_pos.mpr huv).ne']

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
