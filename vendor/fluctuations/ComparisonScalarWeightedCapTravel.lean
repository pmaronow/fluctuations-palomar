module

public import ComparisonScalarSupportZeros
public import ComparisonCapIntervals
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 4000000

theorem comparison_negative_cap_endpoint_slope_signs
    (H : ℝ→ℝ) {a b da db : ℝ} (hab : a<b)
    (ha : H a=0) (hb : H b=0) (hnegative : ∀r∈Ioo a b,H r<0)
    (hda : HasDerivAt H da a) (hdb : HasDerivAt H db b) : da ≤ 0 ∧ 0 ≤ db := by
  constructor
  · apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hda).2
    filter_upwards [Ioo_mem_nhdsGT hab] with r hr
    rw [slope_def_field,ha,sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hnegative r hr).le (sub_nonneg.mpr hr.1.le)
  · apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hdb).1
    filter_upwards [Ioo_mem_nhdsLT hab] with r hr
    rw [slope_def_field,hb,sub_zero]
    exact div_nonneg_iff.mpr (Or.inr ⟨(hnegative r hr).le,sub_nonpos.mpr hr.2.le⟩)

theorem comparison_negative_cap_spin_endpoint_bounds
    (H S : ℝ→ℝ) {a b ca cb : ℝ} (hab : a<b)
    (ha : H a=0) (hb : H b=0) (hnegative : ∀r∈Ioo a b,H r<0)
    (hca : 0<ca) (hcb : 0<cb)
    (hda : HasDerivAt H (ca*(a-S a)) a) (hdb : HasDerivAt H (cb*(b-S b)) b) :
    a ≤ S a ∧ S b ≤ b := by
  have hsign := comparison_negative_cap_endpoint_slope_signs H hab ha hb hnegative hda hdb
  constructor
  · by_contra hn
    have hh : 0<a-S a := by linarith
    have hp := mul_pos hca hh
    linarith [hsign.1]
  · have hh : 0 ≤ b-S b := (mul_nonneg_iff_of_pos_left hcb).mp hsign.2
    linarith

theorem comparison_cap_spin_radius_error_le_width
    (S : ℝ→ℝ) {a b r : ℝ} (hS : MonotoneOn S (Icc a b))
    (ha : a ≤ S a) (hb : S b ≤ b) (hr : r∈Icc a b) : |S r-r| ≤ b-a := by
  have hab := hr.1.trans hr.2
  have hleft := hS ⟨le_rfl,hab⟩ hr hr.1
  have hright := hS hr ⟨hab,le_rfl⟩ hr.2
  exact abs_le.mpr ⟨by linarith [hr.1,hr.2],by linarith [hr.1,hr.2]⟩

theorem comparison_weighted_cap_travel_calibration
    {N delta U L d a x e : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (hx : 0<x) (hax : a ≤ x) (he : e ≤ d^2)
    (hcal : L*d^2 ≤ a^3) :
    e*((L/N^delta)*Real.log ((1+U)/U))/x^3 ≤ Real.log ((1+U)/U)/N^delta := by
  have hden : 0<N^delta := Real.rpow_pos_of_pos hN _
  have hratio : 1 ≤ (1+U)/U := (le_div_iff₀ hU).mpr (by linarith)
  have hlog : 0 ≤ Real.log ((1+U)/U) := Real.log_nonneg hratio
  have heL : e*L ≤ x^3 := (mul_le_mul_of_nonneg_right he hL).trans (by
    have hh := pow_le_pow_left₀ ha hax 3
    nlinarith [hcal])
  apply (div_le_iff₀ (pow_pos hx 3)).mpr
  have hh := mul_le_mul_of_nonneg_right heL (div_nonneg hlog hden.le)
  convert hh using 1 <;> field_simp

theorem comparison_native_constraint_cubic_room {N E d : ℝ} (hd : 0<d) :
    comparisonConstraintLength N E d*d^2 ≤ (comparisonLowerScale N E d)^3 := by
  have hh : comparisonConstraintLength N E d ≤ (comparisonLowerScale N E d)^3/d^2 := by
    unfold comparisonConstraintLength
    exact min_le_right _ _
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mp hh

theorem comparison_scalar_native_cap_calibration
    {N delta E d lam x : ℝ} (hN : 0<N) (hE : 0<E) (hd : 0<d)
    (hlam : 0 ≤ lam) (hld : lam ≤ d^2) (hx : 0<x)
    (hax : comparisonLowerScale N E d ≤ x) (r : ℝ) :
    laplaceComparisonStrength d lam r*
      ((comparisonConstraintLength N E d/N^delta)*
        Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E))/x^3 ≤
      Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)/N^delta := by
  have hU := comparisonSmallMass_pos hN hE
  have ha := comparisonLowerScale_pos hN hE hd
  have hL := comparisonConstraintLength_pos hN hE hd
  exact comparison_weighted_cap_travel_calibration hN hU hL.le ha.le hx hax
    ((laplaceComparisonStrength_le d hlam r).trans hld) (comparison_native_constraint_cubic_room hd)

theorem comparison_scalar_negative_cap_weighted_error
    {N delta E d lam x a b r : ℝ} (hN : 0<N) (hE : 0<E) (hd : 0<d)
    (hlam : 0<lam) (hld : lam ≤ d^2) (hx : 0<x)
    (hax : comparisonLowerScale N E d ≤ x)
    (S : ℝ→ℝ) (hS : MonotoneOn S (Icc a b))
    (ha : a ≤ S a) (hb : S b ≤ b) (hr : r∈Icc a b)
    (htravel : b-a ≤ (comparisonConstraintLength N E d/N^delta)*
      Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)) :
    laplaceComparisonStrength d lam r*|S r-r|/x^3 ≤
      Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)/N^delta := by
  have he := (laplaceComparisonStrength_pos d hlam r).le
  calc
    _ ≤ laplaceComparisonStrength d lam r*(b-a)/x^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (comparison_cap_spin_radius_error_le_width S hS ha hb hr) he) (pow_pos hx 3).le
    _ ≤ laplaceComparisonStrength d lam r*
        ((comparisonConstraintLength N E d/N^delta)*
          Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E))/x^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htravel he) (pow_pos hx 3).le
    _ ≤ _ := comparison_scalar_native_cap_calibration hN hE hd hlam.le hld hx hax r

theorem comparison_native_cap_log_le {N E : ℝ} (hN : 2 ≤ N) (hE : 0<E) (hE1 : E ≤ 1) :
    Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E) ≤ 2*Real.log N := by
  have hNp : 0<N := by linarith
  have heq : (1+comparisonSmallMass N E)/comparisonSmallMass N E=1+N*E := by
    unfold comparisonSmallMass
    field_simp
    ring
  have hpos : 0<1+N*E := by positivity
  have hle : 1+N*E ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left hE1 hNp.le
    nlinarith
  rw [heq]
  calc
    _ ≤ Real.log (N^2) := Real.log_le_log hpos hle
    _ = _ := by rw [Real.log_pow];norm_num

theorem comparison_weighted_cap_log_rate_tendsto
    (N : ℕ→ℝ) {delta : ℝ} (hdelta : 0<delta) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n=>2*Real.log (N n)/(N n)^delta) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop hdelta).tendsto_div_nhds_zero
  simpa only [Function.comp_def,mul_zero,mul_div_assoc] using (hh.comp hN).const_mul 2

theorem comparison_rescaled_scalar_origin_zero
    (Gamma : ℕ→ℝ→ℝ) (x : ℕ→ℝ) (g : ℝ→ℝ) {T : ℝ}
    (hGamma : ∀n,Gamma n 0=0)
    (hG : TendstoLocallyUniformly (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g atTop) :
    g 0=0 := by
  have hh := (hG.tendstoLocallyUniformlyOn (s:=Set.univ)).tendsto_at (a:=(0:ℝ)) (mem_univ _)
  have hz : Tendsto (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n) 0) atTop (𝓝 0) := by
    convert tendsto_const_nhds (x:=(0:ℝ)) using 1
    funext n
    simp [comparisonRescaledScalarResponse,hGamma n]
  exact tendsto_nhds_unique hh hz

end OAI.SKFluctuations.LaplaceWindowFormalization
