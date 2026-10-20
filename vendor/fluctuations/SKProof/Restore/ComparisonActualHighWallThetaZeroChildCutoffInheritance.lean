module

public import ComparisonActualHighWallThetaZeroChildClockNumerics
public import ComparisonActualHighWallComparableBandClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem theta_zero_child_cutoff_inheritance
    {m delta cl cu Az C0 Ct D Bclock c0:ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim:ℕ→ℕ) (hdim:Tendsto dim atTop atTop)
    (M:(n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (htarget:∀ᶠn in atTop,comparisonConditionalScale (M n).data.N delta
      (M n).data.E (M n).lam≤(M n).xs)
    (hweak:Tendsto (fun n=>laplaceComparisonStrength (M n).data.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0)):
    ∀ᶠn in atTop,comparisonLowerScale (M n).data.N (M n).data.E (M n).data.d≤
      actualChildCutoff (dim n+1) delta c0 (M n).data.d (M n).lam (M n).xs:=by
  have Hweak:=hweak.eventually (eventually_le_nhds zero_lt_one)
  have hdim1:Tendsto (fun n=>dim n+1) atTop atTop:=
    (tendsto_add_atTop_nat 1).comp hdim
  filter_upwards [hdim1.eventually (eventually_actual_child_parameters_from_target
      hm hdelta (one_div_pos.mpr hC0) hc0 hmargin),Hweak,htarget]
    with n hn hnweak hntarget
  have hlo:(1/C0)*(M n).data.N^(-(2:ℝ)/3+m)*(M n).data.d≤(M n).data.E:=by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using (M n).hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup:(M n).data.E≤(M n).data.d^2/Real.sqrt (dim n+1:ℕ):=
    (le_div_iff₀ (Real.sqrt_pos.mpr (M n).data.hN)).mpr
      (by simpa only [mul_comm] using (M n).hupper)
  exact (hn (M n).data.d (M n).lam (M n).data.E (M n).xs
    (M n).data.hd (M n).hlam (M n).hld (M n).data.hE (M n).hxs
    hlo hup hntarget (by simpa only [one_mul] using
      (div_le_iff₀ (sq_pos_of_pos (M n).hxs)).mp hnweak)).2.2.2.1

theorem theta_zero_omission_ratio_inherits_child_cutoff
    {m delta cl cu Az C0 Ct D Bclock c0:ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim:ℕ→ℕ) (hdim:Tendsto dim atTop atTop)
    (M:(n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (htarget:∀ᶠn in atTop,comparisonConditionalScale (M n).data.N delta
      (M n).data.E (M n).lam≤(M n).xs)
    (hweak:Tendsto (fun n=>laplaceComparisonStrength (M n).data.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hs:Tendsto (fun n=>(M n).data.s/comparisonLowerScale
      (M n).data.N (M n).data.E (M n).data.d) atTop (𝓝 0)):
    Tendsto (fun n=>(M n).data.s/
      actualChildCutoff (dim n+1) delta c0 (M n).data.d (M n).lam (M n).xs)
      atTop (𝓝 0):=by
  apply squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (M n).data.hs.1.le
    (actual_child_cutoff_pos_le_radius (M n).data.hN hc0
      (M n).hlam (M n).hxs).1.le)) _ hs
  filter_upwards [theta_zero_child_cutoff_inheritance hm hdelta hC0 hc0 hmargin
    dim hdim M htarget hweak] with n hn
  exact div_le_div_of_nonneg_left (M n).data.hs.1.le
    (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).data.hN) (M n).data.hE)
      (M n).data.hd) hn

end OAI.SKFluctuations.LaplaceWindowFormalization
