module

public import ComparisonCalibrationWeightedMass
public import FiniteProfileRigidity
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 3500000

theorem comparison_monotone_linear_limit_locally_uniform
    (q : ℕ → ℝ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hq : ∀n, MonotoneOn (q n) (Ioi (0 : ℝ)))
    (hlim : ∀v : ℝ, 0 < v → Tendsto (fun n => q n v) atTop (𝓝 (v/kappa))) :
    TendstoLocallyUniformlyOn q (fun v => v/kappa) atTop (Ioi (0 : ℝ)) := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro eps heps v hv
  change 0 < v at hv
  let d := min (v/2) (kappa*eps/8)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdv : d ≤ v/2 := min_le_left _ _
  have hde : d ≤ kappa*eps/8 := min_le_right _ _
  have hl : 0 < v-d := by linarith
  have hu : 0 < v+d := by linarith
  have hlow := (hlim (v-d) hl).eventually
    (lt_mem_nhds (show (v-d)/kappa-eps/2 < (v-d)/kappa by linarith))
  have hupp := (hlim (v+d) hu).eventually
    (gt_mem_nhds (show (v+d)/kappa < (v+d)/kappa+eps/2 by linarith))
  refine ⟨Ioo (v-d) (v+d),mem_nhdsWithin_of_mem_nhds
    (Ioo_mem_nhds (by linarith) (by linarith)),?_⟩
  filter_upwards [hlow,hupp] with n hnlo hnup w hw
  have hwpos : 0 < w := hl.trans hw.1
  have hlo := hq n hl hwpos hw.1.le
  have hup := hq n hwpos hu hw.2.le
  have hdq : 2*d/kappa ≤ eps/4 := (div_le_iff₀ hkappa).mpr (by nlinarith)
  have hwlo : w/kappa-(v-d)/kappa < 2*d/kappa := by
    rw [←sub_div]
    exact div_lt_div_of_pos_right (by linarith [hw.2]) hkappa
  have hwhi : (v+d)/kappa-w/kappa < 2*d/kappa := by
    rw [←sub_div]
    exact div_lt_div_of_pos_right (by linarith [hw.1]) hkappa
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

structure ComparisonShiftedInverseSequence where
  origin : ℕ → ℝ
  u0 : ℕ → ℝ
  c : ℕ → ℝ
  k : ℕ → ℝ → ℝ
  M : ℕ → ℝ → ℝ
  hwork : ∀n, origin n ≤ 1
  hc : ∀n, 0 < c n
  hk : ∀n, ContinuousOn (k n) (Icc (origin n) 1)
  hkc : ∀n r, r ∈ Icc (origin n) 1 → c n ≤ k n r
  hm : ∀n, MonotoneOn (M n) (Icc (0 : ℝ) 1)
  hM : ∀n, 0 ≤ M n 1
  alpha : (n : ℕ) → inverseIntegralConstraints (origin n) (u0 n) (k n) (M n)

namespace ComparisonShiftedInverseSequence

def radius (A : ComparisonShiftedInverseSequence) (n : ℕ) : ℝ → ℝ :=
  comparisonCalibrationConstrainedRadius (A.hwork n) (A.hc n) (A.hk n)
    (A.hkc n) (A.hm n) (A.hM n) (A.alpha n)

theorem radius_monotone (A : ComparisonShiftedInverseSequence) (n : ℕ) :
    Monotone (A.radius n) :=
  comparison_calibration_constrained_radius_monotone (A.hwork n) (A.hc n) (A.hk n)
    (A.hkc n) (A.hm n) (A.hM n) (A.alpha n)

theorem radius_inverse (A : ComparisonShiftedInverseSequence) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc (A.u0 n) 1) : (A.alpha n).val.val (A.radius n u) = u :=
  (comparison_calibration_constrained_radius_mass_spec (A.hwork n) (A.hc n) (A.hk n)
    (A.hkc n) (A.hm n) (A.hM n) (A.alpha n) hu).1

theorem rescaled_radius_monotone (A : ComparisonShiftedInverseSequence)
    (x : ℕ → ℝ) (hx : ∀n, 0 < x n) (n : ℕ) :
    Monotone (fun v => A.radius n (x n*v)/x n) := by
  intro u v huv
  exact div_le_div_of_nonneg_right
    (A.radius_monotone n (mul_le_mul_of_nonneg_left huv (hx n).le)) (hx n).le

theorem rescaled_mass_eventually_working (A : ComparisonShiftedInverseSequence)
    (x : ℕ → ℝ) (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    {v : ℝ} (hv : 0 < v) :
    ∀ᶠ n in atTop, x n*v ∈ Icc (A.u0 n) 1 := by
  have hlow := hu0.eventually (gt_mem_nhds hv)
  have hlim : Tendsto (fun n => x n*v) atTop (𝓝 0) := by simpa using hx0.mul_const v
  have hupp := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hlow,hupp] with n hnlo hnup
  exact ⟨by simpa only [mul_comm] using (div_lt_iff₀ (hx n)).mp hnlo |>.le,hnup.le⟩

theorem rescaled_inverse_tendsto (A : ComparisonShiftedInverseSequence)
    (x : ℕ → ℝ) {kappa v : ℝ} (hkappa : 0 < kappa) (hv : 0 < v)
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    (hCDF : ∀t : ℝ, 0 < t →
      Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n) atTop (𝓝 (kappa*t))) :
    Tendsto (fun n => A.radius n (x n*v)/x n) atTop (𝓝 (v/kappa)) := by
  let U := fun n t => (A.alpha n).val.val (x n*t)/x n
  have hmono n : Monotone (U n) := by
    intro s t hst
    exact div_le_div_of_nonneg_right
      ((A.alpha n).val.property.2 (mul_le_mul_of_nonneg_left hst (hx n).le)) (hx n).le
  apply quantile_tendsto_of_linear_cdf hkappa hv U _ hmono hCDF
  filter_upwards [A.rescaled_mass_eventually_working x hx hx0 hu0 hv] with n hn
  dsimp [U]
  have hcancel : x n*(A.radius n (x n*v)/x n)=A.radius n (x n*v) := by
    field_simp [(hx n).ne']
  rw [hcancel,A.radius_inverse n hn,mul_div_cancel_left₀ _ (hx n).ne']

theorem rescaled_inverse_locally_uniform (A : ComparisonShiftedInverseSequence)
    (x : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    (hCDF : ∀t : ℝ, 0 < t →
      Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n) atTop (𝓝 (kappa*t))) :
    TendstoLocallyUniformlyOn (fun n v => A.radius n (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0 : ℝ)) := by
  exact comparison_monotone_linear_limit_locally_uniform _ hkappa
    (fun n => (A.rescaled_radius_monotone x hx n).monotoneOn _)
    (fun _ hv => A.rescaled_inverse_tendsto x hkappa hv hx hx0 hu0 hCDF)

theorem rescaled_inverse_shell_bounds (A : ComparisonShiftedInverseSequence)
    (x : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    (hCDF : ∀t : ℝ, 0 < t →
      Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n) atTop (𝓝 (kappa*t))) :
    ∀ᶠ n in atTop, ∀v ∈ Icc (1/2 : ℝ) 1,
      x n/(4*kappa) ≤ A.radius n (x n*v) ∧ A.radius n (x n*v) ≤ 2*x n/kappa := by
  have hh := inverse_shell_bounds_eventually hkappa (fun n v => A.radius n (x n*v)/x n)
    (fun n => (A.rescaled_radius_monotone x hx n).monotoneOn _)
    (A.rescaled_inverse_tendsto x hkappa (by norm_num : (0 : ℝ) < 1/2) hx hx0 hu0 hCDF)
    (A.rescaled_inverse_tendsto x hkappa (by norm_num : (0 : ℝ) < 1) hx hx0 hu0 hCDF)
  filter_upwards [hh] with n hn v hv
  have hlo := (le_div_iff₀ (hx n)).mp (hn v hv).1
  have hup := (div_le_iff₀ (hx n)).mp (hn v hv).2
  constructor
  · convert hlo using 1
    ring
  · convert hup using 1
    ring

end ComparisonShiftedInverseSequence
end OAI.SKFluctuations.LaplaceWindowFormalization
