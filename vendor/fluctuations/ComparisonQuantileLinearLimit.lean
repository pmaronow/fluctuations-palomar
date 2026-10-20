module

public import ComparisonGlobalClockLawIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 3500000

theorem comparison_quantile_cdf_ge_of_clock_le (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    {t v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hclock : q v ≤ t) :
    v ≤ (quantileMassProfile q hqb).val t := by
  rw [quantileMassProfile_cdf q hq hqb]
  have hsub : Iic (⟨v,hv⟩ : ParisiFinite.OrderPoint) ⊆
      {u : ParisiFinite.OrderPoint | q (u : ℝ) ≤ t} := by
    intro u hu
    exact (hq u.property hv hu).trans hclock
  have hm := measureReal_mono (μ := (uniformOrderMass : Measure ParisiFinite.OrderPoint)) hsub
  have he : (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      (Iic (⟨v,hv⟩ : ParisiFinite.OrderPoint)) = v := by
    change (volume (Iic (⟨v,hv⟩ : ParisiFinite.OrderPoint))).toReal = v
    rw [unitInterval.volume_Iic,ENNReal.toReal_ofReal hv.1]
  exact he.symm.trans_le hm

theorem comparison_quantile_tendsto_of_linear_law
    (q : ℕ → ℝ → ℝ) (x : ℕ → ℝ) {kappa v : ℝ}
    (hq : ∀n, MonotoneOn (q n) (Icc (0 : ℝ) 1))
    (hqb : ∀n u, u ∈ Icc (0 : ℝ) 1 → q n u ∈ Icc (0 : ℝ) 1)
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hkappa : 0 < kappa) (hv : 0 < v)
    (hCDF : ∀t > 0, Tendsto (fun n => (quantileMassProfile (q n) (hqb n)).val (x n*t)/x n)
      atTop (𝓝 (kappa*t))) :
    Tendsto (fun n => q n (x n*v)/x n) atTop (𝓝 (v/kappa)) := by
  have htarget : 0 < v/kappa := div_pos hv hkappa
  have hvalue : kappa*(v/kappa)=v := by field_simp
  have hsmall : ∀ᶠ n in atTop, x n*v ∈ Icc (0 : ℝ) 1 := by
    have ht : Tendsto (fun n => x n*v) atTop (𝓝 0) := by simpa using hx0.mul_const v
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    exact ⟨mul_nonneg (hx n).le hv.le,hn.le⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let t := (max 0 a+v/kappa)/2
    have hmax : max 0 a < v/kappa := max_lt htarget ha
    have htpos : 0 < t := by dsimp [t]; linarith [le_max_left 0 a]
    have hat : a < t := by dsimp [t]; linarith [le_max_right 0 a]
    have htq : t < v/kappa := by dsimp [t]; linarith
    have hlt : kappa*t < v := by nlinarith
    filter_upwards [hsmall,(hCDF t htpos).eventually (gt_mem_nhds hlt)] with n hn hnt
    have hqt : x n*t < q n (x n*v) := by
      by_contra hh
      have hc := comparison_quantile_cdf_ge_of_clock_le (q n) (hq n) (hqb n) hn (not_lt.mp hh)
      have hc' := div_le_div_of_nonneg_right hc (hx n).le
      rw [mul_div_cancel_left₀ _ (hx n).ne'] at hc'
      linarith
    exact hat.trans ((lt_div_iff₀ (hx n)).mpr (by simpa only [mul_comm] using hqt))
  · intro a ha
    let t := (a+v/kappa)/2
    have htpos : 0 < t := by dsimp [t]; linarith
    have hqt : v/kappa < t := by dsimp [t]; linarith
    have hta : t < a := by dsimp [t]; linarith
    have hgt : v < kappa*t := by nlinarith
    filter_upwards [hsmall,(hCDF t htpos).eventually (lt_mem_nhds hgt)] with n hn hnt
    have hqt' : q n (x n*v) ≤ x n*t := by
      by_contra hh
      have hc := quantileMassProfile_le_of_larger_clock (q n) (hq n) (hqb n) hn (not_le.mp hh)
      have hc' := div_le_div_of_nonneg_right hc (hx n).le
      rw [mul_div_cancel_left₀ _ (hx n).ne'] at hc'
      linarith
    exact ((div_le_iff₀ (hx n)).mpr (by simpa only [mul_comm] using hqt')).trans_lt hta

theorem comparison_eventually_monotone_linear_limit_locally_uniform
    (q : ℕ → ℝ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hq : ∀R > 0, ∀ᶠ n in atTop, MonotoneOn (q n) (Icc (0 : ℝ) R))
    (hlim : ∀v > 0, Tendsto (fun n => q n v) atTop (𝓝 (v/kappa))) :
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
  filter_upwards [hlow,hupp,hq (v+d) hu] with n hnlo hnup hnmono w hw
  have hww : w ∈ Icc (0 : ℝ) (v+d) := ⟨by linarith [hw.1],hw.2.le⟩
  have hlo := hnmono ⟨hl.le,by linarith⟩ hww hw.1.le
  have hup := hnmono hww ⟨hu.le,le_rfl⟩ hw.2.le
  have hdq : 2*d/kappa ≤ eps/4 := (div_le_iff₀ hkappa).mpr (by nlinarith)
  have hwlo : w/kappa-(v-d)/kappa < 2*d/kappa := by
    rw [←sub_div]
    exact div_lt_div_of_pos_right (by linarith [hw.2]) hkappa
  have hwhi : (v+d)/kappa-w/kappa < 2*d/kappa := by
    rw [←sub_div]
    exact div_lt_div_of_pos_right (by linarith [hw.1]) hkappa
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem comparison_quantile_locally_uniform_of_linear_law
    (q : ℕ → ℝ → ℝ) (x : ℕ → ℝ) {kappa : ℝ}
    (hq : ∀n, MonotoneOn (q n) (Icc (0 : ℝ) 1))
    (hqb : ∀n u, u ∈ Icc (0 : ℝ) 1 → q n u ∈ Icc (0 : ℝ) 1)
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hkappa : 0 < kappa)
    (hCDF : ∀t > 0, Tendsto (fun n => (quantileMassProfile (q n) (hqb n)).val (x n*t)/x n)
      atTop (𝓝 (kappa*t))) :
    TendstoLocallyUniformlyOn (fun n v => q n (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0 : ℝ)) := by
  apply comparison_eventually_monotone_linear_limit_locally_uniform _ hkappa ?_
    (fun _ hv => comparison_quantile_tendsto_of_linear_law q x hq hqb hx hx0 hkappa hv hCDF)
  intro R hR
  have ht : Tendsto (fun n => x n*R) atTop (𝓝 0) := by simpa using hx0.mul_const R
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  intro u hu v hv huv
  have hb s (hs : s ∈ Icc (0 : ℝ) R) : x n*s ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hx n).le hs.1,(mul_le_mul_of_nonneg_left hs.2 (hx n).le).trans hn.le⟩
  exact div_le_div_of_nonneg_right
    (hq n (hb u hu) (hb v hv) (mul_le_mul_of_nonneg_left huv (hx n).le)) (hx n).le

end OAI.SKFluctuations.LaplaceWindowFormalization
