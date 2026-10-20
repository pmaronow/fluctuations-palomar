module

public import ComparisonActualHighWallFixedCovarianceMargins
public import ComparisonActualHighWallChildClockIncrements
public import ComparisonNativeActualComparableBandClocks
public import ComparisonNativeActualChildParameterGrowth
public import ComparisonActualConcreteHighWallAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unnecessarySimpa false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

 theorem wall_radius_le_regular_cap
    (P : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc P.data.s 1) :
    P.data.wallRadius P.alpha u ≤ P.z+u/cl := by
  have hR:=P.data.wallRadius_bounds P.alpha u
  have hspec:=P.data.wallRadius_spec P.alpha hu
  by_cases hz : P.z ≤ P.data.wallRadius P.alpha u
  · have H:=(P.regular _ ⟨hz,hR.2⟩).1
    rw [hspec] at H
    have Hdiv : P.data.wallRadius P.alpha u ≤ u/cl :=
      (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using H)
    linarith [P.hz.1,P.data.hrbounds.1]
  · have Hdiv : 0 ≤ u/cl:=div_nonneg (P.data.hs.1.le.trans hu.1) hcl.le
    linarith [le_of_not_ge hz]

 theorem high_clock_formula
    (P : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc P.data.s 1) :
    |P.data.b P.alpha u-P.data.T|=P.data.g (P.data.wallRadius P.alpha u) ∧
      |P.data.h P.alpha u|=P.data.g (P.data.wallRadius P.alpha u)*P.data.wallRadius P.alpha u := by
  have hR:=P.data.wallRadius_bounds P.alpha u
  have hg : 0 ≤ P.data.g (P.data.wallRadius P.alpha u):=
    (laplaceComparisonStrength_pos _ (sq_pos_of_pos P.data.hd) _).le
  have hfield:=P.data.high_field_clock P.alpha hu
  rw [(P.data.clock_coe P.alpha ⟨P.data.hs.1.le.trans hu.1,hu.2⟩).2] at hfield
  constructor
  · dsimp only [ActualHighWallData.b]
    rw [wallChangedMatrix_on P.data.hr P.data.hs1 P.data.hc P.data.hk P.data.hkc
      P.data.hm P.data.hM P.data.g P.data.hg.continuous
      P.data.T P.data.epsilon P.data.theta P.alpha hu]
    have he : P.data.wallRadius P.alpha u=(constrainedQuantile P.data.hr P.data.hc
      P.data.hk P.data.hkc P.data.hm P.data.hM P.alpha ⟨u,hu⟩:ℝ) := by
      unfold ActualHighWallData.wallRadius comparisonCalibrationConstrainedRadius
      rw [IccExtend_of_mem _ _ hu]
      rfl
    rw [←he]
    simpa only [sub_sub_cancel_left,abs_neg,abs_of_nonneg hg]
  · rw [hfield,abs_of_nonneg (mul_nonneg hg (P.data.hrbounds.1.le.trans hR.1))]

end ActualHighWallOverlapMinimum

 theorem eventually_actual_wall_child_positive_band_increments
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) {eta Cmass : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hCmass : 0 ≤ Cmass)
    (hmargin : 0 < 9*m-298*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      x∈Ioc (0:ℝ) 1 → comparisonConditionalScale P.data.N delta P.data.E (P.data.d^2) ≤ x →
      P.data.g x ≤ (eta*c0)^3*x^2 → P.z ≤ Az*x →
      ∀y : ℝ,actualChildCutoff n delta c0 P.data.d (P.data.d^2) x ≤ y →
      ∀u∈Icc P.data.s (min (Cmass*y) 1),
        |P.data.b P.alpha u-P.data.T| ≤ eta^2*y^2 ∧
        |P.data.h P.alpha u| ≤ max 1 (Az+Cmass/cl)*eta^2*y^3 := by
  let C:=max 1 (Az+Cmass/cl)
  have hC : 1 ≤ C:=le_max_left _ _
  have hC0' : 0 ≤ C:=zero_le_one.trans hC
  filter_upwards [eventually_actual_child_numeric_clock_increments_from_target
    hdelta hC0 hc0 hc01 heta heta1 hC hmargin] with n hn
  intro P x hx htarget hweak hz y hay u hu
  have hlo : (1/C0)*P.data.N^(-(2:ℝ)/3+m)*P.data.d ≤ P.data.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using P.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : P.data.E ≤ P.data.d^2/Real.sqrt n :=
    (le_div_iff₀ (Real.sqrt_pos.mpr P.data.hN)).mpr (by simpa only [mul_comm] using P.hupper)
  have Hnum:=hn P.data.d (P.data.d^2) P.data.E x P.data.hd
    (sq_pos_of_pos P.data.hd) le_rfl P.data.hE hlo hup hx htarget hweak
  let a:=actualChildCutoff n delta c0 P.data.d (P.data.d^2) x
  have ha : 0 < a:=(actual_child_cutoff_pos_le_radius P.data.hN hc0
    (sq_pos_of_pos P.data.hd) hx.1).1
  have hy : 0 < y:=ha.trans_le hay
  have hu1 : u∈Icc P.data.s 1:=⟨hu.1,hu.2.trans (min_le_right _ _)⟩
  have huCy : u ≤ Cmass*y:=hu.2.trans (min_le_left _ _)
  have hrwall:=P.data.wallRadius_bounds P.alpha u
  have hr : P.data.wallRadius P.alpha u∈Icc (0:ℝ) 1:=
    ⟨P.data.hrbounds.1.le.trans hrwall.1,hrwall.2⟩
  have Hzero:=Hnum 0 (by norm_num) (mul_nonneg hC0' hx.1.le)
  have hlam : P.data.d^2 ≤ eta^2*a^2 := by
    simpa only [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape,
      mul_zero,zero_div,ite_eq_left (by norm_num : (0:ℝ) ≤ 1),mul_one] using Hzero.1
  have Hg : P.data.g (P.data.wallRadius P.alpha u) ≤ eta^2*y^2 :=
    (laplaceComparisonStrength_le P.data.d (sq_nonneg P.data.d) _).trans
      (hlam.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hay 2) (sq_nonneg eta)))
  rw [(P.high_clock_formula hu1).1,(P.high_clock_formula hu1).2]
  refine ⟨Hg,?_⟩
  have Hr : P.data.wallRadius P.alpha u ≤ Az*x+(Cmass/cl)*y := by
    have H:=P.wall_radius_le_regular_cap hcl hu1
    have Hdiv : u/cl ≤ (Cmass/cl)*y := by
      convert div_le_div_of_nonneg_right huCy hcl.le using 1
      ring
    linarith only [H,Hdiv,hz]
  by_cases hyx : y ≤ x
  · have HrCx : P.data.wallRadius P.alpha u ≤ C*x := by
      have H:=mul_le_mul_of_nonneg_left hyx (div_nonneg hCmass hcl.le)
      have H':=mul_le_mul_of_nonneg_right (le_max_right 1 (Az+Cmass/cl)) hx.1.le
      nlinarith only [Hr,H,H']
    have HH:=(Hnum (P.data.wallRadius P.alpha u) hr HrCx).2
    have Hpow:=pow_le_pow_left₀ ha.le hay 3
    have Het : eta^3 ≤ eta^2 := by
      have H:=mul_le_mul_of_nonneg_left heta1 (sq_nonneg eta)
      nlinarith only [H]
    have H1:=mul_le_mul_of_nonneg_left Hpow (mul_nonneg hC0' (pow_nonneg heta.le 3))
    have H2:=mul_le_mul_of_nonneg_left Het (mul_nonneg hC0' (pow_nonneg hy.le 3))
    change P.data.g (P.data.wallRadius P.alpha u)*P.data.wallRadius P.alpha u ≤ C*eta^2*y^3
    nlinarith only [HH,H1,H2]
  · have HrCy : P.data.wallRadius P.alpha u ≤ C*y := by
      have H:=mul_le_mul_of_nonneg_left (le_of_not_ge hyx) hAz
      have H':=mul_le_mul_of_nonneg_right (le_max_right 1 (Az+Cmass/cl)) hy.le
      nlinarith only [Hr,H,H']
    have H:=mul_le_mul Hg HrCy hr.1 (by positivity : 0 ≤ eta^2*y^2)
    change P.data.g (P.data.wallRadius P.alpha u)*P.data.wallRadius P.alpha u ≤ C*eta^2*y^3
    nlinarith only [H]

 def SequentialComparableBareClocks (a : ℕ→ℝ) (b h : ℕ→ℝ→ℝ) (T : ℝ) : Prop :=
  ∀y : ℕ→ℝ,Tendsto y atTop (𝓝 0) → (∀ᶠn in atTop,a n ≤ y n) →
    ∀c C epsilon : ℝ,0 < c → 0 ≤ C → 0 < epsilon → ∀ᶠn in atTop,
      ∀u∈Icc (c*y n) (min (C*y n) 1),
        |b n u-T| ≤ epsilon*(y n)^2 ∧ |h n u| ≤ epsilon*(y n)^3

 theorem actual_wall_first_child_comparable_bare_clocks
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n)) atTop (𝓝 0)) :
    SequentialComparableBareClocks
      (fun n=>actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n))
      (fun n=>(P n).data.b (P n).alpha) (fun n=>(P n).data.h (P n).alpha) T := by
  intro y hy hay c Cmass epsilon hc hCmass heps
  let C:=max 1 (Az+Cmass/cl)
  let eta:=min 1 (epsilon/(C+1))
  have hC : 1 ≤ C:=le_max_left _ _
  have hC0' : 0 ≤ C:=zero_le_one.trans hC
  have heta : 0 < eta:=lt_min zero_lt_one (div_pos heps (by positivity))
  have heta1 : eta ≤ 1:=min_le_left _ _
  have Het : eta*(C+1) ≤ epsilon:=
    (le_div_iff₀ (by positivity : 0 < C+1)).mp (min_le_right _ _)
  have Het2 : eta^2 ≤ eta := by nlinarith
  have hsave : eta^2 ≤ epsilon ∧ C*eta^2 ≤ epsilon := by
    have H:=mul_le_mul_of_nonneg_left Het2 hC0'
    constructor <;> nlinarith only [Het,Het2,H,heta.le,hC,mul_nonneg heta.le hC0']
  have Hweak:=hweak.eventually (gt_mem_nhds (pow_pos (mul_pos heta hc0) 3))
  have Hs:=hs.eventually (eventually_le_nhds hc)
  have hdim1 : Tendsto (fun n=>dim n+1) atTop atTop:=
    (tendsto_add_atTop_nat 1).comp hdim
  filter_upwards [hdim1.eventually (eventually_actual_wall_child_positive_band_increments
    hdelta hcl hAz hC0 hc0 hc01 heta heta1 hCmass hmargin),
    Hweak,Hs,hxunit,htarget,hcap,hay,hT] with n hn hnweak hnS hnunit hntarget hncap hny hnT
  intro u hu
  have ha : 0 < actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n):=
    (actual_child_cutoff_pos_le_radius (P n).data.hN hc0 (sq_pos_of_pos (P n).data.hd) (hx n)).1
  have hypos : 0 < y n:=ha.trans_le hny
  have hsy : (P n).data.s ≤ c*y n :=
    ((div_le_iff₀ ha).mp hnS).trans (mul_le_mul_of_nonneg_left hny hc.le)
  have Hweak' : (P n).data.g (x n) ≤ (eta*c0)^3*(x n)^2 :=
    (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le
  have H:=hn (P n) (x n) ⟨hx n,hnunit⟩ hntarget Hweak' hncap (y n) hny u ⟨hsy.trans hu.1,hu.2⟩
  rw [hnT] at H
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right hsave.1 (sq_nonneg (y n))),
    H.2.trans (mul_le_mul_of_nonneg_right hsave.2 (pow_nonneg hypos.le 3))⟩

 theorem SequentialComparableBareClocks.toNative
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
    {a : ℕ→ℝ} {b h : ℕ→ℝ→ℝ}
    (H : SequentialComparableBareClocks a b h T)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (ha : ∀ᶠn in atTop,a n ≤ comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d)
    (hb : ∀ᶠn in atTop,∀u,(M n).b u=b n u)
    (hh : ∀ᶠn in atTop,∀u,(M n).h u=h n u) :
    NativeOverlapMinimum.NativeSequentialComparableBandClocks M T := by
  intro y hy hay c C epsilon hc hC hepsilon
  have hay' : ∀ᶠn in atTop,a n ≤ y n := by
    filter_upwards [ha,hay] with n hn hn'
    exact hn.trans hn'
  filter_upwards [H y hy hay' c C epsilon hc hC hepsilon,hb,hh] with n hn hnb hnh
  simpa only [hnb,hnh] using hn

 theorem actual_wall_child_cutoff_inheritance
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0)) :
    ∀ᶠn in atTop,comparisonLowerScale (P n).data.N (P n).data.E (P n).data.d ≤
      actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n) := by
  have Hweak:=hweak.eventually (eventually_le_nhds zero_lt_one)
  have hdim1 : Tendsto (fun n=>dim n+1) atTop atTop:=
    (tendsto_add_atTop_nat 1).comp hdim
  filter_upwards [hdim1.eventually (eventually_actual_child_parameters_from_target
    hm hdelta (one_div_pos.mpr hC0) hc0 hmargin),Hweak,htarget] with n hn hnweak hntarget
  have hlo : (1/C0)*(P n).data.N^(-(2:ℝ)/3+m)*(P n).data.d ≤ (P n).data.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using (P n).hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : (P n).data.E ≤ (P n).data.d^2/Real.sqrt (dim n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (P n).data.hN)).mpr
      (by simpa only [mul_comm] using (P n).hupper)
  exact (hn (P n).data.d ((P n).data.d^2) (P n).data.E (x n)
    (P n).data.hd (sq_pos_of_pos (P n).data.hd) le_rfl (P n).data.hE (hx n) hlo hup hntarget
    (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak)).2.2.2.1

 theorem actual_wall_omission_ratio_inherits_child_cutoff
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(P n).data.s/
      comparisonLowerScale (P n).data.N (P n).data.E (P n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (x n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (P n).data.hs.1.le
    (actual_child_cutoff_pos_le_radius (P n).data.hN hc0
      (sq_pos_of_pos (P n).data.hd) (hx n)).1.le)) _ hs
  filter_upwards [actual_wall_child_cutoff_inheritance hm hdelta hC0 hc0 hmargin
    dim hdim P x hx htarget hweak] with n hn
  exact div_le_div_of_nonneg_left (P n).data.hs.1.le
    (div_pos (mul_pos (Real.sqrt_pos.mpr (P n).data.hN) (P n).data.hE) (P n).data.hd) hn

 theorem concrete_wall_omission_ratio_tendsto_zero
    {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n : ℕ=>wallHighMass m n/
      comparisonLowerScale (n:ℝ) (wallHighError m n) (wallHighD m n)) atTop (𝓝 0) := by
  have H:=(tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<5) hm)).comp
    tendsto_natCast_atTop_atTop
  apply H.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  simp only [Function.comp_apply]
  rw [wallHighLowerScale_eq m (by omega)]
  unfold wallHighMass
  rw [←Real.rpow_sub (by exact_mod_cast (show 0<n by omega))]
  congr 1
  ring

 theorem actual_concrete_wall_first_child_comparable_bare_clocks
    {m cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hE : ∀ᶠn in atTop,(P n).data.E=wallHighError m (dim n+1))
    (hd : ∀ᶠn in atTop,(P n).data.d=wallHighD m (dim n+1))
    (hs : ∀ᶠn in atTop,(P n).data.s=wallHighMass m (dim n+1))
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N (m/10000)
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0)) :
    SequentialComparableBareClocks
      (fun n=>actualChildCutoff (dim n+1) (m/10000) c0 (P n).data.d ((P n).data.d^2) (x n))
      (fun n=>(P n).data.b (P n).alpha) (fun n=>(P n).data.h (P n).alpha) T := by
  have hdelta : 0 < m/10000:=by positivity
  have Hratio : Tendsto (fun n=>(P n).data.s/
      comparisonLowerScale (P n).data.N (P n).data.E (P n).data.d) atTop (𝓝 0) := by
    apply ((concrete_wall_omission_ratio_tendsto_zero hm).comp
      ((tendsto_add_atTop_nat 1).comp hdim)).congr'
    filter_upwards [hE,hd,hs] with n hnE hnd hns
    simp only [Function.comp_apply,hnE,hnd,hns,ActualHighWallData.N]
  exact actual_wall_first_child_comparable_bare_clocks hdelta hcl hAz hC0 hc0 hc01
    (by linarith) dim hdim P hT x hx hxunit htarget hcap hweak
    (actual_wall_omission_ratio_inherits_child_cutoff hm hdelta hC0 hc0 (by linarith)
      dim hdim P x hx htarget hweak Hratio)

end OAI.SKFluctuations.LaplaceWindowFormalization
