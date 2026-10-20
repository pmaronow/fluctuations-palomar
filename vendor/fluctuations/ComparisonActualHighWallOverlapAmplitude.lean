module

public import ComparisonNativeOverlapRawAmplitude
public import ConcreteWallParameters
public import ActualWallMinimum
public import ActualMixedClockCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 7000000

structure ActualHighWallData (n : ℕ) (delta : ℝ) where
  E : ℝ
  d : ℝ
  s : ℝ
  T : ℝ
  epsilon : ℝ
  theta : ℝ
  tau : ℝ
  hn : 0 < n
  hE : 0 < E
  hd : 0 < d
  hd1 : d ≤ 1
  hs : s ∈ Ioc (0:ℝ) (1/4)
  hq : 2 ≤ (n:ℝ)^delta
  hsmall : comparisonSmallMass (n:ℝ) E ≤ d
  hepsilon : epsilon ∈ Ioo (0:ℝ) T
  htheta : theta ∈ Icc (0:ℝ) 1
  htau : 0 < tau
  hdepsilon : d^2 ≤ epsilon

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
abbrev N (_a : ActualHighWallData n delta) := (n:ℝ)
abbrev rmin := concreteWallRadius a.N delta a.E a.d a.s
abbrev k := concreteWallFloor a.N delta a.E
abbrev M := concreteWallCap a.N delta a.E a.d
abbrev g := laplaceComparisonStrength a.d (a.d^2)
theorem hN : 0 < a.N := Nat.cast_pos.mpr a.hn
theorem hrbounds : 0 < a.rmin ∧ a.rmin ≤ a.d/4 ∧ a.rmin ≤ 1/2 :=
  concreteWallRadius_bounds a.hN a.hE a.hd a.hd1 a.hs.1.le a.hq a.hsmall
theorem hr : a.rmin ≤ 1 := a.hrbounds.2.2.trans (by norm_num)
theorem hs1 : a.s ≤ 1 := a.hs.2.trans (by norm_num)
theorem hU : 0 < comparisonSmallMass a.N a.E := concreteWallSmallMass_pos a.hN a.hE
theorem hL : 0 < comparisonConstraintLength a.N a.E a.d :=
  concreteWallConstraintLength_pos a.hN a.hE a.hd
theorem hc : 0 < a.k 1 := comparisonFloor_pos a.hN a.hU (by norm_num)
theorem hk : ContinuousOn a.k (Icc a.rmin 1) :=
  comparisonFloor_continuousOn a.hN a.hU a.hrbounds.1.le
theorem hkc : ∀r∈Icc a.rmin 1,a.k 1 ≤ a.k r :=
  fun r hr => comparisonFloor_lower_on a.hN a.hU a.hrbounds.1.le hr
theorem hm : MonotoneOn a.M (Icc (0:ℝ) 1) :=
  comparisonCap_monotoneOn a.hN a.hU.le a.hL a.hE a.hd.le
theorem hM : 0 ≤ a.M 1 :=
  comparisonCap_nonneg a.hN a.hU.le a.hL a.hE a.hd.le zero_le_one
theorem hg : ContDiff ℝ 1 a.g := laplaceComparisonStrength_contDiff _ _
abbrev Profile := inverseIntegralConstraints a.rmin a.s a.k a.M
abbrev b (alpha : a.Profile) :=
  wallChangedMatrix a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta alpha
abbrev h (alpha : a.Profile) :=
  wallChangedField a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta a.tau a.d alpha
abbrev bf (alpha : a.Profile) := fun u => (a.b alpha u).toNNReal
abbrev hf (alpha : a.Profile) := fun u => (a.h alpha u).toNNReal
abbrev objective (alpha : a.Profile) :=
  wallObjective a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta a.tau a.d n 0 alpha

theorem admissible (alpha : a.Profile) :
    MonotoneOn (a.b alpha) (Icc (0:ℝ) 1) ∧
      MonotoneOn (a.h alpha) (Icc (0:ℝ) 1) ∧
      0 ≤ a.b alpha 0 ∧ 0 ≤ a.h alpha 0 := by
  have hgmono := laplaceComparisonStrength_monotonicities a.hd.ne' (sq_pos_of_pos a.hd)
    a.hrbounds.1.le
  exact wall_changed_clocks_admissible a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
    a.g a.hg.continuous a.hs.1 a.htau a.hrbounds.1.le a.hepsilon a.htheta a.hdepsilon
    (concreteWallStrength_initial a.hN a.hE a.hd a.hd1 a.hs.1.le a.hq a.hsmall)
    hgmono.1 hgmono.2 (fun r _ => laplaceComparisonStrength_le _ (sq_nonneg _) r) alpha

theorem bf_monotone (alpha : a.Profile) : MonotoneOn (a.bf alpha) (Icc (0:ℝ) 1) :=
  toNNReal_monotoneOn (a.admissible alpha).1
theorem hf_monotone (alpha : a.Profile) : MonotoneOn (a.hf alpha) (Icc (0:ℝ) 1) :=
  toNNReal_monotoneOn (a.admissible alpha).2.1

theorem clock_coe (alpha : a.Profile) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (a.bf alpha u:ℝ)=a.b alpha u ∧ (a.hf alpha u:ℝ)=a.h alpha u := by
  have hb := (a.admissible alpha).2.2.1.trans ((a.admissible alpha).1 (by norm_num) hu hu.1)
  have hh := (a.admissible alpha).2.2.2.trans ((a.admissible alpha).2.1 (by norm_num) hu hu.1)
  exact ⟨Real.coe_toNNReal _ hb,Real.coe_toNNReal _ hh⟩

theorem root_field_zero (alpha : a.Profile) : a.hf alpha 0=0 := by
  apply NNReal.coe_injective
  rw [(a.clock_coe alpha (by norm_num)).2]
  dsimp only [h]
  rw [wallChangedField_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta a.tau a.d alpha a.hs.1,wallPsi_zero,mul_zero]
  rfl

theorem total_clock_le (alpha : a.Profile) :
    ∀u∈Icc (0:ℝ) 1,(a.hf alpha u:ℝ)+(a.bf alpha u:ℝ) ≤ a.T := by
  intro u hu
  rw [(a.clock_coe alpha hu).1,(a.clock_coe alpha hu).2]
  dsimp only [b,h]
  by_cases hus : u<a.s
  · rw [wallChangedMatrix_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta alpha hus,
      wallChangedField_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta a.tau a.d alpha hus]
    have hamp := wall_low_amplitude_bound (d:=a.d) a.hepsilon a.htheta a.hrbounds.1.le
    have hpsi := wallPsi_mem a.hs.1 a.htau ⟨hu.1,hus.le⟩
    have hlow := mul_le_mul_of_nonneg_left hpsi.2 hamp.1
    have hr1 := a.hrbounds.2.2.trans (by norm_num : (1/2:ℝ) ≤ 1)
    have hds := mul_le_mul_of_nonneg_left hr1 (sq_nonneg a.d)
    have htheta := mul_nonneg a.htheta.1 (wallLowStrength_bounds a.hepsilon).1
    nlinarith [a.hdepsilon]
  · have huhi : u∈Icc a.s 1 := ⟨le_of_not_gt hus,hu.2⟩
    rw [wallChangedMatrix_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta alpha huhi,
      wallChangedField_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta a.tau a.d alpha huhi]
    have hq := (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,huhi⟩).property.2
    have hg := (laplaceComparisonStrength_pos a.d (sq_pos_of_pos a.hd)
      (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,huhi⟩)).le
    nlinarith [mul_le_mul_of_nonneg_left hq hg]

theorem low_field_cubic (alpha : a.Profile) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (hus : u<a.s) :
    (a.hf alpha u:ℝ) ≤ a.d^3/16 := by
  rw [(a.clock_coe alpha hu).2]
  dsimp only [h]
  rw [wallChangedField_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta a.tau a.d alpha hus]
  have hamp := wall_low_amplitude_bound (d:=a.d) a.hepsilon a.htheta a.hrbounds.1.le
  have hp := mul_le_mul_of_nonneg_left (wallPsi_mem a.hs.1 a.htau ⟨hu.1,hus.le⟩).2 hamp.1
  have hr := mul_le_mul_of_nonneg_left a.hrbounds.2.1 (sq_nonneg a.d)
  nlinarith

theorem high_bare_field_monotone :
    MonotoneOn (wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin) (Icc a.s 1) := by
  intro u hu v hv huv
  simp only [wallBareField,ite_eq_right (not_lt.mpr hu.1),ite_eq_right (not_lt.mpr hv.1)]
  exact le_rfl

theorem field_clock_budget (alpha : a.Profile) :
    (a.hf alpha 1:ℝ)-(a.hf alpha 0:ℝ) ≤ a.T := by
  have ht := a.total_clock_le alpha 1 (by norm_num)
  rw [a.root_field_zero alpha]
  simpa only [NNReal.coe_zero,sub_zero] using
    (show (a.hf alpha 1:ℝ) ≤ a.T by linarith [(a.bf alpha 1).coe_nonneg])

theorem exists_minimum : ∃alpha : a.Profile,∀beta : a.Profile,a.objective alpha≤a.objective beta := by
  have hgmono := laplaceComparisonStrength_monotonicities a.hd.ne' (sq_pos_of_pos a.hd)
    a.hrbounds.1.le
  exact wallObjective_minimum a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.hs.1 a.htau a.hrbounds.1.le a.hepsilon a.htheta a.hdepsilon
    (concreteWallStrength_initial a.hN a.hE a.hd a.hd1 a.hs.1.le a.hq a.hsmall)
    hgmono.1 hgmono.2 (fun r _ => laplaceComparisonStrength_le _ (sq_nonneg _) r)
    (concreteWallCap_continuous _ _ _ _)
    (concreteWallConstraints_nonempty a.hN a.hE a.hd a.hd1
      ⟨a.hs.1.le,a.hs.2.trans (by norm_num)⟩ a.hq a.hsmall) n a.hn 0

end ActualHighWallData

structure ActualHighWallOverlapMinimum
    (n : ℕ) (m delta cl cu Az C0 Ct D Bclock : ℝ) where
  data : ActualHighWallData n delta
  alpha : data.Profile
  minimum : ∀beta : data.Profile,data.objective alpha ≤ data.objective beta
  xs : ℝ
  z : ℝ
  hxs : 0 < xs
  hscale : comparisonLowerScale n data.E data.d ≤ xs
  hsxs : data.s ≤ xs
  hz : z∈Icc data.rmin 1
  hzxs : z ≤ Az*xs
  hdD : data.d ≤ D
  hupper : Real.sqrt (n:ℝ)*data.E ≤ data.d^2
  hlower : (n:ℝ)^(-(2:ℝ)/3+m)*data.d ≤ C0*data.E
  htest : (n:ℝ)*data.E^2 ≤ Ct*data.g xs*xs^2
  regular : ∀r∈Icc z 1,cl*r≤alpha.val.val r ∧ alpha.val.val r≤cu*r
  hT : data.T ≤ Bclock

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
abbrev bf := a.data.bf a.alpha
abbrev hf := a.data.hf a.alpha

theorem inverse_minimum :
    ∀beta : a.data.Profile,
      inverseCompensatedPressure a.data.hr a.data.hs1 a.data.hc a.data.hk a.data.hkc
        a.data.hm a.data.hM a.data.g a.data.hg.continuous n
        (wallBareMatrix a.data.T a.data.epsilon a.data.theta a.data.s)
        (wallBareField a.data.T a.data.epsilon a.data.theta a.data.s a.data.tau
          a.data.d a.data.rmin) 0 a.alpha ≤
      inverseCompensatedPressure a.data.hr a.data.hs1 a.data.hc a.data.hk a.data.hkc
        a.data.hm a.data.hM a.data.g a.data.hg.continuous n
        (wallBareMatrix a.data.T a.data.epsilon a.data.theta a.data.s)
        (wallBareField a.data.T a.data.epsilon a.data.theta a.data.s a.data.tau
          a.data.d a.data.rmin) 0 beta := by
  intro beta
  have h := a.minimum beta
  change _+_ ≤ _+_ at h
  exact (add_le_add_iff_right _).mp h

theorem radius_le_smallMass : a.data.rmin ≤ comparisonSmallMass a.data.N a.data.E := by
  have hcap := a.data.hq.trans (concreteWallCap_ge a.data.hN a.data.hE a.data.hd a.data.hs.1.le)
  change comparisonSmallMass a.data.N a.data.E/(2*a.data.M a.data.s) ≤ _
  apply (div_le_iff₀ (by linarith : 0 < 2*a.data.M a.data.s)).mpr
  nlinarith [a.data.hU]

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_overlap_moment_normalized
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠ n in atTop,
      ∀a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,
        pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n a.bf a.hf)
          (fun sigma tau => |orderedOverlap n sigma tau|^(2*(ell+1))) u ≤
          K*(a.xs+u)^(2*(ell+1)) := by
  obtain ⟨K,hK,hamp⟩ := comparison_minimum_retained_overlap_moment_normalized
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz (by norm_num : (0:ℝ)<1/3) hC0 hCt
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp,eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hnamp hndepth hnlog hn1
  intro a u hu
  let w := a.data
  have hN1 : (1:ℝ)≤w.N := by exact_mod_cast hn1
  have hnd : 1/w.N ≤ w.d := by
    have hh := hndepth w.E w.d w.hE w.hd a.hlower
    have hs : comparisonLowerScale n w.E w.d ≤ w.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ w.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hh.trans hs
  have hr0 : w.rmin∈Icc (0:ℝ) (1/4) :=
    ⟨w.hrbounds.1.le,w.hrbounds.2.1.trans (by linarith [w.hd1])⟩
  have hs0 : w.s∈Icc (0:ℝ) (1/4) := ⟨w.hs.1.le,w.hs.2⟩
  have hslow : ∀r∈Icc a.z 1,(1/3)/Real.log (n:ℝ) ≤ 1-comparisonLogSlope w.g r := by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog w.hd hnd
      (sq_pos_of_pos w.hd) le_rfl ⟨w.hrbounds.1.le.trans (a.hz.1.trans hr.1),hr.2⟩
  have hp : ∀r∈Ioc w.rmin 1,comparisonLogSlope w.g r∈Icc (0:ℝ) 1 := by
    intro r hr
    exact ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' (sq_pos_of_pos w.hd).ne' r).1,
      (laplaceComparisonStrength_logSlope_mem w.hd.ne' (sq_pos_of_pos w.hd).ne' r).2.le⟩
  have hpoint := hnamp w.hn w.hE w.hd hr0 hs0 w.g a.alpha w.hg
    (fun r _ => laplaceComparisonStrength_pos w.d (sq_pos_of_pos w.hd) r) hp
    (wallBareMatrix w.T w.epsilon w.theta w.s)
    (wallBareField w.T w.epsilon w.theta w.s w.tau w.d w.rmin)
    (fun beta => (w.admissible beta).1) (fun beta => (w.admissible beta).2.1)
    (fun beta => (w.admissible beta).2.2.1) (fun beta => (w.admissible beta).2.2.2)
    a.inverse_minimum ⟨u,hu.1⟩ hu.2 a.xs a.z a.hxs a.hscale a.hsxs
    a.radius_le_smallMass a.hz a.hzxs a.hdD a.hupper a.hlower a.htest a.regular hslow
    w.high_bare_field_monotone ((w.field_clock_budget a.alpha).trans a.hT)
  change pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n a.bf a.hf)
    (fun sigma tau => |orderedOverlap n sigma tau|^(2*(ell+1))) u ≤
      K*(a.xs+u)^(2*(ell+1)) at hpoint
  exact hpoint

theorem eventually_actual_high_wall_B_normalized
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠ n in atTop,
      ∀a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,orderedPathB n a.bf a.hf u ≤ K*(a.xs+u)^2 := by
  obtain ⟨K,hK,hamp⟩ := eventually_actual_high_wall_overlap_moment_normalized
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp] with n hn
  intro a u hu
  have hpoint := hn a u hu
  have hpair := orderedPathPair_eq_completed n a.data.hn a.bf a.hf
    (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha)
    (fun sigma tau => (orderedOverlap n sigma tau)^2) hu
  have habs : (fun sigma tau : Spin n => |orderedOverlap n sigma tau|^(2*(0+1)))=
      fun sigma tau => (orderedOverlap n sigma tau)^2 := by
    funext sigma tau
    norm_num
  rw [habs,←hpair] at hpoint
  simpa only [orderedPathB,Nat.zero_add,Nat.mul_one] using hpoint

theorem eventually_actual_high_wall_omitted_clock_amplitude
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠ n in atTop,
      ∀a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.xs ≤ a.data.d → ∀u∈Ioo (0:ℝ) a.data.s,
        orderedPathS n a.bf a.hf u ≤ C*a.data.d ∧
        Real.sqrt (orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2) ≤ C*a.data.d ∧
        actualMixedClock n a.bf a.hf u ≤ (1/16+Bclock*C)*a.data.d := by
  obtain ⟨K,hK,hamp⟩ := eventually_actual_high_wall_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C := 2*Real.sqrt K
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hamp] with n hn
  intro a hxsD u hu
  let w := a.data
  have hu1 : u∈Ioc (0:ℝ) 1 := ⟨hu.1,hu.2.le.trans w.hs1⟩
  have hucc : u∈Icc (0:ℝ) 1 := ⟨hu1.1.le,hu1.2⟩
  have hSK := orderedPath_SK_bounds n w.hn a.bf a.hf
    (w.bf_monotone a.alpha) (w.hf_monotone a.alpha) hu1
  have hsum : a.xs+u ≤ 2*w.d := by linarith [hu.2,a.hsxs]
  have hsum0 : 0 ≤ a.xs+u := by linarith [a.hxs,hu.1]
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  have hB := (hn a u hu1).trans (mul_le_mul_of_nonneg_left hsq hK.le)
  have hCeq : C^2=4*K := by dsimp only [C];nlinarith [Real.sq_sqrt hK.le]
  have hS : orderedPathS n a.bf a.hf u ≤ C*w.d := by
    nlinarith [hSK.2.2.1,mul_pos hC w.hd]
  have hD : Real.sqrt (orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2) ≤ C*w.d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(mul_pos hC w.hd).le,?_⟩
    nlinarith [sq_nonneg (orderedPathS n a.bf a.hf u)]
  have hfield := w.low_field_cubic a.alpha hucc hu.2
  have htotal := w.total_clock_le a.alpha u hucc
  have hb : (a.bf u:ℝ) ≤ Bclock := by
    have ht : w.T≤Bclock := a.hT
    nlinarith [(a.hf u).coe_nonneg]
  have hproduct := mul_le_mul hb hS hSK.1
    (show 0≤Bclock from (a.bf u).coe_nonneg.trans hb)
  have hd3 : w.d^3≤w.d := by
    have hd2 := mul_le_mul_of_nonneg_left w.hd1 w.hd.le
    have hd3 := mul_le_mul_of_nonneg_left hd2 w.hd.le
    nlinarith [w.hd1]
  refine ⟨hS,hD,?_⟩
  unfold actualMixedClock
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
