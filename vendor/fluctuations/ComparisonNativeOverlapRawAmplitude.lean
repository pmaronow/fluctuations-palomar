module

public import ComparisonNativeBroadFamilyAssembly
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalTerminalPairLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

structure NativeOverlapContext (n : ℕ) (delta : ℝ) where
  E : ℝ
  d : ℝ
  hn : 0< n
  hE : 0< E
  hd : 0< d

namespace NativeOverlapContext
abbrev N {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := (n:ℝ)
abbrev U {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := comparisonSmallMass c.N c.E
abbrev L {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := comparisonConstraintLength c.N c.E c.d
abbrev k {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := comparisonFloor c.N delta c.U
abbrev M {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := comparisonCap c.N delta c.U c.L c.E c.d
abbrev floor {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := c.k 1

theorem hN {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : 0< c.N := by exact_mod_cast c.hn
theorem hU {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : 0< c.U := comparisonSmallMass_pos c.hN c.hE
theorem hL {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : 0< c.L := comparisonConstraintLength_pos c.hN c.hE c.hd
theorem hc {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : 0< c.floor := comparisonFloor_pos c.hN c.hU (by norm_num)
theorem hk {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : ContinuousOn c.k (Icc (0:ℝ) 1) := comparisonFloor_continuousOn c.hN c.hU le_rfl
theorem hkc {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : ∀r∈Icc (0:ℝ) 1,c.floor≤ c.k r := fun r hr=>comparisonFloor_lower_on c.hN c.hU le_rfl hr
theorem hm {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : MonotoneOn c.M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn c.hN c.hU.le c.hL c.hE c.hd.le
theorem hM {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) : 0≤ c.M 1 := comparisonCap_nonneg c.hN c.hU.le c.hL c.hE c.hd.le zero_le_one
abbrev Profile {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) := inverseIntegralConstraints 0 0 c.k c.M
abbrev R {n : ℕ} {delta : ℝ} (c : NativeOverlapContext n delta) (α : c.Profile) := comparisonSweepQuantile c.hc c.hk c.hkc c.hm c.hM α
end NativeOverlapContext

structure NativeOverlapMinimum (n : ℕ) (m delta cl cu Az C0 Ct D Bclock : ℝ) where
  context : NativeOverlapContext n delta
  lam : ℝ
  hlam : 0< lam
  hld : lam≤ context.d^2
  alpha : context.Profile
  b : ℝ→ℝ
  h : ℝ→ℝ
  hb : MonotoneOn b (Icc (0:ℝ) 1)
  hlb : lam≤ b 0
  hh : MonotoneOn h (Icc (0:ℝ) 1)
  hh0 : 0≤ h 0
  minimum : ∀β:context.Profile,
    comparisonVariableEndpointObjective context.hc context.hk context.hkc context.hm context.hM
      n b h context.d lam alpha≤
    comparisonVariableEndpointObjective context.hc context.hk context.hkc context.hm context.hM
      n b h context.d lam β
  xs : ℝ
  z : ℝ
  hxs : 0< xs
  hscale : comparisonLowerScale n context.E context.d≤ xs
  hz : z∈Icc (0:ℝ) 1
  hzxs : z≤ Az*xs
  hdD : context.d≤ D
  hupper : Real.sqrt (n:ℝ)*context.E≤ context.d^2
  hlower : (n:ℝ)^(-(2:ℝ)/3+m)*context.d≤ C0*context.E
  htest : (n:ℝ)*context.E^2≤ Ct*laplaceComparisonStrength context.d lam xs*xs^2
  regular : ∀r∈Icc z 1,cl*r≤ alpha.val.val r ∧ alpha.val.val r≤ cu*r
  clockBudget :
    ((h 1+laplaceComparisonStrength context.d lam (context.R alpha 1)*context.R alpha 1).toNNReal:ℝ)-
    ((h 0+laplaceComparisonStrength context.d lam (context.R alpha 0)*context.R alpha 0).toNNReal:ℝ)≤ Bclock

namespace NativeOverlapMinimum
abbrev R {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) := a.context.R a.alpha
abbrev bf {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :=
  fun u=>(a.b u-laplaceComparisonStrength a.context.d a.lam (a.R u)).toNNReal
abbrev hf {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :=
  fun u=>(a.h u+laplaceComparisonStrength a.context.d a.lam (a.R u)*a.R u).toNNReal
end NativeOverlapMinimum

theorem eventually_native_comparison_B_normalized
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃K : ℝ,0< K ∧ ∀ᶠ n in atTop,
      ∀a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,orderedPathB n a.bf a.hf u≤ K*(a.xs+u)^2 := by
  obtain ⟨K,hK,hamp⟩ := comparison_minimum_retained_overlap_moment_normalized
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz (by norm_num : (0:ℝ)<1/3) hC0 hCt
  have hlog : ∀ᶠ n : ℕ in atTop,1≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp,eventually_comparisonLowerScale_depth hC0 hm,hlog,eventually_ge_atTop (1:ℕ)]
    with n hnamp hndepth hnlog hn1
  intro a u hu
  let c := a.context
  have hN1 : (1:ℝ)≤ c.N := by exact_mod_cast hn1
  have hnd : 1/c.N≤ c.d := by
    have hh := hndepth c.E c.d c.hE c.hd a.hlower
    have hs : comparisonLowerScale n c.E c.d≤ c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hh.trans hs
  let g := laplaceComparisonStrength c.d a.lam
  let hg := (laplaceComparisonStrength_contDiff c.d a.lam).continuous
  let ie := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one c.hc c.hk c.hkc c.hm c.hM g hg a.alpha)
  let iq := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one c.hc c.hk c.hkc c.hm c.hM (fun r=>g r*r)
      (hg.mul continuous_id) a.alpha)
  let bi := fun v=>(a.b v-ie v).toNNReal
  let hi := fun v=>(a.h v+iq v).toNNReal
  have had β := comparisonVariableEndpoint_inverse_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 β
  have hmin : ∀β:c.Profile,
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        g hg n a.b a.h 0 a.alpha≤
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        g hg n a.b a.h 0 β := by
    intro β
    have hh := a.minimum β
    rw [comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM n c.hn
        a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha,
      comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM n c.hn
        a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 β] at hh
    exact hh
  have hslow : ∀r∈Icc a.z 1,(1/3)/Real.log (n:ℝ)≤1-comparisonLogSlope g r := by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog c.hd hnd a.hlam a.hld
      (Icc_subset_Icc a.hz.1 le_rfl hr)
  have hclock : (hi 1:ℝ)-(hi 0:ℝ)≤ Bclock := by
    dsimp [hi,iq]
    rw [fullMassCoefficient_eq_sweepQuantile c.hc c.hk c.hkc c.hm c.hM _ _ a.alpha
        (show (1:ℝ)∈Icc (0:ℝ) 1 by simp),
      fullMassCoefficient_eq_sweepQuantile c.hc c.hk c.hkc c.hm c.hM _ _ a.alpha
        (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
    exact a.clockBudget
  let up : PositiveMass := ⟨u,hu.1⟩
  have hbMono : MonotoneOn bi (Icc (0:ℝ) 1) := toNNReal_monotoneOn (had a.alpha).1
  have hhMono : MonotoneOn hi (Icc (0:ℝ) 1) := toNNReal_monotoneOn (had a.alpha).2.1
  have hb0 := (had a.alpha).2.2.1
  have hh0 := (had a.alpha).2.2.2
  have hpoint := hnamp c.hn c.hE c.hd (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4))
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4)) g a.alpha
    (laplaceComparisonStrength_contDiff _ _) (fun r _=>laplaceComparisonStrength_pos c.d a.hlam r)
    (fun r _=>by
      have hp:=laplaceComparisonStrength_logSlope_mem c.hd.ne' a.hlam.ne' r
      exact ⟨hp.1,hp.2.le⟩)
    a.b a.h (fun β=>(had β).1) (fun β=>(had β).2.1)
    (fun β=>(had β).2.2.1) (fun β=>(had β).2.2.2) hmin up hu.2 a.xs a.z
    a.hxs a.hscale a.hxs.le c.hU.le a.hz a.hzxs a.hdD a.hupper a.hlower a.htest
    a.regular hslow a.hh hclock
  have hpair := orderedPathPair_eq_completed n c.hn bi hi hbMono hhMono
    (fun σ τ=>(orderedOverlap n σ τ)^2) hu
  have habs : (fun σ τ:Spin n=>|orderedOverlap n σ τ|^(2*(0+1)))=
      fun σ τ=>(orderedOverlap n σ τ)^2 := by funext σ τ;norm_num
  rw [habs] at hpoint
  rw [←hpair,comparisonVariableEndpoint_inverse_pair_eq c.hc c.hk c.hkc c.hm c.hM
    n c.hn a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha _ hu] at hpoint
  simpa only [orderedPathB,Nat.zero_add,Nat.mul_one] using hpoint

theorem native_comparison_thermal_intervalIntegrable
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2) volume 0 1 := by
  have had := comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk
    a.context.hkc a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le a.hlb
    a.hb a.hh a.hh0 a.alpha
  have he : n-1+1=n := by have hn:=a.context.hn;omega
  simpa only [he] using physicalOrderedThermal_intervalIntegrable (n-1) a.bf a.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)

private theorem native_comparison_low_mass_integral_of_actual_amplitude
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock K : ℝ}
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (hK : 0< K)
    (hamp : ∀u∈Ioc (0:ℝ) 1,orderedPathB n a.bf a.hf u≤ K*(a.xs+u)^2)
    {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    (∫u in 0..v,orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2)≤ K*(a.xs+v)^2*v := by
  have hi := (native_comparison_thermal_intervalIntegrable a).mono_set
    (by rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hv.2)
  have hbound : ∀ᵐ u∂volume.restrict (Icc (0:ℝ) v),
      orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2≤ K*(a.xs+v)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hne
    have hu0 : 0< u := lt_of_le_of_ne hu.1 hne.symm
    have hb := hamp u ⟨hu0,hu.2.trans hv.2⟩
    have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [a.hxs] : 0≤ a.xs+u) (add_le_add le_rfl hu.2) 2) hK.le
    linarith [sq_nonneg (orderedPathS n a.bf a.hf u)]
  have hb := intervalIntegral.integral_mono_ae_restrict hv.1 hi intervalIntegrable_const hbound
  simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_zero,mul_comm] using hb

theorem eventually_native_comparison_low_mass_thermal
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃K : ℝ,0< K ∧ ∀ᶠ n in atTop,
      ∀a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀v∈Icc (0:ℝ) 1,
        (∫u in 0..v,orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2)≤ K*(a.xs+v)^2*v := by
  obtain ⟨K,hK,hamp⟩ := eventually_native_comparison_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp] with n hn
  intro a v hv
  exact native_comparison_low_mass_integral_of_actual_amplitude a hK (hn a) hv

theorem eventually_native_comparison_initial_wall_thermal
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃K : ℝ,0< K ∧ ∀ᶠ n in atTop,
      ∀a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
        (∫u in 0..min (8*a.context.U) 1,orderedPathB n a.bf a.hf u-(orderedPathS n a.bf a.hf u)^2)≤
          8*K*(a.xs+8*a.context.U)^2*a.context.U := by
  obtain ⟨K,hK,harea⟩ := eventually_native_comparison_low_mass_thermal (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [harea] with n hn
  intro a
  have hU := a.context.hU
  have hv0 : 0≤ min (8*a.context.U) 1 := le_min (by positivity) zero_le_one
  have hh := hn a (min (8*a.context.U) 1) ⟨hv0,min_le_right _ _⟩
  have hs := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg a.hxs.le hv0)
      (add_le_add le_rfl (min_le_left _ _)) 2) hK.le
  have hp := mul_le_mul hs (min_le_left (8*a.context.U) 1) hv0
    (mul_nonneg hK.le (sq_nonneg _))
  have heq : (K*(a.xs+8*a.context.U)^2)*(8*a.context.U)=8*K*(a.xs+8*a.context.U)^2*a.context.U := by ring
  exact hh.trans (by simpa only [heq] using hp)

end OAI.SKFluctuations.LaplaceWindowFormalization
