module

public import ComparisonSignedCavityRestBoundarySchedule
public import ComparisonSignedCavityObservedStarClockTransport
public import ComparisonSignedCavityObservedCalibrationScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem eventually_actual_rest_all_high_resampling_from_raw
    (ell : ℕ) (Bclock Ccal Rmacro F Craw : ℝ) (hCraw : 0 ≤ Craw)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.xs^2 ≤ Ccal^2*laplaceComparisonStrength a.context.d a.lam a.xs→
      ∀us : List PositiveMass,(∀v∈us,v.val ≤ 1)→
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(a.bf (partitionPoint 0 as j):ℝ)) (fun _=>(a.hf (partitionPoint 0 as j):ℝ))
        let Q:=fun j=>restFiniteRealVariance n (q j)
        let steps:=nativeSampledPhysicalSteps n a.bf a.hf as
        let W:=max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))
        (physicalRawRatio n (ell+1) steps 0 a.xs
          (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (Q 0 i)))) id measurable_id)^2 ≤ Craw→
        ∀(low high : ℕ),high ≤ as.length→W ≤ Rmacro/2→
          4*W ≤ a.R (partitionPoint 0 as high)→
          a.z ≤ min (a.R (partitionPoint 0 as high)/8) (Rmacro/4)→
          a.R (partitionPoint 0 as low) ≤ min (a.R (partitionPoint 0 as high)/8) (Rmacro/4)→
          originalBoundaryResamplingMoment n (ell+1) as Q low high ≤ 
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*a.xs) W
              (partitionPoint 0 as high))^(2*(ell+1)) := by
  let ce := 1/Ccal^3
  let A := (((1:ℝ)/6)/Real.log 2+4)^4
  let Hsmall := 4*cu*F/(cl/8)^2
  let Hmacro := F/((cl/8)^2*(Rmacro/2))
  let H₀ := max Hsmall Hmacro
  have hCcalpos : 0 < Ccal := zero_lt_one.trans_le hCcal
  have hce : 0 < ce := by dsimp [ce];positivity
  have hF : 0 ≤ F := by linarith
  have hHsmall : 0 ≤ Hsmall := by dsimp [Hsmall];positivity
  have hHmacro : 0 ≤ Hmacro := by dsimp [Hmacro];positivity
  have hH₀ : 0 ≤ H₀ := hHsmall.trans (le_max_left _ _)
  have hsave := eventually_original_boundary_resampling_from_full_schedule ell 4 0 Bclock A Craw H₀ (ce/48)
    (by dsimp [A];positivity) hCraw hH₀ (by positivity) hgap
  have hlog : ∀ᶠ n : ℕ in atTop,1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hpower : ∀ᶠ n : ℕ in atTop,2*C0  ≤  (n:ℝ)^m :=
    ((tendsto_rpow_atTop hm).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2*C0))
  filter_upwards [hsave,(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm),
    hlog,hpower,eventually_gt_atTop (1:ℕ)] with n hnsave hndepth hnlog hnpower hn1
  intro a hcompare us hus
  let c := a.context
  have hN1 : (1:ℝ) ≤ c.N := by change (1:ℝ) ≤ (n+1:ℕ); exact_mod_cast (show 1 ≤ n+1 by omega)
  have hNgt : 1<(n:ℝ) := by exact_mod_cast hn1
  have hnlogN : 1 ≤ Real.log c.N := hnlog.trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by change (n:ℝ) ≤ (n+1:ℕ); push_cast; linarith))
  have hN : 0 < (n:ℝ) := zero_lt_one.trans hNgt
  have hnd : 1/c.N ≤ c.d := by
    have H := hndepth c.E c.d c.hE c.hd a.hlower
    have H' : comparisonLowerScale ((n+1:ℕ):ℝ) c.E c.d ≤ c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact H.trans H'
  have hcritical : (n:ℝ)^(-(1:ℝ)/6+m) ≤ (2*C0)*a.xs := by
    have H:=observed_critical_power_succ (show 1 ≤ n by omega) (show -1 ≤ -(1:ℝ)/6+m by linarith)
    have Hmin:=native_minimum_original_boundary_critical_radius hC0 a
    nlinarith
  have hxscrit : (n:ℝ)^(-(1:ℝ)/6)  ≤  a.xs := by
    have H := mul_le_mul_of_nonneg_right hnpower (Real.rpow_nonneg hN.le (-(1:ℝ)/6))
    rw [←Real.rpow_add hN] at H
    have he : m+(-(1:ℝ)/6)=-(1:ℝ)/6+m := by ring
    rw [he] at H
    exact (mul_le_mul_iff_right₀ (show 0 < 2*C0 by positivity)).mp (by simpa only [mul_comm] using H.trans hcritical)
  obtain ⟨hW,hWd,hstrength⟩ := actual_direct_test_calibration_strength c.hd a.hlam a.hld a.hxs hCcal hcompare
  let W := max a.xs (Real.sqrt (laplaceComparisonStrength c.d a.lam a.xs))
  have hxW : a.xs  ≤  W := le_max_left _ _
  have hmesh : ∀ᶠ j : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/c.floor  ≤  a.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const c.floor).eventually
      (gt_mem_nhds (show 0/c.floor<a.xs/16 by simpa only [zero_div] using
        (show 0 < a.xs/16 from div_pos a.hxs (by norm_num))))).mono
    intro j hj
    simpa using hj.le
  filter_upwards [hmesh] with j hmj
  dsimp only
  intro hraw low high hhigh hWmacro hhighW hzs hlow
  let as := finiteCutMasses us j
  let rh := a.R (partitionPoint 0 as high)
  let s := min (rh/4) (Rmacro/2)
  have hrh : 0 < rh := lt_of_lt_of_le (by positivity : 0 < 4*W) hhighW
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hWs : W  ≤  s := le_min (by dsimp [rh];linarith) hWmacro
  have hxss : a.xs  ≤  s := hxW.trans hWs
  have hzs' : a.z  ≤  s/2 := by
    have H1 := hzs.trans (min_le_left _ _)
    have H2 := hzs.trans (min_le_right _ _)
    by_cases he : rh/4  ≤  Rmacro/2
    · rw [show s=rh/4 from min_eq_left he]
      linarith
    · rw [show s=Rmacro/2 from min_eq_right (le_of_not_ge he)]
      linarith
  have hlow' : a.R (partitionPoint 0 as low)  ≤  s/2 := by
    have H1 := hlow.trans (min_le_left _ _)
    have H2 := hlow.trans (min_le_right _ _)
    by_cases he : rh/4  ≤  Rmacro/2
    · rw [show s=rh/4 from min_eq_left he]
      linarith
    · rw [show s=Rmacro/2 from min_eq_right (le_of_not_ge he)]
      linarith
  have hsR : 2*s  ≤  Rmacro := by
    have H : s  ≤  Rmacro/2 := min_le_right _ _
    linarith
  have hslow : (n:ℝ)^(-((1:ℝ)/6))  ≤  s := by
    simpa only [neg_div] using hxscrit.trans hxss
  have htwo : 2*s  ≤  rh := by
    have H : s  ≤  rh/4 := min_le_left _ _
    linarith
  have ho := finiteCutMasses_ordered us hus j
  have hend := finiteCutMasses_end us hus j
  have hpart := finiteCutMasses_mesh us hus j
  have hmeshnonneg : 0 ≤ (((j+1:ℕ):ℝ)⁻¹) := by positivity
  have hsmall : (((j+1:ℕ):ℝ)⁻¹)/c.floor  ≤  s/16 := hmj.trans (by linarith)
  have hregular : ∀v∈Icc (s/2) 1,cl*v  ≤  a.alpha.val.val v ∧ a.alpha.val.val v  ≤  cu*v :=
    fun v hv=>a.regular v (Icc_subset_Icc hzs' le_rfl hv)
  obtain ⟨J,hJ,hJmacro,hJone,hJlog⟩ := exists_actual_boundary_dyadic_count
    hNgt hnlog hs hmacro hsR hRhalf hslow
  obtain ⟨cs,t,anchor,duration,hlen,hlt,hth,htlen,hlast,hends,hclocks,hscales,hcount,hDpos⟩ :=
    exists_actual_comparison_rest_boundary_projection_schedule (low:=low) (high:=high) n (show 0 < n by omega) c.hc c.hk c.hkc c.hm c.hM
      a.alpha a.b a.h a.hb a.hlb a.hh a.hh0 hN1 hnlogN c.hd hnd a.hlam a.hld
      as ho hend hmeshnonneg hpart hs hsmall hW hWs hce hstrength hcl hcu.le
      hmacro hFmass hFradius a.hxs.le hxss hregular hJ hJmacro hJone hhigh hlow' htwo a.clockBudget
  have hv1 : partitionPoint 0 as high  ≤  1 := (partitionPoint_mem as ho high).2
  have hrange : rh∈Icc a.z 1 :=
    ⟨hzs'.trans (by linarith),(comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM a.alpha _).2⟩
  have hlower := (a.regular rh hrange).1
  rw [comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM a.alpha
    (partitionPoint_mem as ho high)] at hlower
  have hv : 0 < partitionPoint 0 as high := lt_of_lt_of_le (mul_pos hcl hrh) hlower
  have hanchor : F/((cl/8)^2*s) ≤ H₀/partitionPoint 0 as high := by
    by_cases he : rh/4 ≤ Rmacro/2
    · have hs' : s=rh/4 := min_eq_left he
      have heq : a.R (partitionPoint 0 as high)=4*s := by rw [hs'];dsimp [rh];ring
      have H := (actual_comparison_boundary_schedule_high_anchor c.hc c.hk c.hkc c.hm c.hM
        a.alpha as ho hs hcl hF heq hregular).2
      apply H.trans
      exact div_le_div_of_nonneg_right (le_max_left Hsmall Hmacro) hv.le
    · have hs' : s=Rmacro/2 := min_eq_right (le_of_not_ge he)
      rw [hs']
      have H : Hmacro ≤ Hmacro/partitionPoint 0 as high := by
        apply (le_div_iff₀ hv).mpr
        exact (mul_le_mul_of_nonneg_left hv1 hHmacro).trans_eq (mul_one Hmacro)
      apply H.trans
      exact div_le_div_of_nonneg_right (le_max_right Hsmall Hmacro) hv.le
  have hcount' : ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ A*(Real.log (n:ℝ))^4 := by
    apply hcount.trans
    have H := pow_le_pow_left₀ (Nat.cast_nonneg (J+3)) hJlog 4
    simpa only [mul_pow,A] using H
  let steps := nativeSampledPhysicalSteps n a.bf a.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(a.bf (partitionPoint 0 as j):ℝ)) (fun _=>(a.hf (partitionPoint 0 as j):ℝ))
  let Q := fun j=>restFiniteRealVariance n (q j)
  have had:=comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha
  have hb : MonotoneOn a.bf (Icc (0:ℝ) 1):=toNNReal_monotoneOn had.1
  have hh : MonotoneOn a.hf (Icc (0:ℝ) 1):=toNNReal_monotoneOn had.2.1
  have heq : clockSteps as (cumulativeIncrements (Q 0) (fun z=>Q (z+1)))=steps := by
    rw [←restFinite_cumulativeIncrements]
    exact native_sampled_physical_clock_eq n a.bf a.hf hb hh as ho
  apply hnsave as ho Q low high t hlt hth hhigh
    (ce*W^3/(24*Real.log c.N)) a.xs (F/((cl/8)^2*s)) ((2*C0)*a.xs) W (partitionPoint 0 as high)
    hDpos a.hxs (by positivity) (mul_pos (show 0 < 2*C0 by positivity) a.hxs) hW hv hcritical cs anchor duration
  · simpa only [heq,steps] using hlast
  · simpa only [heq,steps] using hends
  · simpa only [heq,steps] using hclocks
  · simpa only [heq,steps] using hscales
  · exact hcount'
  · rw [heq]
    simpa only [pow_zero,mul_one] using hraw
  · exact hanchor
  · have hl:=observed_log_succ_le_twice (show 2 ≤ n by omega)
    have H:=div_le_div_of_nonneg_left (show 0 ≤ ce*W^3 by positivity)
      (show 0 < 24*Real.log c.N by positivity)
      (show 24*Real.log c.N ≤ 48*Real.log (n:ℝ) by change 24*Real.log ((n+1:ℕ):ℝ) ≤ _; linarith)
    convert H using 1
    ring

end OAI.SKFluctuations.LaplaceWindowFormalization
