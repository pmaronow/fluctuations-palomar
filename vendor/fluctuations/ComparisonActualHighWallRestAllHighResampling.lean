module

public import ComparisonActualHighWallRestBoundarySchedule
public import ComparisonActualHighWallBoundaryResampling
public import ComparisonSignedCavityObservedCalibrationScale
public import ComparisonSignedCavityRestAllHighResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem eventually_actual_high_wall_rest_all_high_resampling_from_raw
    (ell : ℕ) (Bclock Rmacro F Craw : ℝ) (hCraw : 0 ≤ Craw)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.xs=a.data.d →
      ∀us : List PositiveMass,(∀v∈us,v.val ≤ 1)→
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(a.bf (partitionPoint 0 as j):ℝ)) (fun _=>(a.hf (partitionPoint 0 as j):ℝ))
        let Q:=fun j=>restFiniteRealVariance n (q j)
        let steps:=nativeSampledPhysicalSteps n a.bf a.hf as
        let W:=a.data.d
        (physicalRawRatio n (ell+1) steps 0 a.xs
          (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (Q 0 i)))) id measurable_id)^2 ≤ Craw→
        ∀(low high : ℕ),high ≤ as.length→W ≤ Rmacro/2→
          4*W ≤ a.data.wallRadius a.alpha (partitionPoint 0 as high)→
          a.z ≤ min (a.data.wallRadius a.alpha (partitionPoint 0 as high)/8) (Rmacro/4)→
          a.data.wallRadius a.alpha (partitionPoint 0 as low) ≤ min (a.data.wallRadius a.alpha (partitionPoint 0 as high)/8) (Rmacro/4)→
          originalBoundaryResamplingMoment n (ell+1) as Q low high ≤ 
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*a.xs) W
              (partitionPoint 0 as high))^(2*(ell+1)) := by
  let ce := (1:ℝ)
  let A := (((1:ℝ)/6)/Real.log 2+4)^4
  let Hsmall := 4*cu*F/(cl/8)^2
  let Hmacro := F/((cl/8)^2*(Rmacro/2))
  let H₀ := max Hsmall Hmacro
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
  intro a hwork us hus
  let c := a.data
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
    have Hmin:=actual_high_wall_original_boundary_critical_radius hC0 a
    nlinarith
  have hxscrit : (n:ℝ)^(-(1:ℝ)/6)  ≤  a.xs := by
    have H := mul_le_mul_of_nonneg_right hnpower (Real.rpow_nonneg hN.le (-(1:ℝ)/6))
    rw [←Real.rpow_add hN] at H
    have he : m+(-(1:ℝ)/6)=-(1:ℝ)/6+m := by ring
    rw [he] at H
    exact (mul_le_mul_iff_right₀ (show 0 < 2*C0 by positivity)).mp (by simpa only [mul_comm] using H.trans hcritical)
  let W:=c.d
  have hW : 0 < W:=c.hd
  have hxW : a.xs ≤ W:=hwork.le
  have hstrength : ce*W^2 ≤ c.g W:=by
    have H:=laplaceComparisonStrength_lower c.hd (sq_pos_of_pos c.hd) c.hd
    have He : c.d^3/c.d=c.d^2:=by field_simp
    rw [He,min_self] at H
    simpa only [ce,W,one_mul,ActualHighWallData.g] using H
  have hmesh : ∀ᶠ j : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/(c.k 1)  ≤  a.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const (c.k 1)).eventually
      (gt_mem_nhds (show 0/(c.k 1)<a.xs/16 by simpa only [zero_div] using
        (show 0 < a.xs/16 from div_pos a.hxs (by norm_num))))).mono
    intro j hj
    simpa using hj.le
  filter_upwards [hmesh] with j hmj
  dsimp only
  intro hraw low high hhigh hWmacro hhighW hzs hlow
  let as := finiteCutMasses us j
  let rh := a.data.wallRadius a.alpha (partitionPoint 0 as high)
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
  have hlow' : a.data.wallRadius a.alpha (partitionPoint 0 as low)  ≤  s/2 := by
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
  have hsmall : (((j+1:ℕ):ℝ)⁻¹)/(c.k 1)  ≤  s/16 := hmj.trans (by linarith)
  have hregular : ∀v∈Icc (s/2) 1,cl*v  ≤  a.alpha.val.val v ∧ a.alpha.val.val v  ≤  cu*v :=
    fun v hv=>a.regular v (Icc_subset_Icc hzs' le_rfl hv)
  obtain ⟨J,hJ,hJmacro,hJone,hJlog⟩ := exists_actual_boundary_dyadic_count
    hNgt hnlog hs hmacro hsR hRhalf hslow
  obtain ⟨cs,t,anchor,duration,hlen,hlt,hth,htlen,hlast,hends,hclocks,hscales,hcount,hDpos⟩ :=
    exists_actual_high_wall_rest_boundary_projection_schedule (low:=low) (high:=high) c a.alpha
      n (show 0 < n by omega) hN1 hnlogN hnd
      as ho hend hmeshnonneg hpart hs (a.hz.1.trans hzs') hsmall hW hWs hce hstrength hcl hcu.le
      hmacro hFmass hFradius a.hxs.le hxss hregular hJ hJmacro hJone hhigh hlow' htwo
  have hv1 : partitionPoint 0 as high  ≤  1 := (partitionPoint_mem as ho high).2
  have hrange : rh∈Icc a.z 1 :=
    ⟨hzs'.trans (by linarith),(c.wallRadius_bounds a.alpha _).2⟩
  have hlower := (a.regular rh hrange).1
  have hmasshigh : c.s ≤ partitionPoint 0 as high:=by
    apply (c.wallRadius_high_mass a.alpha ?_).le
    change c.rmin < rh
    have HH:=a.hz.1.trans hzs'
    linarith
  rw [c.wallRadius_spec a.alpha ⟨hmasshigh,hv1⟩] at hlower
  have hv : 0 < partitionPoint 0 as high := lt_of_lt_of_le (mul_pos hcl hrh) hlower
  have hanchor : F/((cl/8)^2*s) ≤ H₀/partitionPoint 0 as high := by
    by_cases he : rh/4 ≤ Rmacro/2
    · have hs' : s=rh/4 := min_eq_left he
      have heq : a.data.wallRadius a.alpha (partitionPoint 0 as high)=4*s := by rw [hs'];dsimp [rh];ring
      have H := (actual_high_wall_boundary_schedule_high_anchor c a.alpha as ho hs
        (a.hz.1.trans hzs') hcl hF heq hregular).2
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
  have hb : MonotoneOn a.bf (Icc (0:ℝ) 1):=a.data.bf_monotone a.alpha
  have hh : MonotoneOn a.hf (Icc (0:ℝ) 1):=a.data.hf_monotone a.alpha
  have heq : clockSteps as (cumulativeIncrements (Q 0) (fun z=>Q (z+1)))=steps := by
    rw [←restFinite_cumulativeIncrements]
    exact native_sampled_physical_clock_eq n a.bf a.hf hb hh as ho
  apply hnsave as ho Q low high t hlt hth hhigh
    (ce*W^3/(24*Real.log c.N)) a.xs (F/((cl/8)^2*s)) ((2*C0)*a.xs) W (partitionPoint 0 as high)
    hDpos a.hxs (by positivity) (mul_pos (show 0 < 2*C0 by positivity) a.hxs) hW hv hcritical cs anchor duration
  · simpa only [heq,steps] using hlast
  · simpa only [heq,steps] using hends
  · intro jj
    have HH:=hclocks jj
    exact ⟨HH.1,HH.2.1,HH.2.2.1.trans a.hT,by simpa only [heq,steps] using HH.2.2.2⟩
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
