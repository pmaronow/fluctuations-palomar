module

public import ComparisonActualHighWallCanonicalProjectionGeometry
public import ComparisonActualHighWallBufferEndpointGeometryAlong
public import ComparisonActualHighWallStarProjectionScalarsAlong

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum
theorem eventually_actual_high_wall_fixed_canonical_projection_geometry_along
    {m delta cl cu Az C0 Ct D Bclock L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta<3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0)) :
    let W:=fun n=>(M n).data.d
    ∃Kv Cprof Lcount H0 : ℝ,1 ≤ Kv ∧ 0 < Cprof ∧ 0 < Lcount ∧ 0 < H0 ∧
      ∀ᶠn : ℕ in atTop,
      max (M n).xs (Real.sqrt ((M n).data.g (M n).xs))=W n ∧
      W n ≤ (M n).data.d ∧ (W n)^2 ≤ (M n).data.g (W n) ∧
      (M n).xs ≤ Kv*W n ∧ Kv*W n ≤ 1 ∧
      ∀Cs : ℝ,∀w : ActualSlowWindowChoice,IsActualHighWallCalibratedSlowWindow (M n) (W n) L Cs w →
      ∀future : PositiveMass,
        future.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3) →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → w.star∈us → future∈us →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let q:=completedPathClock (dim n+1) (M n).bf (M n).hf
        let steps:=sampleClockSteps q 0 as
        Nonempty (OriginalStarProjectionGeometry steps
          (physicalRetainedIndex steps w.star.val).val (physicalRetainedIndex steps future.val).val
          (M n).xs (H0/(Kv*W n)) (Kv*W n)
          ((M n).data.N^(-(3*actualSlowWindowExponent m delta)))
          (M n).data.d ((M n).data.d^2) (M n).data.E delta Cprof Lcount H0 Bclock) := by
  dsimp only
  let W:=fun n=>(M n).data.d
  have hxs n : (M n).xs ≤ W n:=by rw [hfixed n]
  have hW n : 0 < W n:=(M n).data.hd
  obtain ⟨Kv,Ks,Cprof,Lcount,hKv,hKs,hCp,hLc,Hscalar⟩:=
    eventually_actual_high_wall_fixed_slow_window_projection_scalars_along
      hm hdelta hroom hcl hcu hAz hC0 hL (by norm_num : (0:ℝ)<1/24) dim hdim M hfixed hWlim
  let aBand:=calibratedBandStart cu Az
  let F:=9+2*cu
  let H0:=actualStarProjectionAnchorConstant aBand Kv Ks cl cu F
  have ha : 0 < aBand:=calibrated_band_start_pos hcu hAz
  have ha1 : 1 ≤ aBand:=by
    dsimp only [aBand,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu,hAz]
  have hKvpos : 0 < Kv:=zero_lt_one.trans_le hKv
  have hKspos : 0 < Ks:=hKvpos.trans_le hKs
  have hH0 : 0 < H0:=(actual_star_projection_anchor_bounds (F:=F)
    ha hKvpos hKspos hcl hcu.le (hW 0)).1
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((dim n+1:ℕ):ℝ):=
    ((tendsto_add_atTop_nat 1).comp hdim).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have Hdepth:=((tendsto_add_atTop_nat 1).comp hdim).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hvunit:=(hWlim.const_mul Kv).eventually (eventually_le_nhds (show Kv*(0:ℝ)<1 by simp))
  refine ⟨Kv,Cprof,Lcount,H0,hKv,hCp,hLc,hH0,?_⟩
  filter_upwards [Hscalar,Hlog,Hdepth,Hvunit] with n hnScalar hnLog hnDepth hnVunit
  have hxv : (M n).xs ≤ Kv*W n:=(hxs n).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKv (hW n).le)
  have hstrength : (W n)^2 ≤ (M n).data.g (W n):=by rw [(M n).data.strength_at_scale]
  refine ⟨(M n).fixed_canonical_scale (hfixed n),le_rfl,hstrength,hxv,hnVunit,?_⟩
  intro Cs w hw future hfuture us hus hstar hfutureus
  obtain ⟨hanchor,_,hfork,hgap,hRv,hRs,hWv,hWs,hz,hfour,_,htcap,hcaproom,hcaplower,_,
    _,hshort,J,hJ,hreach,hJone,hcount⟩:=hnScalar Cs w hw
  have hN : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ):=by exact_mod_cast Nat.succ_pos (dim n)
  have hnd : 1/((dim n+1:ℕ):ℝ) ≤ (M n).data.d:=by
    have H:=hnDepth (M n).data.E (M n).data.d (M n).data.hE (M n).data.hd (M n).hlower
    have H' : comparisonLowerScale (M n).data.N (M n).data.E (M n).data.d ≤ (M n).data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ (M n).data.hd).mpr (by simpa only [pow_two] using (M n).hupper)
    exact H.trans H'
  have Hanchor:=actual_star_projection_anchor_bounds (F:=F)
    ha hKvpos hKspos hcl hcu.le (hW n)
  have hHlater : F/((cl/8)^2*(Ks*W n)) ≤ H0/(Kv*W n):=Hanchor.2.2.1
  have hHfirst : (1+4*cu)*(Ks*W n) ≤ (H0/(Kv*W n))*(aBand*W n)^2:=Hanchor.2.2.2
  have hFmass : 1+2*cu ≤ F:=by dsimp only [F];linarith
  have hFradius : 1+1/((1:ℝ)/8) ≤ F:=by dsimp only [F];norm_num;linarith
  have hshort' : (M n).data.g (Kv*W n)*
      ((M n).data.N^(-(3*actualSlowWindowExponent m delta)))*(Kv*W n)/
      (3*(M n).data.M (Cprof*(Kv*W n))*Real.log ((dim n+1:ℕ):ℝ)) ≤
        (1:ℝ)*(W n)^3/(24*Real.log ((dim n+1:ℕ):ℝ)):=by
    convert hshort using 1;ring
  have hwall : (M n).data.rmin ≤ (Ks*W n)/2:=by
    have Hr:=(M n).data.hrbounds.2.1
    change (M n).data.rmin ≤ W n/4 at Hr
    linarith only [Hr,hWs,(hW n)]
  have hhigh : (M n).data.s ≤ aBand*W n:=by
    have HS:=(M n).hsxs.trans (hxs n)
    exact HS.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (hW n).le)
  apply eventually_retained_actual_high_wall_star_projection_geometry (M n) hcl hcu.le
    hN hnLog hnd (hW n) hWs hwall hfour (by norm_num : (0:ℝ)<1)
    (by simpa only [one_mul] using hstrength) hz (by norm_num : (0:ℝ)<1/8)
    hFmass hFradius ((hxs n).trans hWs) (mul_pos hKvpos (hW n)) hnVunit
    (Real.rpow_pos_of_pos (M n).data.hN _) hCp.le hcaproom (hcl.trans_le hcaplower)
    hshort' hHlater hHfirst le_rfl hJ hreach hJone hcount w.star future
    (by rw [hfuture];exact hfork.le)
    (by rw [hfuture];linarith only [hRs]) (by rw [hfuture];exact hRv)
    (mul_pos ha (hW n)) hhigh hanchor (by rw [hfuture];exact htcap)
    (by rw [hfuture];exact hgap) us hus hstar hfutureus

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
