module

public import ComparisonActualHighWallStarProjectionScalars
public import ComparisonActualHighWallStarProjectionGeometry
public import ComparisonSignedCavityActualStarProjectionAnchors

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization
namespace NativeStarBuffer

theorem eventually_retained_actual_high_wall_star_projection_geometry
    {n : ℕ} {m delta cl cu Az C0 Ct Ddepth Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct Ddepth Bclock)
    (hcl : 0 < cl) (hcu : 0 ≤ cu)
    (hN : 1 ≤ (n:ℝ)) (hlog : 1 ≤ Real.log (n:ℝ)) (hnd : 1/(n:ℝ) ≤ M.data.d)
    {W s v theta ce Rmacro F Cprof H H₀ Lcount a₀ : ℝ}
    (hW : 0 < W) (hWs : W ≤ s) (hwall : M.data.rmin ≤ s/2)
    (hfour : 4*s ≤ 1) (hce : 0 < ce)
    (hstrength : ce*W^2 ≤ laplaceComparisonStrength M.data.d (M.data.d^2) W)
    (hregular : M.z ≤ s/2) (hmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hxss : M.xs ≤ s) (hv : 0 < v) (hv1 : v ≤ 1) (htheta : 0 < theta)
    (hCprof : 0 ≤ Cprof) (hcaproom : Cprof*v ≤ 1)
    (hcap : 0 < M.data.M (Cprof*v))
    (hshortlater : laplaceComparisonStrength M.data.d (M.data.d^2) v*theta*v/
      (3*M.data.M (Cprof*v)*Real.log (n:ℝ)) ≤ ce*W^3/(24*Real.log (n:ℝ)))
    (hHlater : F/((cl/8)^2*s) ≤ H)
    (hHfirst : (1+4*cu)*s ≤ H*a₀^2) (hHupper : H ≤ H₀/v)
    {J : ℕ} (hJ : 1 ≤ J) (hJmacro : Rmacro ≤ (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s ≤ 1) (hcount : ((J+4:ℕ):ℝ) ≤ Lcount*Real.log (n:ℝ))
    (star future : PositiveMass) (hfork : star.val ≤ future.val)
    (htradius : M.data.wallRadius M.alpha future.val ≤ s/2) (htradiusv : M.data.wallRadius M.alpha future.val ≤ v)
    (ha₀ : 0 < a₀) (hanchorHigh : M.data.s ≤ a₀) (hanchor : a₀ ≤ star.val)
    (htcap : future.val ≤ Cprof*v) (hgap : theta*v ≤ future.val-star.val)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (hstar : star∈us) (hfuture : future∈us) :
    ∀ᶠj : ℕ in atTop,
      let as := finiteCutMasses us j
      let q := completedPathClock n M.bf M.hf
      let steps := sampleClockSteps q 0 as
      Nonempty (OriginalStarProjectionGeometry steps
        (physicalRetainedIndex steps star.val).val (physicalRetainedIndex steps future.val).val
        M.xs H v theta M.data.d (M.data.d^2) M.data.E delta Cprof Lcount H₀ Bclock) := by
  have hs : 0 < s := hW.trans_le hWs
  have hmeshlimit : ∀ᶠj : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/(M.data.k 1) ≤ s/16 := by
    have ht := uniformMasses_mesh_tendsto.div_const (M.data.k 1)
    simp only [zero_div] at ht
    exact (ht.eventually (gt_mem_nhds (by positivity : (0:ℝ) < s/16))).mono (fun _ h=>h.le)
  filter_upwards [hmeshlimit] with j hj
  let as := finiteCutMasses us j
  let q := completedPathClock n M.bf M.hf
  let steps := sampleClockSteps q 0 as
  let ho := finiteCutMasses_ordered us hus j
  have hlen (u : PositiveMass) : (physicalRetainedIndex steps u.val).val ≤ as.length := by
    exact (splitClockSteps_length_le steps u.val).trans (by simp [steps,sampleClockSteps_length])
  have hnode (u : PositiveMass) (hu : u∈us) :
      partitionPoint 0 as (physicalRetainedIndex steps u.val).val=u.val := by
    rw [←physicalCutMass_sampleClockSteps q 0 as _ (hlen u)]
    exact physicalRetainedIndex_mass q as ho u (finiteCutMasses_nodes us j hu)
  exact actual_high_wall_original_star_projection_geometry M hcl hcu hN hlog hnd
    as ho (finiteCutMasses_end us hus j)
    (by positivity : 0 ≤ (((j+1:ℕ):ℝ)⁻¹)) (finiteCutMasses_mesh us hus j)
    hW hWs hwall hj hfour hce hstrength hregular hmacro hFmass hFradius hxss hv hv1 htheta
    hCprof hcaproom hcap hshortlater hHlater hHfirst hHupper
    hJ hJmacro hJone hcount (physicalRetainedIndex_mono steps hfork) (hlen future)
    (by
      change M.data.wallRadius M.alpha (partitionPoint 0 as (physicalRetainedIndex steps future.val).val) ≤ s/2
      rw [hnode future hfuture]
      exact htradius)
    (by
      change M.data.wallRadius M.alpha (partitionPoint 0 as (physicalRetainedIndex steps future.val).val) ≤ v
      rw [hnode future hfuture]
      exact htradiusv)
    ha₀ hanchorHigh (by
      change a₀ ≤ partitionPoint 0 as (physicalRetainedIndex steps star.val).val
      rw [hnode star hstar]
      exact hanchor)
    (by
      change partitionPoint 0 as (physicalRetainedIndex steps future.val).val ≤ Cprof*v
      rw [hnode future hfuture]
      exact htcap)
    (by
      change theta*v ≤ partitionPoint 0 as (physicalRetainedIndex steps future.val).val-
        partitionPoint 0 as (physicalRetainedIndex steps star.val).val
      rw [hnode future hfuture,hnode star hstar]
      exact hgap)

end NativeStarBuffer
end OAI.SKFluctuations

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_fixed_canonical_projection_geometry
    {m delta cl cu Az C0 Ct D Bclock L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta<3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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
        let q:=completedPathClock (n+1) (M n).bf (M n).hf
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
    eventually_actual_high_wall_fixed_slow_window_projection_scalars
      hm hdelta hroom hcl hcu hAz hC0 hL (by norm_num : (0:ℝ)<1/24) M hfixed hWlim
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
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ):=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
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
  have hN : (1:ℝ) ≤ ((n+1:ℕ):ℝ):=by exact_mod_cast Nat.succ_pos n
  have hnd : 1/((n+1:ℕ):ℝ) ≤ (M n).data.d:=by
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
      (3*(M n).data.M (Cprof*(Kv*W n))*Real.log ((n+1:ℕ):ℝ)) ≤
        (1:ℝ)*(W n)^3/(24*Real.log ((n+1:ℕ):ℝ)):=by
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
