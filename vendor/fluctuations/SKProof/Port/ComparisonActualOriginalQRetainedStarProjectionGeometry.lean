module

public import ComparisonNativeInheritedStarMinimumRetainedProjection
public import SKProof.Port.ComparisonActualOriginalQFullStarProjectionGeometry

@[expose] public section
set_option linter.unusedVariables false

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization
namespace NativeStarBuffer

theorem eventually_retained_actual_minimum_inherited_star_projection_geometry_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct Ddepth Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct Ddepth Bclock)
    (hcl : 0 < cl) (hcu : 0  ≤  cu)
    (hN : 1  ≤  ((n+1:ℕ):ℝ)) (hlog : 1  ≤  Real.log ((n+1:ℕ):ℝ)) (hnd : 1/((n+1:ℕ):ℝ)  ≤  M.data.d)
    {W s v theta ce Rmacro F Cprof H H₀ Lcount a₀ : ℝ}
    (hW : 0 < W) (hWs : W  ≤  s)
    (hfour : 4*s  ≤  1) (hce : 0 < ce)
    (hstrength : ce*W^2  ≤  laplaceComparisonStrength M.data.d M.lam W)
    (hregular : M.z  ≤  s/2) (hmacro : 0 < Rmacro)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hxss : M.xs  ≤  s) (hv : 0 < v) (hv1 : v  ≤  1) (htheta : 0 < theta)
    (hCprof : 0  ≤  Cprof) (hcaproom : Cprof*v  ≤  1)
    (hcap : 0 < M.data.M (Cprof*v))
    (hshortlater : laplaceComparisonStrength M.data.d M.lam v*theta*v/
      (3*M.data.M (Cprof*v)*Real.log ((n+1:ℕ):ℝ))  ≤  ce*W^3/(24*Real.log ((n+1:ℕ):ℝ)))
    (hHlater : F/((cl/8)^2*s)  ≤  H)
    (hHfirst : (1+4*cu)*s  ≤  H*a₀^2) (hHupper : H  ≤  H₀/v)
    {J : ℕ} (hJ : 1  ≤  J) (hJmacro : Rmacro  ≤  (2:ℝ)^J*s)
    (hJone : (2:ℝ)^J*s  ≤  1) (hcount : ((J+4:ℕ):ℝ)  ≤  Lcount*Real.log ((n+1:ℕ):ℝ))
    (star future : PositiveMass) (hhighstar : M.data.s ≤ star.val) (hfork : star.val  ≤  future.val)
    (htradius : M.sweepRadius future.val  ≤  s/2) (htradiusv : M.sweepRadius future.val  ≤  v)
    (ha₀ : 0 < a₀) (hanchor : a₀  ≤  star.val)
    (htcap : future.val  ≤  Cprof*v) (hgap : theta*v  ≤  future.val-star.val)
    (us : List PositiveMass) (hus : ∀u∈us,u.val  ≤  1)
    (hstar : star∈us) (hfuture : future∈us) :
    ∀ᶠj : ℕ in atTop,
      let as := finiteCutMasses us j
      let q := completedPathClock (n+1) M.sweepBf M.sweepHf
      let steps := sampleClockSteps q 0 as
      Nonempty (OriginalStarProjectionGeometry steps
        (physicalRetainedIndex steps star.val).val (physicalRetainedIndex steps future.val).val
        M.xs H v theta M.data.d M.lam M.data.E delta Cprof Lcount H₀ Bclock) := by
  have hs : 0 < s := hW.trans_le hWs
  have hmeshlimit : ∀ᶠj : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/M.data.floor  ≤  s/16 := by
    have ht := uniformMasses_mesh_tendsto.div_const M.data.floor
    simp only [zero_div] at ht
    exact (ht.eventually (gt_mem_nhds (by positivity : (0:ℝ) < s/16))).mono (fun _ h=>h.le)
  filter_upwards [hmeshlimit] with j hj
  let as := finiteCutMasses us j
  let q := completedPathClock (n+1) M.sweepBf M.sweepHf
  let steps := sampleClockSteps q 0 as
  let ho := finiteCutMasses_ordered us hus j
  have hlen (u : PositiveMass) : (physicalRetainedIndex steps u.val).val  ≤  as.length := by
    exact (splitClockSteps_length_le steps u.val).trans (by simp [steps,sampleClockSteps_length])
  have hnode (u : PositiveMass) (hu : u∈us) :
      partitionPoint 0 as (physicalRetainedIndex steps u.val).val=u.val := by
    rw [←physicalCutMass_sampleClockSteps q 0 as _ (hlen u)]
    exact physicalRetainedIndex_mass q as ho u (finiteCutMasses_nodes us j hu)
  exact actual_minimum_inherited_original_star_projection_geometry_original_q M hcl hcu hN hlog hnd
    as ho (finiteCutMasses_end us hus j)
    (by positivity : 0  ≤  (((j+1:ℕ):ℝ)⁻¹)) (finiteCutMasses_mesh us hus j)
    hW hWs hj hfour hce hstrength hregular hmacro hFmass hFradius hxss hv hv1 htheta
    hCprof hcaproom hcap hshortlater hHlater hHfirst hHupper
    hJ hJmacro hJone hcount (physicalRetainedIndex_mono steps hfork) (hlen future)
    (by
      change M.sweepRadius (partitionPoint 0 as (physicalRetainedIndex steps future.val).val)  ≤  s/2
      rw [hnode future hfuture]
      exact htradius)
    (by
      change M.sweepRadius (partitionPoint 0 as (physicalRetainedIndex steps future.val).val)  ≤  v
      rw [hnode future hfuture]
      exact htradiusv)
    ha₀ (by
      change a₀  ≤  partitionPoint 0 as (physicalRetainedIndex steps star.val).val
      rw [hnode star hstar]
      exact hanchor)
    (by
      change M.data.s ≤ partitionPoint 0 as (physicalRetainedIndex steps star.val).val
      rw [hnode star hstar]
      exact hhighstar)
    (by
      change partitionPoint 0 as (physicalRetainedIndex steps future.val).val  ≤  Cprof*v
      rw [hnode future hfuture]
      exact htcap)
    (by
      change theta*v  ≤  partitionPoint 0 as (physicalRetainedIndex steps future.val).val-
        partitionPoint 0 as (physicalRetainedIndex steps star.val).val
      rw [hnode future hfuture,hnode star hstar]
      exact hgap)

end NativeStarBuffer
end OAI.SKFluctuations
