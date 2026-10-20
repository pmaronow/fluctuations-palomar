module

public import ComparisonSignedCavityProjectedGammaRowTopology
public import ComparisonSignedCavityPhysicalProjectionFactorization

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_projected_gamma_row_spine
    (n : ℕ) {pre mid tail : List PositiveMass}
    {A T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    (h : NativeProjectionSpine base (pre.length+mid.length) P)
    (hA : NativeTargetStarSingleton A base.target (pre.length+mid.length))
    (hT : NativeTargetStarSingleton T P.target (pre.length+mid.length))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : pre.length+mid.length < U) :
    let center:=pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
    nativeResetProjectedGammaRow n T P M U V q K 0 center=
      nativeResetProjectedGammaRow n A base M U V q K h.toothCount center := by
  dsimp only
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) (C (pre.length+mid.length))
  have HY (u : Spin n) : BddSmooth 0 (fun y=>Y y u):=
    native_star_centered_projection_smooth n ho.suffix_end.suffix_end _ _ u 0
  have HH:=h.paired_signed_disorder_row hA hT (restWeight_pos n) (restFeature n) 0 ho R C 0 q
    (fun y σ u=>Y y u-Y y (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))
    (fun σ u=>(HY u).sub (HY _)) 0
    (nativeProjectedGammaTopology (pre++(mid++tail)) U V M.R K)
  have HF (y : RestCoordinate n→ℝ) (u : Spin n) :
      nativeStarPairFactor (restWeight n) (restFeature n) (pre++(mid++tail))
        (pre.length+mid.length) (cumulativeIncrements (q 0) (fun j=>q (j+1)))
        (fun u v=>R u v-C (pre.length+mid.length)) y u=Y y u :=
    nativeStarPairFactor_two_level_centered_projection n pre mid tail _ _ y u
  simp only [HF,h.restTargetRead] at HH
  rw [native_reset_projected_gamma_row_high_form n T P M U V q K 0 _ ho hU,
    native_reset_projected_gamma_row_high_form n A base M U V q K h.toothCount _ ho hU]
  simpa only [nativeResetPairedProjectionValue,pow_zero,mul_one,
    R,C,Y] using HH

end OAI.SKFluctuations.Cavity
