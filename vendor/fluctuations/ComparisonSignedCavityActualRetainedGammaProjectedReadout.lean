module

public import ComparisonSignedCavityRetainedGammaFreshFold
public import ComparisonSignedCavityProjectionSpinePhysicalRow
public import ComparisonSignedCavityStarFieldMeanScale
public import ComparisonSignedCavityActualResourceRestReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

private theorem retained_gamma_pair_factor_smul (n : ℕ) (as : List PositiveMass)
    (star : ℕ) (q : ℕ→RestCoordinate n→ℝ≥0) (A : Spin n→Spin n→ℝ)
    (beta : ℝ) (y : RestCoordinate n→ℝ) (u : Spin n) :
    nativeStarPairFactor (restWeight n) (restFeature n) as star q (fun v z=>beta*A v z) y u=
      beta*nativeStarPairFactor (restWeight n) (restFeature n) as star q A y u := by
  simp only [nativeStarPairFactor,ClockTree.expect,Finset.mul_sum,mul_left_comm]

theorem native_reset_projected_gamma_row_eq_full_of_radius_le
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : U≤(pre++(mid++tail)).length)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    nativeResetProjectedGammaRow n T P M U V q K d center=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
        nativeResetPairedProjectionValue n T P M p q d center)).sum := by
  unfold nativeResetProjectedGammaRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hhigh : U≤p.tree.splitIndex (p.embed P.target) p.mark
  · have Hrad:=comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mono _ ho hhigh)
    simp only [hhigh,hV.trans Hrad,and_self,ite_true]
  · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (lt_of_not_ge hhigh)]
    simp only [mul_zero,zero_mul]

theorem native_actual_generated_retained_gamma_affine_eq_reset_row
    {n : ℕ} {pre mid tail : List PositiveMass}
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {i U k : ℕ} {seed : List NativeResourceMark}
    {P₀ : NativeResourceTerm i (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed k T P₀)
    (hi : i≤pre.length+mid.length) (hs : pre.length+mid.length<U)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (alpha offset beta center : ℝ) :
    let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) j)
    nativeRetainedGammaProjectedDisplacement T P₀.live.test.target (pre.length+mid.length) U q K
      (fun u v=>beta*(R u v-center))
      (fun σ=>alpha*nativeRestGeneratedTestValue T P₀.live.test R C σ-offset)=
      (-beta*alpha/2)*nativeResetProjectedGammaRow n T P₀.live.test M U V q K 0 center := by
  dsimp only
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let P:=nativeRestGeneratedTestValue T P₀.live.test R C
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) center
  have HF (y : RestCoordinate n→ℝ) (u : Spin n) :
      nativeStarPairFactor (restWeight n) (restFeature n) as star
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun v z=>beta*(R v z-center)) y u=
        beta*Y y u := by
    rw [retained_gamma_pair_factor_smul]
    exact congrArg (beta*·) (nativeStarPairFactor_two_level_centered_projection n pre mid tail _ center y u)
  rw [native_actual_generated_retained_gamma_eq_paired_source hP hi hs ho,
    native_retained_gamma_paired_row_fresh_fold T P₀.live.test.target star U hs hP.highCut_le_length ho,
    native_reset_projected_gamma_row_eq_full_of_radius_le n T P₀.live.test M U V q K 0 center ho hP.highCut_le_length hV]
  have Hsum : ((T.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed P₀.live.test.target) r.mark*
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) r.tree.cavityLeft
        (r.tree.cavityLeftSlot (r.embed P₀.live.test.target)) star 0 q
        (fun y σ=>((alpha*P (r.restRestrict σ)-offset)-
          (alpha*P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P₀.live.test.target)
            (r.restRestrict σ) (r.restSpin σ))-offset))*
          (nativeStarPairFactor (restWeight n) (restFeature n) as star
            (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun v z=>beta*(R v z-center)) y (r.restSpin σ)-
          nativeStarPairFactor (restWeight n) (restFeature n) as star
            (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun v z=>beta*(R v z-center)) y
            (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P₀.live.test.target)))) 0)).sum=
      (-beta*alpha)*((T.markedAttach 0).map (fun r=>r.coeff*
        fullScalarCutGamma r.tree U K (r.embed P₀.live.test.target) r.mark*
        nativeResetPairedProjectionValue n T P₀.live.test M r q 0 center)).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    simp only [HF]
    have Htest : (fun y σ=>((alpha*P (r.restRestrict σ)-offset)-
        (alpha*P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P₀.live.test.target)
          (r.restRestrict σ) (r.restSpin σ))-offset))*
        (beta*Y y (r.restSpin σ)-beta*Y y
          (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P₀.live.test.target))))=
      (fun y σ=>(-beta*alpha)*((Y y (r.restSpin σ)-Y y
        (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P₀.live.test.target)))*
        (P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P₀.live.test.target)
          (r.restRestrict σ) (r.restSpin σ))-P (r.restRestrict σ)))) := by
      funext y σ
      ring
    rw [Htest,native_star_field_disorder_mean_const_mul]
    dsimp only [nativeResetPairedProjectionValue]
    simp only [pow_zero,mul_one]
    ring
  calc
    _=(1/2:ℝ)*((-beta*alpha)*((T.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed P₀.live.test.target) r.mark*
      nativeResetPairedProjectionValue n T P₀.live.test M r q 0 center)).sum) := congrArg ((1/2:ℝ)*·) Hsum
    _=_:=by ring

end OAI.SKFluctuations.Cavity
