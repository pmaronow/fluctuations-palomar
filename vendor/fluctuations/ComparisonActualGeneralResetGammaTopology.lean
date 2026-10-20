module

public import ComparisonActualGeneralResetGammaRowAlgebra
public import ComparisonSignedCavityProjectedGammaRowTopology
public import ComparisonSignedCavityProjectionSpinePhysicalRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem actual_general_reset_projected_gamma_row_high_form
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : pre.length+mid.length < U) :
    actualGeneralResetProjectedGammaRow n T P bf hf radius U V q K d center=
      ((nativeHighMarkedRows T P.target (pre.length+mid.length) 0).map fun p=>
        p.coeff*nativeProjectedGammaTopology (pre++(mid++tail)) U V radius K
          (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
        actualGeneralResetPairedProjectionValue n T P bf hf p q d center).sum := by
  unfold actualGeneralResetProjectedGammaRow
  have HF:=native_list_sum_filter_of_zero (T.markedAttach 0)
    (fun p=>decide (pre.length+mid.length < p.tree.splitIndex (p.embed P.target) p.mark))
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
      (if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
          V ≤ radius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
        actualGeneralResetPairedProjectionValue n T P bf hf p q d center else 0)) (by
      intro p _ hp
      have hn:¬pre.length+mid.length < p.tree.splitIndex (p.embed P.target) p.mark:=of_decide_eq_false hp
      have hx:¬U ≤ p.tree.splitIndex (p.embed P.target) p.mark:=fun h=>hn (hU.trans_le h)
      simp [hx])
  rw [←HF,←nativeHighMarkedRows_eq_filter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [fullScalarCutGamma_marked_eq_topology T ho]
  simp only [nativeProjectedGammaTopology,MarkedPlacement.hit,decide_eq_true_eq]
  split_ifs <;> ring

theorem actual_general_projected_gamma_row_spine
    (n : ℕ) {pre mid tail : List PositiveMass}
    {A T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    (h : NativeProjectionSpine base (pre.length+mid.length) P)
    (hA : NativeTargetStarSingleton A base.target (pre.length+mid.length))
    (hT : NativeTargetStarSingleton T P.target (pre.length+mid.length))
    (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : pre.length+mid.length < U) :
    let center:=pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
    actualGeneralResetProjectedGammaRow n T P bf hf radius U V q K 0 center=
      actualGeneralResetProjectedGammaRow n A base bf hf radius U V q K h.toothCount center := by
  dsimp only
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) (C (pre.length+mid.length))
  have HY (u : Spin n) : BddSmooth 0 (fun y=>Y y u):=
    native_star_centered_projection_smooth n ho.suffix_end.suffix_end _ _ u 0
  have HH:=h.paired_signed_disorder_row hA hT (restWeight_pos n) (restFeature n) 0 ho R C 0 q
    (fun y σ u=>Y y u-Y y (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))
    (fun σ u=>(HY u).sub (HY _)) 0
    (nativeProjectedGammaTopology (pre++(mid++tail)) U V radius K)
  have HF (y : RestCoordinate n→ℝ) (u : Spin n) :
      nativeStarPairFactor (restWeight n) (restFeature n) (pre++(mid++tail))
        (pre.length+mid.length) (cumulativeIncrements (q 0) (fun j=>q (j+1)))
        (fun u v=>R u v-C (pre.length+mid.length)) y u=Y y u :=
    nativeStarPairFactor_two_level_centered_projection n pre mid tail _ _ y u
  simp only [HF,h.restTargetRead] at HH
  rw [actual_general_reset_projected_gamma_row_high_form n T P bf hf radius U V q K 0 _ ho hU,
    actual_general_reset_projected_gamma_row_high_form n A base bf hf radius U V q K h.toothCount _ ho hU]
  simpa only [actualGeneralResetPairedProjectionValue,pow_zero,mul_one,
    R,C,Y] using HH

end OAI.SKFluctuations.Cavity
