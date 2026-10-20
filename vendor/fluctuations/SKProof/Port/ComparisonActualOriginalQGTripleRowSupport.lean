module

public import SKProof.Port.ComparisonActualOriginalQActualTripleGValue
public import ComparisonSignedCavityGTripleRowSupport
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQGWordSupportValue
public import SKProof.Port.ComparisonActualOriginalQGTripleRowAlgebra

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_triple_spine_G_high_sum_eq_row_original_q
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length)
    (V : ℝ) (hV : V≤M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) :
    ((nativeHighMarkedRows B base.target (pre.length+mid.length) 0).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed base.target) (pre.length+mid.length) 0).map (fun r=>r.coeff*
        ((nativeHighMarkedRows r.tree (r.embed (p.embed base.target)) (pre.length+mid.length) 0).map
          (fun z=>z.coeff*nativeActualTripleSpineGValue_original_q spine M U p r z q)).sum)).sum)).sum=
      nativeActualTripleSpineGRow_original_q spine M U V q := by
  rw [native_three_high_nested_full_of_support B base.target (pre.length+mid.length)
    (fun p r z=>nativeActualTripleSpineGValue_original_q spine M U p r z q) (by
      intro p hp r hr z hz hlow
      apply native_actual_triple_spine_G_value_zero_of_not_support_original_q spine M ho U hU p r hr z hz q
      intro HH
      exact hlow ⟨hs.trans_le HH.1,hs.trans_le HH.2.1,hs.trans_le HH.2.2.1⟩)]
  unfold nativeActualTripleSpineGRow_original_q
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  apply congrArg (fun a=>p.coeff*a)
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  apply congrArg (fun a=>r.coeff*a)
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  apply congrArg (fun a=>z.coeff*a)
  by_cases H : U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
      U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
      U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
      z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark
  · have HR:=M.R_monotone (partitionPoint_mono _ ho H.1)
    rw [ite_eq_left ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2,hV.trans HR⟩]
  · rw [native_actual_triple_spine_G_value_zero_of_not_support_original_q spine M ho U hU p r hr z hz q H]
    simp only [ite_self]

end OAI.SKFluctuations.Cavity
