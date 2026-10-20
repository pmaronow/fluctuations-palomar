module

public import ComparisonActualGeneralGWordSupportValue
public import ComparisonActualGeneralGTripleRowAlgebra
public import ComparisonSignedCavityGTripleRowSupport

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_triple_spine_G_high_sum_eq_row
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ) (hRadius : Monotone radius)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length)
    (V : ℝ) (hV : V≤radius (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) :
    ((nativeHighMarkedRows B base.target (pre.length+mid.length) 0).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed base.target) (pre.length+mid.length) 0).map (fun r=>r.coeff*
        ((nativeHighMarkedRows r.tree (r.embed (p.embed base.target)) (pre.length+mid.length) 0).map
          (fun z=>z.coeff*actualGeneralTripleSpineGValue spine bf hf U p r z q)).sum)).sum)).sum=
      actualGeneralTripleSpineGRow spine bf hf radius U V q := by
  rw [native_three_high_nested_full_of_support B base.target (pre.length+mid.length)
    (fun p r z=>actualGeneralTripleSpineGValue spine bf hf U p r z q) (by
      intro p hp r hr z hz hlow
      apply actual_general_triple_spine_G_value_zero_of_not_support spine bf hf ho U hU p r hr z hz q
      intro HH
      exact hlow ⟨hs.trans_le HH.1,hs.trans_le HH.2.1,hs.trans_le HH.2.2.1⟩)]
  unfold actualGeneralTripleSpineGRow
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
  · have HR:=hRadius (partitionPoint_mono _ ho H.1)
    rw [ite_eq_left ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2,hV.trans HR⟩]
  · rw [actual_general_triple_spine_G_value_zero_of_not_support spine bf hf ho U hU p r hr z hz q H]
    simp only [ite_self]

end OAI.SKFluctuations.Cavity
