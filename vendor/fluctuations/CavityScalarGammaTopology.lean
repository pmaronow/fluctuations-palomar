module

public import CavityScalarAttachmentTopology
public import CavityFullRetainedCoefficients
public import CavityAttachedTree

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

def scalarCutPairAtSplit (as : List PositiveMass) (U : ℕ) (K : ℕ→ℝ) (j : ℕ) : ℝ :=
  (ClockTree.pairClock (S:=Bool) as j).disorderExpect (fun _=>(1/2:ℝ)) scalarFeature 0
    (fun k _=>relocatedClock U 0 K k)
    (fun σ=>spinValue (ClockTree.pairSpin as j σ).1*
      spinValue (ClockTree.pairSpin as j σ).2) 0

def scalarGammaFromTopology (as : List PositiveMass) (U : ℕ) (K : ℕ→ℝ)
    (j : ℕ) (diagonal : ℝ) : ℝ :=
  diagonal+(1-diagonal)*scalarCutPairAtSplit as U K j

theorem scalarCutGamma_eq_pair_or_diagonal {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (a c : T.Slot) :
    scalarCutGamma T U K a c =
      if a=c then 1 else scalarCutPairAtSplit as U K (T.splitIndex a c) := by
  classical
  by_cases hac : a=c
  · subst c
    simp only [ite_true,scalarCutGamma,scalarCutMoment,ClockTree.slotProduct,mul_one]
    have he : (fun σ=>spinValue (T.atSlot σ a)*spinValue (T.atSlot σ a))=(fun _=>1) := by
      funext σ
      exact spinValue_sq _
    rw [he,T.disorderExpect_one (by intro σ; norm_num) scalarFeature ho]
  · simp only [hac,ite_false,scalarCutGamma,scalarCutMoment,ClockTree.slotProduct,mul_one]
    exact T.disorderExpect_pairAtSlot_actual (w:=fun _=>(1/2:ℝ))
      (by intro σ; norm_num) scalarFeature ho
      0 (fun k _=>relocatedClock U 0 K k) 0 a c hac (fun σ τ=>spinValue σ*spinValue τ)

theorem fullScalarCutGamma_marked_eq_topology {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (p : ClockTree.MarkedPlacement T) :
    fullScalarCutGamma p.tree U K (p.embed s) p.mark=
      scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark) (p.hit s) := by
  classical
  change scalarCutGamma p.tree.cavityRight U K
    (p.tree.cavityRightSlot (p.embed s)) (p.tree.cavityRightSlot p.mark)=_
  rw [scalarCutGamma_eq_pair_or_diagonal p.tree.cavityRight ho,
    p.tree.splitIndex_cavityRight]
  have heq : p.tree.cavityRightSlot (p.embed s)=p.tree.cavityRightSlot p.mark ↔
      p.embed s=p.mark := (p.tree.cavityRightSlot).injective.eq_iff
  by_cases h : p.embed s=p.mark
  · simp only [if_pos (heq.mpr h),scalarGammaFromTopology,ClockTree.MarkedPlacement.hit,
      if_pos h.symm,sub_self,zero_mul,add_zero]
  · have hn : p.tree.cavityRightSlot (p.embed s)≠p.tree.cavityRightSlot p.mark :=
      fun H=>h (heq.mp H)
    simp only [if_neg hn,scalarGammaFromTopology,ClockTree.MarkedPlacement.hit,
      if_neg (Ne.symm h),sub_zero,one_mul,zero_add]

theorem scalarCutGamma_marked_eq_topology {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (p : ClockTree.MarkedPlacement T) :
    scalarCutGamma p.tree U K (p.embed s) p.mark=
      scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark) (p.hit s) := by
  classical
  rw [scalarCutGamma_eq_pair_or_diagonal p.tree ho]
  by_cases h : p.embed s=p.mark
  · simp only [if_pos h,scalarGammaFromTopology,ClockTree.MarkedPlacement.hit,
      if_pos h.symm,sub_self,zero_mul,add_zero]
  · simp only [if_neg h,scalarGammaFromTopology,ClockTree.MarkedPlacement.hit,
      if_neg (Ne.symm h),sub_zero,one_mul,zero_add]

theorem native_full_gamma_row_eq_scalar (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (a : ℝ) :
    ((T.markedAttach a).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum =
    (((T.scalarTopology).markedAttach a).map (fun p=>p.coeff*
      scalarCutGamma p.tree U K (p.embed (T.scalarTopologySlot s)) p.mark)).sum := by
  simp_rw [fullScalarCutGamma_marked_eq_topology T ho,
    scalarCutGamma_marked_eq_topology T.scalarTopology ho]
  exact T.markedAttach_scalar_topology_fold a s (scalarGammaFromTopology as U K)

theorem native_rest_gamma_row_eq_scalar (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (a : ℝ) :
    ((T.markedAttach a).map (fun p=>p.coeff*
      scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark) (p.hit s))).sum =
    (((T.scalarTopology).markedAttach a).map (fun p=>p.coeff*
      scalarCutGamma p.tree U K (p.embed (T.scalarTopologySlot s)) p.mark)).sum := by
  simp_rw [scalarCutGamma_marked_eq_topology T.scalarTopology ho]
  exact T.markedAttach_scalar_topology_fold a s (scalarGammaFromTopology as U K)

end OAI.SKFluctuations.Cavity
