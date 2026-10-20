module

public import ComparisonSignedCavityOriginalCMarkedCanonicalSource
public import ComparisonSignedCavityGRestorationIntegral

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem ActualNaturalBoundaryShape.native_double_marked_low_pair_test
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (b S : ℕ→ℝ) (u z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    (fun σ=>(G.canonicalMinimumSource M forms).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
      (b (T.splitIndex u z)*(deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot u),false))
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot z),false))-
          S (T.splitIndex u z))))=
    fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalMinimumSource M forms).product σ*
      (b (r.tree.splitIndex (r.embed (p.embed u)) (r.embed (p.embed z)))*
        (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed (p.embed u))))
          (joinSpin (r.tree.atSlot σ (r.embed (p.embed z))))-
          S (r.tree.splitIndex (r.embed (p.embed u)) (r.embed (p.embed z))))) := by
  funext σ
  rw [G.nativeCDoubleMarkedLift_canonical_product M forms p hp r hr]
  rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  simp only [p.restRestrict_at,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

theorem actual_minimum_original_G_diagonal_restoration_zero
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (J : T.Assignment→ℝ) (a c e : T.Slot) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K T
      (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e e σ)=0 := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  exact native_actual_law_restoration_zero_test n _ U b h K T ho _
    (fun σ=>by simp only [nativeOriginalHighGAtom,ne_eq,not_true_eq_false,and_false,ite_false,mul_zero])
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm

end OAI.SKFluctuations.Cavity
