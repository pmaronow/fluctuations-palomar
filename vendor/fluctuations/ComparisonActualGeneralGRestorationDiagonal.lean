module

public import ComparisonSignedCavityGRestorationIntegral

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem actual_general_G_word_diagonal_restoration_zero
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (g : NativeOriginalGMarkedWord T) (U : ℕ) (P : T.Assignment→ℝ) (a : T.Slot)
    (hdiag : g.z.embed g.r.mark=g.z.mark) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K g.tree
      (g.originalRestorationTest U K b S P a)=0 := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n bf hf
    hbf hhf (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (bf u:ℝ) ≤ bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (hf u:ℝ) ≤ hf v from hhf hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n bf hf hbf hhf) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  exact native_actual_law_restoration_zero_test n _ U b h K g.tree ho _
    (g.originalRestorationTest_diagonal_zero U K b S P a hdiag)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm

end OAI.SKFluctuations.Cavity
