module

public import ComparisonSignedCavityOriginalZeroRestoration

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem actual_general_original_zero_test_restoration
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (J : T.Assignment→ℝ) (hJ : ∀σ,J σ=0) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K T
      J=0 := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n bf hf
    hbf hhf (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (bf u:ℝ)≤bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (hf u:ℝ)≤hf v from hhf hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n bf hf
      hbf hhf) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  exact native_actual_law_restoration_zero_test n _ U b h K T ho _
    hJ
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm

theorem actual_general_original_high_pair_restoration_zero_payload
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (P : T.cavityLeft.Assignment→ℝ) (hP : ∀σ,P σ=0) (a c : T.Slot) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeOriginalHighPairRestoration n q U b h K S T P a c=0 := by
  dsimp only
  unfold nativeOriginalHighPairRestoration
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hy
  apply mul_eq_zero.mpr
  right
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hy
  rw [actual_general_original_zero_test_restoration bf hf hbf hhf r.tree ho U _
    (fun σ=>by rw [hP,zero_mul])]
  exact mul_zero _

theorem actual_general_original_G_diagonal_restoration_zero
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (J : T.Assignment→ℝ) (a c e : T.Slot) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeActualLawRestorationRemainder n q U b h K T
      (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e e σ)=0 := by
  dsimp only
  apply actual_general_original_zero_test_restoration bf hf hbf hhf T ho U
  intro σ
  simp only [nativeOriginalHighGAtom,ne_eq,not_true_eq_false,and_false,ite_false,mul_zero]

end OAI.SKFluctuations.Cavity
