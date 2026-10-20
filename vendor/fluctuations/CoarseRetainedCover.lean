module

public import CoarseThreeCellBudget
public import RetainedWindowGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def coarsePhysicalCentralCell {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (i : ℕ) : Finset (Fin (steps.length+1)) :=
  physicalIntervalCells steps (P (i+1)) (P (i+2))

theorem coarsePhysicalCentralCells_disjoint {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (hP : Monotone P) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (coarsePhysicalCentralCell steps P i) (coarsePhysicalCentralCell steps P j) := by
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  have hi := (mem_physicalIntervalCells steps _ _ k).mp hki
  have hj := (mem_physicalIntervalCells steps _ _ k).mp hkj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := hP (show i+2 ≤ j+1 by omega)
    omega
  · have hp := hP (show j+2 ≤ i+1 by omega)
    omega

theorem coarsePhysicalCentralCells_cover {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (hP : Monotone P) (N : ℕ) :
    (Finset.range N).biUnion (coarsePhysicalCentralCell steps P)=
      physicalIntervalCells steps (P 1) (P (N+1)) := by
  induction N with
  | zero => ext j; simp [coarsePhysicalCentralCell]
  | succ N ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ih]
    ext j
    simp only [Finset.mem_union,coarsePhysicalCentralCell,mem_physicalIntervalCells,Nat.add_assoc,Nat.reduceAdd]
    have h1 := hP (show 1 ≤ N+1 by omega)
    have h2 := hP (show N+1 ≤ N+2 by omega)
    omega

theorem coarsePhysicalCentralCells_mass_sum {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (hP : Monotone P) (I : Finset ℕ) :
    physicalWindowMass steps 0 (I.biUnion (coarsePhysicalCentralCell steps P))=
      ∑ i  ∈  I, physicalWindowMass steps 0 (coarsePhysicalCentralCell steps P i) := by
  unfold physicalWindowMass
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact coarsePhysicalCentralCells_disjoint steps P hP hij

def coarsePhysicalGoodCells {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (S : ℕ → ℝ) (N : ℕ) (osc : ℝ) : Finset (Fin (steps.length+1)) :=
  ((Finset.range N)\badThreeProfileBlocks S N osc).biUnion (coarsePhysicalCentralCell steps P)

theorem coarsePhysicalGoodCells_subset {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (hP : Monotone P) (S : ℕ → ℝ) (N : ℕ) (osc : ℝ)
    (hPN : P (N+1) ≤ steps.length) :
    coarsePhysicalGoodCells steps P S N osc ⊆ physicalIntervalCells steps 0 steps.length := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := Finset.mem_biUnion.mp hj
  have hiN := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  have hp := hP (show i+2 ≤ N+1 by omega)
  have hj' := (mem_physicalIntervalCells steps _ _ j).mp hij
  exact (mem_physicalIntervalCells steps 0 steps.length j).mpr ⟨Nat.zero_le _,by omega⟩

theorem coarsePhysicalGoodCells_omitted_mass {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (hP : Monotone P) (S : ℕ → ℝ) (hS : Monotone S)
    (N : ℕ) {osc width edge : ℝ} (hosc : 0<osc) (hwidth : 0 ≤ width)
    (hPN : P (N+1) ≤ steps.length)
    (hwhole : physicalWindowMass steps 0 (physicalIntervalCells steps 0 steps.length)=1)
    (hcentral : 1-edge ≤ physicalWindowMass steps 0 (physicalIntervalCells steps (P 1) (P (N+1))))
    (hcell : ∀ i ∈ Finset.range N, physicalWindowMass steps 0 (coarsePhysicalCentralCell steps P i) ≤ width) :
    physicalWindowMass steps 0
      ((physicalIntervalCells steps 0 steps.length)\coarsePhysicalGoodCells steps P S N osc) ≤ 
        edge+3*width*(S (N+2)-S 0)/osc := by
  let B := badThreeProfileBlocks S N osc
  let w := fun i => physicalWindowMass steps 0 (coarsePhysicalCentralCell steps P i)
  have hB : B ⊆ Finset.range N := Finset.filter_subset _ _
  have hb := badThreeProfileBlocks_mass_bound S hS N hosc hwidth w
    (fun i hi => hcell i (hB hi))
  have hsplit : (∑ i ∈ (Finset.range N)\B,w i)+(∑ i ∈ B,w i)=∑ i ∈ Finset.range N,w i :=
    Finset.sum_sdiff hB
  have hselected : physicalWindowMass steps 0 (coarsePhysicalGoodCells steps P S N osc)=
      ∑ i ∈ (Finset.range N)\B,w i :=
    coarsePhysicalCentralCells_mass_sum steps P hP _
  have htotal : physicalWindowMass steps 0 (physicalIntervalCells steps (P 1) (P (N+1)))=
      ∑ i ∈ Finset.range N,w i := by
    rw [← coarsePhysicalCentralCells_cover steps P hP N]
    exact coarsePhysicalCentralCells_mass_sum steps P hP _
  have hout : physicalWindowMass steps 0
      ((physicalIntervalCells steps 0 steps.length)\coarsePhysicalGoodCells steps P S N osc)+
      physicalWindowMass steps 0 (coarsePhysicalGoodCells steps P S N osc)=1 := by
    unfold physicalWindowMass
    rw [Finset.sum_sdiff (coarsePhysicalGoodCells_subset steps P hP S N osc hPN)]
    exact hwhole
  rw [hselected] at hout
  rw [htotal] at hcentral
  linarith

theorem coarsePhysicalGoodCells_index {ι : Type} (steps : List (GaussianStep ι))
    (P : ℕ → ℕ) (S : ℕ → ℝ) (N : ℕ) (osc : ℝ)
    {j : Fin (steps.length+1)} (hj : j ∈ coarsePhysicalGoodCells steps P S N osc) :
    ∃ i<N, S (i+3)-S i ≤ osc ∧ P (i+1) ≤ j.val ∧ j.val<P (i+2) := by
  obtain ⟨i,hi,hj⟩ := Finset.mem_biUnion.mp hj
  have hi' := Finset.mem_sdiff.mp hi
  have hn := Finset.mem_range.mp hi'.1
  have hgood : S (i+3)-S i ≤ osc := by
    by_contra h
    apply hi'.2
    exact Finset.mem_filter.mpr ⟨hi'.1,lt_of_not_ge h⟩
  exact ⟨i,hn,hgood,(mem_physicalIntervalCells steps _ _ j).mp hj⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
