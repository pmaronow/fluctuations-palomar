module

public import CoarseRetainedGridCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Set
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

def coarseMassWidth (a : ℝ) (N : ℕ) : ℝ := (1-a)/(N+2:ℝ)

theorem coarseMassWidth_pos {a : ℝ} (ha : a<1) (N : ℕ) : 0<coarseMassWidth a N := by
  unfold coarseMassWidth
  positivity

def coarseMassNode {a : ℝ} (ha : 0<a) (ha1 : a<1) (N i : ℕ) : PositiveMass :=
  ⟨a+((min i (N+2):ℕ):ℝ)*coarseMassWidth a N, by
    have hw := (coarseMassWidth_pos ha1 N).le
    positivity⟩

theorem coarseMassNode_le_one {a : ℝ} (ha : 0<a) (ha1 : a<1) (N i : ℕ) :
    (coarseMassNode ha ha1 N i).val ≤ 1 := by
  have hden : 0<(N+2:ℝ) := by positivity
  have hm : ((min i (N+2):ℕ):ℝ) ≤ (N+2:ℝ) := by exact_mod_cast Nat.min_le_right i (N+2)
  have hw := mul_le_mul_of_nonneg_right hm (coarseMassWidth_pos ha1 N).le
  have he : (N+2:ℝ)*coarseMassWidth a N=1-a := by unfold coarseMassWidth; field_simp
  change a+((min i (N+2):ℕ):ℝ)*coarseMassWidth a N ≤ 1
  rw [he] at hw
  linarith

theorem coarseMassNode_monotone {a : ℝ} (ha : 0<a) (ha1 : a<1) (N : ℕ) :
    Monotone (fun i => (coarseMassNode ha ha1 N i).val) := by
  intro i j hij
  change a+((min i (N+2):ℕ):ℝ)*coarseMassWidth a N ≤ a+((min j (N+2):ℕ):ℝ)*coarseMassWidth a N
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast min_le_min_right (N+2) hij
  · exact (coarseMassWidth_pos ha1 N).le

theorem coarseMassNode_grid {a : ℝ} (ha : 0<a) (ha1 : a<1) (N i : ℕ) (hi : i ≤ N+2) :
    (coarseMassNode ha ha1 N i).val=a+(i:ℝ)*coarseMassWidth a N := by
  simp only [coarseMassNode,min_eq_left hi]

theorem coarseMassNode_last {a : ℝ} (ha : 0<a) (ha1 : a<1) (N : ℕ) :
    (coarseMassNode ha ha1 N (N+2)).val=1 := by
  rw [coarseMassNode_grid ha ha1 N (N+2) le_rfl]
  have he : (N+2:ℝ)*coarseMassWidth a N=1-a := by unfold coarseMassWidth; field_simp
  rw [show ((N+2:ℕ):ℝ)=(N+2:ℝ) by norm_num,he]
  ring

def coarseMassNodes {a : ℝ} (ha : 0<a) (ha1 : a<1) (N : ℕ) : List PositiveMass :=
  (List.range (N+3)).map (coarseMassNode ha ha1 N)

theorem coarseMassNodes_bound {a : ℝ} (ha : 0<a) (ha1 : a<1) (N : ℕ) :
    ∀ u ∈ coarseMassNodes ha ha1 N, u.val ≤ 1 := by
  intro u hu
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
  exact coarseMassNode_le_one ha ha1 N i

theorem coarseMassNode_mem {a : ℝ} (ha : 0<a) (ha1 : a<1) (N i : ℕ) :
    coarseMassNode ha ha1 N i ∈ coarseMassNodes ha ha1 N := by
  apply List.mem_map.mpr
  refine ⟨min i (N+2),List.mem_range.mpr (by omega),?_⟩
  apply Subtype.ext
  simp only [coarseMassNode,min_assoc,min_self]

theorem canonicalCoarseGoodCells_omitted_mass {ι : Type} (q : ℝ → ι → ℝ≥0)
    {a : ℝ} (ha : 0<a) (ha1 : a<1) (N k : ℕ) {osc : ℝ} (hosc : 0<osc)
    (S : ℕ → ℝ) (hS : Monotone S) (hS0 : 0 ≤ S 0) (hS1 : S (N+2) ≤ 1) :
    let as := finiteCutMasses (coarseMassNodes ha ha1 N) k
    let steps := sampleClockSteps q 0 as
    let P := fun i => retainedMassPrefixIndex (coarseMassNode ha ha1 N i).val as
    physicalWindowMass steps 0
      ((physicalIntervalCells steps 0 steps.length)\coarsePhysicalGoodCells steps P S N osc) ≤ 
        a+2*coarseMassWidth a N+3*coarseMassWidth a N/osc := by
  dsimp only
  apply retainedEqualWidthGoodCells_omitted_mass q _
    (finiteCutMasses_ordered _ (coarseMassNodes_bound ha ha1 N) k)
    (finiteCutMasses_end _ (coarseMassNodes_bound ha ha1 N) k)
    (coarseMassNode ha ha1 N)
    (fun i => finiteCutMasses_nodes _ k (coarseMassNode_mem ha ha1 N i))
    (coarseMassNode_monotone ha ha1 N) N
    (coarseMassWidth_pos ha1 N).le hosc
    (fun i hi => coarseMassNode_grid ha ha1 N i hi)
    (coarseMassNode_last ha ha1 N) S hS hS0 hS1

end OAI.SKFluctuations.LaplaceWindowFormalization
