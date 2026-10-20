module

public import CoarseRetainedCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Set
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

theorem retainedEqualWidthGoodCells_omitted_mass {ι : Type} (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    (u : ℕ → PositiveMass) (hu : ∀ i, u i ∈ as) (hU : Monotone (fun i => (u i).val))
    (N : ℕ) {a width osc : ℝ} (hwidth : 0 ≤ width) (hosc : 0<osc)
    (hgrid : ∀ i ≤ N+2, (u i).val=a+(i:ℝ)*width) (hunit : (u (N+2)).val=1)
    (S : ℕ → ℝ) (hS : Monotone S) (hS0 : 0 ≤ S 0) (hS1 : S (N+2) ≤ 1) :
    let steps := sampleClockSteps q 0 as
    let P := fun i => retainedMassPrefixIndex (u i).val as
    physicalWindowMass steps 0
      ((physicalIntervalCells steps 0 steps.length)\coarsePhysicalGoodCells steps P S N osc) ≤ 
        a+2*width+3*width/osc := by
  dsimp only
  let steps := sampleClockSteps q 0 as
  let P := fun i => retainedMassPrefixIndex (u i).val as
  have hP : Monotone P := fun i j hij =>
    retainedMassPrefixIndex_monotone as ho (u i) (u j) (hu i) (hu j) (hU hij)
  have hPN : P (N+1) ≤ steps.length := by
    simpa only [steps,sampleClockSteps_length] using retainedMassPrefixIndex_le_length (u (N+1)).val as
  have hwhole : physicalWindowMass steps 0 (physicalIntervalCells steps 0 steps.length)=1 := by
    rw [physicalIntervalMass _ 0 (Nat.zero_le _) (Nat.le_succ _)]
    simp only [steps,sampleClockSteps_length]
    rw [physicalCutMass_sampleClockSteps q 0 as as.length le_rfl,physicalPartitionPoint_length,hend]
    rw [physicalCutMass_sampleClockSteps q 0 as 0 (Nat.zero_le _)]
    cases as <;> simp [partitionPoint]
  have hcell (i : ℕ) (hi : i ∈ Finset.range N) :
      physicalWindowMass steps 0 (coarsePhysicalCentralCell steps P i) ≤ width := by
    have hgeom := (physicalRetainedWindow_geometry q as ho (u (i+1)) (u (i+2))
      (hu _) (hu _) (hU (by omega))).1
    have hiN := Finset.mem_range.mp hi
    change physicalWindowMass steps 0 (coarsePhysicalCentralCell steps P i)=_ at hgeom
    rw [hgeom,hgrid (i+2) (by omega),hgrid (i+1) (by omega)]
    simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hcentral : 1-(a+2*width) ≤ 
      physicalWindowMass steps 0 (physicalIntervalCells steps (P 1) (P (N+1))) := by
    have hgeom := (physicalRetainedWindow_geometry q as ho (u 1) (u (N+1))
      (hu _) (hu _) (hU (by omega))).1
    have htot := hgrid (N+2) le_rfl
    rw [hunit] at htot
    change physicalWindowMass steps 0 (physicalIntervalCells steps (P 1) (P (N+1)))=_ at hgeom
    rw [hgeom,hgrid (N+1) (by omega),hgrid 1 (by omega)]
    simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at htot ⊢
    linarith
  have hb := coarsePhysicalGoodCells_omitted_mass steps P hP S hS N hosc hwidth hPN hwhole hcentral hcell
  apply hb.trans
  apply add_le_add_right _
  simpa only [mul_one] using div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : S (N+2)-S 0 ≤ 1) (by positivity : 0 ≤ 3*width)) hosc.le

end OAI.SKFluctuations.LaplaceWindowFormalization
