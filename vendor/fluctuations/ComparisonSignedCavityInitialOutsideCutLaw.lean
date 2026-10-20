module

public import ComparisonSignedCavityInitialIndexedCutGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set
open scoped BigOperators
variable {S ι : Type} [Fintype S] [Fintype ι]
set_option maxHeartbeats 18000000

def nativeInitialDisorderJointRows {as : List PositiveMass} {T : ClockTree S as}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (ps : List (MarkedPlacement T)) (H : T.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  nativeInitialMarkedRowsValue ps (fun V R B=>V.disorderExpect w φ v q (fun σ=>H (R σ) (B σ)) x)

theorem native_initial_original_outside_eq_cut_add_retained_resampling
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (i : ℕ) (a : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeInitialDisorderJointRows w φ v q (nativeOutsideMarkedRows T s i a) H x=
      nativeInitialDisorderJointRows w φ v q (nativeInitialIndexedCutRows T i a) H x+
        nativeInitialDisorderJointRows w φ v q (nativeInitialOutsideCutResidualRows T s i a) H x :=
  native_initial_outside_to_indexed_cut_exact T s i a _

theorem native_initial_retained_resampling_eq_original_minus_cut
    {as : List PositiveMass} (T : ClockTree S as) (i : ℕ) (a : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeInitialDisorderJointRows w φ v q (nativeInitialRetainedPastCutRows T i a) H x=
      nativeInitialDisorderJointRows w φ v q (T.markedAttach a) H x-
        nativeInitialDisorderJointRows w φ v q (nativeInitialIndexedCutRows T i a) H x := by
  have H:=native_initial_retained_past_cut_exact T i a
    (fun V R B=>V.disorderExpect w φ v q (fun σ=>H (R σ) (B σ)) x)
  dsimp only [nativeInitialDisorderJointRows]
  linarith only [H]

theorem native_initial_cut_row_abs_le_mass_weighted_bound
    {as : List PositiveMass} (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (T : ClockTree S as) (ho : MassOrdered 0 as)
    (i : ℕ) (v : ι→ℝ) (q : ℕ→ι→ℝ) (H : T.Assignment→S→ℝ) (x : ι→ℝ)
    {C : ℝ} (hC : 0≤C)
    (hrow : ∀p∈nativeInitialIndexedCutRows T i 0,
      |p.tree.disorderExpect w φ v q (fun σ=>H (p.restrict σ) (p.spin σ)) x|≤C) :
    |nativeInitialDisorderJointRows w φ v q (nativeInitialIndexedCutRows T i 0) H x|≤
      2*(T.leaves:ℝ)*partitionPoint 0 as i*C := by
  dsimp only [nativeInitialDisorderJointRows,nativeInitialMarkedRowsValue]
  apply (abs_list_sum_le _).trans
  simp only [List.map_map,Function.comp_def,abs_mul]
  have Hsum : ((nativeInitialIndexedCutRows T i 0).map (fun p=>|p.coeff| *
      |p.tree.disorderExpect w φ v q (fun σ=>H (p.restrict σ) (p.spin σ)) x|)).sum≤
      ((nativeInitialIndexedCutRows T i 0).map (fun p=>|p.coeff| *C)).sum := by
    exact List.sum_le_sum (fun p hp=>mul_le_mul_of_nonneg_left (hrow p hp) (abs_nonneg _))
  apply Hsum.trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right (by simpa only [sub_zero] using native_initial_indexed_cut_variation T i ho) hC

end OAI.SKFluctuations.Cavity
