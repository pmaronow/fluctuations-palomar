module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def badThreeProfileBlocks (S : ℕ → ℝ) (N : ℕ) (osc : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun i => osc < S (i+3)-S i)

theorem threeProfileBlocks_sum (S : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (S (i+3)-S i))=
      S (N+2)+S (N+1)+S N-S 2-S 1-S 0 := by
  induction N with
  | zero => simp; ring
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

theorem badThreeProfileBlocks_card_bound (S : ℕ → ℝ) (hS : Monotone S)
    (N : ℕ) (osc : ℝ) :
    osc*((badThreeProfileBlocks S N osc).card:ℝ) ≤ 3*(S (N+2)-S 0) := by
  have hb : ∑ i ∈ badThreeProfileBlocks S N osc, osc ≤
      ∑ i ∈ badThreeProfileBlocks S N osc, (S (i+3)-S i) :=
    Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
  have hs : ∑ i ∈ badThreeProfileBlocks S N osc, (S (i+3)-S i) ≤
      ∑ i ∈ Finset.range N, (S (i+3)-S i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i hi hni
    exact sub_nonneg.mpr (hS (by omega))
  simp only [Finset.sum_const,nsmul_eq_mul] at hb
  rw [threeProfileBlocks_sum] at hs
  nlinarith [hS (show 0≤1 by omega), hS (show 0≤2 by omega),
    hS (show N≤N+2 by omega), hS (show N+1≤N+2 by omega)]

theorem badThreeProfileBlocks_mass_bound (S : ℕ → ℝ) (hS : Monotone S)
    (N : ℕ) {osc width : ℝ} (hosc : 0 < osc) (hwidth : 0 ≤ width)
    (weight : ℕ → ℝ) (hw : ∀ i ∈ badThreeProfileBlocks S N osc, weight i ≤ width) :
    ∑ i ∈ badThreeProfileBlocks S N osc, weight i ≤
      3*width*(S (N+2)-S 0)/osc := by
  have hs := Finset.sum_le_sum hw
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := mul_le_mul_of_nonneg_left (badThreeProfileBlocks_card_bound S hS N osc) hwidth
  apply (le_div_iff₀ hosc).mpr
  have hh := mul_le_mul_of_nonneg_right hs hosc.le
  nlinarith

theorem badThreeProfileBlocks_equalWidth_bound (S : ℕ → ℝ) (hS : Monotone S)
    (N : ℕ) (hN : 0<N) {osc : ℝ} (hosc : 0<osc)
    (h0 : 0≤S 0) (h1 : S (N+2)≤1)
    (weight : ℕ → ℝ) (hw : ∀ i ∈ badThreeProfileBlocks S N osc, weight i≤1/(N:ℝ)) :
    ∑ i ∈ badThreeProfileBlocks S N osc, weight i ≤ 3/((N:ℝ)*osc) := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hb := badThreeProfileBlocks_mass_bound S hS N hosc (by positivity : 0≤1/(N:ℝ)) weight hw
  apply hb.trans
  apply (div_le_iff₀ hosc).mpr
  field_simp
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
