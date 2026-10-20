module

public import SKBarriers2.Dynamics.Anchors
public import SKOptimized.PredictableWindows
public import OAI.Probability.SKBarriers.Dynamics.PredictableGrid

@[expose] public section

noncomputable section

namespace SKBarriers2.Dynamics

open OAI.SK OAI.SK.Analytic Set Filter Classical
open scoped BigOperators Topology

theorem predictable_grid_profile_time_union_bound {N : ℕ} (hN : 0 < N)
    {K I : Type*} [Fintype K] [Fintype I]
    (center : K → (j : ℕ) → (Fin j → Fin N) → ℝ)
    (offset : ℕ → ℝ) (radius : I → ℕ → ℝ) (selected : I → ℕ → Prop)
    (width : ℝ) (hwidth : 0 < width)
    (hradius : ∀ a j, 0 ≤ radius a j) (p : ℕ) :
    ((SKOptimized.FiniteLaw.uniformFin N hN).iid (Fin p)).prob (fun z =>
      ∃ k : K, ∃ a : I, ∀ i : Fin p, selected a i.val →
        |center k i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
          SKOptimized.thresholdGrid N (offset i.val) width (z i)| ≤ radius a i.val) ≤
      (Fintype.card K : ℝ) * ∑ a : I, ∏ i : Fin p, if selected a i.val then
        (2 * radius a i.val / width + 1 / (N : ℝ)) else 1 := by
  classical
  refine (SKOptimized.FiniteLaw.prob_exists _ _).trans ?_
  calc
    _ ≤ ∑ k : K, ∑ a : I, ∏ i : Fin p, if selected a i.val then
        (2 * radius a i.val / width + 1 / (N : ℝ)) else 1 := by
      apply Finset.sum_le_sum
      intro k _
      exact SKOptimized.predictable_grid_profile_union_bound hN (center k)
        offset radius selected width hwidth hradius p
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem exists_grid_without_profile_at_time {N : ℕ} (hN : 0 < N)
    {K I : Type*} [Fintype K] [Fintype I]
    (center : K → (j : ℕ) → (Fin j → Fin N) → ℝ)
    (offset : ℕ → ℝ) (radius : I → ℕ → ℝ) (selected : I → ℕ → Prop)
    (width : ℝ) (hwidth : 0 < width)
    (hradius : ∀ a j, 0 ≤ radius a j) (p : ℕ)
    (hcount : (Fintype.card K : ℝ) * (∑ a : I, ∏ i : Fin p,
      if selected a i.val then (2 * radius a i.val / width + 1 / (N : ℝ)) else 1) < 1) :
    ∃ z : Fin p → Fin N, ¬ ∃ k : K, ∃ a : I,
      ∀ i : Fin p, selected a i.val →
        |center k i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
          SKOptimized.thresholdGrid N (offset i.val) width (z i)| ≤ radius a i.val := by
  classical
  by_contra h
  push Not at h
  let P := (SKOptimized.FiniteLaw.uniformFin N hN).iid (Fin p)
  have hfull : 1 ≤ P.prob (fun z => ∃ k : K, ∃ a : I,
      ∀ i : Fin p, selected a i.val →
        |center k i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
          SKOptimized.thresholdGrid N (offset i.val) width (z i)| ≤ radius a i.val) := by
    rw [← P.prob_true]
    exact P.prob_mono (fun z _ => h z)
  have hbound := predictable_grid_profile_time_union_bound hN center offset
    radius selected width hwidth hradius p
  exact (not_lt_of_ge (hfull.trans hbound)) hcount

def gridThresholdArray {N p : ℕ} (offset : ℕ → ℝ) (width : ℝ)
    (z : Fin p → Fin N) (i : ℕ) : ℝ :=
  if hi : i < p then SKOptimized.thresholdGrid N (offset i) width (z ⟨i, hi⟩)
  else offset i

private lemma gridThresholdArray_prefix {N p : ℕ} (offset : ℕ → ℝ) (width : ℝ)
    (z : Fin p → Fin N) {j : ℕ} (hj : j < p) :
    ∀ i < j, gridThresholdArray offset width z i =
      gridThresholdArray offset width (fun a : Fin j => z ⟨a.val, a.isLt.trans hj⟩) i := by
  intro i hi
  simp only [gridThresholdArray, dite_eq_left hi, dite_eq_left (hi.trans hj)]

namespace AnchorData

variable {n : ℕ} (D : AnchorData n)

def gridCenter {N : ℕ} (offset : ℕ → ℝ) (width : ℝ) (k j : ℕ)
    (z : Fin j → Fin N) : ℝ :=
  overlap (D.reference (gridThresholdArray offset width z) j) (D.x k)

lemma gridCenter_eq {N p : ℕ} (offset : ℕ → ℝ) (width : ℝ)
    (z : Fin p → Fin N) (k : ℕ) (i : Fin p) :
    D.gridCenter offset width k i.val (fun a => z ⟨a.val, a.isLt.trans i.isLt⟩) =
      overlap (D.reference (gridThresholdArray offset width z) i.val) (D.x k) := by
  unfold gridCenter
  rw [D.reference_predictable (gridThresholdArray offset width z)
    (gridThresholdArray offset width (fun a => z ⟨a.val, a.isLt.trans i.isLt⟩)) i.val
    (gridThresholdArray_prefix offset width z i.isLt)]

end AnchorData

theorem exists_grid_without_marker_witness {n N : ℕ} (D : AnchorData n)
    (hN : 0 < N) (hB : 0 < D.B) (hT0 : 0 ≤ D.scales.T0)
    (offset : ℕ → ℝ) (width : ℝ) (hwidth : 0 < width)
    (hcount : ((D.m : ℝ) + 1) * (2 * D.scales.T0 / width + 1 / (N : ℝ)) ^ D.M < 1) :
    ∃ z : Fin D.p → Fin N, ¬ ∃ k ≤ D.m, ∀ a < D.M,
      |overlap (D.reference (gridThresholdArray offset width z) (a * D.B)) (D.x k) -
        gridThresholdArray offset width z (a * D.B)| ≤ D.scales.T0 := by
  classical
  have hc : (Fintype.card (Fin (D.m + 1)) : ℝ) *
      (∑ _a : Unit, ∏ i : Fin D.p, if i.val % D.B = 0 then
        (2 * D.scales.T0 / width + 1 / (N : ℝ)) else 1) < 1 := by
    rw [Fintype.sum_unique]
    change (Fintype.card (Fin (D.m + 1)) : ℝ) *
      (∏ i : Fin (D.B * D.M), if i.val % D.B = 0 then
        (2 * D.scales.T0 / width + 1 / (N : ℝ)) else 1) < 1
    rw [prod_block_marker D.B D.M hB]
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hcount
  obtain ⟨z, hz⟩ := exists_grid_without_profile_at_time hN
    (fun k : Fin (D.m + 1) => D.gridCenter offset width k.val)
    offset (fun _ : Unit => fun _ => D.scales.T0)
    (fun _ : Unit => fun i => i % D.B = 0) width hwidth (fun _ _ => hT0) D.p
    (by
      convert hc using 1
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> rfl)
  refine ⟨z, ?_⟩
  rintro ⟨k, hk, hw⟩
  apply hz
  refine ⟨⟨k, by omega⟩, (), ?_⟩
  intro i hi
  rw [D.gridCenter_eq]
  have ha : i.val / D.B < D.M := by
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    simpa only [AnchorData.p, Nat.mul_comm] using i.isLt
  have he : i.val / D.B * D.B = i.val := by
    have hm := Nat.mod_add_div i.val D.B
    rw [hi, zero_add, Nat.mul_comm] at hm
    exact hm
  have hw' := hw (i.val / D.B) ha
  rw [he] at hw'
  simpa only [gridThresholdArray, dite_eq_left i.isLt] using hw'

private lemma exists_fine_marker_grid (m M : ℕ) (γ₀ : ℝ)
    (hcount : ((m : ℝ) + 1) * γ₀ ^ M < 1) :
    ∃ N : ℕ, 0 < N ∧ ((m : ℝ) + 1) * (γ₀ + 1 / (N : ℝ)) ^ M < 1 := by
  have hlim : Tendsto (fun N : ℕ => ((m : ℝ) + 1) * (γ₀ + 1 / (N : ℝ)) ^ M)
      atTop (𝓝 (((m : ℝ) + 1) * γ₀ ^ M)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.mul ((tendsto_const_nhds.add
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0))).pow M)
  exact ((eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds hcount))).exists

structure ThresholdIntervalGeometry {n : ℕ} (D : AnchorData n)
    (offset : ℕ → ℝ) (width : ℝ) : Prop where
  width_pos : 0 < width
  range : ∀ i < D.p, D.scales.tLo ≤ offset i ∧ offset i + width ≤ D.scales.tHi
  separation : ∀ i a, i < a → a < D.p →
    D.scales.S ≤ offset a - (offset i + width)

theorem ThresholdIntervalGeometry.thresholdGeometry {n : ℕ} {D : AnchorData n}
    {offset : ℕ → ℝ} {width : ℝ} (g : ThresholdIntervalGeometry D offset width)
    {r : ℕ → ℝ} (hr : ∀ i < D.p, r i ∈ Icc (offset i) (offset i + width)) :
    ThresholdGeometry D r := by
  constructor
  · intro i hi
    exact ⟨(g.range i hi).1.trans (hr i hi).1, (hr i hi).2.trans (g.range i hi).2⟩
  · intro i a hia ha
    have hi := hr i (hia.trans ha)
    have ha' := hr a ha
    linarith only [g.separation i a hia ha, hi.2, ha'.1]

theorem exists_thresholds_without_marker_witness {n : ℕ} {D : AnchorData n}
    (hB : 0 < D.B) (hT0 : 0 ≤ D.scales.T0)
    {offset : ℕ → ℝ} {width : ℝ} (g : ThresholdIntervalGeometry D offset width)
    (hcount : ((D.m : ℝ) + 1) * (2 * D.scales.T0 / width) ^ D.M < 1) :
    ∃ r : ℕ → ℝ, ThresholdGeometry D r ∧
      ¬ ∃ k ≤ D.m, ∀ a < D.M,
        |overlap (D.reference r (a * D.B)) (D.x k) - r (a * D.B)| ≤ D.scales.T0 := by
  obtain ⟨N, hN, hcountN⟩ := exists_fine_marker_grid D.m D.M
    (2 * D.scales.T0 / width) hcount
  obtain ⟨z, hz⟩ := exists_grid_without_marker_witness D hN hB hT0
    offset width g.width_pos hcountN
  refine ⟨gridThresholdArray offset width z, g.thresholdGeometry ?_, hz⟩
  intro i hi
  rw [gridThresholdArray, dite_eq_left hi]
  exact SKOptimized.thresholdGrid_mem hN g.width_pos (offset i) (z ⟨i, hi⟩)

theorem positive_endpoint_of_marker_count {n : ℕ} {D : AnchorData n}
    (h : AnchorHypotheses D) {offset : ℕ → ℝ} {width : ℝ}
    (g : ThresholdIntervalGeometry D offset width)
    (hcount : ((D.m : ℝ) + 1) * (2 * D.scales.T0 / width) ^ D.M < 1) :
    0 < overlap (D.pick 0 D.fallback 0) (D.x D.m) := by
  have hB : 0 < D.B := by have := h.block_size; omega
  have hT0 : 0 ≤ D.scales.T0 := by
    dsimp [AnchorScales.T0]
    linarith only [h.numerics.epsilon_pos, h.numerics.transfer_nonneg, h.numerics.jump_nonneg]
  obtain ⟨r, hg, hno⟩ := exists_thresholds_without_marker_witness hB hT0 g hcount
  exact positive_endpoint_of_no_marker_witness h r hg hno

end SKBarriers2.Dynamics
