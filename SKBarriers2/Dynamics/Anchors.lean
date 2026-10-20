module

public import SKBarriers2.Dynamics.AnchorsBasic

@[expose] public section

noncomputable section
namespace SKBarriers2.Dynamics

open OAI.SK OAI.SK.Analytic Set
open SKOptimized (retainedSuccessor laterRetained)

lemma reset_block_start {B j : ℕ} (_hB : 0 < B) (hj : 0 < j) (hr : j % B = 0) :
    (j - 1) / B * B + B = j := by
  have hmul : j / B * B = j := by
    have hh := Nat.mod_add_div j B
    rw [hr] at hh
    simpa only [Nat.zero_add, Nat.mul_comm B] using hh
  have hq : j / B = (j - 1) / B + 1 := by
    simpa only [Nat.sub_add_cancel hj] using
      (Nat.succ_div_of_dvd (a := j - 1) (b := B) (by
        simpa only [Nat.sub_add_cancel hj] using Nat.dvd_of_mod_eq_zero hr))
  rw [hq, Nat.add_mul, one_mul] at hmul
  exact hmul

lemma reset_protects_prefix {B H j : ℕ} {A D : Finset ℕ}
    (hB : H + 2 ≤ B) (hj : 0 < j) (hr : j % B = 0)
    (hp : PrefixShape B H j A) (hs : IsRetainedSuffix A D) (hc : D.card ≤ H) :
    ∀ i ∈ A, i < j - H → i ∈ A \ D := by
  have hb : 0 < B := by omega
  have hstart := reset_block_start hb hj hr
  have hblock : Finset.Ico ((j - 1) / B * B) (((j - 1) / B * B) + B) ⊆ A := by
    intro i hi
    obtain ⟨hil, hiu⟩ := Finset.mem_Ico.mp hi
    exact hp.2.1 i hil (by omega)
  intro i hi hit
  apply (complete_block_protection hs hc hB hblock).1 i hi
  omega

lemma terminal_suffix_interval {A D : Finset ℕ} {s j : ℕ}
    (hsj : s ≤ j) (hA : ∀ i ∈ A, i < j) (hfull : ∀ i, s ≤ i → i < j → i ∈ A)
    (hs : IsRetainedSuffix A D) (hbefore : ∀ i ∈ D, s ≤ i) :
    ∃ c, s ≤ c ∧ c ≤ j ∧ D = Finset.Ico c j := by
  classical
  by_cases hd : D.Nonempty
  · let c := D.min' hd
    have hcm : c ∈ D := Finset.min'_mem D hd
    have hcj := hA c (hs.1 hcm)
    refine ⟨c, hbefore c hcm, hcj.le, ?_⟩
    ext i
    constructor
    · intro hi
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le D i hi, hA i (hs.1 hi)⟩
    · intro hi
      obtain ⟨hci, hij⟩ := Finset.mem_Ico.mp hi
      exact hs.2 hcm (hfull i ((hbefore c hcm).trans hci) hij) hci
  · have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
    exact ⟨j, hsj, le_rfl, by simp only [he, Finset.Ico_self]⟩

theorem prefixShape_step {B H j : ℕ} {A D : Finset ℕ}
    (hB : H + 2 ≤ B) (hj : 0 < j) (hp : PrefixShape B H j A)
    (hs : IsRetainedSuffix A D) (hc : D.card ≤ H)
    (hcompat : j % B ≠ 0 → j - 1 ∉ D) :
    PrefixShape B H (j + 1) (insert j (A \ D)) := by
  classical
  have hBpos : 0 < B := by omega
  have hrange : ∀ i ∈ insert j (A \ D), i < j + 1 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · exact Nat.lt_succ_of_lt (hp.1 i (Finset.mem_sdiff.mp hi).1)
  have hdivmul := Nat.div_mul_le_self j B
  have hprev := Nat.div_mul_le_self (j - 1) B
  by_cases hr : j % B = 0
  · have hstart := reset_block_start hBpos hj hr
    have hq : j / B = (j - 1) / B + 1 := by
      simpa only [Nat.sub_add_cancel hj] using
        (Nat.succ_div_of_dvd (a := j - 1) (b := B) (by
          simpa only [Nat.sub_add_cancel hj] using Nat.dvd_of_mod_eq_zero hr))
    have hmul : j / B * B = j := by rw [hq, Nat.add_mul, one_mul]; exact hstart
    have hbefore : ∀ i ∈ D, (j - 1) / B * B ≤ i := by
      intro i hi
      by_contra h
      have hiA := hs.1 hi
      have hsurv := reset_protects_prefix hB hj hr hp hs hc i hiA (by omega)
      exact (Finset.mem_sdiff.mp hsurv).2 hi
    obtain ⟨c, hcl, hcj, hD⟩ := terminal_suffix_interval (hprev.trans (by omega)) hp.1 hp.2.1 hs hbefore
    have hcard : j - c ≤ H := by simpa only [hD, Nat.card_Ico] using hc
    refine ⟨hrange, ?_, ?_⟩
    · intro i hil hij
      simp only [Nat.add_sub_cancel, hmul] at hil
      have he : i = j := by omega
      rw [he]
      exact Finset.mem_insert_self _ _
    · intro b hb
      simp only [Nat.add_sub_cancel] at hb
      by_cases hold : b < (j - 1) / B
      · obtain ⟨h, hh, hprefix⟩ := hp.2.2 b hold
        refine ⟨h, hh, ?_⟩
        intro i hil hiu
        have hbs := Nat.mul_le_mul_right B (show b + 1 ≤ (j - 1) / B by omega)
        have hij : i < j := by omega
        have hiD : i ∉ D := by rw [hD]; simp only [Finset.mem_Ico]; omega
        have hijne : i ≠ j := by omega
        simpa only [Finset.mem_insert, hijne, false_or, Finset.mem_sdiff, hiD,
          not_false_eq_true, and_true] using hprefix i hil hiu
      · have he : b = (j - 1) / B := by omega
        subst b
        refine ⟨j - c, hcard, ?_⟩
        intro i hil hiu
        have hiu' : i < j := by
          rw [Nat.add_mul, one_mul] at hiu
          omega
        have hiA := hp.2.1 i hil hiu'
        have hijne : i ≠ j := by omega
        simp only [Finset.mem_insert, hijne, false_or, Finset.mem_sdiff, hiA, true_and,
          hD, Finset.mem_Ico]
        rw [Nat.add_mul, one_mul]
        omega
  · have hq : j / B = (j - 1) / B := by
      simpa only [Nat.sub_add_cancel hj] using
        (Nat.succ_div_of_not_dvd (a := j - 1) (b := B) (by
          simpa only [Nat.sub_add_cancel hj] using
            (fun hd => hr (Nat.mod_eq_zero_of_dvd hd))))
    have hlast := hp.2.1 (j - 1) hprev (by omega)
    have hD : D = ∅ := retainedSuffix_empty_of_last hs
      (fun i hi => Nat.le_pred_of_lt (hp.1 i hi)) hlast (hcompat hr)
    rw [hD, Finset.sdiff_empty]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hD, Finset.sdiff_empty] using hrange
    · intro i hil hij
      simp only [Nat.add_sub_cancel, hq] at hil
      by_cases he : i = j
      · rw [he]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hp.2.1 i hil (by omega))
    · intro b hb
      simp only [Nat.add_sub_cancel, hq] at hb
      obtain ⟨h, hh, hprefix⟩ := hp.2.2 b hb
      refine ⟨h, hh, ?_⟩
      intro i hil hiu
      have hbs := Nat.mul_le_mul_right B (show b + 1 ≤ (j - 1) / B by omega)
      have hijne : i ≠ j := by omega
      simpa only [Finset.mem_insert, hijne, false_or] using hprefix i hil hiu

namespace AnchorData

variable {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ)

lemma run_refs (j i : ℕ) (hi : i < j) : (D.run r j).refs i = D.reference r i := by
  exact greedyRun_refs D.fallback D.pick D.x r D.scales.b D.m j i hi

lemma run_range (j : ℕ) : ∀ i ∈ (D.run r j).kept, i < j := by
  exact greedyRun_range D.fallback D.pick D.x r D.scales.b D.m j

lemma reference_mem (h : AnchorHypotheses D) (i : ℕ) (hi : i < D.p) :
    D.reference r i ∈ D.pool i := by
  unfold reference greedyReference pick bankPick
  split_ifs with hsel
  · exact hsel.choose_spec.1
  · exact h.fallback_mem i hi

lemma run_step_kept (j : ℕ) :
    (D.run r (j + 1)).kept = insert j ((D.run r j).kept \ D.deletions r j) := by
  rfl

lemma run_step_time (j : ℕ) (hj : j ≠ 0) :
    (D.run r (j + 1)).time =
      lastCrossing (fun k => overlap (D.reference r j) (D.x k)) (r j) (D.run r j).time := by
  simp only [run, greedyRun, ite_eq_right hj]
  rfl

lemma reference_zero : D.reference r 0 = D.pick 0 D.fallback 0 := by
  rfl

lemma reference_predictable (s : ℕ → ℝ) (i : ℕ) (hi : ∀ a < i, r a = s a) :
    D.reference r i = D.reference s i := by
  exact greedyReference_predictable D.fallback D.pick D.x r s D.scales.b D.m i hi

end AnchorData

theorem AnchorState.threshold_window {n : ℕ} {D : AnchorData n} {r : ℕ → ℝ} {j : ℕ}
    (hn : AnchorNumerics D.scales) (st : AnchorState D r j)
    {i : ℕ} (hi : i ∈ (D.run r j).kept) :
    |overlap (D.reference r i) (D.x (D.run r j).time) - r i| ≤ D.scales.T1 := by
  have hir := st.shape.1 i hi
  by_cases hlast : i = j - 1
  · rw [hlast]
    have hb := st.latest_band
    have hd : |overlap (D.reference r (j - 1)) (D.x (D.run r j).time) - r (j - 1)| ≤
        D.scales.d := by
      apply abs_le.mpr
      constructor <;> linarith [hb.1, hb.2, hn.jump_nonneg]
    exact hd.trans hn.jump_le_T1
  · have hil : i < j - 1 := by omega
    have hw := st.strict_window i hi hil
    have hc := st.center_rewired i hi hil
    have ht := abs_add_le
      (overlap (D.reference r i) (D.x (D.run r j).time) -
        overlap (D.reference r i) (D.reference r (retainedSuccessor (D.run r j).kept i)))
      (overlap (D.reference r i) (D.reference r (retainedSuccessor (D.run r j).kept i)) - r i)
    rw [sub_add_sub_cancel] at ht
    dsimp [AnchorScales.A1, AnchorScales.T1] at *
    linarith

theorem AnchorState.original_window {n : ℕ} {D : AnchorData n} {r : ℕ → ℝ} {j : ℕ}
    (st : AnchorState D r j) {i : ℕ} (hi : i ∈ (D.run r j).kept)
    (hil : i < j - 1) (ho : i + 1 ∈ (D.run r j).kept) :
    |overlap (D.reference r i) (D.x (D.run r j).time) - r i| ≤ D.scales.T0 := by
  have hw := st.strict_window i hi hil
  have hc := st.center_original i hi hil ho
  have ht := abs_add_le
    (overlap (D.reference r i) (D.x (D.run r j).time) -
      overlap (D.reference r i) (D.reference r (retainedSuccessor (D.run r j).kept i)))
    (overlap (D.reference r i) (D.reference r (retainedSuccessor (D.run r j).kept i)) - r i)
  rw [sub_add_sub_cancel] at ht
  dsimp [AnchorScales.A0, AnchorScales.T0] at *
  linarith

theorem anchor_initial_state {n : ℕ} {D : AnchorData n}
    (h : AnchorHypotheses D) {r : ℕ → ℝ} (hg : ThresholdGeometry D r)
    (hend : overlap (D.reference r 0) (D.x D.m) ≤ 0) : AnchorState D r 1 := by
  classical
  have hB : 0 < D.B := by have := h.block_size; omega
  have hp : 0 < D.p := Nat.mul_pos hB (by have := h.blocks_pos; omega)
  have hc := h.coverage 0 hp D.fallback (by intro i hi; omega) 0 (Nat.zero_le _)
    (by intro i _ hi; omega)
  have hsel : D.scales.qStar ≤ overlap (D.reference r 0) (D.x 0) := by
    rw [D.reference_zero r]
    exact (bankPick_spec D.pool D.fallback D.B D.x (D.scales.C / 3)
      D.scales.qStar 0 D.fallback 0 (by
        simpa only [show 3 * (D.scales.C / 3) = D.scales.C by ring] using hc)).1
  have hr := hg.range 0 hp
  have hstart : r 0 < overlap (D.reference r 0) (D.x 0) := by
    have hT : 0 ≤ D.scales.T1 := h.numerics.jump_nonneg.trans h.numerics.jump_le_T1
    linarith [h.numerics.selection_margin, hr.2]
  have hband := firstCrossing_band (fun k => overlap (D.reference r 0) (D.x k))
    (r 0) D.scales.d D.m hstart (by linarith [h.numerics.threshold_pos, hr.1])
    (h.jumps (D.reference r 0))
  have hkept : (D.run r 1).kept = {0} := by
    simp [AnchorData.run, greedyRun]
  have htime : (D.run r 1).time =
      firstCrossing (fun k => overlap (D.reference r 0) (D.x k)) (r 0) D.m := by
    rfl
  refine ⟨by simpa only [htime] using hband.1,
    (fun i hi => D.run_refs r 1 i hi), (fun i hi => D.reference_mem r h i (by omega)),
    ?_, ?_, hsel, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkept]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have he : i = 0 := Finset.mem_singleton.mp hi
      omega
    · intro i _ hi
      have he : i = 0 := by omega
      simpa only [he] using Finset.mem_singleton_self 0
    · intro b hb
      simp only [Nat.sub_self, Nat.zero_div] at hb
      omega
  · rw [hkept]; exact Finset.mem_singleton_self _
  · simpa only [Nat.sub_self, hkept] using Finset.mem_singleton_self 0
  · simpa only [Nat.sub_self, htime] using hband.2
  · intro i _ hi; omega
  · intro i _ hi; omega
  · intro i _ hi; omega
  · intro i hi a ha hia
    rw [hkept] at hi ha
    have := Finset.mem_singleton.mp hi
    have := Finset.mem_singleton.mp ha
    omega
  · intro i _ hi; omega

namespace AnchorData

variable {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ)

lemma deletions_eq (j : ℕ) : D.deletions r j =
    (D.run r j).kept.filter (fun i => D.scales.b < |overlap (D.reference r i) (D.reference r j)|) := by
  classical
  apply Finset.filter_congr
  intro i hi
  rw [D.run_refs r j i (D.run_range r j i hi)]

end AnchorData

structure GreedySelection {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ) (j : ℕ) : Prop where
  selected : D.scales.qStar ≤ overlap (D.reference r j) (D.x (D.run r j).time)
  cell : ∀ i, j / D.B * D.B ≤ i → i < j →
    |overlap (D.reference r i) (D.reference r j)| ≤ D.scales.C
  transferred : ∀ i ∈ (D.run r j).kept, i ∉ D.deletions r j →
    |overlap (D.reference r i) (D.reference r j) -
      overlap (D.reference r i) (D.x (D.run r j).time)| ≤ D.scales.ζ
  new_pair : ∀ i ∈ (D.run r j).kept, i ∉ D.deletions r j →
    |overlap (D.reference r i) (D.reference r j) - r i| ≤ D.scales.V
  suffix : IsRetainedSuffix (D.run r j).kept (D.deletions r j)
  card : (D.deletions r j).card ≤ D.H
  nonreset_empty : j % D.B ≠ 0 → D.deletions r j = ∅
  shape_next : PrefixShape D.B D.H (j + 1) (D.run r (j + 1)).kept
  zero_survives : 0 ∈ (D.run r j).kept \ D.deletions r j

theorem greedy_selection {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (hg : ThresholdGeometry D r) {j : ℕ}
    (hj : 0 < j) (hjp : j < D.p) (st : AnchorState D r j) : GreedySelection D r j := by
  classical
  have hB : 0 < D.B := by have := h.block_size; omega
  have hcellrange := Nat.mul_le_mul_right D.B
    (Nat.div_le_div_right (show j - 1 ≤ j by omega) : (j - 1) / D.B ≤ j / D.B)
  have htarget (i : ℕ) (hi : i ∈ (D.run r j).kept) :
      |overlap (D.reference r i) (D.x (D.run r j).time)| ≤ D.scales.tHi + D.scales.T1 := by
    have hw := st.threshold_window h.numerics hi
    have hr := hg.range i ((D.run_range r j i hi).trans hjp)
    have hrpos : 0 ≤ r i := h.numerics.threshold_pos.le.trans hr.1
    have ht := abs_add_le
      (overlap (D.reference r i) (D.x (D.run r j).time) - r i) (r i)
    rw [sub_add_cancel, abs_of_nonneg hrpos] at ht
    linarith [hr.2]
  have hcov := h.coverage j hjp (D.run r j).refs
    (fun i hi => by rw [D.run_refs r j i hi]; exact D.reference_mem r h i (hi.trans hjp))
    (D.run r j).time st.time_le (by
      intro i hil hij
      rw [D.run_refs r j i hij]
      have hi := st.shape.2.1 i (hcellrange.trans hil) hij
      have ht := htarget i hi
      linarith [h.numerics.cell_margin, h.numerics.T1_le_V])
  have hspec := bankPick_spec D.pool D.fallback D.B D.x (D.scales.C / 3)
    D.scales.qStar j (D.run r j).refs (D.run r j).time (by
      simpa only [show 3 * (D.scales.C / 3) = D.scales.C by ring] using hcov)
  change D.scales.qStar ≤ overlap (D.reference r j) (D.x (D.run r j).time) ∧ _ at hspec
  have hcell : ∀ i, j / D.B * D.B ≤ i → i < j →
      |overlap (D.reference r i) (D.reference r j)| ≤ D.scales.C := by
    intro i hil hij
    have ht := hspec.2 i hil hij
    rw [D.run_refs r j i hij] at ht
    change |overlap (D.reference r i) (D.reference r j)| ≤ 3 * (D.scales.C / 3) at ht
    simpa only [show 3 * (D.scales.C / 3) = D.scales.C by ring] using ht
  have hcompat (i : ℕ) (hi : i ∈ (D.run r j).kept) (hd : i ∉ D.deletions r j) :
      |overlap (D.reference r i) (D.reference r j)| ≤ D.scales.b := by
    rw [D.deletions_eq r j] at hd
    simpa only [Finset.mem_filter, hi, true_and, not_lt] using hd
  have htransfer (i : ℕ) (hi : i ∈ (D.run r j).kept) (hd : i ∉ D.deletions r j) :
      |overlap (D.reference r i) (D.reference r j) -
        overlap (D.reference r i) (D.x (D.run r j).time)| ≤ D.scales.ζ := by
    apply h.transfer i j (D.run_range r j i hi) hjp
      (D.reference r i) (D.reference_mem r h i ((D.run_range r j i hi).trans hjp))
      (D.reference r j) (D.reference_mem r h j hjp)
      (D.run r j).time st.time_le hspec.1 (hcompat i hi hd)
    linarith [htarget i hi, h.numerics.cell_margin, h.numerics.conflict_margin, h.numerics.T1_le_V]
  have hnew (i : ℕ) (hi : i ∈ (D.run r j).kept) (hd : i ∉ D.deletions r j) :
      |overlap (D.reference r i) (D.reference r j) - r i| ≤ D.scales.V := by
    have ht := abs_add_le
      (overlap (D.reference r i) (D.reference r j) -
        overlap (D.reference r i) (D.x (D.run r j).time))
      (overlap (D.reference r i) (D.x (D.run r j).time) - r i)
    rw [sub_add_sub_cancel] at ht
    dsimp [AnchorScales.V]
    linarith [htransfer i hi hd, st.threshold_window h.numerics hi]
  have hs : IsRetainedSuffix (D.run r j).kept (D.deletions r j) := by
    rw [D.deletions_eq r j]
    apply conflicts_are_suffix_of_errors _ (D.reference r) (D.reference r j) r
      (Eold := D.scales.V) (Enew := D.scales.V) (F := D.scales.ζ) (S := D.scales.S)
      h.numerics.locking_margin.le h.numerics.locking_margin.le
      (by linarith [h.numerics.suffix_margin])
    · intro i hi
      have hr := hg.range i ((D.run_range r j i hi).trans hjp)
      exact ⟨h.numerics.threshold_pos.le.trans hr.1, hr.2⟩
    · intro i _ a ha hia
      exact hg.separation i a hia ((D.run_range r j a ha).trans hjp)
    · exact st.pair_error
    · intro i hi hb
      apply hnew i hi
      rw [D.deletions_eq r j]
      simp only [Finset.mem_filter, not_and, not_lt]
      exact fun _ => hb
    · intro i hi a ha hia hb hbi hbn
      exact h.magnitude i a j hia (D.run_range r j a ha) hjp
        (D.reference r i) (D.reference_mem r h i ((D.run_range r j i hi).trans hjp))
        (D.reference r a) (D.reference_mem r h a ((D.run_range r j a ha).trans hjp))
        (D.reference r j) (D.reference_mem r h j hjp) hb hbi hbn
  have hc : (D.deletions r j).card ≤ D.H := by
    rw [D.deletions_eq r j]
    apply h.packing _ (D.reference r) (D.reference r j)
    intro i hi a ha hia
    have hp : ∀ i ∈ (D.run r j).kept, ∀ a ∈ (D.run r j).kept, i < a →
        |overlap (D.reference r i) (D.reference r a)| ≤ D.scales.C := by
      intro i hi a ha hia
      have he := st.pair_error i hi a ha hia
      have hr := hg.range i ((D.run_range r j i hi).trans hjp)
      have hrpos : 0 ≤ r i := h.numerics.threshold_pos.le.trans hr.1
      have ht := abs_add_le (overlap (D.reference r i) (D.reference r a) - r i) (r i)
      rw [sub_add_cancel, abs_of_nonneg hrpos] at ht
      linarith [h.numerics.cell_margin, hr.2]
    rcases lt_or_gt_of_ne hia with hia | hai
    · exact hp i hi a ha hia
    · rw [overlap_comm]
      exact hp a ha i hi hai
  have hlast : j % D.B ≠ 0 → j - 1 ∉ D.deletions r j := by
    intro hr hd
    have hdecomp : j % D.B + j / D.B * D.B = j := by
      simpa only [Nat.mul_comm D.B] using Nat.mod_add_div j D.B
    have ht := hcell (j - 1) (by omega) (by omega)
    rw [D.deletions_eq r j] at hd
    have hconf := (Finset.mem_filter.mp hd).2
    linarith [h.numerics.conflict_margin]
  refine ⟨hspec.1, hcell, htransfer, hnew, hs, hc, ?_, ?_, ?_⟩
  · intro hr
    exact retainedSuffix_empty_of_last hs
      (fun i hi => Nat.le_pred_of_lt (D.run_range r j i hi)) st.latest_kept (hlast hr)
  · rw [D.run_step_kept r j]
    exact prefixShape_step h.block_size hj st.shape hs hc hlast
  · by_cases hr : j % D.B = 0
    · apply reset_protects_prefix h.block_size hj hr st.shape hs hc 0 st.zero_kept
      have hstart := reset_block_start hB hj hr
      have := h.block_size
      omega
    · have he := retainedSuffix_empty_of_last hs
        (fun i hi => Nat.le_pred_of_lt (D.run_range r j i hi)) st.latest_kept (hlast hr)
      simpa only [he, Finset.sdiff_empty] using st.zero_kept

theorem PrefixShape.first_two {B H j : ℕ} {A : Finset ℕ}
    (hB : H + 2 ≤ B) (hp : PrefixShape B H j A) {b : ℕ} (hb : b * B < j) :
    b * B ∈ A ∧ (b * B + 1 < j → b * B + 1 ∈ A) := by
  have hBpos : 0 < B := by omega
  have hbq : b ≤ (j - 1) / B := by
    apply (Nat.le_div_iff_mul_le hBpos).mpr
    omega
  by_cases hlt : b < (j - 1) / B
  · obtain ⟨h, hh, hprefix⟩ := hp.2.2 b hlt
    have he : (b + 1) * B = b * B + B := by rw [Nat.add_mul, one_mul]
    constructor
    · apply (hprefix (b * B) le_rfl (by omega)).mpr
      omega
    · intro _
      apply (hprefix (b * B + 1) (by omega) (by omega)).mpr
      omega
  · have he : b = (j - 1) / B := by omega
    constructor
    · exact hp.2.1 (b * B) (by rw [he]) hb
    · intro hb1
      exact hp.2.1 (b * B + 1) (by rw [he]; omega) hb1

theorem PrefixShape.replacement {B H j : ℕ} {A : Finset ℕ}
    (hB : H + 2 ≤ B) (hp : PrefixShape B H j A)
    {i : ℕ} (hi : i ∈ A) (hil : i < j - 1) (hmissing : i + 1 ∉ A) :
    let a := retainedSuccessor A i
    a = (i / B + 1) * B ∧ (a = j - 1 ∨ a + 1 ∈ A) := by
  have hBpos : 0 < B := by omega
  have hmul := Nat.div_mul_le_self i B
  have hmod := Nat.mod_lt i hBpos
  have hdecomp : i % B + i / B * B = i := by
    simpa only [Nat.mul_comm B] using Nat.mod_add_div i B
  have hend : i < (i / B + 1) * B := by
    rw [Nat.add_mul, one_mul]
    omega
  have hiq : i / B ≤ (j - 1) / B := Nat.div_le_div_right (by omega)
  have hq : i / B < (j - 1) / B := by
    by_contra h
    have he : i / B = (j - 1) / B := by omega
    exact hmissing (hp.2.1 (i + 1) (by rw [← he]; omega) (by omega))
  have he_le := Nat.mul_le_mul_right B (show i / B + 1 ≤ (j - 1) / B by omega)
  have hprev := Nat.div_mul_le_self (j - 1) B
  have hep : (i / B + 1) * B < j := by omega
  obtain ⟨heA, heA1⟩ := hp.first_two hB hep
  obtain ⟨h, hh, hprefix⟩ := hp.2.2 (i / B) hq
  have hcut : i < (i / B + 1) * B - h := (hprefix i hmul hend).mp hi
  have hcut1 : (i / B + 1) * B - h ≤ i + 1 := by
    by_cases he : i + 1 < (i / B + 1) * B
    · by_contra hgt
      exact hmissing ((hprefix (i + 1) (by omega) he).mpr (by omega))
    · omega
  have hsucc : retainedSuccessor A i = (i / B + 1) * B := by
    apply SKOptimized.retainedSuccessor_eq_of_least heA hend
    intro k hk hik
    by_contra hke
    have hkin : k < (i / B + 1) * B := by omega
    have hkl : i / B * B ≤ k := by omega
    have hkc := (hprefix k hkl hkin).mp hk
    omega
  dsimp only
  rw [hsucc]
  refine ⟨rfl, ?_⟩
  by_cases he : (i / B + 1) * B = j - 1
  · exact Or.inl he
  · exact Or.inr (heA1 (by omega))

theorem deleted_successor_was_original {B H j : ℕ} {A D : Finset ℕ}
    (hB : H + 2 ≤ B) (hj : 0 < j) (hp : PrefixShape B H j A)
    (hs : IsRetainedSuffix A D) (hc : D.card ≤ H)
    (hreset : j % B = 0) {i : ℕ} (hi : i ∈ A \ D)
    (ha : retainedSuccessor A i ∈ D) : i + 1 ∈ A := by
  have hBpos : 0 < B := by omega
  have hstart := reset_block_start hBpos hj hreset
  have hsA := hp.2.1 ((j - 1) / B * B) le_rfl (by omega)
  have hsSurv := reset_protects_prefix hB hj hreset hp hs hc
    ((j - 1) / B * B) hsA (by omega)
  have hil : (j - 1) / B * B ≤ i := by
    by_contra h
    exact (Finset.mem_sdiff.mp hsSurv).2
      (SKOptimized.all_later_deleted_of_successor_deleted hs ha _ hsA (by omega))
  have hal := hp.1 _ (hs.1 ha)
  have hnonempty : (laterRetained A i).Nonempty := by
    by_contra hempty
    have he : retainedSuccessor A i = i := by
      simp only [SKOptimized.retainedSuccessor, dite_eq_right hempty]
    rw [he] at ha
    exact (Finset.mem_sdiff.mp hi).2 ha
  have hia := SKOptimized.lt_retainedSuccessor hnonempty
  exact hp.2.1 (i + 1) (by omega) (by omega)

theorem greedy_anchor_search_data {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (hg : ThresholdGeometry D r) {j : ℕ}
    (hj : 0 < j) (hjp : j < D.p) (st : AnchorState D r j) (gs : GreedySelection D r j) :
    let A := (D.run r j).kept \ D.deletions r j
    let K := (D.run r (j + 1)).kept
    let a := retainedSuccessor K
    let c := fun i => overlap (D.reference r i) (D.reference r (a i))
    AnchorSearch D.scales A j r c a (fun i => i + 1 ∈ K) ∧
    (∀ i ∈ A, |overlap (D.reference r i) (D.x (D.run r j).time) - c i| < 2 * D.scales.ε) := by
  classical
  dsimp only
  let A := (D.run r j).kept \ D.deletions r j
  let K := (D.run r (j + 1)).kept
  let a := retainedSuccessor K
  let c := fun i => overlap (D.reference r i) (D.reference r (a i))
  have hK : K = insert j A := D.run_step_kept r j
  have hrange (i : ℕ) (hi : i ∈ A) : i < j :=
    D.run_range r j i (Finset.mem_sdiff.mp hi).1
  have ha_nonempty (i : ℕ) (hi : i ∈ A) : (laterRetained K i).Nonempty := by
    refine ⟨j, Finset.mem_filter.mpr ⟨?_, hrange i hi⟩⟩
    rw [hK]; exact Finset.mem_insert_self _ _
  have hamem (i : ℕ) (hi : i ∈ A) : a i ∈ K :=
    SKOptimized.retainedSuccessor_mem (ha_nonempty i hi)
  have ha_gt (i : ℕ) (hi : i ∈ A) : i < a i :=
    SKOptimized.lt_retainedSuccessor (ha_nonempty i hi)
  have ha_le (i : ℕ) (hi : i ∈ A) : a i ≤ j := by
    have ht := gs.shape_next.1 (a i) (hamem i hi)
    omega
  have hcenters (i : ℕ) (hi : i ∈ A) :
      (i + 1 ∈ K → |c i - r i| ≤ D.scales.A0) ∧
      |c i - r i| ≤ D.scales.A1 ∧
      |overlap (D.reference r i) (D.x (D.run r j).time) - c i| < 2 * D.scales.ε := by
    have hiA := (Finset.mem_sdiff.mp hi).1
    have hiD := (Finset.mem_sdiff.mp hi).2
    have htr := gs.transferred i hiA hiD
    have htr' : |overlap (D.reference r i) (D.x (D.run r j).time) -
        overlap (D.reference r i) (D.reference r j)| ≤ D.scales.ζ := by
      rw [abs_sub_comm]; exact htr
    have hnewwindow : |overlap (D.reference r i) (D.x (D.run r j).time) -
        overlap (D.reference r i) (D.reference r j)| < 2 * D.scales.ε :=
      htr'.trans_lt h.numerics.transfer_small
    have hcenternew (E : ℝ)
        (hw : |overlap (D.reference r i) (D.x (D.run r j).time) - r i| ≤ E) :
        |overlap (D.reference r i) (D.reference r j) - r i| ≤ E + D.scales.ζ := by
      have ht := abs_add_le
        (overlap (D.reference r i) (D.reference r j) -
          overlap (D.reference r i) (D.x (D.run r j).time))
        (overlap (D.reference r i) (D.x (D.run r j).time) - r i)
      rw [sub_add_sub_cancel] at ht
      linarith
    by_cases hlast : i = j - 1
    · have hanew : a i = j := by
        apply SKOptimized.retainedSuccessor_eq_of_least
          (by rw [hK]; exact Finset.mem_insert_self _ _) (hrange i hi)
        intro k hk hik
        rw [hK] at hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact le_rfl
        · have hklt := hrange k hk
          omega
      have hband : |overlap (D.reference r i) (D.x (D.run r j).time) - r i| ≤ D.scales.d := by
        rw [hlast]
        apply abs_le.mpr
        constructor <;> linarith [st.latest_band.1, st.latest_band.2, h.numerics.jump_nonneg]
      have hc0 : |c i - r i| ≤ D.scales.A0 := by
        dsimp only [c]
        rw [hanew]
        dsimp [AnchorScales.A0]
        linarith [hcenternew D.scales.d hband]
      refine ⟨fun _ => hc0, hc0.trans h.numerics.A0_le_A1, ?_⟩
      simpa only [c, hanew] using hnewwindow
    · have hil : i < j - 1 := by have := hrange i hi; omega
      have hold_nonempty : (laterRetained (D.run r j).kept i).Nonempty :=
        ⟨j - 1, Finset.mem_filter.mpr ⟨st.latest_kept, hil⟩⟩
      by_cases hdeleted : retainedSuccessor (D.run r j).kept i ∈ D.deletions r j
      · have hreset : j % D.B = 0 := by
          by_contra hr
          rw [gs.nonreset_empty hr] at hdeleted
          exact Finset.notMem_empty _ hdeleted
        have horig := deleted_successor_was_original h.block_size hj st.shape gs.suffix
          gs.card hreset hi hdeleted
        have hanew : a i = j := by
          rw [show a i = retainedSuccessor (insert j A) i by rw [← hK]]
          exact SKOptimized.retainedSuccessor_rewired gs.suffix hdeleted (hrange i hi)
        have hc1 : |c i - r i| ≤ D.scales.A1 := by
          dsimp only [c]
          rw [hanew]
          have ht := hcenternew D.scales.T0 (st.original_window hiA hil horig)
          dsimp [AnchorScales.T0, AnchorScales.A1] at *
          linarith
        refine ⟨?_, hc1, ?_⟩
        · intro ho
          have he := SKOptimized.retainedSuccessor_eq_add_one ho
          change a i = i + 1 at he
          omega
        · simpa only [c, hanew] using hnewwindow
      · have hapreserved : a i = retainedSuccessor (D.run r j).kept i := by
          rw [show a i = retainedSuccessor (insert j A) i by rw [← hK]]
          exact SKOptimized.retainedSuccessor_preserved hold_nonempty hdeleted (D.run_range r j)
        refine ⟨?_, ?_, ?_⟩
        · intro ho
          have ho_old : i + 1 ∈ (D.run r j).kept := by
            rw [hK] at ho
            rcases Finset.mem_insert.mp ho with he | ho
            · omega
            · exact (Finset.mem_sdiff.mp ho).1
          simpa only [c, hapreserved] using st.center_original i hiA hil ho_old
        · simpa only [c, hapreserved] using st.center_rewired i hiA hil
        · simpa only [c, hapreserved] using st.strict_window i hiA hil
  refine ⟨⟨ha_gt, ha_le, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi halt
    change a i < j at halt
    have ha := hamem i hi
    rw [hK] at ha
    rcases Finset.mem_insert.mp ha with he | ha
    · omega
    · exact ha
  · intro i hi ho
    exact (hcenters i hi).1 ho
  · intro i hi
    exact (hcenters i hi).2.1
  · intro i hi
    by_cases ho : i + 1 ∈ K
    · exact Or.inl ho
    · have hrep := gs.shape_next.replacement h.block_size
        (by change i ∈ K; rw [hK]; exact Finset.mem_insert_of_mem hi)
        (by simpa only [Nat.add_sub_cancel] using hrange i hi) ho
      rcases hrep.2 with he | ho
      · exact Or.inr (Or.inl (by simpa only [Nat.add_sub_cancel] using he))
      · exact Or.inr (Or.inr ho)
  · intro i hi
    exact hg.separation i (a i) (ha_gt i hi) (lt_of_le_of_lt (ha_le i hi) hjp)
  · intro i hi
    exact (hcenters i hi).2.2

theorem greedy_anchor_step {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (hg : ThresholdGeometry D r) {j : ℕ}
    (hj : 0 < j) (hjp : j < D.p) (st : AnchorState D r j) : AnchorState D r (j + 1) := by
  classical
  have gs := greedy_selection h hg hj hjp st
  obtain ⟨hs, hw⟩ := greedy_anchor_search_data h hg hj hjp st gs
  let A := (D.run r j).kept \ D.deletions r j
  let K := (D.run r (j + 1)).kept
  let a := retainedSuccessor K
  have hK : K = insert j A := D.run_step_kept r j
  obtain ⟨N⟩ := h.narrow
  have hcross := anchor_search_crossing N h.numerics hg hjp st.time_le
    (fun i hi => D.reference_mem r h i (lt_of_le_of_lt hi hjp)) hs gs.zero_survives st.initial_overlap hw gs.selected h.jumps
  obtain ⟨_, hband, hwindow⟩ := hcross
  have htime := D.run_step_time r j (by omega)
  have htimele : (D.run r (j + 1)).time ≤ (D.run r j).time := by
    rw [htime]
    exact lastCrossing_le _ _ _
  have hold (i : ℕ) (hi : i ∈ K) (hil : i < j) : i ∈ A := by
    rw [hK] at hi
    rcases Finset.mem_insert.mp hi with he | hi
    · omega
    · exact hi
  refine ⟨htimele.trans st.time_le, (fun i hi => D.run_refs r (j + 1) i hi),
    (fun i hi => D.reference_mem r h i (by omega)), gs.shape_next, ?_, st.initial_overlap, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · change 0 ∈ K
    rw [hK]
    exact Finset.mem_insert_of_mem gs.zero_survives
  · simp only [Nat.add_sub_cancel]
    rw [D.run_step_kept r j]
    exact Finset.mem_insert_self _ _
  · simpa only [Nat.add_sub_cancel, htime] using hband
  · intro i hi hil ho
    simp only [Nat.add_sub_cancel] at hil
    exact hs.center_original i (hold i hi hil) ho
  · intro i hi hil
    simp only [Nat.add_sub_cancel] at hil
    exact hs.center_all i (hold i hi hil)
  · intro i hi hil
    simp only [Nat.add_sub_cancel] at hil
    rw [htime]
    exact hwindow _ le_rfl (lastCrossing_le _ _ _) i (hold i hi hil)
  · intro i hi b hb hib
    have hbr := gs.shape_next.1 b hb
    have hir : i < j := by omega
    have hiold := hold i hi hir
    by_cases he : b = j
    · subst b
      exact gs.new_pair i (Finset.mem_sdiff.mp hiold).1 (Finset.mem_sdiff.mp hiold).2
    · have hbl : b < j := by omega
      have hbold := hold b hb hbl
      exact st.pair_error i (Finset.mem_sdiff.mp hiold).1 b (Finset.mem_sdiff.mp hbold).1 hib
  · intro i hi hil ho
    exact gs.shape_next.replacement h.block_size hi hil ho

theorem greedy_anchor_states {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (hg : ThresholdGeometry D r)
    (hend : overlap (D.reference r 0) (D.x D.m) ≤ 0) :
    ∀ j, 1 ≤ j → j ≤ D.p → AnchorState D r j := by
  intro j
  induction j with
  | zero => intro hj _; omega
  | succ j ih =>
    intro _ hjp
    by_cases hj : j = 0
    · subst j
      exact anchor_initial_state h hg hend
    · exact greedy_anchor_step h hg (by omega) (by omega) (ih (by omega) (by omega))

theorem older_membership_step {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} {j i : ℕ} (hj : 0 < j) (st : AnchorState D r j)
    (gs : GreedySelection D r j) (hi : i < (j - 1) / D.B * D.B) :
    (i ∈ (D.run r (j + 1)).kept ↔ i ∈ (D.run r j).kept) := by
  classical
  have hprev := Nat.div_mul_le_self (j - 1) D.B
  have hij : i < j := by omega
  rw [D.run_step_kept r j]
  constructor
  · intro hmem
    rcases Finset.mem_insert.mp hmem with he | hmem
    · omega
    · exact (Finset.mem_sdiff.mp hmem).1
  · intro hmem
    apply Finset.mem_insert_of_mem
    by_cases hr : j % D.B = 0
    · apply reset_protects_prefix h.block_size hj hr st.shape gs.suffix gs.card i hmem
      have hstart := reset_block_start (show 0 < D.B by have := h.block_size; omega) hj hr
      have := h.block_size
      omega
    · simpa only [gs.nonreset_empty hr, Finset.sdiff_empty] using hmem

theorem greedy_older_immutable {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (hg : ThresholdGeometry D r)
    (states : ∀ j, 1 ≤ j → j ≤ D.p → AnchorState D r j)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hkp : k ≤ D.p)
    {i : ℕ} (hi : i < (j - 1) / D.B * D.B) :
    (i ∈ (D.run r k).kept ↔ i ∈ (D.run r j).kept) := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    have st := states k (by omega) (by omega)
    have gs := greedy_selection h hg (by omega) (by omega) st
    have hmon := Nat.mul_le_mul_right D.B
      (Nat.div_le_div_right (show j - 1 ≤ k - 1 by omega) : (j - 1) / D.B ≤ (k - 1) / D.B)
    exact (older_membership_step h (by omega) st gs (hi.trans_le hmon)).trans (ih (by omega))

lemma PrefixShape.missing_before_current {B H j : ℕ} {A : Finset ℕ}
    (hB : H + 2 ≤ B) (hp : PrefixShape B H j A) {i : ℕ}
    (_hi : i ∈ A) (hil : i < j - 1) (ho : i + 1 ∉ A) :
    i + 1 < (j - 1) / B * B := by
  have hBpos : 0 < B := by omega
  have hs := Nat.div_mul_le_self (j - 1) B
  have hstartmem := (hp.first_two hB (b := (j - 1) / B) (by omega)).1
  by_contra h
  exact ho (hp.2.1 (i + 1) (by omega) (by omega))

theorem greedy_one_time_rewiring {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (hg : ThresholdGeometry D r)
    (states : ∀ j, 1 ≤ j → j ≤ D.p → AnchorState D r j)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hkp : k ≤ D.p)
    {i : ℕ} (hi : i ∈ (D.run r j).kept) (hil : i < j - 1)
    (ho : i + 1 ∉ (D.run r j).kept) :
    retainedSuccessor (D.run r k).kept i = retainedSuccessor (D.run r j).kept i := by
  have stj := states j hj (hjk.trans hkp)
  have stk := states k (by omega) hkp
  have hbefore := stj.shape.missing_before_current h.block_size hi hil ho
  have hmemk := (greedy_older_immutable h hg states hj hjk hkp (by omega : i < (j - 1) / D.B * D.B)).mpr hi
  have hmissingk : i + 1 ∉ (D.run r k).kept := by
    intro hmem
    exact ho ((greedy_older_immutable h hg states hj hjk hkp hbefore).mp hmem)
  have hrepj := stj.replacement i hi hil ho
  have hrepk := stk.replacement i hmemk (by omega) hmissingk
  exact hrepk.1.trans hrepj.1.symm

theorem greedy_marker_witness {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (st : AnchorState D r D.p) :
    ∃ k ≤ D.m, ∀ a < D.M,
      |overlap (D.reference r (a * D.B)) (D.x k) - r (a * D.B)| ≤ D.scales.T0 := by
  refine ⟨(D.run r D.p).time, st.time_le, ?_⟩
  intro a ha
  have hB2 : 2 ≤ D.B := by have := h.block_size; omega
  have hmul := Nat.mul_le_mul_right D.B (show a + 1 ≤ D.M by omega)
  rw [Nat.add_mul, one_mul] at hmul
  have hpend : D.M * D.B = D.p := by exact Nat.mul_comm _ _
  have ha1 : a * D.B + 1 < D.p := by omega
  obtain ⟨hamem, ha1mem⟩ := st.shape.first_two h.block_size (by omega : a * D.B < D.p)
  exact st.original_window hamem (by omega) (ha1mem ha1)

theorem finite_successor_anchor : FiniteSuccessorAnchorStatement := by
  intro n D h r hg hend
  have states := greedy_anchor_states h hg hend
  have hB : 0 < D.B := by have := h.block_size; omega
  have hp : 1 ≤ D.p := by
    have hp0 : 0 < D.p := Nat.mul_pos hB (show 0 < D.M by have := h.blocks_pos; omega)
    omega
  refine ⟨states, ?_, ?_, ?_, ?_, greedy_marker_witness h (states D.p hp le_rfl)⟩
  · intro j hjp hr
    have hj : 0 < j := by
      by_contra hh
      have he : j = 0 := by omega
      subst j
      exact hr (Nat.zero_mod _)
    exact (greedy_selection h hg hj hjp (states j (by omega) hjp.le)).nonreset_empty hr
  · intro j hjp hr hj i hi hit
    have st := states j (by omega) hjp.le
    have gs := greedy_selection h hg hj hjp st
    exact (Finset.mem_sdiff.mp
      (reset_protects_prefix h.block_size hj hr st.shape gs.suffix gs.card i hi hit)).2
  · intro j k hj hjk hkp i hi
    exact greedy_older_immutable h hg states hj hjk hkp hi
  · intro j k hj hjk hkp i hi hil ho
    exact greedy_one_time_rewiring h hg states hj hjk hkp hi hil ho

structure FinalPrefixProfile {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ) (k : ℕ)
    (h : Fin (D.M - 1) → Fin (D.H + 1)) : Prop where
  retained : ∀ b : Fin (D.M - 1), ∀ t, t < D.B →
    (b.val * D.B + t ∈ (D.run r D.p).kept ↔ t < D.B - (h b).val)
  original : ∀ b : Fin (D.M - 1), ∀ t, t < D.B - (h b).val →
    (b.val * D.B + t + 1 ∈ (D.run r D.p).kept ↔
      (h b).val = 0 ∨ t + 1 < D.B - (h b).val)
  old_windows : ∀ b : Fin (D.M - 1), ∀ t, t < D.B - (h b).val →
    |overlap (D.reference r (b.val * D.B + t)) (D.x k) - r (b.val * D.B + t)| ≤
      if (h b).val = 0 ∨ t + 1 < D.B - (h b).val then D.scales.T0 else D.scales.T1
  last_complete : ∀ t, t < D.B → (D.M - 1) * D.B + t ∈ (D.run r D.p).kept
  last_original_windows : ∀ t, t < D.B - 1 →
    |overlap (D.reference r ((D.M - 1) * D.B + t)) (D.x k) -
      r ((D.M - 1) * D.B + t)| ≤ D.scales.T0
  newest_band : overlap (D.reference r (D.p - 1)) (D.x k) ∈
    Icc (r (D.p - 1) - D.scales.d) (r (D.p - 1))

theorem final_prefix_profile {n : ℕ} {D : AnchorData n} (h : AnchorHypotheses D)
    {r : ℕ → ℝ} (st : AnchorState D r D.p) :
    ∃ pattern : Fin (D.M - 1) → Fin (D.H + 1), ∃ k ≤ D.m,
      FinalPrefixProfile D r k pattern := by
  classical
  have hB : 0 < D.B := by have := h.block_size; omega
  have hp : 0 < D.p := Nat.mul_pos hB (show 0 < D.M by have := h.blocks_pos; omega)
  have hreset : D.p % D.B = 0 := Nat.mod_eq_zero_of_dvd ⟨D.M, rfl⟩
  have hstart := reset_block_start hB hp hreset
  have hend : (D.M - 1) * D.B + D.B = D.p := by
    calc
      (D.M - 1) * D.B + D.B = (D.M - 1 + 1) * D.B := by ring
      _ = D.M * D.B := by rw [Nat.sub_add_cancel h.blocks_pos]
      _ = D.p := Nat.mul_comm _ _
  have hq : (D.p - 1) / D.B = D.M - 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := Nat.mul_lt_mul_of_pos_right hlt hB
      omega
    · have hm := Nat.mul_lt_mul_of_pos_right hgt hB
      omega
  have hex (b : Fin (D.M - 1)) : ∃ z : Fin (D.H + 1),
      ∀ i, b.val * D.B ≤ i → i < (b.val + 1) * D.B →
        (i ∈ (D.run r D.p).kept ↔ i < (b.val + 1) * D.B - z.val) := by
    obtain ⟨z, hz, hpre⟩ := st.shape.2.2 b.val (by rw [hq]; exact b.isLt)
    exact ⟨⟨z, by omega⟩, hpre⟩
  choose pattern hpattern using hex
  have hret (b : Fin (D.M - 1)) (t : ℕ) (ht : t < D.B) :
      (b.val * D.B + t ∈ (D.run r D.p).kept ↔ t < D.B - (pattern b).val) := by
    have he : (b.val + 1) * D.B = b.val * D.B + D.B := by ring
    have hz := (pattern b).isLt
    have hb := h.block_size
    have hpre := hpattern b (b.val * D.B + t) (by omega) (by omega)
    rw [he, Nat.add_sub_assoc (show (pattern b).val ≤ D.B by omega)] at hpre
    simpa only [Nat.add_lt_add_iff_left] using hpre
  have hbefore (b : Fin (D.M - 1)) : (b.val + 1) * D.B < D.p := by
    have hm := Nat.mul_le_mul_right D.B (show b.val + 1 ≤ D.M - 1 by have := b.isLt; omega)
    omega
  have horig (b : Fin (D.M - 1)) (t : ℕ) (ht : t < D.B - (pattern b).val) :
      (b.val * D.B + t + 1 ∈ (D.run r D.p).kept ↔
        (pattern b).val = 0 ∨ t + 1 < D.B - (pattern b).val) := by
    have hz := (pattern b).isLt
    have hb := h.block_size
    by_cases hzero : (pattern b).val = 0
    · have hmem : b.val * D.B + t + 1 ∈ (D.run r D.p).kept := by
        by_cases hin : t + 1 < D.B
        · have hm := (hret b (t + 1) hin).mpr (by omega)
          simpa only [Nat.add_assoc] using hm
        · have he : b.val * D.B + t + 1 = (b.val + 1) * D.B := by
            rw [Nat.add_mul, one_mul]
            omega
          rw [he]
          exact (st.shape.first_two h.block_size (hbefore b)).1
      exact ⟨fun _ => Or.inl hzero, fun _ => hmem⟩
    · have ht1 : t + 1 < D.B := by omega
      have hm := hret b (t + 1) ht1
      simpa only [Nat.add_assoc, hzero, false_or] using hm
  refine ⟨pattern, (D.run r D.p).time, st.time_le, hret, horig, ?_, ?_, ?_, st.latest_band⟩
  · intro b t ht
    have hz := (pattern b).isLt
    have hb := h.block_size
    have htB : t < D.B := by omega
    have hi := (hret b t htB).mpr ht
    by_cases ho : (pattern b).val = 0 ∨ t + 1 < D.B - (pattern b).val
    · rw [ite_eq_left ho]
      apply st.original_window hi
      · have he : (b.val + 1) * D.B = b.val * D.B + D.B := by ring
        have hbp := hbefore b
        omega
      · exact (horig b t ht).mpr ho
    · rw [ite_eq_right ho]
      exact st.threshold_window h.numerics hi
  · intro t ht
    apply st.shape.2.1
    · rw [hq]; omega
    · omega
  · intro t ht
    have hb := h.block_size
    have hi : (D.M - 1) * D.B + t ∈ (D.run r D.p).kept := by
      apply st.shape.2.1
      · rw [hq]; omega
      · omega
    apply st.original_window hi (by omega)
    apply st.shape.2.1
    · rw [hq]; omega
    · omega

theorem finite_successor_anchor_profile {n : ℕ} {D : AnchorData n}
    (h : AnchorHypotheses D) {r : ℕ → ℝ} (hg : ThresholdGeometry D r)
    (hend : overlap (D.reference r 0) (D.x D.m) ≤ 0) :
    ∃ pattern : Fin (D.M - 1) → Fin (D.H + 1), ∃ k ≤ D.m,
      FinalPrefixProfile D r k pattern := by
  have hB : 0 < D.B := by have := h.block_size; omega
  have hp : 1 ≤ D.p := Nat.mul_pos hB (show 0 < D.M by have := h.blocks_pos; omega)
  exact final_prefix_profile h ((finite_successor_anchor n D h r hg hend).states D.p hp le_rfl)

theorem initial_reference_independent {n : ℕ} (D : AnchorData n) (r s : ℕ → ℝ) :
    D.reference r 0 = D.reference s 0 := by
  exact D.reference_predictable r s 0 (by intro i hi; omega)

theorem positive_endpoint_of_no_marker_witness {n : ℕ} {D : AnchorData n}
    (h : AnchorHypotheses D) (r : ℕ → ℝ) (hg : ThresholdGeometry D r)
    (hno : ¬ ∃ k ≤ D.m, ∀ a < D.M,
      |overlap (D.reference r (a * D.B)) (D.x k) - r (a * D.B)| ≤ D.scales.T0) :
    0 < overlap (D.pick 0 D.fallback 0) (D.x D.m) := by
  by_contra hsign
  have hend : overlap (D.reference r 0) (D.x D.m) ≤ 0 := by
    rw [D.reference_zero r]
    exact le_of_not_gt hsign
  exact hno ((finite_successor_anchor n D h r hg hend).marker_windows)

end SKBarriers2.Dynamics
