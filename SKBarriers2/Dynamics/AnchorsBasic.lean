module

public import OAI.Probability.SKBarriers.Dynamics.GreedyRecursion
public import OAI.Probability.SKBarriers.Dynamics.ConflictSuffix
public import OAI.Probability.SKBarriers.Dynamics.ProtectedStep
public import SKOptimized.SuccessorAnchors

@[expose] public section

noncomputable section

namespace SKBarriers2.Dynamics

open OAI.SK OAI.SK.Analytic Set
open SKOptimized (retainedSuccessor laterRetained)

structure AnchorScales where
  tLo : ℝ
  tHi : ℝ
  C : ℝ
  b : ℝ
  bPrime : ℝ
  qStar : ℝ
  ρ : ℝ
  ε : ℝ
  ζ : ℝ
  d : ℝ
  S : ℝ

namespace AnchorScales

def A0 (s : AnchorScales) : ℝ := s.ζ + s.d
def A1 (s : AnchorScales) : ℝ := 2 * s.ε + 2 * s.ζ + s.d
def T0 (s : AnchorScales) : ℝ := 2 * s.ε + s.ζ + s.d
def T1 (s : AnchorScales) : ℝ := 4 * s.ε + 2 * s.ζ + s.d
def V (s : AnchorScales) : ℝ := s.T1 + s.ζ
def centerRadius (s : AnchorScales) : ℝ := 3 * s.ε + 2 * s.ζ + 3 * s.d / 2

end AnchorScales

structure AnchorNumerics (s : AnchorScales) : Prop where
  rho_pos : 0 < s.ρ
  epsilon_pos : 0 < s.ε
  jump_nonneg : 0 ≤ s.d
  transfer_nonneg : 0 ≤ s.ζ
  transfer_small : s.ζ < 2 * s.ε
  jump_small : s.d / 2 ≤ s.ε
  threshold_pos : 0 < s.tLo
  threshold_order : s.tLo ≤ s.tHi
  cell_margin : s.tHi + s.V < s.C
  conflict_margin : s.C < s.b
  locking_margin : s.tHi + s.V < s.bPrime
  selection_margin : s.tHi + s.T1 < s.qStar
  suffix_margin : 2 * s.V + s.ζ < s.S
  exit_margin : s.ρ + 5 * s.ε + 4 * s.ζ + 7 * s.d / 2 ≤ s.S

structure AnchorData (n : ℕ) where
  B : ℕ
  H : ℕ
  M : ℕ
  m : ℕ
  scales : AnchorScales
  pool : ℕ → Finset (Config n)
  fallback : ℕ → Config n
  x : ℕ → Config n

namespace AnchorData

variable {n : ℕ}

def p (D : AnchorData n) : ℕ := D.B * D.M

def pick (D : AnchorData n) : ℕ → (ℕ → Config n) → ℕ → Config n :=
  bankPick D.pool D.fallback D.B D.x (D.scales.C / 3) D.scales.qStar

def run (D : AnchorData n) (r : ℕ → ℝ) (j : ℕ) : GreedyRecord n :=
  greedyRun D.fallback D.pick D.x r D.scales.b D.m j

def reference (D : AnchorData n) (r : ℕ → ℝ) (i : ℕ) : Config n :=
  greedyReference D.fallback D.pick D.x r D.scales.b D.m i

def deletions (D : AnchorData n) (r : ℕ → ℝ) (j : ℕ) : Finset ℕ :=
  (D.run r j).kept.filter fun i =>
    D.scales.b < |overlap ((D.run r j).refs i) (D.reference r j)|

end AnchorData

structure ThresholdGeometry {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ) : Prop where
  range : ∀ i < D.p, r i ∈ Icc D.scales.tLo D.scales.tHi
  separation : ∀ i a, i < a → a < D.p → D.scales.S ≤ r a - r i

structure NarrowInput {n : ℕ} (D : AnchorData n) where
  centerRegion : Set ℝ
  localDomain : ℝ → ℝ → ℝ → Prop
  remoteDomain : ℝ → ℝ → ℝ → Prop
  excludedPair : Config n → Config n → Prop
  forbidden : Config n → Config n → Config n → Prop
  center_band : ∀ t ∈ Icc D.scales.tLo D.scales.tHi, ∀ c,
    |c - t| ≤ D.scales.centerRadius → c ∈ centerRegion
  cover : ∀ i a, i < a → a < D.p → ∀ v ∈ D.pool i, ∀ w ∈ D.pool a,
    ∀ k ≤ D.m,
    let c := (overlap v (D.x k) + overlap v w) / 2
    let δ := (overlap v (D.x k) - overlap v w) / 2
    let q := overlap w (D.x k)
    c ∈ centerRegion → D.scales.ε ≤ |δ| → |δ| ≤ 2 * D.scales.ε →
    D.scales.ρ ≤ q - c →
    localDomain c δ q ∨ remoteDomain c δ q ∨ excludedPair w (D.x k)
  local_forbidden : ∀ v x w,
    localDomain ((overlap v x + overlap v w) / 2)
      ((overlap v x - overlap v w) / 2) (overlap w x) → forbidden v x w
  remote_forbidden : ∀ v x w,
    remoteDomain ((overlap v x + overlap v w) / 2)
      ((overlap v x - overlap v w) / 2) (overlap w x) → forbidden v x w
  pair_forbidden : ∀ v x w, excludedPair w x → forbidden v x w
  avoid : ∀ i a, i < a → a < D.p → ∀ v ∈ D.pool i, ∀ w ∈ D.pool a,
    ∀ k ≤ D.m, ¬ forbidden v (D.x k) w

structure AnchorHypotheses {n : ℕ} (D : AnchorData n) : Prop where
  dimension_pos : 0 < n
  blocks_pos : 1 ≤ D.M
  block_size : D.H + 2 ≤ D.B
  numerics : AnchorNumerics D.scales
  fallback_mem : ∀ j < D.p, D.fallback j ∈ D.pool j
  orientations : ∀ j < D.p, ∀ v ∈ D.pool j, flip v ∈ D.pool j
  jumps : ∀ v k, k < D.m → |overlap v (D.x (k + 1)) - overlap v (D.x k)| ≤ D.scales.d
  coverage : ∀ j < D.p, ∀ v : ℕ → Config n,
    (∀ i < j, v i ∈ D.pool i) → ∀ u ≤ D.m,
    (∀ i, j / D.B * D.B ≤ i → i < j → |overlap (v i) (D.x u)| ≤ D.scales.C) →
    ∃ w ∈ D.pool j, D.scales.qStar ≤ overlap w (D.x u) ∧
      ∀ i, j / D.B * D.B ≤ i → i < j → |overlap (v i) w| ≤ D.scales.C
  transfer : ∀ i j, i < j → j < D.p → ∀ v ∈ D.pool i, ∀ w ∈ D.pool j,
    ∀ u ≤ D.m, D.scales.qStar ≤ overlap w (D.x u) →
    |overlap v w| ≤ D.scales.b → |overlap v (D.x u)| ≤ D.scales.b →
    |overlap v w - overlap v (D.x u)| ≤ D.scales.ζ
  magnitude : ∀ i a j, i < a → a < j → j < D.p →
    ∀ v ∈ D.pool i, ∀ z ∈ D.pool a, ∀ w ∈ D.pool j,
    D.scales.b < |overlap v w| → |overlap z v| ≤ D.scales.bPrime →
    |overlap z w| ≤ D.scales.bPrime →
    abs (|overlap z v| - |overlap z w|) ≤ D.scales.ζ
  packing : ∀ A : Finset ℕ, ∀ v : ℕ → Config n, ∀ w : Config n,
    (∀ i ∈ A, ∀ a ∈ A, i ≠ a → |overlap (v i) (v a)| ≤ D.scales.C) →
    (A.filter fun i => D.scales.b < |overlap (v i) w|).card ≤ D.H
  narrow : Nonempty (NarrowInput D)

def PrefixShape (B H j : ℕ) (A : Finset ℕ) : Prop :=
  (∀ i ∈ A, i < j) ∧
  (∀ i, (j - 1) / B * B ≤ i → i < j → i ∈ A) ∧
  ∀ b, b < (j - 1) / B → ∃ h ≤ H,
    ∀ i, b * B ≤ i → i < (b + 1) * B → (i ∈ A ↔ i < (b + 1) * B - h)

structure AnchorState {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ) (j : ℕ) : Prop where
  time_le : (D.run r j).time ≤ D.m
  refs_eq : ∀ i < j, (D.run r j).refs i = D.reference r i
  refs_mem : ∀ i < j, D.reference r i ∈ D.pool i
  shape : PrefixShape D.B D.H j (D.run r j).kept
  zero_kept : 0 ∈ (D.run r j).kept
  initial_overlap : D.scales.qStar ≤ overlap (D.reference r 0) (D.x 0)
  latest_kept : j - 1 ∈ (D.run r j).kept
  latest_band : overlap (D.reference r (j - 1)) (D.x (D.run r j).time) ∈
    Icc (r (j - 1) - D.scales.d) (r (j - 1))
  center_original : ∀ i ∈ (D.run r j).kept, i < j - 1 →
    i + 1 ∈ (D.run r j).kept →
    |overlap (D.reference r i)
      (D.reference r (retainedSuccessor (D.run r j).kept i)) - r i| ≤ D.scales.A0
  center_rewired : ∀ i ∈ (D.run r j).kept, i < j - 1 →
    |overlap (D.reference r i)
      (D.reference r (retainedSuccessor (D.run r j).kept i)) - r i| ≤ D.scales.A1
  strict_window : ∀ i ∈ (D.run r j).kept, i < j - 1 →
    |overlap (D.reference r i) (D.x (D.run r j).time) -
      overlap (D.reference r i)
        (D.reference r (retainedSuccessor (D.run r j).kept i))| < 2 * D.scales.ε
  pair_error : ∀ i ∈ (D.run r j).kept, ∀ a ∈ (D.run r j).kept, i < a →
    |overlap (D.reference r i) (D.reference r a) - r i| ≤ D.scales.V
  replacement : ∀ i ∈ (D.run r j).kept, i < j - 1 → i + 1 ∉ (D.run r j).kept →
    let a := retainedSuccessor (D.run r j).kept i
    a = (i / D.B + 1) * D.B ∧ (a = j - 1 ∨ a + 1 ∈ (D.run r j).kept)

structure AnchorConclusion {n : ℕ} (D : AnchorData n) (r : ℕ → ℝ) : Prop where
  states : ∀ j, 1 ≤ j → j ≤ D.p → AnchorState D r j
  nonreset_empty : ∀ j < D.p, j % D.B ≠ 0 → D.deletions r j = ∅
  reset_protection : ∀ j < D.p, j % D.B = 0 → 0 < j →
    ∀ i ∈ (D.run r j).kept, i < j - D.H → i ∉ D.deletions r j
  older_immutable : ∀ j k, 1 ≤ j → j ≤ k → k ≤ D.p →
    ∀ i, i < (j - 1) / D.B * D.B →
      (i ∈ (D.run r k).kept ↔ i ∈ (D.run r j).kept)
  one_time_rewiring : ∀ j k, 1 ≤ j → j ≤ k → k ≤ D.p →
    ∀ i ∈ (D.run r j).kept, i < j - 1 → i + 1 ∉ (D.run r j).kept →
      retainedSuccessor (D.run r k).kept i = retainedSuccessor (D.run r j).kept i
  marker_windows : ∃ k ≤ D.m, ∀ a < D.M,
    |overlap (D.reference r (a * D.B)) (D.x k) - r (a * D.B)| ≤ D.scales.T0

def FiniteSuccessorAnchorStatement : Prop :=
  ∀ (n : ℕ) (D : AnchorData n), AnchorHypotheses D → ∀ r : ℕ → ℝ,
    ThresholdGeometry D r → overlap (D.reference r 0) (D.x D.m) ≤ 0 →
    AnchorConclusion D r

namespace AnchorNumerics

variable {s : AnchorScales} (h : AnchorNumerics s)

include h

lemma A0_nonneg : 0 ≤ s.A0 := by
  dsimp [AnchorScales.A0]
  linarith [h.transfer_nonneg, h.jump_nonneg]

lemma A0_le_A1 : s.A0 ≤ s.A1 := by
  dsimp [AnchorScales.A0, AnchorScales.A1]
  linarith [h.transfer_nonneg, h.epsilon_pos]

lemma T0_le_T1 : s.T0 ≤ s.T1 := by
  dsimp [AnchorScales.T0, AnchorScales.T1]
  linarith [h.transfer_nonneg, h.epsilon_pos]

lemma T1_le_V : s.T1 ≤ s.V := by
  dsimp [AnchorScales.V]
  linarith [h.transfer_nonneg]

lemma jump_le_T1 : s.d ≤ s.T1 := by
  dsimp [AnchorScales.T1]
  linarith [h.transfer_nonneg, h.epsilon_pos]

end AnchorNumerics

theorem packing_from_gram {n H : ℕ} (hn : 0 < n) {b C : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hCb : C < b ^ 2 / 2)
    (hH : ⌈2 / b ^ 2⌉₊ ≤ H) (A : Finset ℕ) (v : ℕ → Config n) (w : Config n)
    (hpair : ∀ i ∈ A, ∀ a ∈ A, i ≠ a → |overlap (v i) (v a)| ≤ C) :
    (A.filter fun i => b < |overlap (v i) w|).card ≤ H := by
  exact (conflict_filter_card hn A v w b C hb hC hCb hpair).trans hH

theorem conflicts_are_suffix_of_errors {n : ℕ} (A : Finset ℕ)
    (v : ℕ → Config n) (w : Config n) (r : ℕ → ℝ)
    {b bPrime tHi Eold Enew F S : ℝ}
    (hsmallOld : tHi + Eold ≤ bPrime) (hsmallNew : tHi + Enew ≤ bPrime)
    (hsep : Eold + Enew + F < S)
    (hr : ∀ i ∈ A, 0 ≤ r i ∧ r i ≤ tHi)
    (hspacing : ∀ i ∈ A, ∀ a ∈ A, i < a → S ≤ r a - r i)
    (hold : ∀ i ∈ A, ∀ a ∈ A, i < a → |overlap (v i) (v a) - r i| ≤ Eold)
    (hnew : ∀ a ∈ A, |overlap (v a) w| ≤ b → |overlap (v a) w - r a| ≤ Enew)
    (hlock : ∀ i ∈ A, ∀ a ∈ A, i < a → b < |overlap (v i) w| →
      |overlap (v a) (v i)| ≤ bPrime → |overlap (v a) w| ≤ bPrime →
      abs (|overlap (v a) (v i)| - |overlap (v a) w|) ≤ F) :
    IsRetainedSuffix A (A.filter fun i => b < |overlap (v i) w|) := by
  classical
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro i a hi ha hia
  obtain ⟨hiA, hconf⟩ := Finset.mem_filter.mp hi
  by_cases he : i = a
  · simpa only [he] using hi
  have hia' : i < a := lt_of_le_of_ne hia he
  by_contra hnot
  have hcompat : |overlap (v a) w| ≤ b := by
    simpa only [Finset.mem_filter, ha, true_and, not_lt] using hnot
  have ho := hold i hiA a ha hia'
  rw [overlap_comm (v i) (v a)] at ho
  have hn := hnew a ha hcompat
  have hoa : abs (|overlap (v a) (v i)| - r i) ≤ Eold := by
    simpa only [abs_of_nonneg (hr i hiA).1] using
      (abs_abs_sub_abs_le_abs_sub _ _).trans ho
  have hna : abs (|overlap (v a) w| - r a) ≤ Enew := by
    simpa only [abs_of_nonneg (hr a ha).1] using
      (abs_abs_sub_abs_le_abs_sub _ _).trans hn
  have hbi : |overlap (v a) (v i)| ≤ bPrime := by
    linarith only [(abs_le.mp hoa).2, (hr i hiA).2, hsmallOld]
  have hbn : |overlap (v a) w| ≤ bPrime := by
    linarith only [(abs_le.mp hna).2, (hr a ha).2, hsmallNew]
  have hl := hlock i hiA a ha hia' hconf hbi hbn
  linarith only [(abs_le.mp hoa).2, (abs_le.mp hna).1, (abs_le.mp hl).1,
    hspacing i hiA a ha hia', hsep]

theorem NarrowInput.no_narrow {n : ℕ} {D : AnchorData n} (N : NarrowInput D)
    {i a k : ℕ} (hia : i < a) (ha : a < D.p) {v w : Config n}
    (hv : v ∈ D.pool i) (hw : w ∈ D.pool a) (hk : k ≤ D.m)
    (hc : (overlap v (D.x k) + overlap v w) / 2 ∈ N.centerRegion)
    (hδlo : D.scales.ε ≤ |(overlap v (D.x k) - overlap v w) / 2|)
    (hδhi : |(overlap v (D.x k) - overlap v w) / 2| ≤ 2 * D.scales.ε)
    (hgap : D.scales.ρ ≤ overlap w (D.x k) - (overlap v (D.x k) + overlap v w) / 2) :
    False := by
  have hav := N.avoid i a hia ha v hv w hw k hk
  rcases N.cover i a hia ha v hv w hw k hk hc hδlo hδhi hgap with hl | hr | hp
  · exact hav (N.local_forbidden v (D.x k) w hl)
  · exact hav (N.remote_forbidden v (D.x k) w hr)
  · exact hav (N.pair_forbidden v (D.x k) w hp)

structure AnchorSearch (s : AnchorScales) (A : Finset ℕ) (j : ℕ)
    (r c : ℕ → ℝ) (a : ℕ → ℕ) (original : ℕ → Prop) : Prop where
  anchor_gt : ∀ i ∈ A, i < a i
  anchor_le : ∀ i ∈ A, a i ≤ j
  anchor_old : ∀ i ∈ A, a i < j → a i ∈ A
  center_original : ∀ i ∈ A, original i → |c i - r i| ≤ s.A0
  center_all : ∀ i ∈ A, |c i - r i| ≤ s.A1
  no_double_rewire : ∀ i ∈ A, original i ∨ a i = j ∨ original (a i)
  separation : ∀ i ∈ A, s.S ≤ r (a i) - r i

theorem anchor_first_exit {s : AnchorScales} (hn : AnchorNumerics s)
    {A : Finset ℕ} {j : ℕ} {r c : ℕ → ℝ} {a : ℕ → ℕ} {original : ℕ → Prop}
    (hs : AnchorSearch s A j r c a original) (f : ℕ → ℝ)
    (hall : ∀ i ∈ A, |f i - c i| ≤ 2 * s.ε + s.d)
    (hnew : r j - s.d ≤ f j) {i : ℕ} (hi : i ∈ A)
    (hexit : 2 * s.ε ≤ |f i - c i|) :
    s.ε ≤ |(f i - c i) / 2| ∧ |(f i - c i) / 2| ≤ 2 * s.ε ∧
    |(f i + c i) / 2 - r i| ≤ s.centerRadius ∧
    s.ρ ≤ f (a i) - (f i + c i) / 2 := by
  have habs : |(f i - c i) / 2| = |f i - c i| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hc := abs_le.mp (hs.center_all i hi)
  have hf := abs_le.mp (hall i hi)
  have hrall : (f i + c i) / 2 ≤ r i + 3 * s.ε + 2 * s.ζ + 3 * s.d / 2 := by
    dsimp [AnchorScales.A1] at hc
    linarith
  have hrorg : original i →
      (f i + c i) / 2 ≤ r i + s.ε + s.ζ + 3 * s.d / 2 := by
    intro ho
    have hc0 := abs_le.mp (hs.center_original i hi ho)
    dsimp [AnchorScales.A0] at hc0
    linarith
  refine ⟨by rw [habs]; linarith, by rw [habs]; linarith [hall i hi, hn.jump_small], ?_, ?_⟩
  · apply abs_le.mpr
    dsimp [AnchorScales.centerRadius, AnchorScales.A1] at *
    constructor <;> linarith
  · by_cases hnewa : a i = j
    · rw [hnewa]
      have hsep := hs.separation i hi
      rw [hnewa] at hsep
      linarith [hn.exit_margin, hn.epsilon_pos, hn.transfer_nonneg, hn.jump_nonneg]
    · have halt : a i < j := lt_of_le_of_ne (hs.anchor_le i hi) hnewa
      have ha := hs.anchor_old i hi halt
      have hqa : r (a i) - 4 * s.ε - 2 * s.ζ - 2 * s.d ≤ f (a i) := by
        have hca := abs_le.mp (hs.center_all (a i) ha)
        have hfa := abs_le.mp (hall (a i) ha)
        dsimp [AnchorScales.A1] at hca
        linarith
      have hqorg : original (a i) → r (a i) - 2 * s.ε - s.ζ - 2 * s.d ≤ f (a i) := by
        intro ho
        have hca := abs_le.mp (hs.center_original (a i) ha ho)
        have hfa := abs_le.mp (hall (a i) ha)
        dsimp [AnchorScales.A0] at hca
        linarith
      apply SKOptimized.first_exit_gap (ρ := s.ρ) (ε := s.ε) (η := s.ζ / 2)
        (d := s.d) (r := (f i + c i) / 2) (q := f (a i)) (ri := r i) (ra := r (a i))
        (originalI := original i) (originalA := original (a i))
      · linarith [hn.transfer_nonneg]
      · rcases hs.no_double_rewire i hi with ho | he | ho
        · exact Or.inl ho
        · exact False.elim (hnewa he)
        · exact Or.inr ho
      · intro ho
        linarith [hrorg ho]
      · linarith [hrall]
      · intro ho
        linarith [hqorg ho]
      · linarith [hqa]
      · linarith [hn.exit_margin, hs.separation i hi]

theorem simultaneous_backward_windows {s : AnchorScales} (hn : AnchorNumerics s)
    {A : Finset ℕ} {j l u : ℕ} {r c : ℕ → ℝ} {a : ℕ → ℕ} {original : ℕ → Prop}
    (hs : AnchorSearch s A j r c a original) (f : ℕ → ℕ → ℝ)
    (hend : ∀ i ∈ A, |f i u - c i| < 2 * s.ε)
    (hjump : ∀ i ∈ A, ∀ k, l ≤ k → k < u → |f i (k + 1) - f i k| ≤ s.d)
    (hnew : ∀ k, l ≤ k → k ≤ u → r j - s.d ≤ f j k)
    (havoid : ∀ i ∈ A, ∀ k, l ≤ k → k ≤ u →
      s.ε ≤ |(f i k - c i) / 2| → |(f i k - c i) / 2| ≤ 2 * s.ε →
      |(f i k + c i) / 2 - r i| ≤ s.centerRadius →
      s.ρ ≤ f (a i) k - (f i k + c i) / 2 → False) :
    ∀ k, l ≤ k → k ≤ u → ∀ i ∈ A, |f i k - c i| < 2 * s.ε := by
  intro k hlk hku
  induction hku using Nat.decreasingInduction with
  | self => exact hend
  | @of_succ k hku ih =>
    have hall : ∀ i ∈ A, |f i k - c i| ≤ 2 * s.ε + s.d := by
      intro i hi
      have ht : |f i k - c i| ≤ |f i (k + 1) - c i| + |f i (k + 1) - f i k| := by
        have H := abs_add_le (f i (k + 1) - c i) (-(f i (k + 1) - f i k))
        rw [show f i (k + 1) - c i + -(f i (k + 1) - f i k) = f i k - c i by ring,
          abs_neg] at H
        exact H
      have hnxt := ih (by omega) i hi
      linarith [hjump i hi k hlk hku]
    intro i hi
    by_contra hfail
    obtain ⟨hlo, hhi, hc, hgap⟩ := anchor_first_exit hn hs (fun a => f a k)
      hall (hnew k hlk hku.le) hi (le_of_not_gt hfail)
    exact havoid i hi k hlk hku.le hlo hhi hc hgap

theorem anchor_search_crossing {n : ℕ} {D : AnchorData n} (N : NarrowInput D)
    (hn : AnchorNumerics D.scales) {r : ℕ → ℝ} (hg : ThresholdGeometry D r)
    {A : Finset ℕ} {j u : ℕ} {v : ℕ → Config n} {a : ℕ → ℕ}
    {original : ℕ → Prop} (hj : j < D.p) (hu : u ≤ D.m)
    (hmem : ∀ i ≤ j, v i ∈ D.pool i)
    (hsearch : AnchorSearch D.scales A j r
      (fun i => overlap (v i) (v (a i))) a original)
    (hzero : 0 ∈ A) (hinit : D.scales.qStar ≤ overlap (v 0) (D.x 0))
    (hend : ∀ i ∈ A, |overlap (v i) (D.x u) - overlap (v i) (v (a i))| < 2 * D.scales.ε)
    (hselected : D.scales.qStar ≤ overlap (v j) (D.x u))
    (hjump : ∀ v k, k < D.m →
      |overlap v (D.x (k + 1)) - overlap v (D.x k)| ≤ D.scales.d) :
    let l := lastCrossing (fun k => overlap (v j) (D.x k)) (r j) u
    (∃ k ≤ u, overlap (v j) (D.x k) ≤ r j) ∧
    overlap (v j) (D.x l) ∈ Icc (r j - D.scales.d) (r j) ∧
    (∀ k, l ≤ k → k ≤ u → ∀ i ∈ A,
      |overlap (v i) (D.x k) - overlap (v i) (v (a i))| < 2 * D.scales.ε) := by
  dsimp only
  let l := lastCrossing (fun k => overlap (v j) (D.x k)) (r j) u
  have htop : r j < overlap (v j) (D.x u) := by
    have hT : 0 ≤ D.scales.T1 := hn.jump_nonneg.trans hn.jump_le_T1
    linarith [(hg.range j hj).2, hn.selection_margin]
  have hstep : ∀ k, k < u →
      |overlap (v j) (D.x (k + 1)) - overlap (v j) (D.x k)| ≤ D.scales.d := by
    intro k hk
    exact hjump (v j) k (lt_of_lt_of_le hk hu)
  have hwindows : ∀ k, l ≤ k → k ≤ u → ∀ i ∈ A,
      |overlap (v i) (D.x k) - overlap (v i) (v (a i))| < 2 * D.scales.ε := by
    apply simultaneous_backward_windows hn hsearch (fun i k => overlap (v i) (D.x k)) hend
    · intro i _ k _ hk
      exact hjump (v i) k (lt_of_lt_of_le hk hu)
    · exact lastCrossing_search _ _ _ _ hn.jump_nonneg htop hstep
    · intro i hi k _ hk hlo hhi hc hgap
      have hia := hsearch.anchor_gt i hi
      have haj := hsearch.anchor_le i hi
      have hip : i < D.p := lt_of_lt_of_le hia (haj.trans hj.le)
      exact N.no_narrow hia (lt_of_le_of_lt haj hj)
        (hmem i (le_trans hia.le haj)) (hmem (a i) haj) (hk.trans hu)
        (N.center_band (r i) (hg.range i hip) _ hc) hlo hhi hgap
  have hex : ∃ k ≤ u, overlap (v j) (D.x k) ≤ r j := by
    by_contra hnone
    have hl : l = 0 := lastCrossing_zero_of_none _ _ _ hnone
    have hw := hwindows 0 (by omega) (Nat.zero_le _) 0 hzero
    have hc := hsearch.center_all 0 hzero
    have h0p : 0 < D.p := Nat.zero_lt_of_lt hj
    have hr0 := (hg.range 0 h0p).2
    have ht := hn.selection_margin
    dsimp [AnchorScales.A1, AnchorScales.T1] at hc ht
    linarith [(abs_lt.mp hw).2, (abs_le.mp hc).2]
  exact ⟨hex, lastCrossing_band _ _ _ _ htop hex hstep, hwindows⟩

theorem complete_block_protection {A D : Finset ℕ} {s B H : ℕ}
    (hs : IsRetainedSuffix A D) (hcard : D.card ≤ H) (hB : H + 2 ≤ B)
    (hblock : Finset.Ico s (s + B) ⊆ A) :
    (∀ i ∈ A, i < s + B - H → i ∈ A \ D) ∧
    (s ∈ A \ D ∧ s + 1 ∈ A \ D) ∧
    retainedSuccessor (A \ D) s = s + 1 := by
  have hpacket : SKOptimized.RetainedSuffix A D := hs
  refine ⟨?_, SKOptimized.retainedSuffix_preserves_first_two hpacket hcard hB hblock,
    SKOptimized.replacement_anchor_is_original hpacket hcard hB hblock⟩
  intro i hi his
  apply SKOptimized.retainedSuffix_preserves_prefix hpacket hcard
    (k := B - H - 1) (by omega) hblock hi
  omega

theorem unique_rewired_boundary {A D : Finset ℕ} {i k j : ℕ}
    (hs : IsRetainedSuffix A D) (hi : i ∈ A \ D) (hk : k ∈ A \ D)
    (hia : retainedSuccessor A i ∈ D) (hka : retainedSuccessor A k ∈ D)
    (hmax : ∀ z ∈ A, z < j) :
    i = k ∧ retainedSuccessor (insert j (A \ D)) i = j := by
  have hiA := (Finset.mem_sdiff.mp hi).1
  have hkA := (Finset.mem_sdiff.mp hk).1
  have he : i = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hik | hki
    · exact (Finset.mem_sdiff.mp hk).2
        (SKOptimized.all_later_deleted_of_successor_deleted hs hia k hkA hik)
    · exact (Finset.mem_sdiff.mp hi).2
        (SKOptimized.all_later_deleted_of_successor_deleted hs hka i hiA hki)
  exact ⟨he, SKOptimized.retainedSuccessor_rewired hs hia (hmax i hiA)⟩

end SKBarriers2.Dynamics
