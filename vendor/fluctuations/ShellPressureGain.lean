module

public import FiniteChordGain
public import SKFluctuationsOAI.Probability.SKFluctuations.OrderedSKRateDirection
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRetainTwo
public import LowerLedger

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem lowerEpsilon_eventually_le_scale_square {m k : ℝ}
    (hm : 0 < m) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, lowerEpsilon n ≤ k * lowerScale m n ^ 2 := by
  have hp := eventually_coefficient_rpow_le (c := 1) (d := k)
    (q := -(1 : ℝ) / 3) (r := -(1 : ℝ) / 3 + 10 * m) hk (by linarith)
  filter_upwards [hp, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  calc
    lowerEpsilon n = 1 * (n : ℝ) ^ (-(1 : ℝ) / 3) := by simp [lowerEpsilon]
    _ ≤ k * (n : ℝ) ^ (-(1 : ℝ) / 3 + 10 * m) := hn
    _ = k * lowerScale m n ^ 2 := by
      unfold lowerScale
      rw [← Real.rpow_mul_natCast hnreal.le]
      congr 1
      congr 1
      norm_num
      ring

theorem chord_cost_monotoneOn
    (delta e r : ℝ → ℝ) (s : Set ℝ)
    (hd : AntitoneOn delta s) (he : AntitoneOn e s)
    (hd0 : ∀ u ∈ s, 0 ≤ delta u) (he0 : ∀ u ∈ s, 0 < e u)
    (hr0 : ∀ u ∈ s, 0 ≤ r u)
    (her : MonotoneOn (fun u => e u * r u) s) :
    MonotoneOn (fun u => (e u * r u) ^ 2 / (delta u + e u)) s := by
  intro u hu v hv huv
  apply div_le_div₀ (sq_nonneg _)
  · exact pow_le_pow_left₀ (mul_nonneg (he0 u hu).le (hr0 u hu)) (her hu hv huv) 2
  · exact add_pos_of_nonneg_of_pos (hd0 v hv) (he0 v hv)
  · exact add_le_add (hd hu hv huv) (he hu hv huv)

theorem compensation_penalty_monotoneOn
    (e r : ℝ → ℝ) (s : Set ℝ)
    (he0 : ∀ u ∈ s, 0 ≤ e u) (hr0 : ∀ u ∈ s, 0 ≤ r u)
    (hr : MonotoneOn r s) (her : MonotoneOn (fun u => e u * r u) s) :
    MonotoneOn (fun u => e u * r u ^ 2) s := by
  intro u hu v hv huv
  calc
    e u * r u ^ 2 = (e u * r u) * r u := by ring
    _ ≤ (e v * r v) * r v := mul_le_mul (her hu hv huv) (hr hu hv huv)
      (hr0 u hu) (mul_nonneg (he0 v hv) (hr0 v hv))
    _ = e v * r v ^ 2 := by ring

theorem massStepSum_below_node (as : List PositiveMass) {a : ℝ}
    (ha : MassOrdered a as) (cut : PositiveMass) (hcut : cut ∈ as) :
    massStepSum as a
      (fun j => if partitionPoint a as j < cut.val then 1 else 0) = cut.val - a := by
  have hzero {bs : List PositiveMass} {b t : ℝ}
      (hb : MassOrdered b bs) (ht : t ≤ b) :
      massStepSum bs b (fun j => if partitionPoint b bs j < t then 1 else 0) = 0 := by
    have hf : (fun j => if partitionPoint b bs j < t then (1 : ℝ) else 0) =
        (fun _ => 0) := by
      funext j
      exact if_neg (not_lt.mpr (ht.trans (partitionPoint_mem bs hb j).1))
    rw [hf, massStepSum_const]
    ring
  induction as generalizing a with
  | nil => simp only [List.not_mem_nil] at hcut
  | cons b bs ih =>
    change (b.val - a) * (if a < cut.val then 1 else 0) +
      massStepSum bs b.val
        (fun j => if partitionPoint b.val bs j < cut.val then 1 else 0) = _
    rcases List.mem_cons.mp hcut with rfl | hcut
    · rw [hzero ha.2.2 le_rfl]
      by_cases hab : a < cut.val
      · simp [hab]
      · have hab' : a = cut.val := le_antisymm ha.2.1 (not_lt.mp hab)
        simp [hab']
    · have hbc : b.val ≤ cut.val := MassOrdered.le_of_mem ha.2.2 hcut
      by_cases hab : a < cut.val
      · rw [if_pos hab, mul_one, ih ha.2.2 hcut]
        ring
      · have hac : a = cut.val := le_antisymm (ha.2.1.trans hbc) (not_lt.mp hab)
        have hbc' : b.val = cut.val := le_antisymm hbc (hac ▸ ha.2.1)
        rw [if_neg hab, mul_zero, hzero ha.2.2 hbc'.ge]
        simp [hac]

theorem massStepSum_shell_nodes (as : List PositiveMass) (ha : MassOrdered 0 as)
    {s : ℝ} (hs : 0 < s)
    (hhalf : (⟨s / 2, by positivity⟩ : PositiveMass) ∈ as)
    (hend : (⟨s, hs⟩ : PositiveMass) ∈ as) :
    massStepSum as 0
      (fun j => if s / 2 ≤ partitionPoint 0 as j ∧ partitionPoint 0 as j < s
        then 1 else 0) = s / 2 := by
  have hf (j : ℕ) :
      (if s / 2 ≤ partitionPoint 0 as j ∧ partitionPoint 0 as j < s then (1 : ℝ) else 0) =
        (if partitionPoint 0 as j < s then 1 else 0) -
          (if partitionPoint 0 as j < s / 2 then 1 else 0) := by
    by_cases hj : partitionPoint 0 as j < s / 2
    · have hj' : partitionPoint 0 as j < s := hj.trans (by linarith)
      simp [hj, hj', not_le.mpr hj]
    · simp [hj, not_lt.mp hj]
  simp_rw [hf]
  rw [massStepSum_sub, massStepSum_below_node as ha ⟨s, hs⟩ hend,
    massStepSum_below_node as ha ⟨s / 2, by positivity⟩ hhalf]
  ring

theorem chord_shell_gain_pointwise {epsilon e r c s : ℝ}
    (hepsilon : 0 < epsilon) (he : epsilon ≤ e)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hr : c * s ≤ r) :
    (epsilon / 2) * (c * s) ^ 2 ≤ epsilon * e / (epsilon + e) * r ^ 2 := by
  have hepos : 0 < e := hepsilon.trans_le he
  have hden : 0 < epsilon + e := add_pos hepsilon hepos
  have hfactor : epsilon / 2 ≤ epsilon * e / (epsilon + e) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hepsilon.le (sub_nonneg.mpr he)]
  have hr0 : 0 ≤ r := (mul_nonneg hc hs).trans hr
  have hrsq : (c * s) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hc hs) hr 2
  exact (mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hrsq
      (div_nonneg (mul_nonneg hepsilon.le hepos.le) hden.le))

theorem finite_shell_gain {as : List PositiveMass}
    (ha : MassOrdered 0 as) (shell : ℕ → Prop) [DecidablePred shell]
    (epsilon c s : ℝ) (delta e r : ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (he : ∀ j, j ≤ as.length → 0 ≤ e j)
    (hdelta : ∀ j, j ≤ as.length → 0 ≤ delta j)
    (hdeltashell : ∀ j, j ≤ as.length → shell j → delta j = epsilon)
    (heshell : ∀ j, j ≤ as.length → shell j → epsilon ≤ e j)
    (hrshell : ∀ j, j ≤ as.length → shell j → c * s ≤ r j)
    (hmass : s / 2 ≤ massStepSum as 0 (fun j => if shell j then 1 else 0)) :
    c ^ 2 * epsilon * s ^ 3 / 16 ≤
      (1 / 4 : ℝ) * massStepSum as 0
        (fun j => delta j * e j / (delta j + e j) * r j ^ 2) := by
  have hpoint (j : ℕ) (hj : j ≤ as.length) :
      (epsilon / 2) * (c * s) ^ 2 * (if shell j then 1 else 0) ≤
        delta j * e j / (delta j + e j) * r j ^ 2 := by
    by_cases hjsh : shell j
    · rw [hdeltashell j hj hjsh]
      simpa only [if_pos hjsh, mul_one] using
        chord_shell_gain_pointwise hepsilon (heshell j hj hjsh) hc hs
          (hrshell j hj hjsh)
    · simp only [if_neg hjsh, mul_zero]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (hdelta j hj) (he j hj))
          (add_nonneg (hdelta j hj) (he j hj))) (sq_nonneg _)
  have hsum := massStepSum_mono as ha hpoint
  rw [massStepSum_const_mul] at hsum
  have hmass' := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (epsilon / 2) * (c * s) ^ 2 by positivity)
  nlinarith

theorem finite_pressure_strict_shell_gain
    (n : ℕ) (hn : 0 < n) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (b₀ b₁ e r : ℕ → ℝ) (error epsilon c s : ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hs : 0 < s)
    (hhalf : (⟨s / 2, by positivity⟩ : PositiveMass) ∈ as)
    (hend : (⟨s, hs⟩ : PositiveMass) ∈ as)
    (he : ∀ j, 0 ≤ e j) (hb01 : ∀ j, b₁ j ≤ b₀ j)
    (hb0 : Monotone b₀) (hbchild : Monotone (fun j => b₁ j - e j))
    (hhchild : Monotone (fun j => e j * r j))
    (hb00 : 0 ≤ b₀ 0) (hbc0 : 0 ≤ b₁ 0 - e 0) (hr0 : 0 ≤ r 0)
    (hdeltashell : ∀ j, j ≤ as.length →
      s / 2 ≤ partitionPoint 0 as j ∧ partitionPoint 0 as j < s →
        b₀ j - b₁ j = epsilon)
    (heshell : ∀ j, j ≤ as.length →
      s / 2 ≤ partitionPoint 0 as j ∧ partitionPoint 0 as j < s → epsilon ≤ e j)
    (hrshell : ∀ j, j ≤ as.length →
      s / 2 ≤ partitionPoint 0 as j ∧ partitionPoint 0 as j < s → c * s ≤ r j)
    (x : OrderedFeatureIndex n → ℝ)
    (hcomparison : finiteCompensatedPressure n as b₁ (fun _ => 0) e r x ≤
      orderedSKPressure n as b₁ (fun _ => 0) x + error) :
    c ^ 2 * epsilon * s ^ 3 / 16 - error ≤
      orderedSKPressure n as b₁ (fun _ => 0) x -
        orderedSKPressure n as b₀ (fun _ => 0) x := by
  have hgain := finite_shell_gain ha
    (fun j => s / 2 ≤ partitionPoint 0 as j ∧ partitionPoint 0 as j < s)
    epsilon c s (fun j => b₀ j - b₁ j) e r hepsilon hc.le hs.le
    (fun j _ => he j) (fun j _ => sub_nonneg.mpr (hb01 j))
    hdeltashell heshell hrshell
    (massStepSum_shell_nodes as ha hs hhalf hend).ge
  have hpressure := finite_pressure_gain_of_compensated_comparison n hn as
    ha.pairwise ha.members_le_one b₀ b₁ e r error he hb01 hb0 hbchild hhchild
    hb00 hbc0 hr0 x hcomparison
  linarith

theorem path_shell_gain {epsilon c s : ℝ} (delta e r : ℝ → ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 ≤ c) (hs : 0 < s) (hs1 : s ≤ 1)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hdelta : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ delta u)
    (hdeltashell : ∀ u ∈ Ioo (s / 2) s, delta u = epsilon)
    (heshell : ∀ u ∈ Ioo (s / 2) s, epsilon ≤ e u)
    (hrshell : ∀ u ∈ Ioo (s / 2) s, c * s ≤ r u)
    (hi : IntervalIntegrable
      (fun u => delta u * e u / (delta u + e u) * r u ^ 2) volume 0 1) :
    c ^ 2 * epsilon * s ^ 3 / 16 ≤
      (1 / 4 : ℝ) *
        (∫ u in (0 : ℝ)..1, delta u * e u / (delta u + e u) * r u ^ 2) := by
  let gain : ℝ → ℝ := fun u => delta u * e u / (delta u + e u) * r u ^ 2
  have h0 : 0 ≤ s / 2 := by positivity
  have hhalf : s / 2 ≤ s := by linarith
  have hishell : IntervalIntegrable gain volume (s / 2) s :=
    hi.mono_set (by
      simp only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num), uIcc_of_le hhalf]
      exact Icc_subset_Icc h0 hs1)
  have hlocal : (epsilon / 2) * (c * s) ^ 2 * (s - s / 2) ≤
      ∫ u in (s / 2)..s, gain u := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hhalf
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => (epsilon / 2) * (c * s) ^ 2) volume (s / 2) s)
      hishell (fun u hu => by
        dsimp [gain]
        rw [hdeltashell u hu]
        exact chord_shell_gain_pointwise hepsilon (heshell u hu) hc hs.le (hrshell u hu))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    nlinarith
  have hglobal : (∫ u in (s / 2)..s, gain u) ≤ ∫ u in (0 : ℝ)..1, gain u := by
    apply intervalIntegral.integral_mono_interval h0 hhalf hs1
    · apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [] with u hu
      dsimp [gain]
      have hui : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      exact mul_nonneg
        (div_nonneg (mul_nonneg (hdelta u hui) (he u hui))
          (add_nonneg (hdelta u hui) (he u hui))) (sq_nonneg _)
    · exact hi
  nlinarith

theorem path_pressure_gain_of_compensated_comparison
    (n : ℕ) (hn : 0 < n) (b₀ b₁ e r : ℝ → ℝ) (error : ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hb01 : ∀ u ∈ Icc (0 : ℝ) 1, b₁ u ≤ b₀ u)
    (hb0 : MonotoneOn b₀ (Icc (0 : ℝ) 1))
    (hb1 : MonotoneOn b₁ (Icc (0 : ℝ) 1))
    (hbchild : MonotoneOn (fun u => b₁ u - e u) (Icc (0 : ℝ) 1))
    (hhchild : MonotoneOn (fun u => e u * r u) (Icc (0 : ℝ) 1))
    (hb00 : 0 ≤ b₀ 0) (hb10 : 0 ≤ b₁ 0)
    (hbc0 : 0 ≤ b₁ 0 - e 0) (hr0 : 0 ≤ r 0)
    (hp : MonotoneOn (fun u => e u * r u ^ 2) (Icc (0 : ℝ) 1))
    (hcost : MonotoneOn
      (fun u => (e u * r u) ^ 2 / (b₀ u - b₁ u + e u)) (Icc (0 : ℝ) 1))
    (x : OrderedFeatureIndex n → ℝ)
    (hcomparison : pathCompensatedPressure n b₁ (fun _ => 0) e r x ≤
      realOrderedSKPathPressure n b₁ (fun _ => 0) x + error) :
    (1 / 4 : ℝ) *
        (∫ u in (0 : ℝ)..1,
          (b₀ u - b₁ u) * e u / (b₀ u - b₁ u + e u) * r u ^ 2) - error ≤
      realOrderedSKPathPressure n b₁ (fun _ => 0) x -
        realOrderedSKPathPressure n b₀ (fun _ => 0) x := by
  let gain : ℝ → ℝ := fun u =>
    (b₀ u - b₁ u) * e u / (b₀ u - b₁ u + e u) * r u ^ 2
  let cost : ℝ → ℝ := fun u =>
    (e u * r u) ^ 2 / (b₀ u - b₁ u + e u)
  have hidentity (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      gain u = e u * r u ^ 2 - cost u := by
    have h := chord_penalty_eq_penalty_sub_gain (he u hu)
      (sub_nonneg.mpr (hb01 u hu)) (r := r u)
    dsimp [gain, cost]
    rw [add_comm (b₀ u - b₁ u) (e u)]
    linarith
  have hip : IntervalIntegrable (fun u => e u * r u ^ 2) volume 0 1 :=
    (show MonotoneOn (fun u => e u * r u ^ 2) (uIcc (0 : ℝ) 1) by
      simpa using hp).intervalIntegrable
  have hic : IntervalIntegrable cost volume 0 1 :=
    (show MonotoneOn cost (uIcc (0 : ℝ) 1) by simpa [cost] using hcost).intervalIntegrable
  have higain : (∫ u in (0 : ℝ)..1, gain u) =
      (∫ u in (0 : ℝ)..1, e u * r u ^ 2) - ∫ u in (0 : ℝ)..1, cost u := by
    rw [← intervalIntegral.integral_sub hip hic]
    apply intervalIntegral.integral_congr
    intro u hu
    exact hidentity u (by simpa using hu)
  have htGain : Tendsto
      (fun k => massStepSum (uniformMasses k) 0
        (fun j => gain (partitionPoint 0 (uniformMasses k) j))) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, gain u)) := by
    have ht := (partitionSum_tendsto hp).sub (partitionSum_tendsto hcost)
    rw [← higain] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro k
    dsimp only
    rw [← massStepSum_sub]
    congr 1
    funext j
    exact (hidentity _ (partitionPoint_mem _ (uniformMasses_ordered k) j)).symm
  have ht₀ := orderedSKPressure_samples_tendsto n hn b₀ (fun _ => 0)
    hb0 (fun _ _ _ _ _ => le_rfl) hb00 (le_refl 0) x
  have ht₁ := orderedSKPressure_samples_tendsto n hn b₁ (fun _ => 0)
    hb1 (fun _ _ _ _ _ => le_rfl) hb10 (le_refl 0) x
  have htcomp := finiteCompensatedPressure_tendsto_path n hn b₁ (fun _ => 0) e r
    hbchild (by simpa only [zero_add] using hhchild) hbc0
    (by simpa only [zero_add] using mul_nonneg (he 0 (by norm_num)) hr0) hp x
  have hlimit : (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1, gain u) -
      (pathCompensatedPressure n b₁ (fun _ => 0) e r x -
        realOrderedSKPathPressure n b₁ (fun _ => 0) x) ≤
      realOrderedSKPathPressure n b₁ (fun _ => 0) x -
        realOrderedSKPathPressure n b₀ (fun _ => 0) x := by
    apply le_of_tendsto_of_tendsto ((htGain.const_mul (1 / 4 : ℝ)).sub
      (htcomp.sub ht₁)) (ht₁.sub ht₀)
    apply Eventually.of_forall
    intro k
    have ha := uniformMasses_ordered k
    apply finite_pressure_gain_of_compensated_comparison n hn (uniformMasses k)
      ha.pairwise ha.members_le_one
      (fun j => b₀ (partitionPoint 0 (uniformMasses k) j))
      (fun j => b₁ (partitionPoint 0 (uniformMasses k) j))
      (fun j => e (partitionPoint 0 (uniformMasses k) j))
      (fun j => r (partitionPoint 0 (uniformMasses k) j))
      (finiteCompensatedPressure n (uniformMasses k)
        (fun j => b₁ (partitionPoint 0 (uniformMasses k) j)) (fun _ => 0)
        (fun j => e (partitionPoint 0 (uniformMasses k) j))
        (fun j => r (partitionPoint 0 (uniformMasses k) j)) x -
        orderedSKPressure n (uniformMasses k)
          (fun j => b₁ (partitionPoint 0 (uniformMasses k) j)) (fun _ => 0) x)
    · exact fun j => he _ (partitionPoint_mem _ ha j)
    · exact fun j => hb01 _ (partitionPoint_mem _ ha j)
    · exact comp_partitionPoint_monotone hb0 _ ha
    · exact comp_partitionPoint_monotone hbchild _ ha
    · exact comp_partitionPoint_monotone hhchild _ ha
    · simpa [partitionPoint] using hb00
    · simpa [partitionPoint] using hbc0
    · simpa [partitionPoint] using hr0
    · linarith
  change (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1, gain u) - error ≤ _
  linarith

theorem path_pressure_strict_shell_gain
    (n : ℕ) (hn : 0 < n) (b₀ b₁ e r : ℝ → ℝ) (error epsilon c s : ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hs : 0 < s) (hs1 : s ≤ 1)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hb01 : ∀ u ∈ Icc (0 : ℝ) 1, b₁ u ≤ b₀ u)
    (hb0 : MonotoneOn b₀ (Icc (0 : ℝ) 1))
    (hb1 : MonotoneOn b₁ (Icc (0 : ℝ) 1))
    (hbchild : MonotoneOn (fun u => b₁ u - e u) (Icc (0 : ℝ) 1))
    (hhchild : MonotoneOn (fun u => e u * r u) (Icc (0 : ℝ) 1))
    (hb00 : 0 ≤ b₀ 0) (hb10 : 0 ≤ b₁ 0)
    (hbc0 : 0 ≤ b₁ 0 - e 0) (hr0 : 0 ≤ r 0)
    (hp : MonotoneOn (fun u => e u * r u ^ 2) (Icc (0 : ℝ) 1))
    (hcost : MonotoneOn
      (fun u => (e u * r u) ^ 2 / (b₀ u - b₁ u + e u)) (Icc (0 : ℝ) 1))
    (hdeltashell : ∀ u ∈ Ioo (s / 2) s, b₀ u - b₁ u = epsilon)
    (heshell : ∀ u ∈ Ioo (s / 2) s, epsilon ≤ e u)
    (hrshell : ∀ u ∈ Ioo (s / 2) s, c * s ≤ r u)
    (x : OrderedFeatureIndex n → ℝ)
    (hcomparison : pathCompensatedPressure n b₁ (fun _ => 0) e r x ≤
      realOrderedSKPathPressure n b₁ (fun _ => 0) x + error) :
    c ^ 2 * epsilon * s ^ 3 / 16 - error ≤
      realOrderedSKPathPressure n b₁ (fun _ => 0) x -
        realOrderedSKPathPressure n b₀ (fun _ => 0) x := by
  have hidentity (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      e u * r u ^ 2 - (e u * r u) ^ 2 / (b₀ u - b₁ u + e u) =
        (b₀ u - b₁ u) * e u / (b₀ u - b₁ u + e u) * r u ^ 2 := by
    have h := chord_penalty_eq_penalty_sub_gain (he u hu)
      (sub_nonneg.mpr (hb01 u hu)) (r := r u)
    rw [add_comm (b₀ u - b₁ u) (e u)]
    linarith
  have hip := (show MonotoneOn (fun u => e u * r u ^ 2) (uIcc (0 : ℝ) 1) by
    simpa using hp).intervalIntegrable (μ := volume)
  have hic := (show MonotoneOn
    (fun u => (e u * r u) ^ 2 / (b₀ u - b₁ u + e u)) (uIcc (0 : ℝ) 1) by
      simpa using hcost).intervalIntegrable (μ := volume)
  have hi := (hip.sub hic).congr (fun u hu =>
    hidentity u ⟨(by simpa using hu.1.le), (by simpa using hu.2)⟩)
  have hgain := path_shell_gain (fun u => b₀ u - b₁ u) e r hepsilon hc.le hs hs1
    he (fun u hu => sub_nonneg.mpr (hb01 u hu)) hdeltashell heshell hrshell hi
  have hpressure := path_pressure_gain_of_compensated_comparison n hn b₀ b₁ e r error
    he hb01 hb0 hb1 hbchild hhchild hb00 hb10 hbc0 hr0 hp hcost x hcomparison
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
