module

public import SKBarriers2.Overshoot.Schedule
public import OAI.Probability.SKBarriers.Parisi.CDFSuffixSemigroup
public import OAI.Probability.SKBarriers.Hierarchy.TimeChainExactPenalty
public import OAI.Probability.SKBarriers.Scalar.PartitionChain

@[expose] public section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2.OW

private theorem splice_monotone (a : ℝ) (f g : ℝ → ℝ)
    (hf : Monotone f) (hg : Monotone g) (ha : f a ≤ g a) :
    Monotone (fun x => if x < a then f x else g x) := by
  intro x y hxy
  by_cases hx : x < a <;> by_cases hy : y < a
  · simpa only [ite_eq_left hx, ite_eq_left hy] using hf hxy
  · simp only [ite_eq_left hx, ite_eq_right hy]
    exact (hf hx.le).trans (ha.trans (hg (le_of_not_gt hy)))
  · exact False.elim (hx (hxy.trans_lt hy))
  · simpa only [ite_eq_right hx, ite_eq_right hy] using hg hxy

private theorem scalarCDFOperator_congr_ae {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {A B : ℝ → ℝ}
    (hA : ∀ x, A x ∈ Icc (0 : ℝ) 1) (hmA : Monotone A)
    (hB : ∀ x, B x ∈ Icc (0 : ℝ) 1) (hmB : Monotone B)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1)
    (he : ∀ᵐ x : ℝ, x ∈ Ioc s (s + t) → A x = B x) (x : ℝ) :
    scalarCDFOperator β A s t f x = scalarCDFOperator β B s t f x := by
  have hz : (∫ y in s..s + t, |A y - B y|) = 0 := by
    rw [intervalIntegral.integral_congr_ae' (g := fun _ => 0) (by
      filter_upwards [he] with y hy hmem
      rw [hy hmem, sub_self, abs_zero])
      (by
        filter_upwards [] with y hy
        exact False.elim (not_lt_of_ge (by linarith [t.coe_nonneg, hy.2]) hy.1)),
      intervalIntegral.integral_zero]
  have H := scalarCDFOperator_cdf_lipschitz hf hLip β hA hmA hB hmB s t ht x
  rw [hz, mul_zero] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

private theorem scalarCDFOperator_congr_Ioo {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {A B : ℝ → ℝ}
    (hA : ∀ x, A x ∈ Icc (0 : ℝ) 1) (hmA : Monotone A)
    (hB : ∀ x, B x ∈ Icc (0 : ℝ) 1) (hmB : Monotone B)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1)
    (he : (Ioo s (s + t)).EqOn A B) :
    scalarCDFOperator β A s t f = scalarCDFOperator β B s t f := by
  funext x
  have hz : (∫ y in s..s + t, |A y - B y|) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le
      (show s ≤ s + (t : ℝ) by linarith [t.coe_nonneg])
      (show (Ioo s (s + t)).EqOn (fun y => |A y - B y|) (fun _ => 0) from
        fun y hy => by
          change |A y - B y| = 0
          rw [he hy, sub_self, abs_zero]), intervalIntegral.integral_zero]
  have H := scalarCDFOperator_cdf_lipschitz hf hLip β hA hmA hB hmB s t ht x
  rw [hz, mul_zero] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

private theorem exists_stieltjes_representative (A : ℝ → ℝ)
    (hA : ∀ x, A x ∈ Icc (0 : ℝ) 1) (hmA : Monotone A) :
    ∃ B : StieltjesFunction ℝ, (∀ x, B x ∈ Icc (0 : ℝ) 1) ∧ B 1 = 1 ∧
      (∀ᵐ x : ℝ, x ≤ 1 → B x = A x) := by
  let C : ℝ → ℝ := fun x => if x < 1 then A x else 1
  have hmC : Monotone C := splice_monotone 1 A (fun _ => 1) hmA monotone_const (hA 1).2
  have hbC (x : ℝ) : C x ∈ Icc (0 : ℝ) 1 := by
    dsimp only [C]
    split_ifs
    · exact hA x
    · exact ⟨zero_le_one, le_rfl⟩
  let B := hmC.stieltjesFunction
  have hbB (x : ℝ) : B x ∈ Icc (0 : ℝ) 1 :=
    ⟨(hbC x).1.trans (hmC.le_rightLim le_rfl),
      (hmC.rightLim_le (lt_add_one x)).trans (hbC (x + 1)).2⟩
  refine ⟨B, hbB, ?_, ?_⟩
  · apply le_antisymm (hbB 1).2
    have H : C 1 ≤ B 1 := hmC.le_rightLim le_rfl
    have hC1 : C 1 = 1 := by simp [C]
    rw [hC1] at H
    exact H
  · have hc : ∀ᵐ x : ℝ, ContinuousAt C x := by
      filter_upwards [hmC.countable_not_continuousAt.ae_notMem volume] with x hx
      exact not_not.mp hx
    filter_upwards [hc, volume.ae_ne (1 : ℝ)] with x hx hne hx1
    have hlt : x < 1 := lt_of_le_of_ne hx1 hne
    change Function.rightLim C x = A x
    rw [hx.continuousWithinAt.rightLim_eq]
    exact ite_eq_left hlt

theorem scalarCDFValue_suffix_semigroup_monotone (β : ℝ) (A : ℝ → ℝ)
    (hA : ∀ x, A x ∈ Icc (0 : ℝ) 1) (hmA : Monotone A) {s q : ℝ}
    (hs : 0 ≤ s) (hsq : s ≤ q) (hq : q ≤ 1) :
    scalarCDFValue β A s (Real.toNNReal (1 - s)) =
      scalarCDFOperator β A s (Real.toNNReal (q - s))
        (scalarCDFValue β A q (Real.toNNReal (1 - q))) := by
  obtain ⟨B, hB, hB1, he⟩ := exists_stieltjes_representative A hA hmA
  have ht (a : ℝ) (ha : 0 ≤ a) : Real.toNNReal (1 - a) ≤ 1 :=
    Real.toNNReal_le_one.mpr (by linarith)
  have hv (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      scalarCDFValue β B a (Real.toNNReal (1 - a)) =
      scalarCDFValue β A a (Real.toNNReal (1 - a)) := by
    funext x
    apply scalarCDFOperator_congr_ae scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hB B.mono hA hmA a _ (ht a ha.1) _ x
    filter_upwards [he] with y hy hmem
    exact hy (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr ha.2)] at hmem; linarith [hmem.2])
  have H := scalarCDFValue_suffix_semigroup β B hB hB1 hs hsq hq
  rw [hv s ⟨hs, hsq.trans hq⟩, hv q ⟨hs.trans hsq, hq⟩] at H
  have hop : scalarCDFOperator β B s (Real.toNNReal (q - s))
      (scalarCDFValue β A q (Real.toNNReal (1 - q))) =
      scalarCDFOperator β A s (Real.toNNReal (q - s))
      (scalarCDFValue β A q (Real.toNNReal (1 - q))) := by
    funext x
    apply scalarCDFOperator_congr_ae
      (scalarCDFValue_regular β hA hmA _ _ (ht q (hs.trans hsq)))
      (scalarCDFValue_lipschitz β hA hmA _ _ (ht q (hs.trans hsq))) β hB B.mono hA hmA
      s _ (Real.toNNReal_le_one.mpr (by linarith)) _ x
    filter_upwards [he] with y hy hmem
    exact hy (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr hsq)] at hmem; linarith [hmem.2])
  rw [hop] at H
  exact H

def uniformTimeGrid (α : ℝ → ℝ) (a len : ℝ) (N : ℕ) : List (ℝ × ℝ≥0) :=
  List.ofFn fun i : Fin N =>
    (α (a + len * (i : ℝ) / (N : ℝ)), Real.toNNReal (len / (N : ℝ)))

private theorem map_range_eq_ofFn {E : Type} (N : ℕ) (f : ℕ → E) :
    (List.range N).map f = List.ofFn (fun i : Fin N => f i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem uniformGridTimes_monotone (a len : ℝ) (N : ℕ) (hlen : 0 ≤ len) :
    Monotone (fun i : Fin (N + 1) => a + len * (i : ℝ) / (N : ℝ)) := by
  intro i j hij
  have hc : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  have H := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hlen) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  dsimp
  linarith

private theorem uniformTimeGrid_partition (α : ℝ → ℝ) (a len : ℝ)
    {N : ℕ} (_hN : 0 < N) (hlen : 0 ≤ len) :
    uniformTimeGrid α a len N =
      partitionTimeChain N (fun i : Fin (N + 1) => a + len * (i : ℝ) / (N : ℝ))
        (uniformGridTimes_monotone a len N hlen)
        (fun i : Fin N => α (a + len * (i : ℝ) / (N : ℝ))) := by
  unfold uniformTimeGrid partitionTimeChain
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · rfl
  · apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (div_nonneg hlen (Nat.cast_nonneg N)), NNReal.coe_mk]
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring

theorem uniformTimeGrid_duration (α : ℝ → ℝ) (a len : ℝ)
    {N : ℕ} (hN : 0 < N) (hlen : 0 ≤ len) :
    (chainDuration (uniformTimeGrid α a len N) : ℝ) = len := by
  rw [uniformTimeGrid_partition α a len hN hlen, partitionTimeChain_duration]
  simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, add_zero]
  rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]
  ring

theorem relativeGridProfile_cell (α : ℝ → ℝ) (a len : ℝ)
    {N : ℕ} (hN : 0 < N) (hlen : 0 < len) (i : Fin N) (x : ℝ)
    (hx : x ∈ Ico (a + len * (i : ℝ) / (N : ℝ))
      (a + len * ((i : ℝ) + 1) / (N : ℝ))) :
    relativeGridProfile α a len N x = α (a + len * (i : ℝ) / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hl : (i : ℝ) ≤ (x - a) * (N : ℝ) / len := by
    apply (le_div_iff₀ hlen).mpr
    have H := (div_le_iff₀ hNr).mp (show len * (i : ℝ) / (N : ℝ) ≤ x - a by linarith [hx.1])
    nlinarith
  have hu : (x - a) * (N : ℝ) / len < (i : ℝ) + 1 := by
    apply (div_lt_iff₀ hlen).mpr
    have H := (lt_div_iff₀ hNr).mp (show x - a < len * ((i : ℝ) + 1) / (N : ℝ) by linarith [hx.2])
    nlinarith
  have hf : ⌊(x - a) * (N : ℝ) / len⌋₊ = (i : ℕ) :=
    Nat.floor_eq_on_Ico i _ ⟨hl, by simpa only [Nat.cast_add, Nat.cast_one] using hu⟩
  rw [relativeGridProfile, hf]

theorem uniformTimeGrid_models (α A : ℝ → ℝ) (a len : ℝ)
    {N : ℕ} (hN : 0 < N) (hlen : 0 < len)
    (hA : ∀ x ∈ Ico a (a + len), A x = relativeGridProfile α a len N x) :
    TimeChainModels A a (uniformTimeGrid α a len N) := by
  rw [uniformTimeGrid_partition α a len hN hlen.le]
  have he : a = a + len * ((0 : Fin (N + 1)) : ℝ) / (N : ℝ) := by simp
  nth_rw 1 [he]
  apply partitionTimeChain_models N
    (fun i : Fin (N + 1) => a + len * (i : ℝ) / (N : ℝ))
    (uniformGridTimes_monotone a len N hlen.le)
    (fun i : Fin N => α (a + len * (i : ℝ) / (N : ℝ)))
  intro i x hx
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcell : x ∈ Ico (a + len * (i : ℝ) / (N : ℝ))
      (a + len * ((i : ℝ) + 1) / (N : ℝ)) := by
    simpa only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hx
  have hwhole : x ∈ Ico a (a + len) := by
    refine ⟨?_, hcell.2.trans_le ?_⟩
    · have hi : 0 ≤ len * (i : ℝ) / (N : ℝ) := by positivity
      linarith [hcell.1]
    · have hi : (i : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
      have H := (div_le_iff₀ hNr).mpr (mul_le_mul_of_nonneg_left hi hlen.le)
      linarith
  rw [hA x hwhole]
  exact relativeGridProfile_cell α a len hN hlen i x hcell

def windowTimeChain (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) : List (ℝ × ℝ≥0) :=
  uniformTimeGrid α s h N ++ uniformTimeGrid α (s + h) (p * h) N ++
    uniformTimeGrid α (s + (1 + p) * h) ((1 - p) * h) N ++
    uniformTimeGrid α (s + 2 * h) (2 * h) N

private theorem scalarGrid_eq_time (β : ℝ) (α : ℝ → ℝ) (s h a len : ℝ)
    {N : ℕ} (_hN : 0 < N) (hd : 0 ≤ h * len) :
    scalarGrid β α s h N a len =
      scaleIncrementChain β (rawTimeChain (uniformTimeGrid α (s + h * a) (h * len) N)) := by
  unfold scalarGrid uniformTimeGrid rawTimeChain scaleIncrementChain
  rw [map_range_eq_ofFn, List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (α (s + h * (a + len * (i : ℝ) / (N : ℝ))),
      β * Real.sqrt (h * len / (N : ℝ))) =
    (α (s + h * a + (h * len) * (i : ℝ) / (N : ℝ)),
      β * Real.sqrt (Real.toNNReal (h * len / (N : ℝ)) : ℝ))
  rw [Real.coe_toNNReal _ (div_nonneg hd (Nat.cast_nonneg N))]
  congr 2
  ring

theorem scalarWindow_eq_time (β : ℝ) (α : ℝ → ℝ) (p s h : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1) :
    scalarWindow β α p s h N = scaleIncrementChain β (rawTimeChain (windowTimeChain α p s h N)) := by
  unfold scalarWindow windowTimeChain
  rw [scalarGrid_eq_time β α s h 0 1 hN (by simpa only [mul_one] using hh),
    scalarGrid_eq_time β α s h 1 p hN (mul_nonneg hh hp.1),
    scalarGrid_eq_time β α s h (1 + p) (1 - p) hN (mul_nonneg hh (sub_nonneg.mpr hp.2)),
    scalarGrid_eq_time β α s h 2 2 hN (mul_nonneg hh (by norm_num))]
  simp only [mul_zero, add_zero, mul_one, mul_comm h p, mul_comm h (1 - p), mul_comm h 2, mul_comm h (1 + p),
    rawTimeChain_append, scaleIncrementChain_append]

private theorem relativeGridProfile_start (α : ℝ → ℝ) (a len : ℝ) (N : ℕ) :
    relativeGridProfile α a len N a = α a := by
  simp [relativeGridProfile]

private theorem relativeGridProfile_end (α : ℝ → ℝ) (a len : ℝ)
    {N : ℕ} (hN : 0 < N) (hlen : 0 < len) :
    relativeGridProfile α a len N (a + len) = α (a + len) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he : (a + len - a) * (N : ℝ) / len = N := by
    field_simp
    ring
  rw [relativeGridProfile, he]
  simp only [Nat.floor_natCast]
  rw [mul_div_cancel_right₀ _ hNr]

private theorem relativeGridProfile_monotone (α : ℝ → ℝ) (hm : Monotone α)
    (a len : ℝ) {N : ℕ} (hN : 0 < N) (hlen : 0 < len) :
    Monotone (relativeGridProfile α a len N) := by
  intro x y hxy
  apply hm
  have hn : (x - a) * (N : ℝ) / len ≤ (y - a) * (N : ℝ) / len := by gcongr
  have hf : (⌊(x - a) * (N : ℝ) / len⌋₊ : ℝ) ≤ ⌊(y - a) * (N : ℝ) / len⌋₊ :=
    Nat.cast_le.mpr (Nat.floor_mono hn)
  gcongr

private def gridPatch (α A : ℝ → ℝ) (a len : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if x < a + len then relativeGridProfile α a len N x else A x

private theorem gridPatch_start (α A : ℝ → ℝ) (a len : ℝ) (N : ℕ) (hlen : 0 < len) :
    gridPatch α A a len N a = α a := by
  rw [gridPatch, ite_eq_left (by linarith), relativeGridProfile_start]

private theorem gridPatch_monotone (α A : ℝ → ℝ) (hmα : Monotone α) (hmA : Monotone A)
    (a len : ℝ) {N : ℕ} (hN : 0 < N) (hlen : 0 < len) (ha : A (a + len) = α (a + len)) :
    Monotone (gridPatch α A a len N) := by
  apply splice_monotone
  · exact relativeGridProfile_monotone α hmα a len hN hlen
  · exact hmA
  · rw [relativeGridProfile_end α a len hN hlen, ha]

private theorem joinedWindowProfile_eq (γ α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) (x : ℝ) :
    joinedWindowProfile γ α p s h N x =
      if x < s then γ x
      else if x < s + h then relativeGridProfile α s h N x
      else if x < s + (1 + p) * h then relativeGridProfile α (s + h) (p * h) N x
      else if x < s + 2 * h then
        relativeGridProfile α (s + (1 + p) * h) ((1 - p) * h) N x
      else if x < s + 4 * h then relativeGridProfile α (s + 2 * h) (2 * h) N x
      else α x := by
  by_cases hx : x < s <;> simp only [joinedWindowProfile, relativeWindowProfile, hx, ite_true, ite_false]

theorem joinedWindowProfile_bounds (γ α : ℝ → ℝ)
    (hγ : ∀ x, γ x ∈ Icc (0 : ℝ) 1) (hα : ∀ x, α x ∈ Icc (0 : ℝ) 1)
    (p s h : ℝ) (N : ℕ) (x : ℝ) : joinedWindowProfile γ α p s h N x ∈ Icc (0 : ℝ) 1 := by
  rw [joinedWindowProfile_eq]
  split_ifs
  · exact hγ x
  all_goals exact hα _

theorem joinedWindowProfile_monotone (γ α : ℝ → ℝ) (hmγ : Monotone γ) (hmα : Monotone α)
    (p s h : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hjoin : γ s ≤ α s) : Monotone (joinedWindowProfile γ α p s h N) := by
  have hp₁ : 0 < p * h := mul_pos hp.1 hh
  have hp₂ : 0 < (1 - p) * h := mul_pos (sub_pos.mpr hp.2) hh
  have h₂ : 0 < 2 * h := by positivity
  let g₃ := gridPatch α α (s + 2 * h) (2 * h) N
  have hm₃ : Monotone g₃ := gridPatch_monotone α α hmα hmα _ _ hN h₂ rfl
  let g₂ := gridPatch α g₃ (s + (1 + p) * h) ((1 - p) * h) N
  have hm₂ : Monotone g₂ := by
    apply gridPatch_monotone α g₃ hmα hm₃ _ _ hN hp₂
    rw [show s + (1 + p) * h + (1 - p) * h = s + 2 * h by ring]
    exact gridPatch_start α α _ _ N h₂
  let g₁ := gridPatch α g₂ (s + h) (p * h) N
  have hm₁ : Monotone g₁ := by
    apply gridPatch_monotone α g₂ hmα hm₂ _ _ hN hp₁
    rw [show s + h + p * h = s + (1 + p) * h by ring]
    exact gridPatch_start α g₃ _ _ N hp₂
  let g₀ := gridPatch α g₁ s h N
  have hm₀ : Monotone g₀ := by
    apply gridPatch_monotone α g₁ hmα hm₁ _ _ hN hh
    exact gridPatch_start α g₂ _ _ N hp₁
  have H : Monotone (fun x => if x < s then γ x else g₀ x) :=
    splice_monotone s γ g₀ hmγ hm₀ (hjoin.trans_eq (gridPatch_start α g₁ s h N hh).symm)
  have he : joinedWindowProfile γ α p s h N = fun x => if x < s then γ x else g₀ x := by
    funext x
    rw [joinedWindowProfile_eq]
    simp only [g₀, g₁, g₂, g₃, gridPatch,
      show s + h + p * h = s + (1 + p) * h by ring,
      show s + (1 + p) * h + (1 - p) * h = s + 2 * h by ring,
      show s + 2 * h + 2 * h = s + 4 * h by ring]
  rw [he]
  exact H

theorem windowTimeChain_duration (α : ℝ → ℝ) (p s h : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (chainDuration (windowTimeChain α p s h N) : ℝ) = 4 * h := by
  simp only [windowTimeChain, chainDuration_append, NNReal.coe_add,
    uniformTimeGrid_duration α s h hN hh.le,
    uniformTimeGrid_duration α (s + h) (p * h) hN (mul_pos hp.1 hh).le,
    uniformTimeGrid_duration α (s + (1 + p) * h) ((1 - p) * h) hN
      (mul_pos (sub_pos.mpr hp.2) hh).le,
    uniformTimeGrid_duration α (s + 2 * h) (2 * h) hN (by positivity)]
  ring

theorem windowTimeChain_mass (α : ℝ → ℝ) (hα : ∀ x, α x ∈ Icc (0 : ℝ) 1)
    (p s h : ℝ) (N : ℕ) : ∀ u ∈ windowTimeChain α p s h N, u.1 ∈ Icc (0 : ℝ) 1 := by
  intro u hu
  simp only [windowTimeChain, List.mem_append] at hu
  rcases hu with ((hu | hu) | hu) | hu
  all_goals
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hα _

theorem windowTimeChain_models (γ α : ℝ → ℝ) (p s h : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1) :
    TimeChainModels (joinedWindowProfile γ α p s h N) s (windowTimeChain α p s h N) := by
  have hp₁ : 0 < p * h := mul_pos hp.1 hh
  have hp₂ : 0 < (1 - p) * h := mul_pos (sub_pos.mpr hp.2) hh
  have H0 : TimeChainModels (joinedWindowProfile γ α p s h N) s
      (uniformTimeGrid α s h N) := by
    apply uniformTimeGrid_models α _ s h hN hh
    intro x hx
    rw [joinedWindowProfile_eq, ite_eq_right (not_lt.mpr hx.1), ite_eq_left hx.2]
  have H1 : TimeChainModels (joinedWindowProfile γ α p s h N) (s + h)
      (uniformTimeGrid α (s + h) (p * h) N) := by
    apply uniformTimeGrid_models α _ (s + h) (p * h) hN hp₁
    intro x hx
    rw [joinedWindowProfile_eq, ite_eq_right (by linarith [hx.1]),
      ite_eq_right (not_lt.mpr hx.1), ite_eq_left (by nlinarith [hx.2])]
  have H2 : TimeChainModels (joinedWindowProfile γ α p s h N) (s + (1 + p) * h)
      (uniformTimeGrid α (s + (1 + p) * h) ((1 - p) * h) N) := by
    apply uniformTimeGrid_models α _ _ _ hN hp₂
    intro x hx
    rw [joinedWindowProfile_eq, ite_eq_right (by nlinarith [hx.1]),
      ite_eq_right (by nlinarith [hx.1]), ite_eq_right (not_lt.mpr hx.1),
      ite_eq_left (by nlinarith [hx.2])]
  have H3 : TimeChainModels (joinedWindowProfile γ α p s h N) (s + 2 * h)
      (uniformTimeGrid α (s + 2 * h) (2 * h) N) := by
    apply uniformTimeGrid_models α _ _ _ hN (by positivity)
    intro x hx
    rw [joinedWindowProfile_eq, ite_eq_right (by linarith [hx.1]),
      ite_eq_right (by linarith [hx.1]), ite_eq_right (by nlinarith [hx.1]),
      ite_eq_right (not_lt.mpr hx.1), ite_eq_left (by linarith [hx.2])]
  have D0 := uniformTimeGrid_duration α s h hN hh.le
  have D1 := uniformTimeGrid_duration α (s + h) (p * h) hN hp₁.le
  have D2 := uniformTimeGrid_duration α (s + (1 + p) * h) ((1 - p) * h) hN hp₂.le
  have H01 := H0.append (by simpa only [D0] using H1)
  have H012 := H01.append (by
    simpa only [chainDuration_append, NNReal.coe_add, D0, D1,
      show s + (h + p * h) = s + (1 + p) * h by ring] using H2)
  exact H012.append (by
    simpa only [chainDuration_append, NNReal.coe_add, D0, D1, D2,
      show s + (h + p * h + (1 - p) * h) = s + 2 * h by ring] using H3)

private theorem joinedWindowProfile_prefix (γ α : ℝ → ℝ) (p s h : ℝ) (N : ℕ)
    {x : ℝ} (hx : x < s) : joinedWindowProfile γ α p s h N x = γ x := by
  exact ite_eq_left hx

private theorem joinedWindowProfile_tail (γ α : ℝ → ℝ) (p s h : ℝ) (N : ℕ)
    (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) 1) {x : ℝ} (hx : s + 4 * h ≤ x) :
    joinedWindowProfile γ α p s h N x = α x := by
  rw [joinedWindowProfile_eq]
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith),
    ite_eq_right (by nlinarith [mul_nonneg hh (sub_nonneg.mpr hp.2)]),
    ite_eq_right (by linarith), ite_eq_right (not_lt.mpr hx)]

theorem scalarWindow_value_joined (β : ℝ) (γ α : ℝ → ℝ)
    (hγ : ∀ x, γ x ∈ Icc (0 : ℝ) 1) (hmγ : Monotone γ)
    (hα : ∀ x, α x ∈ Icc (0 : ℝ) 1) (hmα : Monotone α)
    (p s h : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hjoin : γ s ≤ α s) (hs : 0 ≤ s) (hT : s + 4 * h ≤ 1) :
    scalarCDFValue β (joinedWindowProfile γ α p s h N) 0 1 0 =
      scalarCDFOperator β γ 0 (Real.toNNReal s)
        (scalarIncrementChain (scalarWindow β α p s h N) (Phi β α (s + 4 * h))) 0 := by
  let A := joinedWindowProfile γ α p s h N
  have hbA := joinedWindowProfile_bounds γ α hγ hα p s h N
  have hmA := joinedWindowProfile_monotone γ α hmγ hmα p s h hN hh hp hjoin
  have hp' : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hs1 : s ≤ 1 := by linarith
  have hT0 : 0 ≤ s + 4 * h := by linarith
  have ht : Real.toNNReal (1 - (s + 4 * h)) ≤ 1 := Real.toNNReal_le_one.mpr (by linarith)
  have hΦ : BoundedDerivs (Phi β α (s + 4 * h)) := scalarCDFValue_regular β hα hmα _ _ ht
  have hLipΦ : LipschitzWith 1 (Phi β α (s + 4 * h)) := scalarCDFValue_lipschitz β hα hmα _ _ ht
  have htail : scalarCDFValue β A (s + 4 * h) (Real.toNNReal (1 - (s + 4 * h))) =
      Phi β α (s + 4 * h) := by
    apply scalarCDFOperator_congr_Ioo scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hbA hmA hα hmα _ _ ht
    intro x hx
    exact joinedWindowProfile_tail γ α p s h N hh.le hp' (by linarith [hx.1])
  have hchain : scalarCDFOperator β A s (Real.toNNReal (4 * h)) (Phi β α (s + 4 * h)) =
      scalarIncrementChain (scalarWindow β α p s h N) (Phi β α (s + 4 * h)) := by
    rw [scalarWindow_eq_time β α p s h hN hh.le hp', scalarIncrementChain_rawTimeChain]
    funext x
    apply scalarCDFOperator_eq_chain hΦ hLipΦ β hbA hmA _
      (windowTimeChain_mass α hα p s h N) s _ (Real.toNNReal_le_one.mpr (by linarith))
      _ (windowTimeChain_models γ α p s h hN hh hp) x
    apply NNReal.coe_injective
    rw [windowTimeChain_duration α p s h hN hh hp, Real.coe_toNNReal _ (by positivity)]
  have hsuf : scalarCDFValue β A s (Real.toNNReal (1 - s)) =
      scalarIncrementChain (scalarWindow β α p s h N) (Phi β α (s + 4 * h)) := by
    rw [scalarCDFValue_suffix_semigroup_monotone β A hbA hmA hs (by linarith) hT,
      htail, show s + 4 * h - s = 4 * h by ring, hchain]
  have hpre : scalarCDFOperator β A 0 (Real.toNNReal s)
      (scalarIncrementChain (scalarWindow β α p s h N) (Phi β α (s + 4 * h))) =
      scalarCDFOperator β γ 0 (Real.toNNReal s)
      (scalarIncrementChain (scalarWindow β α p s h N) (Phi β α (s + 4 * h))) := by
    apply scalarCDFOperator_congr_Ioo (scalarIncrementChain_regular _ hΦ)
      (scalarIncrementChain_lipschitz _ (fun u hu => (scalarWindow_mass_mem β α hα p s h N u hu).1)
        hΦ hLipΦ) β hbA hmA hγ hmγ 0 _ (Real.toNNReal_le_one.mpr hs1)
    intro x hx
    exact joinedWindowProfile_prefix γ α p s h N (by
      rw [Real.coe_toNNReal s hs] at hx
      simpa only [zero_add] using hx.2)
  have H := scalarCDFValue_suffix_semigroup_monotone β A hbA hmA (s := 0) (q := s) le_rfl hs hs1
  simp only [sub_zero, Real.toNNReal_one] at H
  rw [hsuf, hpre] at H
  exact congrFun H 0

theorem window_zero_penalty_integral (γ α : ℝ → ℝ)
    (_hγ : ∀ x, γ x ∈ Icc (0 : ℝ) 1) (hmγ : Monotone γ)
    (_hα : ∀ x, α x ∈ Icc (0 : ℝ) 1) (hmα : Monotone α)
    (p s h : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hjoin : γ s ≤ α s) :
    matrixChainPenalty (window α p s h 0 N) (fun _ _ => s) =
      6 * ∫ t in s..s + 4 * h, t * joinedWindowProfile γ α p s h N t := by
  have hmA := joinedWindowProfile_monotone γ α hmγ hmα p s h hN hh hp hjoin
  have hp' : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hr : rawPenalty (scalarWindow 1 α p s h N) s =
      chainQuadraticPenalty s (windowTimeChain α p s h N) := by
    rw [scalarWindow_eq_time 1 α p s h hN hh.le hp']
    simp only [scaleIncrementChain, one_smul, Prod.mk.eta, List.map_id_fun', id_eq,
      rawPenalty_rawTimeChain]
  have H := (windowTimeChain_models γ α p s h hN hh hp).quadraticPenalty hmA
  rw [windowTimeChain_duration α p s h hN hh hp] at H
  rw [window_zero_penalty, hr, H]
  ring

theorem penalty_zero_joined (γ α : ℝ → ℝ)
    (hγ : ∀ x, γ x ∈ Icc (0 : ℝ) 1) (hmγ : Monotone γ)
    (hα : ∀ x, α x ∈ Icc (0 : ℝ) 1) (hmα : Monotone α)
    (p s h : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hjoin : γ s ≤ α s) (hs : 0 ≤ s) (hT : s + 4 * h ≤ 1) :
    penalty γ α p s h 0 N =
      6 * ∫ t in Icc (0 : ℝ) 1, t * joinedWindowProfile γ α p s h N t := by
  let A := joinedWindowProfile γ α p s h N
  have hmA := joinedWindowProfile_monotone γ α hmγ hmα p s h hN hh hp hjoin
  have hi (a b : ℝ) : IntervalIntegrable (fun t => t * A t) volume a b :=
    hmA.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  have ipre : (∫ t in Icc (0 : ℝ) s, t * γ t) = ∫ t in (0 : ℝ)..s, t * A t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    apply intervalIntegral.integral_congr_Ioo_of_le hs
    intro t ht
    change t * γ t = t * joinedWindowProfile γ α p s h N t
    rw [joinedWindowProfile_prefix γ α p s h N ht.2]
  have itail : (∫ t in Icc (s + 4 * h) 1, t * α t) = ∫ t in (s + 4 * h)..1, t * A t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
    apply intervalIntegral.integral_congr_Ioo_of_le hT
    intro t ht
    change t * α t = t * joinedWindowProfile γ α p s h N t
    rw [joinedWindowProfile_tail γ α p s h N hh.le ⟨hp.1.le, hp.2.le⟩ ht.1.le]
  rw [penalty, window_zero_penalty_integral γ α hγ hmγ hα hmα p s h hN hh hp hjoin, ipre, itail]
  calc
    _ = 6 * ((∫ t in (0 : ℝ)..s, t * A t) + (∫ t in s..s + 4 * h, t * A t) +
        ∫ t in (s + 4 * h)..1, t * A t) := by ring
    _ = 6 * ∫ t in (0 : ℝ)..1, t * A t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s (s + 4 * h)),
        intervalIntegral.integral_add_adjacent_intervals (hi 0 (s + 4 * h)) (hi (s + 4 * h) 1)]
    _ = _ := by rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

theorem trialValue_zero_parisi (β : ℝ) (γ α : ℝ → ℝ)
    (hγ : ∀ x, γ x ∈ Icc (0 : ℝ) 1) (hmγ : Monotone γ)
    (hα : ∀ x, α x ∈ Icc (0 : ℝ) 1) (hmα : Monotone α)
    (r d : ℝ) {N : ℕ} (hN : 0 < N) (hd : 0 < d)
    (hs : 0 ≤ r - 2 * d) (hT : r - 2 * d + 4 * (2 * d) ≤ 1)
    (hjoin : γ (r - 2 * d) ≤ α (r - 2 * d)) :
    trialValue β γ α r d 0 N =
      3 * scalarCDFParisi β (joinedWindowProfile γ α (1 / 2) (r - 2 * d) (2 * d) N) := by
  have hh : 0 < 2 * d := by positivity
  have hp : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  rw [trialValue_zero_finite_admissible β γ α hγ hmγ hα hmα r d N
    ⟨hs, by linarith⟩ ⟨by linarith, hT⟩,
    penalty_zero_joined γ α hγ hmγ hα hmα (1 / 2) (r - 2 * d) (2 * d) hN hh hp hjoin hs hT,
    ← scalarWindow_value_joined β γ α hγ hmγ hα hmα (1 / 2) (r - 2 * d) (2 * d)
      hN hh hp hjoin hs hT]
  unfold scalarCDFParisi
  ring

end SKBarriers2.OW
