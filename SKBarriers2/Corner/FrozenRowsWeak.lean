module

public import SKBarriers2.Corner.FrozenRowsMoments5

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem normalizedPartition_rescale (P P₁ P₂ : Fin 4 → ℝ → ℝ) (ρ : ℝ)
    (n : Fin 4) (k : ℝ) :
    normalizedPartitionFirst P (fun n k => ρ * P₁ n k) n k =
        ρ * normalizedPartitionFirst P P₁ n k ∧
      normalizedPartitionSecond P (fun n k => ρ * P₁ n k)
          (fun n k => ρ ^ 2 * P₂ n k) n k =
        ρ ^ 2 * normalizedPartitionSecond P P₁ P₂ n k := by
  unfold normalizedPartitionFirst normalizedPartitionSecond normalizedPartitionMoment
  constructor <;> ring

theorem normalizedThirdRowsSecond_rescale (A A₁ A₂ : Fin 4 → ℝ → ℝ)
    (ρ m : ℝ) (i : Fin 3) (k : ℝ) :
    normalizedThirdRowsSecond m A (fun n k => ρ * A₁ n k)
        (fun n k => ρ ^ 2 * A₂ n k) i k =
      ρ ^ 2 * normalizedThirdRowsSecond m A A₁ A₂ i k := by
  fin_cases i
  · change ρ ^ 2 * A₂ 3 k / m = ρ ^ 2 * (A₂ 3 k / m)
    ring
  · change (ρ ^ 2 * A₂ 2 k * A 1 k + 2 * (ρ * A₁ 2 k) * (ρ * A₁ 1 k) +
      A 2 k * (ρ ^ 2 * A₂ 1 k)) / m =
        ρ ^ 2 * ((A₂ 2 k * A 1 k + 2 * A₁ 2 k * A₁ 1 k + A 2 k * A₂ 1 k) / m)
    ring
  · change (6 * A 1 k * (ρ * A₁ 1 k) ^ 2 + 3 * A 1 k ^ 2 * (ρ ^ 2 * A₂ 1 k)) / m =
      ρ ^ 2 * ((6 * A 1 k * A₁ 1 k ^ 2 + 3 * A 1 k ^ 2 * A₂ 1 k) / m)
    ring

theorem normalizedPartition_weak_bounds
    {P P₁ P₂ : Fin 4 → ℝ → ℝ} {k B t ρ : ℝ}
    (hB : 1 ≤ B) (ht : 0 ≤ t)
    (hb : ∀ n : Fin 4,
      |P n k / P 0 k| ≤ B * t ^ n.val ∧
      |ρ * (P₁ n k / P 0 k)| ≤ B * t ^ n.val ∧
      |ρ ^ 2 * (P₂ n k / P 0 k)| ≤ B * t ^ n.val) (n : Fin 4) :
    |normalizedPartitionMoment P n k| ≤ (6 * B ^ 3) * t ^ n.val ∧
      |ρ * normalizedPartitionFirst P P₁ n k| ≤ (6 * B ^ 3) * t ^ n.val ∧
      |ρ ^ 2 * normalizedPartitionSecond P P₁ P₂ n k| ≤ (6 * B ^ 3) * t ^ n.val := by
  have H := normalizedPartition_bounds
    (P := P) (P₁ := fun n k => ρ * P₁ n k) (P₂ := fun n k => ρ ^ 2 * P₂ n k)
    hB ht (fun n => by simpa only [mul_div_assoc] using hb n) n
  rw [(normalizedPartition_rescale P P₁ P₂ ρ n k).1,
    (normalizedPartition_rescale P P₁ P₂ ρ n k).2] at H
  exact H

theorem thirdPartitionRows_second_weak_control
    {P P₁ P₂ : Fin 4 → ℝ → ℝ} {U : Set ℝ} {B t ρ m : ℝ}
    (hB : 1 ≤ B) (ht : 0 ≤ t) (hm : 0 < m)
    (hZ : ∀ k ∈ U, P 0 k ≠ 0)
    (hd : ∀ k ∈ U, ∀ n, HasDerivAt (P n) (P₁ n k) k ∧
      HasDerivAt (P₁ n) (P₂ n k) k)
    (hb : ∀ k ∈ U, ∀ n : Fin 4,
      |P n k / P 0 k| ≤ B * t ^ n.val ∧
      |ρ * (P₁ n k / P 0 k)| ≤ B * t ^ n.val ∧
      |ρ ^ 2 * (P₂ n k / P 0 k)| ≤ B * t ^ n.val) :
    ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ i, ∀ k ∈ U, HasDerivAt (thirdPartitionRows m P i) (d₁ i k) k ∧
        HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ i, ∀ k ∈ U, |ρ ^ 2 * d₂ i k| ≤
        (((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / m) * t ^ 3) := by
  let A := normalizedPartitionMoment P
  let A₁ := normalizedPartitionFirst P P₁
  let A₂ := normalizedPartitionSecond P P₁ P₂
  refine ⟨normalizedThirdRowsFirst m A A₁, normalizedThirdRowsSecond m A A₁ A₂, ?_, ?_⟩
  · intro i k hk
    have H (n : Fin 4) : HasDerivAt (A n) (A₁ n k) k ∧ HasDerivAt (A₁ n) (A₂ n k) k :=
      normalizedPartition_derivatives (fun n => (hd k hk n).1)
        (fun n => (hd k hk n).2) (hZ k hk) n
    have heq : thirdPartitionRows m P i = normalizedThirdRows m A i :=
      funext (thirdPartitionRows_eq_normalized m P i)
    rw [heq]
    exact normalizedThirdRows_derivatives (fun n => (H n).1) (fun n => (H n).2) m i
  · intro i k hk
    rw [← normalizedThirdRowsSecond_rescale A A₁ A₂ ρ m i k]
    exact normalizedThirdRowsSecond_bound (by positivity : 0 ≤ 6 * B ^ 3) ht hm
      (normalizedPartition_weak_bounds hB ht (hb k hk)) i

structure PartitionIntegralKWeakControl (W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ)
    (U : Set ℝ) (B h : ℝ) : Prop where
  nonzero : ∀ k ∈ U, partitionIntegral W 0 k ≠ 0
  domination : ∀ k ∈ U, ∀ n : Fin 4,
    IntegralDerivativeControl (gaussianReal 0 1) (W n) (W₁ n) k ∧
      IntegralDerivativeControl (gaussianReal 0 1) (W₁ n) (W₂ n) k
  bounds : ∀ k ∈ U, ∀ n : Fin 4,
    |partitionIntegral W n k / partitionIntegral W 0 k| ≤ B * (Real.sqrt h * h) ^ n.val ∧
    |Real.sqrt h * (partitionIntegral W₁ n k / partitionIntegral W 0 k)| ≤
      B * (Real.sqrt h * h) ^ n.val ∧
    |h * (partitionIntegral W₂ n k / partitionIntegral W 0 k)| ≤
      B * (Real.sqrt h * h) ^ n.val
  normalizer : ∀ k ∈ U,
    |partitionIntegral W₁ 0 k / partitionIntegral W 0 k| ≤ B ∧
      |partitionIntegral W₂ 0 k / partitionIntegral W 0 k| ≤ B

theorem PartitionIntegralKWeakControl.rows
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U : Set ℝ} {B h m : ℝ}
    (H : PartitionIntegralKWeakControl W W₁ W₂ U B h)
    (hB : 1 ≤ B) (hh : 0 < h) (hm : 0 < m) :
    ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ i, ∀ k ∈ U, HasDerivAt (thirdPartitionRows m (partitionIntegral W) i) (d₁ i k) k ∧
        HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ i, ∀ k ∈ U, |d₂ i k| ≤
        (((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / m) *
          (Real.sqrt h * h ^ 3)) := by
  obtain ⟨d₁, d₂, hd, hb⟩ := thirdPartitionRows_second_weak_control
    (P₁ := partitionIntegral W₁) (P₂ := partitionIntegral W₂)
    (ρ := Real.sqrt h) (t := Real.sqrt h * h) hB (by positivity) hm H.nonzero
    (fun k hk n => ⟨(H.domination k hk n).1.hasDerivAt,
      (H.domination k hk n).2.hasDerivAt⟩)
    (by simpa only [Real.sq_sqrt hh.le] using H.bounds)
  refine ⟨d₁, d₂, hd, ?_⟩
  intro i k hk
  have Hbound := hb i k hk
  rw [Real.sq_sqrt hh.le, abs_mul, abs_of_pos hh] at Hbound
  have he : (Real.sqrt h * h) ^ 3 = h * (Real.sqrt h * h ^ 3) := by
    calc
      _ = (Real.sqrt h) ^ 2 * (Real.sqrt h * h ^ 3) := by ring
      _ = _ := by rw [Real.sq_sqrt hh.le]
  rw [he] at Hbound
  apply (mul_le_mul_iff_right₀ hh).mp
  convert Hbound using 1; ring

theorem PartitionIntegralKControl.toWeak
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U : Set ℝ} {B h : ℝ}
    (H : PartitionIntegralKControl W W₁ W₂ U B (Real.sqrt h * h))
    (hh : 0 ≤ h) (hh₁ : h ≤ 1) : PartitionIntegralKWeakControl W W₁ W₂ U B h := by
  refine ⟨H.nonzero, H.domination, ?_, ?_⟩
  · intro k hk n
    have hb := H.bounds k hk n
    refine ⟨hb.1, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
      exact (mul_le_of_le_one_left (abs_nonneg _)
        (Real.sqrt_le_one.mpr hh₁)).trans hb.2.1
    · rw [abs_mul, abs_of_nonneg hh]
      exact (mul_le_of_le_one_left (abs_nonneg _) hh₁).trans hb.2.2
  · intro k hk
    simpa only [Fin.val_zero, pow_zero, mul_one] using (H.bounds k hk 0).2

theorem PartitionIntegralKWeakControl.restrict_mono
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U V : Set ℝ} {B D h : ℝ}
    (H : PartitionIntegralKWeakControl W W₁ W₂ U B h)
    (hVU : V ⊆ U) (hBD : B ≤ D) (hh : 0 ≤ h) :
    PartitionIntegralKWeakControl W W₁ W₂ V D h := by
  refine ⟨fun k hk => H.nonzero k (hVU hk),
    fun k hk n => H.domination k (hVU hk) n, ?_, ?_⟩
  · intro k hk n
    have hbound := mul_le_mul_of_nonneg_right hBD
      (pow_nonneg (mul_nonneg (Real.sqrt_nonneg h) hh) n.val)
    exact ⟨((H.bounds k (hVU hk) n).1).trans hbound,
      ((H.bounds k (hVU hk) n).2.1).trans hbound,
      ((H.bounds k (hVU hk) n).2.2).trans hbound⟩
  · intro k hk
    exact ⟨((H.normalizer k (hVU hk)).1).trans hBD,
      ((H.normalizer k (hVU hk)).2).trans hBD⟩

theorem frozenKRegularity_of_partition_integral_weak_controls
    {β B a₀ h₀ κ : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hB : 1 ≤ B) (ha₀ : 0 < a₀)
    (hmass : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → a₀ ≤ α (r - h))
    (H : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 12 → ∃ W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ,
        PartitionIntegralKWeakControl
          (frozenPartitionWeight β α (α (r - h)) (r - h) h z ε j) W₁ W₂
          (Icc (-κ) κ) B h) :
    FrozenKRegularity β α I
      (3 * ((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / a₀) h₀ κ := by
  intro r hr h hh hhsmall z ε hε j hj
  obtain ⟨W₁, W₂, HW⟩ := H r hr h hh hhsmall z ε hε j hj
  have hm := frozenPartitionMass_lower ha₀ (hmass r hr h hh hhsmall) j
  have hmpos : 0 < frozenPartitionMass (α (r - h)) j := (div_pos ha₀ (by norm_num)).trans_le hm
  obtain ⟨d₁, d₂, hd, hb⟩ := HW.rows hB hh hmpos
  refine ⟨d₁, d₂, ?_, ?_⟩
  · intro i k hk
    have heq : frozenThirdPartitionRow β α (α (r - h)) (r - h) h z ε j i =
        thirdPartitionRows (frozenPartitionMass (α (r - h)) j)
          (partitionIntegral (frozenPartitionWeight β α (α (r - h)) (r - h) h z ε j)) i :=
      funext (frozenThirdPartitionRow_eq_moments β α _ _ h z ε hj i)
    rw [heq]
    exact hd i k hk
  · intro i k hk
    let R := (6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have hcoeff : R / frozenPartitionMass (α (r - h)) j ≤ 3 * R / a₀ := by
      calc
        _ ≤ R / (a₀ / 3) := div_le_div_of_nonneg_left hR (div_pos ha₀ (by norm_num)) hm
        _ = _ := by ring
    exact (hb i k hk).trans (by
      change R / frozenPartitionMass (α (r - h)) j * (Real.sqrt h * h ^ 3) ≤ _
      calc
        _ ≤ (3 * R / a₀) * (Real.sqrt h * h ^ 3) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = _ := by ring)

def FrozenPartitionKDerivativeWeak (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ B h₀ κ : ℝ, 1 ≤ B ∧ 0 < h₀ ∧ 0 < κ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 11 → ∃ W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ,
        let W := frozenPartitionWeight β α (α (r - h)) (r - h) h z ε j
        (∀ k ∈ Icc (-κ) κ, ∀ n : Fin 4,
          IntegralDerivativeControl (gaussianReal 0 1) (W n) (W₁ n) k ∧
          IntegralDerivativeControl (gaussianReal 0 1) (W₁ n) (W₂ n) k) ∧
        (∀ k ∈ Icc (-κ) κ,
          |partitionIntegral W₁ 0 k / partitionIntegral W 0 k| ≤ B ∧
          |partitionIntegral W₂ 0 k / partitionIntegral W 0 k| ≤ B) ∧
        (∀ k ∈ Icc (-κ) κ, ∀ n : Fin 4,
          |Real.sqrt h * (partitionIntegral W₁ n k / partitionIntegral W 0 k)| ≤
            B * (Real.sqrt h * h) ^ n.val ∧
          |h * (partitionIntegral W₂ n k / partitionIntegral W 0 k)| ≤
            B * (Real.sqrt h * h) ^ n.val)

theorem scalarData_frozenKRegularity_of_kDerivatives_weak {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (H : FrozenPartitionKDerivativeWeak β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 4 ∧
      FrozenKRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ κ := by
  obtain ⟨B, hD, κ, hB, hhD, hκ, HD⟩ := H
  obtain ⟨hZ, hhZ, HZ⟩ := scalarData_frozen_partition_pos D hl hu
  obtain ⟨hM, M, hhM, _, HM⟩ := scalarData_frozen_raw_moments_zero D hl hu
  obtain ⟨L, hL, _, hhL, HL⟩ := scalarData_frozen_last_partition_k_control D hl hu
  let T := max (max B M) L
  have hBT : B ≤ T := (le_max_left B M).trans (le_max_left _ L)
  have hMT : M ≤ T := (le_max_right B M).trans (le_max_left _ L)
  have hLT : L ≤ T := le_max_right _ _
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity : 0 < l / 2)
  let η := min hD (min hZ (min hM (min hL (min 1 (l / 2)))))
  let ρ := min κ (1 / 4)
  have hη : 0 < η := lt_min hhD (lt_min hhZ (lt_min hhM
    (lt_min hhL (lt_min (by norm_num) (by positivity)))))
  have hρ : 0 < ρ := lt_min hκ (by norm_num)
  have hρhalf : ρ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hsubκ : Icc (-ρ) ρ ⊆ Icc (-κ) κ :=
    fun _ hk => ⟨(neg_le_neg (min_le_left κ (1 / 4))).trans hk.1,
      hk.2.trans (min_le_left _ _)⟩
  have hsub4 : Icc (-ρ) ρ ⊆ Icc (-(1 / 4) : ℝ) (1 / 4) :=
    fun _ hk => ⟨(neg_le_neg (min_le_right κ (1 / 4))).trans hk.1,
      hk.2.trans (min_le_right _ _)⟩
  let R := (6 * T ^ 3) + 4 * (6 * T ^ 3) ^ 2 + 9 * (6 * T ^ 3) ^ 3
  let C := 3 * R / a₀
  have hC : 0 < C := by dsimp only [C, R]; positivity
  refine ⟨C, η, ρ, hC, hη, hρ, min_le_right _ _, ?_⟩
  apply frozenKRegularity_of_partition_integral_weak_controls (hB.trans hBT) ha₀
  · intro r hr h _ hhη
    have hηl : η ≤ l / 2 := (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    exact monotone_cdf _ (by linarith [hr.1, hhη.trans hηl])
  · intro r hr h hh hhη z ε hε j hj
    have hhD' : h ≤ hD := hhη.trans (min_le_left _ _)
    have hhrest := hhη.trans (min_le_right _ _)
    have hhZ' : h ≤ hZ := hhrest.trans (min_le_left _ _)
    have hhrest' := hhrest.trans (min_le_right _ _)
    have hhM' : h ≤ hM := hhrest'.trans (min_le_left _ _)
    have hhrest'' := hhrest'.trans (min_le_right _ _)
    have hhL' : h ≤ hL := hhrest''.trans (min_le_left _ _)
    have hh₁ : h ≤ 1 := hhrest''.trans ((min_le_right _ _).trans (min_le_left _ _))
    by_cases hj11 : j = 11
    · subst j
      exact ⟨_, _, ((HL r hr h hh hhL' z ε hε).toWeak hh.le hh₁).restrict_mono
        hsub4 hLT hh.le⟩
    · obtain ⟨W₁, W₂, hd, hn, hb⟩ := HD r hr h hh hhD' z ε hε j (by omega)
      refine ⟨W₁, W₂, ?_, ?_, ?_, ?_⟩
      · intro k hk
        exact ne_of_gt (HZ r hr h hh hhZ' k ((abs_le.mpr hk).trans hρhalf) z ε hε j hj)
      · intro k hk n
        exact hd k (hsubκ hk) n
      · intro k hk n
        have ht : 0 ≤ (Real.sqrt h * h) ^ n.val := by positivity
        have hscale := mul_le_mul_of_nonneg_right hBT ht
        exact ⟨(HM r hr h hh hhM' k ((abs_le.mpr hk).trans hρhalf) z ε hε j hj n).trans
            (mul_le_mul_of_nonneg_right hMT ht),
          ((hb k (hsubκ hk) n).1).trans hscale,
          ((hb k (hsubκ hk) n).2).trans hscale⟩
      · intro k hk
        exact ⟨((hn k (hsubκ hk)).1).trans hBT, ((hn k (hsubκ hk)).2).trans hBT⟩

theorem scalarData_terminalMixedThirdControl_of_kDerivatives_weak {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (H : FrozenPartitionKDerivativeWeak β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 4 ∧
      TerminalMixedThirdControl β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ κ := by
  obtain ⟨C, h₀, κ, hC, hh₀, hκ, hκ₄, HK⟩ :=
    scalarData_frozenKRegularity_of_kDerivatives_weak D hl hu H
  obtain ⟨h₁, hh₁, _, HT⟩ := scalarData_terminalMixedThirdControl_of_kRegularity D hl hu hh₀
    (hκ₄.trans_lt (by norm_num)) HK
  exact ⟨6 * C, h₁, κ, by positivity, hh₁, hκ, hκ₄, HT⟩

end SKBarriers2.Corner
