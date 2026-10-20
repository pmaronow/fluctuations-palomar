module

public import SKBarriers2.Static.EventBasic
public import SKBarriers2.Static.Remote
public import SKBarriers2.Static.PairFixed
public import SKBarriers2.Rate.Upstream

@[expose] public section

noncomputable section
open scoped NNReal BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI OAI.SK OAI.SK.Analytic

namespace SKBarriers2

def staticLocalSet (n : ℕ) (I : Set ℝ) (ρ E d₀ : ℝ) : Finset (ReplicaConfig n 3) :=
  (narrowSet n I ρ (E * ρ)).filter (fun s => tripleQ s - tripleR s ≤ d₀)

def staticRemoteSet (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ)
    (ρ E d₀ τ : ℝ) : Finset (ReplicaConfig n 3) :=
  (narrowSet n I ρ (E * ρ)).filter (fun s => d₀ < tripleQ s - tripleR s ∧
    |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ)

def staticFixedSet (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (η qs b b' τ : ℝ) :
    Finset (ReplicaConfig n 3) :=
  (signedLockingSetη n qs b η ∪ signedLockingSetη n b b' η).filter
    (fun s => |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ)

structure StaticCutoffs (β : ℝ) (α : ℝ → ℝ) (qs : ℝ) where
  b : ℝ
  b' : ℝ
  τ : ℝ
  cf : ℝ
  b_pos : 0 < b
  b_lt_one : b < 1
  b'_pos : 0 < b'
  b'_lt_b : b' < b
  τ_pos : 0 < τ
  cf_pos : 0 < cf
  gap : ∀ n : ℕ, 0 < n → ∀ η : ℝ, 0 ≤ η →
    ∀ s ∈ staticFixedSet n β α η qs b b' τ,
      matrixConstrainedPressure n 3 β (replicaGram s) ≤
        3 * finiteParisiInf β - cf * η^2

theorem exists_static_cutoffs {β qs : ℝ} (hβ : 0 < β)
    (hqs : 0 < qs) (hqs1 : qs ≤ 1) (μ : ProbabilityMeasure ℝ)
    (hunique : ∀ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ) :
    Nonempty (StaticCutoffs β (cdf (μ : Measure ℝ)) qs) := by
  obtain ⟨b₀, τ₀, cf₀, hb₀, hτ₀, hcf₀, hfix₀⟩ :=
    fixed_pressure_gap_of_unique_minimizer hβ hqs hqs1 μ hunique
  let b := min b₀ (1/2)
  have hb : 0 < b := lt_min hb₀ (by norm_num)
  have hb1 : b < 1 := (min_le_right b₀ (1/2)).trans_lt (by norm_num)
  obtain ⟨b₁, τ₁, cf₁, hb₁, hτ₁, hcf₁, hfix₁⟩ :=
    fixed_pressure_gap_of_unique_minimizer hβ hb hb1.le μ hunique
  let b' := min b₁ (b/2)
  have hb' : 0 < b' := lt_min hb₁ (half_pos hb)
  have hbb' : b' < b := (min_le_right b₁ (b/2)).trans_lt (by linarith)
  let τ := min τ₀ τ₁
  let cf := min cf₀ cf₁
  refine ⟨⟨b, b', τ, cf, hb, hb1, hb', hbb', lt_min hτ₀ hτ₁,
    lt_min hcf₀ hcf₁, ?_⟩⟩
  intro n hn η hη s hs
  obtain ⟨hs, hdev⟩ := Finset.mem_filter.mp hs
  rw [replicaGram_triple_overlap hn]
  have hfeas := replicaGram_triple_overlap hn s ▸ replicaGram_feasible s
  have hx : tripleR s + tripleDelta s = overlap (s 0) (s 1) := by
    unfold tripleR tripleDelta; ring_nf
  have hy : tripleR s - tripleDelta s = overlap (s 0) (s 2) := by
    unfold tripleR tripleDelta; ring_nf
  have hηδ (h : 2 * η < |overlap (s 0) (s 1) - overlap (s 0) (s 2)|) :
      η ≤ |tripleDelta s| := by
    unfold tripleDelta
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [h]
  rcases Finset.mem_union.mp hs with hs | hs
  · obtain ⟨hq, hab, hac, hd⟩ := (Finset.mem_filter.mp hs).2
    have hp := hfix₀ n hn _ _ _
      (by simpa only [hx] using hab.trans (min_le_left b₀ (1/2)))
      (by simpa only [hy] using hac.trans (min_le_left b₀ (1/2)))
      ⟨hq, (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2⟩
      (hdev.trans (min_le_left _ _)) hfeas
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη (hηδ hd) 2) hcf₀.le
    rw [sq_abs] at hs
    have hc := mul_le_mul_of_nonneg_right (min_le_left cf₀ cf₁) (sq_nonneg η)
    nlinarith only [hp, hs, hc]
  · obtain ⟨hq, hab, hac, hd⟩ := (Finset.mem_filter.mp hs).2
    have hp := hfix₁ n hn _ _ _
      (by simpa only [hx] using hab.trans (min_le_left b₁ (b/2)))
      (by simpa only [hy] using hac.trans (min_le_left b₁ (b/2)))
      ⟨hq, (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2⟩
      (hdev.trans (min_le_right _ _)) hfeas
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη (hηδ hd) 2) hcf₁.le
    rw [sq_abs] at hs
    have hc := mul_le_mul_of_nonneg_right (min_le_right cf₀ cf₁) (sq_nonneg η)
    nlinarith only [hp, hs, hc]

theorem forbiddenSet_mass_le_split {n : ℕ} (β : ℝ) (α : ℝ → ℝ)
    {l r ρ E d₀ τ η qs b b' : ℝ} (hl : 0 ≤ l) (hρ : 0 ≤ ρ)
    (hqs : 0 ≤ qs) (hb : 0 ≤ b) (J : Disorder n) :
    replicaGibbsMass β J (forbiddenSet n (Icc l r) ρ (E * ρ) η qs b b') ≤
      replicaGibbsMass β J (staticLocalSet n (Icc l r) ρ E d₀) +
      replicaGibbsMass β J (staticRemoteSet n β α (Icc l r) ρ E d₀ τ) +
      replicaGibbsMass β J (staticFixedSet n β α η qs b b' τ) +
      replicaGibbsMass β J (pairMismatchSet n β α τ) := by
  let P := Finset.univ.filter (fun s : ReplicaConfig n 3 =>
    Fin.tail s ∈ pairMismatchSet n β α τ)
  have hsub : forbiddenSet n (Icc l r) ρ (E * ρ) η qs b b' ⊆
      ((staticLocalSet n (Icc l r) ρ E d₀ ∪
        staticRemoteSet n β α (Icc l r) ρ E d₀ τ) ∪
        staticFixedSet n β α η qs b b' τ) ∪ P := by
    intro s hs
    have hpair (hq : 0 ≤ tripleQ s)
        (hdev : ¬ |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ) : s ∈ P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hq, (not_le.mp hdev).le⟩
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_union.mp hs with hs | hs
      · by_cases hd : tripleQ s - tripleR s ≤ d₀
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, hd⟩)))
        · by_cases hdev : |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, not_le.mp hd, hdev⟩)))
          · have hnarrow := hs
            simp only [narrowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnarrow
            exact Finset.mem_union_right _ (hpair (by linarith [hnarrow.1.1, hnarrow.2.2.2]) hdev)
      · by_cases hdev : |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs, hdev⟩))
        · exact Finset.mem_union_right _ (hpair
            (hqs.trans (Finset.mem_filter.mp hs).2.1) hdev)
    · by_cases hdev : |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hs, hdev⟩))
      · exact Finset.mem_union_right _ (hpair
          (hb.trans (Finset.mem_filter.mp hs).2.1) hdev)
  have h1 := (replicaGibbsMass_mono β J hsub).trans (replicaGibbsMass_union_le β J _ P)
  have h2 := replicaGibbsMass_union_le β J
    (staticLocalSet n (Icc l r) ρ E d₀ ∪ staticRemoteSet n β α (Icc l r) ρ E d₀ τ)
    (staticFixedSet n β α η qs b b' τ)
  have h3 := replicaGibbsMass_union_le β J
    (staticLocalSet n (Icc l r) ρ E d₀) (staticRemoteSet n β α (Icc l r) ρ E d₀ τ)
  rw [replicaGibbsMass_tail] at h1
  linarith only [h1, h2, h3]

theorem staticLocalSet_fractional_gap {β S E g : ℝ} {I : Set ℝ} {ρ : ℕ → ℝ}
    (hlocal : LocalFractionalGap β I ρ S E g) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ᶠ n : ℕ in atTop, 0 < n →
      ∀ s ∈ staticLocalSet n I (ρ n) E d₀,
        fractionalPressure n 3 β (S * ρ n) (replicaGram s) ≤
          3 * finiteParisiInf β - g * ρ n ^ 3 := by
  obtain ⟨d₀, hd₀, hgap⟩ := hlocal
  refine ⟨d₀, hd₀, ?_⟩
  filter_upwards [hgap] with n hn hn0 s hs
  obtain ⟨hs, hd⟩ := Finset.mem_filter.mp hs
  simp only [narrowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  obtain ⟨hr, hδ, hδ', hq⟩ := hs
  rw [replicaGram_triple_overlap hn0]
  exact hn _ hr _ _ (by linarith only [hq]) hd hδ (by simpa only [mul_assoc] using hδ')
    (replicaGram_triple_overlap hn0 s ▸ replicaGram_feasible s)

theorem staticRemoteSet_pressure_gap {n : ℕ} (hn : 0 < n)
    {β l r ρ E d₀ τ δ₀ c : ℝ} (α : ℝ → ℝ)
    (hsmall : 2 * E * ρ ≤ δ₀) (hEρ : 0 ≤ E * ρ)
    (hgap : ∀ x ∈ Icc l r, ∀ q δ : ℝ,
      d₀ ≤ q - x → q ≤ 1 → |q - scalarCDFOverlap β α q| ≤ τ → |δ| ≤ δ₀ →
      Nonempty (MatrixStates n 3 (tripleGram x δ q)) →
      matrixConstrainedPressure n 3 β (tripleGram x δ q) ≤
        3 * finiteParisiInf β - c * δ ^ 2)
    (hc : 0 ≤ c) :
    ∀ s ∈ staticRemoteSet n β α (Icc l r) ρ E d₀ τ,
      matrixConstrainedPressure n 3 β (replicaGram s) ≤
        3 * finiteParisiInf β - (c * E ^ 2) * ρ ^ 2 := by
  intro s hs
  obtain ⟨hs, hd, hdev⟩ := Finset.mem_filter.mp hs
  simp only [narrowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  obtain ⟨hr, hδ, hδ', _⟩ := hs
  have hp := hgap _ hr _ _ hd.le
    (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2 hdev
    (hδ'.trans (by simpa only [mul_assoc] using hsmall))
    (replicaGram_triple_overlap hn s ▸ replicaGram_feasible s)
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEρ hδ 2) hc
  rw [sq_abs] at hsq
  rw [replicaGram_triple_overlap hn]
  nlinarith only [hp, hsq]

def staticGoodEvent (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ)
    (ρ η E g d₀ τ cr cf qs b b' e : ℝ) : Set (Disorder n) :=
  staticDenominatorEvent n β e ∩
    staticNumeratorEvent β tripleReplicaCode (staticLocalSet n I ρ E d₀)
      (3 * finiteParisiInf β - g * ρ ^ 3 / 2) ∩
    staticNumeratorEvent β tripleReplicaCode (staticRemoteSet n β α I ρ E d₀ τ)
      (3 * finiteParisiInf β - cr * ρ ^ 2 / 2) ∩
    staticNumeratorEvent β tripleReplicaCode (staticFixedSet n β α η qs b b' τ)
      (3 * finiteParisiInf β - cf * η ^ 2 / 2) ∩
    staticNumeratorEvent β pairReplicaCode (pairMismatchSet n β α τ)
      (2 * finiteParisiInf β - τ ^ 2 / 4)

theorem measurableSet_staticGoodEvent (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ)
    (ρ η E g d₀ τ cr cf qs b b' e : ℝ) :
    MeasurableSet (staticGoodEvent n β α I ρ η E g d₀ τ cr cf qs b b' e) := by
  exact ((((measurableSet_staticDenominatorEvent n β e).inter
    (measurableSet_staticNumeratorEvent β tripleReplicaCode _ _)).inter
    (measurableSet_staticNumeratorEvent β tripleReplicaCode _ _)).inter
    (measurableSet_staticNumeratorEvent β tripleReplicaCode _ _)).inter
    (measurableSet_staticNumeratorEvent β pairReplicaCode _ _)

theorem staticGoodEvent_mass_le {n : ℕ} (β : ℝ) (α : ℝ → ℝ)
    {l r ρ η E g d₀ τ cr cf qs b b' e : ℝ}
    (hl : 0 ≤ l) (hρ : 0 ≤ ρ) (hqs : 0 ≤ qs) (hb : 0 ≤ b)
    (J : Disorder n)
    (hJ : J ∈ staticGoodEvent n β α (Icc l r) ρ η E g d₀ τ cr cf qs b b' e) :
    replicaGibbsMass β J (forbiddenSet n (Icc l r) ρ (E * ρ) η qs b b') ≤
      (n + 1 : ℝ) ^ 3 *
        (Real.exp ((n : ℝ) * (-g * ρ ^ 3 / 2 + 3 * e)) +
         Real.exp ((n : ℝ) * (-cr * ρ ^ 2 / 2 + 3 * e)) +
         Real.exp ((n : ℝ) * (-cf * η ^ 2 / 2 + 3 * e))) +
      (n + 1 : ℝ) * Real.exp ((n : ℝ) * (-τ ^ 2 / 4 + 2 * e)) := by
  obtain ⟨⟨⟨⟨hden, hloc⟩, hrem⟩, hfix⟩, hpair⟩ := hJ
  have h1 := staticNumeratorEvent_mass_le β tripleReplicaCode
    (staticLocalSet n (Icc l r) ρ E d₀) _ (finiteParisiInf β - e) J hloc hden
  have h2 := staticNumeratorEvent_mass_le β tripleReplicaCode
    (staticRemoteSet n β α (Icc l r) ρ E d₀ τ) _ (finiteParisiInf β - e) J hrem hden
  have h3 := staticNumeratorEvent_mass_le β tripleReplicaCode
    (staticFixedSet n β α η qs b b' τ) _ (finiteParisiInf β - e) J hfix hden
  have h4 := staticNumeratorEvent_mass_le β pairReplicaCode
    (pairMismatchSet n β α τ) _ (finiteParisiInf β - e) J hpair hden
  norm_num only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at h1 h2 h3 h4
  have he1 : (3 * finiteParisiInf β - g * ρ ^ 3 / 2 - 3 * (finiteParisiInf β - e)) =
      -g * ρ ^ 3 / 2 + 3 * e := by ring_nf
  have he2 : (3 * finiteParisiInf β - cr * ρ ^ 2 / 2 - 3 * (finiteParisiInf β - e)) =
      -cr * ρ ^ 2 / 2 + 3 * e := by ring_nf
  have he3 : (3 * finiteParisiInf β - cf * η ^ 2 / 2 - 3 * (finiteParisiInf β - e)) =
      -cf * η ^ 2 / 2 + 3 * e := by ring_nf
  have he4 : (2 * finiteParisiInf β - τ ^ 2 / 4 - 2 * (finiteParisiInf β - e)) =
      -τ ^ 2 / 4 + 2 * e := by ring_nf
  rw [he1] at h1
  rw [he2] at h2
  rw [he3] at h3
  rw [he4] at h4
  have hsplit := forbiddenSet_mass_le_split β α (r := r) (E := E) (d₀ := d₀)
    (τ := τ) (η := η) (b' := b') hl hρ hqs hb J
  nlinarith only [h1, h2, h3, h4, hsplit]

private theorem measureReal_compl_inter_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω) :
    μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

theorem staticGoodEvent_failure_le {n : ℕ} (hn : 0 < n)
    {β l r ρ η S E g d₀ τ cr cf qs b b' e a : ℝ}
    (hβ : β ≠ 0) (α : ℝ → ℝ) (hSρ : 0 < S * ρ)
    (hcr : 0 ≤ cr) (hcf : 0 ≤ cf) (ha : 0 < a)
    (hbias : finiteParisiInf β - quenchedPressure β n ≤ e - a)
    (hlocal : ∀ s ∈ staticLocalSet n (Icc l r) ρ E d₀,
      fractionalPressure n 3 β (S * ρ) (replicaGram s) ≤
        3 * finiteParisiInf β - g * ρ ^ 3)
    (hremote : ∀ s ∈ staticRemoteSet n β α (Icc l r) ρ E d₀ τ,
      matrixConstrainedPressure n 3 β (replicaGram s) ≤
        3 * finiteParisiInf β - cr * ρ ^ 2)
    (hfixed : ∀ s ∈ staticFixedSet n β α η qs b b' τ,
      matrixConstrainedPressure n 3 β (replicaGram s) ≤
        3 * finiteParisiInf β - cf * η ^ 2)
    (hpair : ∀ s ∈ pairMismatchSet n β α τ,
      matrixConstrainedPressure n 2 β (replicaGram s) ≤
        2 * finiteParisiInf β - τ ^ 2 / 2) :
    (disorderLaw n).real
      (staticGoodEvent n β α (Icc l r) ρ η E g d₀ τ cr cf qs b b' e)ᶜ ≤
      variance (fun J : Disorder n => logPartition β J) (disorderLaw n) / ((n : ℝ) * a)^2 +
      (n + 1 : ℝ)^3 *
        (Real.exp (-(n : ℝ) * (S * ρ) * (g * ρ^3 / 2)) +
         Real.exp (-(4 * (cr * ρ^2 / 2)^2 / (Real.pi^2 * β^2 * 3^2)) * n) +
         Real.exp (-(4 * (cf * η^2 / 2)^2 / (Real.pi^2 * β^2 * 3^2)) * n)) +
      (n + 1 : ℝ) * Real.exp (-(4 * (τ^2 / 2 / 2)^2 /
        (Real.pi^2 * β^2 * 2^2)) * n) := by
  have hden := staticDenominatorEvent_failure_le hn β e a ha hbias
  have hloc := staticNumeratorEvent_fractional_failure_le hn (by norm_num : 0 < 3)
    β (S * ρ) (3 * finiteParisiInf β - g * ρ ^ 3) (g * ρ ^ 3 / 2) hSρ
    tripleReplicaCode (fun x y h => tripleReplicaCode_gram hn h)
    (staticLocalSet n (Icc l r) ρ E d₀) hlocal
  have hrem := staticNumeratorEvent_gaussian_failure_le hn (by norm_num : 0 < 3) hβ
    tripleReplicaCode (fun x y h => tripleReplicaCode_gram hn h)
    (staticRemoteSet n β α (Icc l r) ρ E d₀ τ) (cr * ρ^2) (by positivity) hremote
  have hfix := staticNumeratorEvent_gaussian_failure_le hn (by norm_num : 0 < 3) hβ
    tripleReplicaCode (fun x y h => tripleReplicaCode_gram hn h)
    (staticFixedSet n β α η qs b b' τ) (cf * η^2) (by positivity) hfixed
  have hpair' := staticNumeratorEvent_gaussian_failure_le hn (by norm_num : 0 < 2) hβ
    pairReplicaCode (fun x y h => pairReplicaCode_gram hn h)
    (pairMismatchSet n β α τ) (τ^2/2) (by positivity) hpair
  rw [show 3 * finiteParisiInf β - g * ρ^3 + g * ρ^3/2 =
    3 * finiteParisiInf β - g * ρ^3/2 by ring_nf] at hloc
  norm_num only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at hloc hrem hfix hpair'
  rw [show τ^2 / 2 / 2 = τ^2 / 4 by ring_nf] at hpair'
  have h12 := measureReal_compl_inter_le (disorderLaw n)
    (staticDenominatorEvent n β e)
    (staticNumeratorEvent β tripleReplicaCode (staticLocalSet n (Icc l r) ρ E d₀)
      (3 * finiteParisiInf β - g * ρ^3/2))
  have h123 := measureReal_compl_inter_le (disorderLaw n)
    (staticDenominatorEvent n β e ∩
      staticNumeratorEvent β tripleReplicaCode (staticLocalSet n (Icc l r) ρ E d₀)
        (3 * finiteParisiInf β - g * ρ^3/2))
    (staticNumeratorEvent β tripleReplicaCode (staticRemoteSet n β α (Icc l r) ρ E d₀ τ)
      (3 * finiteParisiInf β - cr * ρ^2/2))
  have h1234 := measureReal_compl_inter_le (disorderLaw n)
    (staticDenominatorEvent n β e ∩
      staticNumeratorEvent β tripleReplicaCode (staticLocalSet n (Icc l r) ρ E d₀)
        (3 * finiteParisiInf β - g * ρ^3/2) ∩
      staticNumeratorEvent β tripleReplicaCode (staticRemoteSet n β α (Icc l r) ρ E d₀ τ)
        (3 * finiteParisiInf β - cr * ρ^2/2))
    (staticNumeratorEvent β tripleReplicaCode (staticFixedSet n β α η qs b b' τ)
      (3 * finiteParisiInf β - cf * η^2/2))
  have h12345 := measureReal_compl_inter_le (disorderLaw n)
    (staticDenominatorEvent n β e ∩
      staticNumeratorEvent β tripleReplicaCode (staticLocalSet n (Icc l r) ρ E d₀)
        (3 * finiteParisiInf β - g * ρ^3/2) ∩
      staticNumeratorEvent β tripleReplicaCode (staticRemoteSet n β α (Icc l r) ρ E d₀ τ)
        (3 * finiteParisiInf β - cr * ρ^2/2) ∩
      staticNumeratorEvent β tripleReplicaCode (staticFixedSet n β α η qs b b' τ)
        (3 * finiteParisiInf β - cf * η^2/2))
    (staticNumeratorEvent β pairReplicaCode (pairMismatchSet n β α τ)
      (2 * finiteParisiInf β - τ^2/4))
  change (disorderLaw n).real (staticGoodEvent n β α (Icc l r)
    ρ η E g d₀ τ cr cf qs b b' e)ᶜ ≤ _ at h12345
  norm_num only [show (3 : ℝ)^2 = 9 by norm_num, show (2 : ℝ)^2 = 4 by norm_num]
  rw [show τ^2 / 2 / 2 = τ^2 / 4 by ring_nf]
  nlinarith only [hden, hloc, hrem, hfix, hpair', h12, h123, h1234, h12345]

structure StaticGapData (β : ℝ) (α : ℝ → ℝ) (l r qs : ℝ)
    (ρ η : ℕ → ℝ) (S E g : ℝ) where
  d₀ : ℝ
  τ : ℝ
  cr : ℝ
  cf : ℝ
  b : ℝ
  b' : ℝ
  d₀_pos : 0 < d₀
  τ_pos : 0 < τ
  cr_pos : 0 < cr
  cf_pos : 0 < cf
  b_pos : 0 < b
  b'_pos : 0 < b'
  local_gap : ∀ᶠ n : ℕ in atTop,
    ∀ s ∈ staticLocalSet n (Icc l r) (ρ n) E d₀,
      fractionalPressure n 3 β (S * ρ n) (replicaGram s) ≤
        3 * finiteParisiInf β - g * ρ n ^ 3
  remote_gap : ∀ᶠ n : ℕ in atTop,
    ∀ s ∈ staticRemoteSet n β α (Icc l r) (ρ n) E d₀ τ,
      matrixConstrainedPressure n 3 β (replicaGram s) ≤
        3 * finiteParisiInf β - cr * ρ n ^ 2
  fixed_gap : ∀ᶠ n : ℕ in atTop,
    ∀ s ∈ staticFixedSet n β α (η n) qs b b' τ,
      matrixConstrainedPressure n 3 β (replicaGram s) ≤
        3 * finiteParisiInf β - cf * η n ^ 2
  pair_gap : ∀ᶠ n : ℕ in atTop,
    ∀ s ∈ pairMismatchSet n β α τ,
      matrixConstrainedPressure n 2 β (replicaGram s) ≤
        2 * finiteParisiInf β - τ ^ 2 / 2

theorem exists_staticGapData_with_cutoffs {β l r u H m qs S E g : ℝ} {ρ η : ℕ → ℝ}
    (hβ : 0 < β) (hl : 0 < l) (hlr : l ≤ r) (hru : r < u) (hu : u ≤ 1)
    (hH : 0 < H) (hm : 0 < m) (_hqs : 0 < qs) (_hqs1 : qs ≤ 1) (hE : 0 < E)
    (hρ : Tendsto ρ atTop (𝓝 0)) (hρ0 : ∀ᶠ n in atTop, 0 ≤ ρ n)
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hunique : ∀ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ)
    (hmα : m ≤ cdf (μ : Measure ℝ) l) (K : ℝ≥0)
    (hLip : LipschitzOnWith K (cdf (μ : Measure ℝ)) (Icc (l-H) (r+H)))
    (hΓ : ∀ t ∈ Icc l u, scalarCDFOverlap β (cdf (μ : Measure ℝ)) t = t)
    (cuts : StaticCutoffs β (cdf (μ : Measure ℝ)) qs)
    (hlocal : LocalFractionalGap β (Icc l r) ρ S E g) :
    ∃ G : StaticGapData β (cdf (μ : Measure ℝ)) l r qs ρ η S E g,
      G.b = cuts.b ∧ G.b' = cuts.b' := by
  obtain ⟨d₀, hd₀, hloc⟩ := staticLocalSet_fractional_gap hlocal
  obtain ⟨ν, δ₀, cr, hν, hδ₀, hcr, hrem⟩ := remote_pressure_gap_of_unique_minimizer
    hβ.ne' hl hlr hru hu hH hd₀ hm μ hμ hmin hunique hmα K hLip hΓ
  let τ := min ν cuts.τ
  have hτ : 0 < τ := lt_min hν cuts.τ_pos
  have hτν : τ ≤ ν := min_le_left _ _
  have hτcuts : τ ≤ cuts.τ := min_le_right _ _
  refine ⟨⟨d₀, τ, cr * E^2, cuts.cf, cuts.b, cuts.b', hd₀, hτ,
    mul_pos hcr (sq_pos_of_pos hE), cuts.cf_pos, cuts.b_pos, cuts.b'_pos,
    ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · filter_upwards [hloc, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    exact hn hn0
  · have hsmall : ∀ᶠ n in atTop, 2 * E * ρ n ≤ δ₀ :=
      ((tendsto_const_nhds.mul hρ).eventually (gt_mem_nhds
        (by simpa using hδ₀ : (2 * E) * 0 < δ₀))).mono (fun _ h => h.le)
    filter_upwards [hsmall, hρ0, eventually_gt_atTop (0 : ℕ)] with n hsmall hρ0 hn
    apply staticRemoteSet_pressure_gap hn (cdf (μ : Measure ℝ)) hsmall
      (mul_nonneg hE.le hρ0) (hc := hcr.le)
    intro x hx q δ hd hq hdev hδ hD
    exact hrem n hn x hx q δ hd hq (hdev.trans hτν) hδ hD
  · filter_upwards [hη0, eventually_gt_atTop (0 : ℕ)] with n hη hn s hs
    obtain ⟨hs, hdev⟩ := Finset.mem_filter.mp hs
    exact cuts.gap n hn (η n) hη s (Finset.mem_filter.mpr ⟨hs, hdev.trans hτcuts⟩)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn s hs
    exact pairMismatch_pressure_gap hn β (cdf (μ : Measure ℝ))
      (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
      (supported_probability_cdf_one μ hμ) hmin hτ.le hs

theorem exists_staticGapData {β l r u H m qs S E g : ℝ} {ρ η : ℕ → ℝ}
    (hβ : 0 < β) (hl : 0 < l) (hlr : l ≤ r) (hru : r < u) (hu : u ≤ 1)
    (hH : 0 < H) (hm : 0 < m) (hqs : 0 < qs) (hqs1 : qs ≤ 1) (hE : 0 < E)
    (hρ : Tendsto ρ atTop (𝓝 0)) (hρ0 : ∀ᶠ n in atTop, 0 ≤ ρ n)
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hunique : ∀ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ)
    (hmα : m ≤ cdf (μ : Measure ℝ) l) (K : ℝ≥0)
    (hLip : LipschitzOnWith K (cdf (μ : Measure ℝ)) (Icc (l-H) (r+H)))
    (hΓ : ∀ t ∈ Icc l u, scalarCDFOverlap β (cdf (μ : Measure ℝ)) t = t)
    (hlocal : LocalFractionalGap β (Icc l r) ρ S E g) :
    Nonempty (StaticGapData β (cdf (μ : Measure ℝ)) l r qs ρ η S E g) := by
  obtain ⟨cuts⟩ := exists_static_cutoffs hβ hqs hqs1 μ hunique
  obtain ⟨G, _, _⟩ := exists_staticGapData_with_cutoffs hβ hl hlr hru hu hH hm hqs hqs1 hE
    hρ hρ0 hη0 μ hμ hmin hunique hmα K hLip hΓ cuts hlocal
  exact ⟨G⟩

private theorem rate_n_rho_pow (R γ : ℝ) (k n : ℕ) (hn : 0 < n) :
    (n : ℝ) * rateRho R γ n ^ k =
      R ^ k * (n : ℝ) ^ (1 - (k : ℝ) * γ / 3) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rateRho, mul_pow, ← Real.rpow_natCast ((n : ℝ)^(-γ/3)) k,
    ← Real.rpow_mul hn'.le,
    show -γ / 3 * (k : ℝ) = -((k : ℝ) * γ / 3) by ring_nf,
    Real.rpow_sub hn', Real.rpow_one, Real.rpow_neg hn'.le]
  ring_nf

private theorem rate_n_eta_pow (θ : ℝ) (k n : ℕ) (hn : 0 < n) :
    (n : ℝ) * rateEta θ n ^ k = (n : ℝ) ^ (1 - (k : ℝ) * θ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rateEta, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le,
    show -θ * (k : ℝ) = -((k : ℝ) * θ) by ring_nf,
    Real.rpow_sub hn', Real.rpow_one, Real.rpow_neg hn'.le]
  ring_nf

private theorem polynomial_exp_power_tendsto_zero (k : ℕ) {p c : ℝ}
    (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^k * Real.exp (-c * (n : ℝ)^p))
      atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop hp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((k : ℝ) / p) c hc).comp hpow).const_mul (2^k : ℝ)
  simp only [mul_zero] at ht
  have htop : Tendsto (fun n : ℕ => (2 : ℝ)^k *
      ((n : ℝ)^k * Real.exp (-c * (n : ℝ)^p))) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    change (2 : ℝ)^k * (((n : ℝ)^p)^((k : ℝ)/p) *
      Real.exp (-c * (n : ℝ)^p)) = _
    rw [← Real.rpow_mul (Nat.cast_nonneg n),
      show p * ((k : ℝ)/p) = k by field_simp, Real.rpow_natCast]
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ htop
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ (2 * (n : ℝ))^k * Real.exp (-c * (n : ℝ)^p) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) k)
        (Real.exp_pos _).le
    _ = _ := by rw [mul_pow]; ring_nf

private theorem rate_rho_failure_tendsto_zero {γ θ R c : ℝ}
    (hexp : RateExponents γ θ) (hR : 0 < R) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^3 *
      Real.exp (-c * (n : ℝ) * rateRho R γ n^4)) atTop (𝓝 0) := by
  have ht := polynomial_exp_power_tendsto_zero 3
    (p := 1 - 4 * γ / 3) (c := c * R^4)
    (by linarith [hexp.gamma_lt]) (mul_pos hc (pow_pos hR 4))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  congr 1
  rw [show -c * (n : ℝ) * rateRho R γ n^4 =
    -c * ((n : ℝ) * rateRho R γ n^4) by ring_nf, rate_n_rho_pow R γ 4 n hn]
  norm_num only [Nat.cast_ofNat]
  ring_nf

private theorem rate_eta_failure_tendsto_zero {γ θ c : ℝ}
    (hexp : RateExponents γ θ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^3 *
      Real.exp (-c * (n : ℝ) * rateEta θ n^4)) atTop (𝓝 0) := by
  have ht := polynomial_exp_power_tendsto_zero 3
    (p := 1 - 4 * θ) (c := c) (by linarith [hexp.theta_quarter]) hc
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  congr 1
  rw [show -c * (n : ℝ) * rateEta θ n^4 =
    -c * ((n : ℝ) * rateEta θ n^4) by ring_nf, rate_n_eta_pow θ 4 n hn]
  norm_num only [Nat.cast_ofNat]

private theorem rateRho_cube_eq (R γ : ℝ) (n : ℕ) :
    rateRho R γ n^3 = R^3 * (n : ℝ)^(-γ) := by
  rw [rateRho, mul_pow, ← Real.rpow_natCast ((n : ℝ)^(-γ/3)) 3,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 2
  norm_num

private theorem rate_variance_error_tendsto_zero {γ v : ℝ}
    (hv : v < 2 - 2 * γ) (Cv g R : ℝ) :
    Tendsto (fun n : ℕ => Cv * (n : ℝ)^v /
      ((n : ℝ) * (g * rateRho R γ n^3 / 24))^2) atTop (𝓝 0) := by
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 - 2*γ - v)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      (Cv / (g * R^3 / 24)^2)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  change Cv / (g * R^3 / 24)^2 * (n : ℝ)^(-(2 - 2*γ - v)) = _
  have hden : (n : ℝ) * (g * rateRho R γ n^3 / 24) =
      (g * R^3 / 24) * (n : ℝ)^(1 - γ) := by
    rw [show (n : ℝ) * (g * rateRho R γ n^3 / 24) =
      (g/24) * ((n : ℝ) * rateRho R γ n^3) by ring_nf, rate_n_rho_pow R γ 3 n hn]
    norm_num only [Nat.cast_ofNat]
    rw [show 1 - 3 * γ / 3 = 1 - γ by ring_nf]
    ring_nf
  have hpow : ((n : ℝ)^(1-γ))^2 = (n : ℝ)^(2-2*γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    congr 1
    norm_num
    ring_nf
  rw [hden, mul_pow, hpow,
    show -(2 - 2*γ - v) = v - (2 - 2*γ) by ring_nf, Real.rpow_sub hn']
  ring_nf

theorem staticGoodEvent_probability_tendsto_one
    {β γ θ Cb v Cv R S E g l r qs : ℝ} (α : ℝ → ℝ)
    (hβ : β ≠ 0) (hexp : RateExponents γ θ)
    (hmean : MeanRate β γ Cb) (hvar : VarianceCap β v Cv)
    (hv : v < 2 - 2*γ) (hR : 0 < R) (hS : 0 < S) (hg : 0 < g)
    (hmargin : 24 * Cb < g * R^3)
    (G : StaticGapData β α l r qs (rateRho R γ) (rateEta θ) S E g) :
    Tendsto (fun n => (disorderLaw n).real
      (staticGoodEvent n β α (Icc l r) (rateRho R γ n) (rateEta θ n)
        E g G.d₀ G.τ G.cr G.cf qs G.b G.b' (g * rateRho R γ n^3 / 12)))
      atTop (𝓝 1) := by
  let ρ := rateRho R γ
  let η := rateEta θ
  let Q (n : ℕ) := staticGoodEvent n β α (Icc l r) (ρ n) (η n)
    E g G.d₀ G.τ G.cr G.cf qs G.b G.b' (g * ρ n^3 / 12)
  let kr := 4 * (G.cr/2)^2 / (Real.pi^2 * β^2 * 3^2)
  let kf := 4 * (G.cf/2)^2 / (Real.pi^2 * β^2 * 3^2)
  let kp := 4 * (G.τ^2/2/2)^2 / (Real.pi^2 * β^2 * 2^2)
  have hcr := G.cr_pos
  have hcf := G.cf_pos
  have hτ := G.τ_pos
  have hβ2 : 0 < β^2 := sq_pos_of_ne_zero hβ
  have hkr : 0 < kr := by dsimp only [kr]; positivity
  have hkf : 0 < kf := by dsimp only [kf]; positivity
  have hkp : 0 < kp := by dsimp only [kp]; positivity
  have ht1 := rate_rho_failure_tendsto_zero hexp hR (div_pos (mul_pos hS hg) (by norm_num : (0:ℝ)<2))
  have ht2 := rate_rho_failure_tendsto_zero hexp hR hkr
  have ht3 := rate_eta_failure_tendsto_zero hexp hkf
  have ht4 : Tendsto (fun n : ℕ => (n+1 : ℝ) * Real.exp (-kp * n)) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one] using
      polynomial_exp_power_tendsto_zero 1 (p := 1) zero_lt_one hkp
  let V (n : ℕ) := Cv * (n : ℝ)^v / ((n : ℝ) * (g * ρ n^3 / 24))^2
  let B (n : ℕ) := V n + (n+1 : ℝ)^3 *
    (Real.exp (-(S*g/2) * n * ρ n^4) + Real.exp (-kr * n * ρ n^4) +
      Real.exp (-kf * n * η n^4)) + (n+1 : ℝ) * Real.exp (-kp * n)
  have hB : Tendsto B atTop (𝓝 0) := by
    have ht := ((rate_variance_error_tendsto_zero hv Cv g R).add ((ht1.add ht2).add ht3)).add ht4
    simp only [add_zero] at ht
    convert ht using 1
    funext n
    dsimp only [B, V, ρ, η]
    ring_nf
  have hfail : ∀ᶠ n in atTop, (disorderLaw n).real (Q n)ᶜ ≤ B n := by
    filter_upwards [hmean, hvar, G.local_gap, G.remote_gap, G.fixed_gap, G.pair_gap,
      eventually_gt_atTop (0 : ℕ)] with n hmean hvar hloc hrem hfix hpair hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hρ : 0 < ρ n := mul_pos hR (Real.rpow_pos_of_pos hn' _)
    have hbias : finiteParisiInf β - quenchedPressure β n ≤
        g * ρ n^3 / 12 - g * ρ n^3 / 24 := by
      apply hmean.trans
      rw [show g * ρ n^3/12 - g * ρ n^3/24 = g * ρ n^3/24 by ring_nf,
        rateRho_cube_eq]
      have h := mul_le_mul_of_nonneg_right hmargin.le (Real.rpow_nonneg hn'.le (-γ))
      nlinarith only [h]
    have h := staticGoodEvent_failure_le hn hβ α (mul_pos hS hρ) G.cr_pos.le G.cf_pos.le
      (by positivity : 0 < g * ρ n^3 / 24) hbias hloc hrem hfix hpair
    have hvn := div_le_div_of_nonneg_right hvar (sq_nonneg ((n : ℝ) * (g * ρ n^3 / 24)))
    have hr (x : ℝ) : -(4 * (x * ρ n^2/2)^2 / (Real.pi^2 * β^2 * 3^2)) * n =
        -(4 * (x/2)^2 / (Real.pi^2 * β^2 * 3^2)) * n * ρ n^4 := by ring_nf
    have hf : -(4 * (G.cf * η n^2/2)^2 / (Real.pi^2 * β^2 * 3^2)) * n =
        -kf * n * η n^4 := by dsimp only [kf]; ring_nf
    have hl : -(n : ℝ) * (S * ρ n) * (g * ρ n^3/2) =
        -(S*g/2) * n * ρ n^4 := by ring_nf
    rw [hr G.cr, hf, hl] at h
    change (disorderLaw n).real (Q n)ᶜ ≤ _ at h
    change (disorderLaw n).real (Q n)ᶜ ≤ B n
    dsimp only [B, V, kr, kp]
    linarith only [h, hvn]
  have ht : Tendsto (fun n => (disorderLaw n).real (Q n)ᶜ) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hfail hB
  have ht' : Tendsto (fun n => 1 - (disorderLaw n).real (Q n)ᶜ) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  apply ht'.congr'
  exact Eventually.of_forall (fun n => by
    change 1 - (disorderLaw n).real (Q n)ᶜ = (disorderLaw n).real (Q n)
    have hm : MeasurableSet (Q n) := measurableSet_staticGoodEvent
      n β α (Icc l r) (ρ n) (η n) E g G.d₀ G.τ G.cr G.cf qs G.b G.b' _
    rw [probReal_compl_eq_one_sub hm]
    ring_nf)

theorem quenchedStaticEvent_of_gapData
    {β γ θ Cb v Cv R S E g l r qs : ℝ} (α : ℝ → ℝ)
    (hβ : β ≠ 0) (hexp : RateExponents γ θ)
    (hmean : MeanRate β γ Cb) (hvar : VarianceCap β v Cv)
    (hv : v < 2 - 2*γ) (hR : 0 < R) (hS : 0 < S) (hg : 0 < g)
    (hl : 0 ≤ l) (hqs : 0 ≤ qs) (hmargin : 24 * Cb < g * R^3)
    (G : StaticGapData β α l r qs (rateRho R γ) (rateEta θ) S E g) :
    ∃ c : ℝ, 0 < c ∧ ∃ Q : (n : ℕ) → Set (Disorder n),
      QuenchedStaticEvent β
        (fun n => forbiddenSet n (Icc l r) (rateRho R γ n) (E * rateRho R γ n)
          (rateEta θ n) qs G.b G.b') Q
        (fun n => 2 * (n+1 : ℝ)^3 *
          (Real.exp (-c * n * rateRho R γ n^3) +
           Real.exp (-c * n * rateEta θ n^2) + Real.exp (-c * n))) := by
  let ρ := rateRho R γ
  let η := rateEta θ
  let Q (n : ℕ) := staticGoodEvent n β α (Icc l r) (ρ n) (η n)
    E g G.d₀ G.τ G.cr G.cf qs G.b G.b' (g * ρ n^3 / 12)
  let c := min (g/4) (min (G.cr/4) (min (G.cf/4) (G.τ^2/8)))
  have hcr := G.cr_pos
  have hcf := G.cf_pos
  have hτ := G.τ_pos
  have hc : 0 < c := lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hc1 : c ≤ g/4 := min_le_left _ _
  have hc2 : c ≤ G.cr/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c ≤ G.cf/4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hc4 : c ≤ G.τ^2/8 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hc, Q, (fun n => measurableSet_staticGoodEvent n β α (Icc l r)
    (ρ n) (η n) E g G.d₀ G.τ G.cr G.cf qs G.b G.b' _), ?_, ?_⟩
  · exact staticGoodEvent_probability_tendsto_one α hβ hexp hmean hvar hv hR hS hg hmargin G
  · have hρlim := (rate_scales_tendsto_zero hexp R).1
    have hρ1 : ∀ᶠ n in atTop, ρ n ≤ 1 :=
      (hρlim.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ h => h.le)
    have hgr : ∀ᶠ n in atTop, g * ρ n ≤ G.cr :=
      ((hρlim.const_mul g).eventually (gt_mem_nhds
        (by simpa only [mul_zero] using G.cr_pos))).mono (fun _ h => h.le)
    have hfix : ∀ᶠ n in atTop, g * ρ n^3 ≤ G.cf * η n^2 := by
      have h := ((rate_bias_littleO_eta_square hexp).const_mul_left (g * R^3)).bound G.cf_pos
      filter_upwards [h] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-γ))), Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)] at hn
      simpa only [ρ, rateRho_cube_eq, mul_assoc] using hn
    have hpair : ∀ᶠ n in atTop, g * ρ n^3 / 6 ≤ G.τ^2/8 := by
      have ht := (hρlim.pow 3).const_mul (g/6)
      have h := ht.eventually (gt_mem_nhds (by simpa using
        (div_pos (sq_pos_of_pos G.τ_pos) (by norm_num : (0:ℝ)<8)) : (g/6)*0^3 < G.τ^2/8))
      filter_upwards [h] with n hn
      nlinarith only [hn.le]
    filter_upwards [hρ1, hgr, hfix, hpair, eventually_gt_atTop (0 : ℕ)] with n hρ1 hgr hfix hpair hn J hJ
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hρ : 0 < ρ n := mul_pos hR (Real.rpow_pos_of_pos hn' _)
    have hmass := staticGoodEvent_mass_le β α hl hρ.le hqs G.b_pos.le J hJ
    have hρ32 : ρ n^3 ≤ ρ n^2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hρ1 (sq_nonneg (ρ n))]
    have hbrem := mul_le_mul_of_nonneg_right hgr (sq_nonneg (ρ n))
    have hm1 : -g * ρ n^3/2 + 3*(g*ρ n^3/12) ≤ -c * ρ n^3 := by
      nlinarith only [mul_le_mul_of_nonneg_right hc1 (pow_nonneg hρ.le 3)]
    have hm2 : -G.cr * ρ n^2/2 + 3*(g*ρ n^3/12) ≤ -c * ρ n^3 := by
      nlinarith only [hbrem, mul_le_mul_of_nonneg_right hc2 (sq_nonneg (ρ n)),
        mul_le_mul_of_nonneg_left hρ32 hc.le]
    have hm3 : -G.cf * η n^2/2 + 3*(g*ρ n^3/12) ≤ -c * η n^2 := by
      nlinarith only [hfix, mul_le_mul_of_nonneg_right hc3 (sq_nonneg (η n))]
    have hm4 : -G.τ^2/4 + 2*(g*ρ n^3/12) ≤ -c := by
      nlinarith only [hpair, hc4]
    have he1 : Real.exp ((n : ℝ) * (-g * ρ n^3/2 + 3*(g*ρ n^3/12))) ≤
        Real.exp (-c * n * ρ n^3) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hm1 hn'.le])
    have he2 : Real.exp ((n : ℝ) * (-G.cr * ρ n^2/2 + 3*(g*ρ n^3/12))) ≤
        Real.exp (-c * n * ρ n^3) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hm2 hn'.le])
    have he3 : Real.exp ((n : ℝ) * (-G.cf * η n^2/2 + 3*(g*ρ n^3/12))) ≤
        Real.exp (-c * n * η n^2) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hm3 hn'.le])
    have he4 : Real.exp ((n : ℝ) * (-G.τ^2/4 + 2*(g*ρ n^3/12))) ≤ Real.exp (-c * n) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hm4 hn'.le])
    have hpoly : (n+1 : ℝ) ≤ (n+1 : ℝ)^3 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [sq_nonneg (n : ℝ), pow_nonneg hn0 3]
    calc
      _ ≤ (n+1 : ℝ)^3 * (2 * Real.exp (-c*n*ρ n^3) + Real.exp (-c*n*η n^2)) +
          (n+1 : ℝ) * Real.exp (-c*n) := hmass.trans (by gcongr; linarith only [he1, he2])
      _ ≤ 2 * (n+1 : ℝ)^3 *
          (Real.exp (-c*n*ρ n^3) + Real.exp (-c*n*η n^2) + Real.exp (-c*n)) := by
        have hp := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-c*n)).le
        nlinarith only [hp, mul_nonneg (by positivity : (0:ℝ) ≤ (n+1 : ℝ)^3)
          (Real.exp_pos (-c*n*η n^2)).le,
          mul_nonneg (by positivity : (0:ℝ) ≤ (n+1 : ℝ)^3) (Real.exp_pos (-c*n)).le]

theorem quenchedStaticEvent_of_gaps
    {β γ θ Cb v Cv R S E g l r u H m qs : ℝ}
    (hβ : 0 < β) (hexp : RateExponents γ θ)
    (hmean : MeanRate β γ Cb) (hvar : VarianceCap β v Cv)
    (hv : v < 2 - 2 * γ) (hR : 0 < R)
    (hmargin : 24 * Cb < g * R ^ 3)
    (hS : 0 < S) (hE : 0 < E) (hg : 0 < g)
    (hl : 0 < l) (hlr : l ≤ r) (hru : r < u) (hu : u ≤ 1)
    (hH : 0 < H) (hm : 0 < m) (hqs : 0 < qs) (hqs1 : qs ≤ 1)
    (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hunique : ∀ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ)
    (hmα : m ≤ cdf (μ : Measure ℝ) l) (K : ℝ≥0)
    (hLip : LipschitzOnWith K (cdf (μ : Measure ℝ)) (Icc (l-H) (r+H)))
    (hΓ : ∀ t ∈ Icc l u, scalarCDFOverlap β (cdf (μ : Measure ℝ)) t = t)
    (cuts : StaticCutoffs β (cdf (μ : Measure ℝ)) qs)
    (hlocal : LocalFractionalGap β (Icc l r) (rateRho R γ) S E g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ Q : (n : ℕ) → Set (Disorder n),
        QuenchedStaticEvent β
          (fun n => forbiddenSet n (Icc l r) (rateRho R γ n)
            (E * rateRho R γ n) (rateEta θ n) qs cuts.b cuts.b') Q
          (fun n => C * (n+1 : ℝ)^3 *
            (Real.exp (-c * n * rateRho R γ n^3) +
             Real.exp (-c * n * rateEta θ n^2) + Real.exp (-c * n))) := by
  have hρ0 : ∀ᶠ n : ℕ in atTop, 0 ≤ rateRho R γ n :=
    Eventually.of_forall (fun n => mul_nonneg hR.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hη0 : ∀ᶠ n : ℕ in atTop, 0 ≤ rateEta θ n :=
    Eventually.of_forall (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  obtain ⟨G, hb, hb'⟩ := exists_staticGapData_with_cutoffs hβ hl hlr hru hu hH hm hqs hqs1 hE
    (rate_scales_tendsto_zero hexp R).1 hρ0 hη0 μ hμ hmin hunique hmα K hLip hΓ cuts hlocal
  obtain ⟨c, hc, Q, hQ⟩ := quenchedStaticEvent_of_gapData (cdf (μ : Measure ℝ))
    hβ.ne' hexp hmean hvar hv hR hS hg hl.le hqs.le hmargin G
  refine ⟨2, c, by norm_num, hc, Q, ?_⟩
  simpa only [hb, hb'] using hQ

end SKBarriers2
