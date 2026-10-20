module

public import SKBarriers2.Main.CornerFinal2
public import SKBarriers2.Corner.KStabilityClose
public import SKBarriers2.Corner.FrozenCoef7
public import SKBarriers2.Corner.FrozenRowsMoments3
public import SKBarriers2.Corner.MassPathRegularity
public import SKBarriers2.Corner.MassSensitivityC2Proof

@[expose] public section

noncomputable section
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def WickTailSecondControl (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∃ f₁ f₂ : ℝ → ℝ,
      (∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        HasDerivAt (wickTailCoefficientError β α (α (r - h)) (r - h) h z) (f₁ k) k ∧
        HasDerivAt f₁ (f₂ k) k) ∧
      (∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4), |f₂ k| ≤ C * Real.sqrt h * h ^ 3)

def FrozenPartitionKDerivativeControl (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ B h₀ κ : ℝ, 1 ≤ B ∧ 0 < h₀ ∧ 0 < κ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 11 → ∃ W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ,
        let W := frozenPartitionWeight β α (α (r - h)) (r - h) h z ε j
        (∀ k ∈ Icc (-κ) κ, ∀ n : Fin 4,
          IntegralDerivativeControl (gaussianReal 0 1) (W n) (W₁ n) k ∧
          IntegralDerivativeControl (gaussianReal 0 1) (W₁ n) (W₂ n) k) ∧
        (∀ k ∈ Icc (-κ) κ, ∀ n : Fin 4,
          |partitionIntegral W₁ n k / partitionIntegral W 0 k| ≤
            B * (Real.sqrt h * h) ^ n.val ∧
          |partitionIntegral W₂ n k / partitionIntegral W 0 k| ≤
            B * (Real.sqrt h * h) ^ n.val)

def OpenLeaves (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  WickTailSecondControl β α I ∧
  FrozenPartitionKDerivativeControl β α I ∧
  FirstOrderPathEnergyC2 β α I ∧
  EntropyPathC2Small β α I

theorem scalarData_frozenJetHypotheses_window {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    FrozenJetHypotheses β (cdf (D.μ : Measure ℝ)) (Icc (l / 2) ((u + D.q) / 2))
      (cdf (D.μ : Measure ℝ) (l / 2)) (scalarTerminalJetBound D 12 + 1) := by
  have htime (t : ℝ) (ht : t ∈ Icc (l / 2) ((u + D.q) / 2)) :
      t ∈ Ioo (0 : ℝ) D.q := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hstrip (t : ℝ) (ht : t ∈ Icc (l / 2) ((u + D.q) / 2)) :
      t ∈ Icc (0 : ℝ) 1 :=
    ⟨(htime t ht).1.le, (htime t ht).2.le.trans D.q_mem.2.le⟩
  refine ⟨scalarData_cdf_pos_of_pos D (by positivity),
    by linarith [scalarTerminalJetBound_nonneg D 12], ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨monotone_cdf _ ht.1, cdf_le_one _ _⟩
  · intro t ht
    exact (scalarData_phi_contDiff D (hstrip t ht)).of_le (by simp)
  · intro j hj hj12 t ht x
    exact (scalarData_jet_le D hj hj12 (hstrip t ht) x).trans (by linarith)
  · intro j _ t ht x
    exact D.time_deriv j t (htime t ht) x

theorem frozen_window_cover {q l u : ℝ} (hl : 0 < l) (hu : u < q) :
    0 < min (l / 2) ((q - u) / 6) ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ min (l / 2) ((q - u) / 6) →
        r - h ∈ Icc (l / 2) ((u + q) / 2) ∧
          (r - h) + 4 * h ∈ Icc (l / 2) ((u + q) / 2) := by
  refine ⟨by positivity, ?_⟩
  intro r hr h hh hh₀
  have hh₁ := hh₀.trans (min_le_left _ _)
  have hh₂ := hh₀.trans (min_le_right _ _)
  constructor <;> constructor <;> linarith [hr.1, hr.2]

theorem EvenSecondControl.restrict_radius {f : ℝ → ℝ} {κ ρ A B : ℝ}
    (H : EvenSecondControl f ρ A B) (hκρ : κ ≤ ρ) : EvenSecondControl f κ A B := by
  obtain ⟨f₁, f₂, hd, hb, he⟩ := H
  have hsub : Icc (-κ) κ ⊆ Icc (-ρ) ρ :=
    fun _ hk => ⟨(neg_le_neg hκρ).trans hk.1, hk.2.trans hκρ⟩
  exact ⟨f₁, f₂, fun k hk => hd k (hsub hk), fun k hk => hb k (hsub hk),
    fun k hk => he k (hsub hk)⟩

theorem EvenSecondControl.of_split_derivatives {f g t : ℝ → ℝ} {κ A B D E : ℝ}
    (hg : EvenSecondControl g κ A B)
    (ht : ∃ t₁ t₂ : ℝ → ℝ,
      (∀ k ∈ Icc (-κ) κ, HasDerivAt t (t₁ k) k ∧ HasDerivAt t₁ (t₂ k) k) ∧
      (∀ k ∈ Icc (-κ) κ, |t₂ k| ≤ D + E * |k|))
    (hsplit : f = fun k => g k + t k)
    (heven : ∀ k ∈ Icc (-κ) κ, f (-k) = f k) :
    EvenSecondControl f κ (A + D) (B + E) := by
  obtain ⟨g₁, g₂, hgd, hgb, _⟩ := hg
  obtain ⟨t₁, t₂, htd, htb⟩ := ht
  refine ⟨fun k => g₁ k + t₁ k, fun k => g₂ k + t₂ k, ?_, ?_, heven⟩
  · intro k hk
    rw [hsplit]
    exact ⟨(hgd k hk).1.add (htd k hk).1, (hgd k hk).2.add (htd k hk).2⟩
  · intro k hk
    exact (abs_add_le _ _).trans (by linarith [hgb k hk, htb k hk])

theorem PartitionIntegralKControl.restrict_mono
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U V : Set ℝ} {B D t : ℝ}
    (H : PartitionIntegralKControl W W₁ W₂ U B t)
    (hVU : V ⊆ U) (hBD : B ≤ D) (ht : 0 ≤ t) :
    PartitionIntegralKControl W W₁ W₂ V D t := by
  refine ⟨fun k hk => H.nonzero k (hVU hk),
    fun k hk n => H.domination k (hVU hk) n, ?_⟩
  intro k hk n
  obtain ⟨h₀, h₁, h₂⟩ := H.bounds k (hVU hk) n
  have hbound := mul_le_mul_of_nonneg_right hBD (pow_nonneg ht n.val)
  exact ⟨h₀.trans hbound, h₁.trans hbound, h₂.trans hbound⟩

theorem scalarData_frozenKRegularity_of_kDerivatives {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (H : FrozenPartitionKDerivativeControl β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
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
  let η := min hD (min hZ (min hM hL))
  let ρ := min κ (1 / 4)
  have hη : 0 < η := lt_min hhD (lt_min hhZ (lt_min hhM hhL))
  have hρ : 0 < ρ := lt_min hκ (by norm_num)
  have hρhalf : ρ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hsubκ : Icc (-ρ) ρ ⊆ Icc (-κ) κ :=
    fun _ hk => ⟨(neg_le_neg (min_le_left κ (1 / 4))).trans hk.1,
      hk.2.trans (min_le_left _ _)⟩
  have hsub4 : Icc (-ρ) ρ ⊆ Icc (-(1 / 4) : ℝ) (1 / 4) :=
    fun _ hk => ⟨(neg_le_neg (min_le_right κ (1 / 4))).trans hk.1,
      hk.2.trans (min_le_right _ _)⟩
  obtain ⟨C, h₀, hC, hh₀, _, HK⟩ :=
    scalarData_frozenKRegularity_of_partition_integral_controls D hl
      (hB.trans hBT) hη (κ := ρ) (u := u) (by
        intro r hr h hh hhη z ε hε j hj
        have hhD' : h ≤ hD := hhη.trans (min_le_left _ _)
        have hhrest := hhη.trans (min_le_right _ _)
        have hhZ' : h ≤ hZ := hhrest.trans (min_le_left _ _)
        have hhM' : h ≤ hM := hhrest.trans ((min_le_right _ _).trans (min_le_left _ _))
        have hhL' : h ≤ hL := hhrest.trans ((min_le_right _ _).trans (min_le_right _ _))
        by_cases hj11 : j = 11
        · subst j
          exact ⟨_, _, (HL r hr h hh hhL' z ε hε).restrict_mono hsub4 hLT (by positivity)⟩
        · obtain ⟨W₁, W₂, hd, hb⟩ := HD r hr h hh hhD' z ε hε j (by omega)
          refine ⟨W₁, W₂, ?_, ?_, ?_⟩
          · intro k hk
            exact ne_of_gt (HZ r hr h hh hhZ' k ((abs_le.mpr hk).trans hρhalf) z ε hε j hj)
          · intro k hk n
            exact hd k (hsubκ hk) n
          · intro k hk n
            have ht : 0 ≤ (Real.sqrt h * h) ^ n.val := by positivity
            exact ⟨(HM r hr h hh hhM' k ((abs_le.mpr hk).trans hρhalf) z ε hε j hj n).trans
                (mul_le_mul_of_nonneg_right hMT ht),
              (hb k (hsubκ hk) n).1.trans (mul_le_mul_of_nonneg_right hBT ht),
              (hb k (hsubκ hk) n).2.trans (mul_le_mul_of_nonneg_right hBT ht)⟩)
  exact ⟨C, h₀, ρ, hC, hh₀, hρ, min_le_right _ _, HK⟩

theorem scalarData_wickCoefficientError_even {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
        wickCoefficientError β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z (-k) =
          wickCoefficientError β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z k := by
  have HJ := scalarData_frozenJetHypotheses_window D hl hu
  obtain ⟨hA, hhA, HA⟩ := HJ.uniform_startup
  obtain ⟨hD, hhD, HD⟩ := scalarData_terminalChainDifferentiation D hl hu
  obtain ⟨hE, hhE, HE⟩ := scalarData_frozen_epsilon_even D hl hu
  obtain ⟨hδ, Hcover⟩ := frozen_window_cover hl hu
  refine ⟨min hD (min hE (min (min (l / 2) ((D.q - u) / 6)) hA)),
    lt_min hhD (lt_min hhE (lt_min hδ hhA)), ?_⟩
  intro r hr h hh hh₀ k hk z
  have hhD' := hh₀.trans (min_le_left _ _)
  have hhE' := hh₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhrest := hh₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpoints := Hcover r hr h hh (hhrest.trans (min_le_left _ _))
  have hhk : |(-k)| ≤ 1 / 2 := by simpa only [abs_neg] using hk
  have hQ (t : ℝ) (ht : |t| ≤ 1 / 2) :=
    (HA (r - h) h t z hpoints.1 hpoints.2 hh.le
      (hhrest.trans (min_le_right _ _)) ht).1
  have hp := (frozenTerminalTheta_first_second β _ _ _ h k z
    (hQ k hk) (HD r hr h hh hhD' k hk z)).2.deriv
  have hn := (frozenTerminalTheta_first_second β _ _ _ h (-k) z
    (hQ (-k) hhk) (HD r hr h hh hhD' (-k) hhk z)).2.deriv
  have he : frozenTerminalTheta β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h (-k) z =ᶠ[𝓝 (0 : ℝ)]
      frozenTerminalTheta β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 2)] with ε hε
    exact HE r hr h hh hhE' k hk z ε ⟨hε.1.le, hε.2.le⟩
  have hsecond := hn.symm.trans (he.deriv.deriv_eq.trans hp)
  unfold wickCoefficientError wickRow
  rw [hsecond, wick_jet_evaluation (1 / 2) (-k) (by norm_num),
    wick_jet_evaluation (1 / 2) k (by norm_num)]
  ring

theorem scalarData_wickTail_HT_of_secondControl {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (HW : WickTailSecondControl β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
        EvenSecondControl
          (wickTailCoefficientError β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
          (1 / 4) (C * Real.sqrt h * h ^ 3) 0 := by
  obtain ⟨C, hW, hC, hhW, HW⟩ := HW
  obtain ⟨A, hA, _, hhA, HA⟩ := scalarData_cubicWickCoefficientError_control D hl hu
  obtain ⟨hE, hhE, HE⟩ := scalarData_wickCoefficientError_even D hl hu
  refine ⟨C + 1, min hW (min hA hE), by positivity,
    lt_min hhW (lt_min hhA hhE), ?_⟩
  intro r hr h hh hh₀ z
  obtain ⟨f₁, f₂, hd, hb⟩ := HW r hr h hh (hh₀.trans (min_le_left _ _)) z
  have hc := HA r hr h hh (hh₀.trans ((min_le_right _ _).trans (min_le_left _ _))) z
  refine ⟨f₁, f₂, hd, ?_, ?_⟩
  · intro k hk
    simp only [zero_mul, add_zero]
    exact (hb k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (Real.sqrt_nonneg h))
      (pow_nonneg hh.le 3))
  · intro k hk
    have he := HE r hr h hh
      (hh₀.trans ((min_le_right _ _).trans (min_le_right _ _))) k
      ((abs_le.mpr hk).trans (by norm_num)) z
    rw [wickCoefficientError_split, wickCoefficientError_split] at he
    linarith only [he, hc.choose_spec.choose_spec.2.2 k hk]

theorem TerminalChainDifferentiation.restrict {β h₀ h₁ κ ρ : ℝ}
    {α : ℝ → ℝ} {I : Set ℝ} (H : TerminalChainDifferentiation β α I h₀ κ)
    (hh : h₁ ≤ h₀) (hρ : ρ ≤ κ) : TerminalChainDifferentiation β α I h₁ ρ := by
  intro r hr h hhpos hh₁ k hk z
  exact H r hr h hhpos (hh₁.trans hh) k (hk.trans hρ) z

theorem TerminalMixedThirdControl.restrict {β C h₀ h₁ κ ρ : ℝ}
    {α : ℝ → ℝ} {I : Set ℝ} (H : TerminalMixedThirdControl β α I C h₀ κ)
    (hh : h₁ ≤ h₀) (hρ : ρ ≤ κ) : TerminalMixedThirdControl β α I C h₁ ρ := by
  intro r hr h hhpos hh₁ z
  obtain ⟨hε, H⟩ := H r hr h hhpos (hh₁.trans hh) z
  refine ⟨fun k hk => hε k (hk.trans hρ), ?_⟩
  intro ε hε
  obtain ⟨g₁, g₂, hd, hb, he⟩ := H ε hε
  have hsub : Icc (-ρ) ρ ⊆ Icc (-κ) κ :=
    fun _ hk => ⟨(neg_le_neg hρ).trans hk.1, hk.2.trans hρ⟩
  exact ⟨g₁, g₂, fun k hk => hd k (hsub hk), fun k hk => hb k (hsub hk),
    fun k hk => he k (hsub hk)⟩

theorem scalarData_terminalFrozenRemainderBound_of_leaves {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (HW : WickTailSecondControl β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (HK : FrozenPartitionKDerivativeControl β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨C, hC, hC₀, hhC, HC⟩ :=
    scalarData_terminalSplitDerivativeControl_of_wickTail D hl hu
      (scalarData_wickTail_HT_of_secondControl D hl hu HW)
  obtain ⟨K, hK, κK, hK₀, hhK, hκK, hκK4, HK⟩ :=
    scalarData_frozenKRegularity_of_kDerivatives D hl hu HK
  obtain ⟨hT, hhT, _, HT⟩ := scalarData_terminalMixedThirdControl_of_kRegularity D hl hu
    hhK (hκK4.trans_lt (by norm_num)) HK
  obtain ⟨hD, hhD, HD⟩ := scalarData_terminalChainDifferentiation D hl hu
  have HJ := scalarData_frozenJetHypotheses_window D hl hu
  obtain ⟨hδ, Hcover⟩ := frozen_window_cover hl hu
  let η := min hD (min hC hT)
  let ρ := κK
  have hη : 0 < η := lt_min hhD (lt_min hhC hhT)
  have hρ : 0 < ρ := hκK
  have hρhalf : ρ ≤ 1 / 2 := hκK4.trans (by norm_num)
  apply terminalFrozenRemainderBound_of_derivative_controls (C := C) (D := 6 * K)
    (h₀ := η) (κ := ρ) HJ hC₀
    (mul_pos (by norm_num) hK₀) hη hρ hρhalf hδ Hcover
    (HD.restrict (min_le_left _ _) hρhalf)
  · intro r hr h hh hhη z
    obtain ⟨hR, hF, hW⟩ := HC r hr h hh
      (hhη.trans ((min_le_right _ _).trans (min_le_left _ _))) z
    exact ⟨hR.restrict_radius hκK4, hF.restrict_radius hκK4, hW.restrict_radius hκK4⟩
  · exact HT.restrict ((min_le_right _ _).trans (min_le_right _ _)) le_rfl

theorem scalarData_crude_terminal_massVariation_of_leaves {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (H : OpenLeaves β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨hwick, hraw, hfirst, hentropy⟩ := H
  exact ⟨scalarData_crudeC1 D hl hu,
    scalarData_terminalFrozenRemainderBound_of_leaves D hl hu hwick hraw,
    massVariationBound_of_scalarData_C2 D hl hu
      (massSensitivityC2_of_differentiatedExpansions D hl hu hfirst hentropy)⟩

end SKBarriers2.Corner

namespace SKBarriers2

theorem mainStatement_of_leaves
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        Corner.OpenLeaves β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.MainStatement := by
  apply mainStatement_of_crude_terminal_massVariation
  intro β hβ
  obtain ⟨l₀, hl₀, hl₀q, H⟩ := h β hβ
  refine ⟨l₀, hl₀, hl₀q, ?_⟩
  intro l u hl hlu hu
  exact Corner.scalarData_crude_terminal_massVariation_of_leaves (scalarData β hβ)
    hl (hu.trans_le hl₀q) (H l u hl hlu hu)

theorem subcriticalStatement_of_leaves
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        Corner.OpenLeaves β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.SubcriticalStatement := by
  apply subcriticalStatement_of_crude_terminal_massVariation
  intro β hβ
  obtain ⟨l₀, hl₀, hl₀q, H⟩ := h β hβ
  refine ⟨l₀, hl₀, hl₀q, ?_⟩
  intro l u hl hlu hu
  exact Corner.scalarData_crude_terminal_massVariation_of_leaves (scalarData β hβ)
    hl (hu.trans_le hl₀q) (H l u hl hlu hu)

end SKBarriers2
