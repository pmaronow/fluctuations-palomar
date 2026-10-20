module

public import SKBarriers2.Corner.CoreValue
public import SKBarriers2.Corner.PrefixMoments
public import SKBarriers2.Corner.PenaltyBoundProof
public import SKBarriers2.Main.Final

@[expose] public section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2

private theorem lipschitz_const_mul {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (c : ℝ) :
    LipschitzWith (‖c‖₊ * L) (fun z => c * g z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H := mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (abs_nonneg c)
  simpa only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
    Real.norm_eq_abs, mul_assoc] using H

private theorem small_powers {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    h ^ 3 ≤ h ^ 2 ∧ h ^ 4 ≤ h ^ 2 := by
  have h2 : h ^ 2 ≤ 1 := by nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg h)]
  · nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg h)]

private theorem coefficient_sum_bound {B P h k q g pen : ℝ}
    (hB : 0 ≤ B) (_hP : 0 ≤ P) (hh : 0 < h) (h1 : h ≤ 1)
    (hq : |q| ≤ B) (hg : |g| ≤ B * k ^ 2)
    (hp : |pen| ≤ P * h ^ 2 * k ^ 2) :
    |q * pen + h ^ 3 * g| ≤ (B * P + B) * h ^ 2 * k ^ 2 := by
  calc
    _ ≤ |q| * |pen| + h ^ 3 * |g| := by
      calc
        _ ≤ |q * pen| + |h ^ 3 * g| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_pos (pow_pos hh 3)]
    _ ≤ B * (P * h ^ 2 * k ^ 2) + h ^ 3 * (B * k ^ 2) :=
      add_le_add (mul_le_mul hq hp (abs_nonneg _) hB)
        (mul_le_mul_of_nonneg_left hg (pow_nonneg hh.le _))
    _ ≤ (B * P + B) * h ^ 2 * k ^ 2 := by
      have H := mul_le_mul_of_nonneg_right (small_powers hh h1).1
        (mul_nonneg hB (sq_nonneg k))
      nlinarith only [H]

private theorem interval_room {q l u : ℝ} (hl : 0 < l) (hu : u < q) (hq : q < 1) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      r - h ∈ Ioo (0 : ℝ) q ∧ r - h + 4 * h ∈ Icc (0 : ℝ) 1 := by
  refine ⟨min (l / 2) ((q - u) / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro r hr h hh hh₀
  have hhl := hh₀.trans (min_le_left _ _)
  have hhu := hh₀.trans (min_le_right _ _)
  constructor <;> constructor <;> linarith [hr.1, hr.2]

private def BLTest (g : ℝ → ℝ) : Prop :=
  ∃ L B : ℝ≥0, LipschitzWith L g ∧ ∀ z, |g z| ≤ B

private theorem BLTest.bounded {g : ℝ → ℝ} (hg : BLTest g) : BoundedScalar g := by
  obtain ⟨L, B, hL, hB⟩ := hg
  exact ⟨hL.continuous, B, B.coe_nonneg, hB⟩

private theorem BLTest.add {g f : ℝ → ℝ} (hg : BLTest g) (hf : BLTest f) :
    BLTest (fun z => g z + f z) := by
  obtain ⟨L, B, hL, hB⟩ := hg
  obtain ⟨M, C, hM, hC⟩ := hf
  exact ⟨L + M, B + C, hL.add hM,
    fun z => (abs_add_le _ _).trans (add_le_add (hB z) (hC z))⟩

private theorem BLTest.const_mul {g : ℝ → ℝ} (hg : BLTest g) (c : ℝ) :
    BLTest (fun z => c * g z) := by
  obtain ⟨L, B, hL, hB⟩ := hg
  refine ⟨‖c‖₊ * L, ‖c‖₊ * B, ?_, ?_⟩
  · exact lipschitz_const_mul hL c
  · intro z
    simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_left (hB z) (abs_nonneg c)

private theorem regular_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨C, D, hC, _, hb, _⟩ := hf.2
  refine ⟨⟨C, hC⟩, lipschitzWith_of_nnnorm_fderiv_le
    (hf.1.differentiable (by norm_num)) (fun x => ?_)⟩
  exact_mod_cast hb x

private theorem average_add {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    {f g a : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BLTest g) (ha : BLTest a)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    scalarCDFAverage β α s t f (fun z => g z + a z) x =
      scalarCDFAverage β α s t f g x + scalarCDFAverage β α s t f a x := by
  obtain ⟨K, hK⟩ := regular_lipschitz hf
  have H (b : ℝ → ℝ) (hb : BLTest b) :
      Tendsto (fun n => dyadicScalarAverage β α n s t f b x) atTop
        (𝓝 (scalarCDFAverage β α s t f b x)) := by
    obtain ⟨L, B, hL, hB⟩ := hb
    exact dyadicScalarAverage_tendsto_lipschitz β hα hm hf hK hL hB s t ht x
  apply tendsto_nhds_unique (H _ (hg.add ha))
  convert (H g hg).add (H a ha) using 1
  ext n
  exact scalarHierarchyAverage_add hf hg.bounded ha.bounded _ _ _ x

private theorem average_const_mul {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BLTest g)
    (c s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    scalarCDFAverage β α s t f (fun z => c * g z) x =
      c * scalarCDFAverage β α s t f g x := by
  obtain ⟨K, hK⟩ := regular_lipschitz hf
  have H (b : ℝ → ℝ) (hb : BLTest b) :
      Tendsto (fun n => dyadicScalarAverage β α n s t f b x) atTop
        (𝓝 (scalarCDFAverage β α s t f b x)) := by
    obtain ⟨L, B, hL, hB⟩ := hb
    exact dyadicScalarAverage_tendsto_lipschitz β hα hm hf hK hL hB s t ht x
  apply tendsto_nhds_unique (H _ (hg.const_mul c))
  convert (H g hg).const_mul c using 1
  ext n
  exact scalarHierarchyAverage_const_mul hf hg.bounded _ _ _ x c

private theorem half_jet_bounds {k : ℝ} (hk : |k| ≤ 1 / 2) :
    k ^ 2 ≤ 1 ∧ |riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0| ≤ 3 ∧
      |wickJet (1 / 2) k - wickJet (1 / 2) 0| ≤ 3 := by
  have h2 : k ^ 2 ≤ 1 := by
    have H := mul_self_le_mul_self (abs_nonneg k) hk
    nlinarith [sq_abs k]
  have h4 : k ^ 4 ≤ 1 := by nlinarith [sq_nonneg (k ^ 2 - 1)]
  have h6 : k ^ 6 ≤ 1 := by
    have H := mul_le_mul h4 h2 (sq_nonneg k) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [H]
  refine ⟨h2, ?_, ?_⟩
  · rw [riccati_jet_evaluation _ _ (by norm_num)]
    norm_num only [riccati2, riccati4, c6]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg k, pow_nonneg (sq_nonneg k) 2,
      pow_nonneg (sq_nonneg k) 3]
  · rw [wick_jet_evaluation _ _ (by norm_num)]
    norm_num only [wick2, wick4]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg k, pow_nonneg (sq_nonneg k) 2]

private theorem jet_power_test {β : ℝ} (D : ScalarData β)
    (j n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    BLTest (fun z => jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z ^ n) := by
  let μ := Bridge.overlapMeasure D.μ D.mass_one
  have H := Bridge.parisiSpatialJet_power_test β μ j n s
  simp_rw [← Bridge.jet_succ_eq_parisiSpatialJet β μ j s hs] at H
  simpa only [BLTest, μ, Bridge.realMeasure_overlapMeasure] using H

private theorem average_three {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    {f g₁ g₂ g₃ : ℝ → ℝ} (hf : BoundedDerivs f)
    (h₁ : BLTest g₁) (h₂ : BLTest g₂) (h₃ : BLTest g₃)
    (c₁ c₂ c₃ s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    scalarCDFAverage β α s t f (fun z => c₁ * g₁ z + c₂ * g₂ z + c₃ * g₃ z) x =
      c₁ * scalarCDFAverage β α s t f g₁ x +
        c₂ * scalarCDFAverage β α s t f g₂ x +
        c₃ * scalarCDFAverage β α s t f g₃ x := by
  rw [average_add hα hm hf ((h₁.const_mul c₁).add (h₂.const_mul c₂)) (h₃.const_mul c₃),
    average_add hα hm hf (h₁.const_mul c₁) (h₂.const_mul c₂),
    average_const_mul hα hm hf h₁, average_const_mul hα hm hf h₂,
    average_const_mul hα hm hf h₃]
  all_goals exact ht

private theorem trial_difference {β : ℝ} {α : ℝ → ℝ} {r h k : ℝ}
    (hh : h ≠ 0) (N : ℕ) :
    OW.trialValue β α α r (h / 2) (h * k) N - OW.trialValue β α α r (h / 2) 0 N =
      scalarCDFOperator β (fun t => α t / 3) 0 (Real.toNNReal (r - h))
        (OW.boundary β α (1 / 2) (r - h) h k N) 0 -
      scalarCDFOperator β (fun t => α t / 3) 0 (Real.toNNReal (r - h))
        (OW.boundary β α (1 / 2) (r - h) h 0 N) 0 -
      β ^ 2 / 4 * cornerPenalty α r h k N := by
  have h2 : 2 * (h / 2) = h := by ring
  simp only [OW.trialValue, h2, zero_div, mul_div_cancel_left₀ k hh]
  unfold OW.penalty cornerPenalty
  ring

private theorem prefix_core_bound {β : ℝ} (D : ScalarData β)
    {r h k E B : ℝ} {N : ℕ}
    (hh : 0 < h) (hs : r - h ∈ Icc (0 : ℝ) 1)
    (hT : r - h + 4 * h ∈ Icc (0 : ℝ) 1)
    (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hV : ∀ z, |cornerV β (cdf (D.μ : Measure ℝ)) r h k N z| ≤ B * h ^ 2 * k ^ 2)
    (hcore : ∀ z,
      |cornerV β (cdf (D.μ : Measure ℝ)) r h k N z -
        (cornerQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) z *
            cornerPenalty (cdf (D.μ : Measure ℝ)) r h k N +
          h ^ 3 * cornerCubic β (cdf (D.μ : Measure ℝ)) (r - h) k z)| ≤
          E) :
    let α := cdf (D.μ : Measure ℝ)
    let a := α (r - h)
    OW.trialValue β α α r (h / 2) (h * k) N ≤ OW.trialValue β α α r (h / 2) 0 N +
      β ^ 4 / 4 * cornerAverage β α r h N (fun z => jet β α 2 (r - h) z ^ 2) *
        cornerPenalty α r h k N +
      h ^ 3 * (a ^ 2 * (β ^ 2) ^ 3 *
        cornerAverage β α r h N (fun z => jet β α 2 (r - h) z ^ 3) *
          (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
        a * (β ^ 2) ^ 3 * cornerAverage β α r h N (fun z => jet β α 3 (r - h) z ^ 2) *
          (wickJet (1 / 2) k - wickJet (1 / 2) 0)) -
      β ^ 2 / 4 * cornerPenalty α r h k N +
      E + (B * h ^ 2 * k ^ 2) ^ 2 / 2 := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  have hα : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hm : Monotone α := (cdf _).mono
  have hp : ∀ z, α z / 3 ∈ Icc (0 : ℝ) 1 := fun z =>
    ⟨by linarith [(hα z).1], by linarith [(hα z).2]⟩
  have hpm : Monotone (fun z => α z / 3) := fun _ _ hab =>
    div_le_div_of_nonneg_right (hm hab) (by norm_num)
  let F := OW.boundary β α (1 / 2) (r - h) h 0 N
  let V := cornerV β α r h k N
  have hF : BoundedDerivs F := OW.boundary_regular β α hα hm _ _ _ _ N hT
  have hG : BoundedDerivs (OW.boundary β α (1 / 2) (r - h) h k N) :=
    OW.boundary_regular β α hα hm _ _ _ _ N hT
  have hVr : BoundedDerivs V := by
    change BoundedDerivs (fun z => OW.boundary β α (1 / 2) (r - h) h k N z - F z)
    convert hG.add (hF.const_mul (-1)) using 1
    funext z
    ring
  obtain ⟨K, hK⟩ := regular_lipschitz hF
  obtain ⟨L, hL⟩ := regular_lipschitz hVr
  have ht : Real.toNNReal (r - h) ≤ 1 := Real.toNNReal_le_one.mpr hs.2
  let vB : ℝ≥0 := ⟨B * h ^ 2 * k ^ 2, by positivity⟩
  have Hv := Prefix.scalarCDFOperator_add_remainder β hp hpm hF hVr
    (B := vB) hV 0 _ ht 0
  have hFV : (fun z => F z + V z) = OW.boundary β α (1 / 2) (r - h) h k N := by
    funext z
    dsimp only [F, V, cornerV]
    ring
  rw [hFV] at Hv
  let c₁ := β ^ 4 / 4 * cornerPenalty α r h k N
  let c₂ := h ^ 3 * α (r - h) ^ 2 * (β ^ 2) ^ 3 *
    (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0)
  let c₃ := h ^ 3 * α (r - h) * (β ^ 2) ^ 3 *
    (wickJet (1 / 2) k - wickJet (1 / 2) 0)
  let M := fun z => c₁ * jet β α 2 (r - h) z ^ 2 +
    c₂ * jet β α 2 (r - h) z ^ 3 + c₃ * jet β α 3 (r - h) z ^ 2
  have h₁ := jet_power_test D 1 2 (r - h) hs
  have h₂ := jet_power_test D 1 3 (r - h) hs
  have h₃ := jet_power_test D 2 2 (r - h) hs
  obtain ⟨LM, BM, hLM, hBM⟩ :=
    ((h₁.const_mul c₁).add (h₂.const_mul c₂)).add (h₃.const_mul c₃)
  have hMeq (z : ℝ) : M z = cornerQuadratic β α (r - h) z *
      cornerPenalty α r h k N + h ^ 3 * cornerCubic β α (r - h) k z := by
    dsimp only [M, c₁, c₂, c₃, cornerQuadratic, cornerCubic]
    ring
  have herr := scalarCDFAverage_observable_distance β hp hpm hF hK hL hLM
    (B := vB) hV hBM hE
    (fun z => by change |V z - M z| ≤ _; rw [hMeq]; exact hcore z) 0 _ ht 0
  have hM := average_three (β := β) hp hpm hF h₁ h₂ h₃ c₁ c₂ c₃ 0 _ ht 0
  have hdiff := trial_difference (β := β) (α := α) (r := r) (k := k) hh.ne' N
  dsimp only [vB] at Hv
  dsimp only [cornerAverage, M, c₁, c₂, c₃]
  rw [hM] at herr
  dsimp only [c₁, c₂, c₃] at herr
  have H₁ := (abs_le.mp Hv).2
  have H₂ := (abs_le.mp herr).2
  dsimp only [F, V, α] at H₁ H₂ hdiff
  change _ ≤ (B * h ^ 2 * k ^ 2) ^ 2 / 2 at H₁
  linear_combination H₁ + H₂ + hdiff

private theorem contact_error_bound (a b e₂ e₃ ew x₂ x₃ xw pen h k P : ℝ)
    (hh : 0 ≤ h) (_hP : 0 ≤ P) (hk : |k| ≤ 1 / 2)
    (hc₁ : b * e₂ = 1) (hc₂ : ew = 2 * a * e₃)
    (hpen : |pen| ≤ P * h ^ 2) :
    b ^ 2 / 4 * x₂ * pen +
        h ^ 3 * (a ^ 2 * b ^ 3 * x₃ * (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
          a * b ^ 3 * xw * (wickJet (1 / 2) k - wickJet (1 / 2) 0)) - b / 4 * pen ≤
      a ^ 2 * b ^ 3 * e₃ * h ^ 3 * pressurePolynomial (1 / 2) k +
        |b ^ 2 / 4| * P * h ^ 2 * |x₂ - e₂| +
        h ^ 3 * 3 * (|a ^ 2 * b ^ 3| * |x₃ - e₃| + |a * b ^ 3| * |xw - ew|) := by
  obtain ⟨_, hR, hW⟩ := half_jet_bounds hk
  have hc : b ^ 2 / 4 * e₂ = b / 4 := by
    nlinarith only [congrArg (fun x : ℝ => b / 4 * x) hc₁]
  have H := finite_jet_contact_reduction (1 / 2) k a b e₃ ew (by norm_num) hc₂
  have he : b ^ 2 / 4 * x₂ * pen +
        h ^ 3 * (a ^ 2 * b ^ 3 * x₃ * (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
          a * b ^ 3 * xw * (wickJet (1 / 2) k - wickJet (1 / 2) 0)) - b / 4 * pen =
      a ^ 2 * b ^ 3 * e₃ * h ^ 3 * pressurePolynomial (1 / 2) k +
        b ^ 2 / 4 * (x₂ - e₂) * pen +
        h ^ 3 * (a ^ 2 * b ^ 3 * (x₃ - e₃) *
          (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
          a * b ^ 3 * (xw - ew) * (wickJet (1 / 2) k - wickJet (1 / 2) 0)) := by
    nlinarith only [congrArg (fun x : ℝ => h ^ 3 * x) H,
      congrArg (fun x : ℝ => x * pen) hc]
  rw [he]
  have hq : b ^ 2 / 4 * (x₂ - e₂) * pen ≤ |b ^ 2 / 4| * P * h ^ 2 * |x₂ - e₂| := by
    calc
      _ ≤ |b ^ 2 / 4 * (x₂ - e₂) * pen| := le_abs_self _
      _ = |b ^ 2 / 4| * |x₂ - e₂| * |pen| := by rw [abs_mul, abs_mul]
      _ ≤ |b ^ 2 / 4| * |x₂ - e₂| * (P * h ^ 2) :=
        mul_le_mul_of_nonneg_left hpen (by positivity)
      _ = _ := by ring
  have hR' : a ^ 2 * b ^ 3 * (x₃ - e₃) *
      (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) ≤
        3 * (|a ^ 2 * b ^ 3| * |x₃ - e₃|) := by
    calc
      _ ≤ |a ^ 2 * b ^ 3 * (x₃ - e₃) *
          (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0)| := le_abs_self _
      _ = |a ^ 2 * b ^ 3| * |x₃ - e₃| *
          |riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0| := by rw [abs_mul, abs_mul]
      _ ≤ |a ^ 2 * b ^ 3| * |x₃ - e₃| * 3 :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring
  have hW' : a * b ^ 3 * (xw - ew) * (wickJet (1 / 2) k - wickJet (1 / 2) 0) ≤
      3 * (|a * b ^ 3| * |xw - ew|) := by
    calc
      _ ≤ |a * b ^ 3 * (xw - ew) * (wickJet (1 / 2) k - wickJet (1 / 2) 0)| := le_abs_self _
      _ = |a * b ^ 3| * |xw - ew| * |wickJet (1 / 2) k - wickJet (1 / 2) 0| := by
        rw [abs_mul, abs_mul]
      _ ≤ |a * b ^ 3| * |xw - ew| * 3 := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hR' hW') (pow_nonneg hh 3)
  linarith

private theorem value_error_le {h k : ℝ} (hh : 0 < h) (h1 : h ≤ 1)
    (hk : |k| ≤ 1 / 2) :
    Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3 ≤ 2 * h ^ 2 * k ^ 2 := by
  have hs : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr h1
  have hk1 : |k| ≤ 1 := hk.trans (by norm_num)
  have hk3 : |k| ^ 3 ≤ k ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hk1 (sq_nonneg |k|)
    nlinarith only [H, sq_abs k]
  have H₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ h ^ 3 * k ^ 2 by positivity)
  have H₂ := mul_le_mul_of_nonneg_left hk3 (pow_nonneg hh.le 3)
  have H₃ := mul_le_mul_of_nonneg_right (small_powers hh h1).1 (sq_nonneg k)
  nlinarith only [H₁, H₂, H₃]

theorem cornerExpansion_of_coreValue {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q)
    (hvalue : CoreValue β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpen : PenaltyBound β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CornerExpansion' β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  have hα : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hm : Monotone α := (cdf _).mono
  obtain ⟨A, hA, HA⟩ := coreCoefficientControl_of_scalarData D
  obtain ⟨C, hc, κ, hC, hhc, hκ, Hc⟩ := hvalue
  obtain ⟨P, hp, hP, hhp, Hp⟩ := hpen
  obtain ⟨hf, hhf, Hf⟩ := prefixMomentConvergence_of_scalarData D hl hu
  obtain ⟨hg, hhg, Hg⟩ := interval_room hl hu D.q_mem.2
  let B : ℝ := A * P + A + 2 * C + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨C + B ^ 2 / 2, min 1 (min hc (min hp (min hf hg))), min κ (1 / 2),
    by positivity, by positivity, lt_min hκ (by norm_num), ?_⟩
  intro r hr h hh hh₀ k hk ε hε
  simp only [le_min_iff] at hh₀ hk
  obtain ⟨hh1, hhc', hhp', hhf', hhg'⟩ := hh₀
  obtain ⟨hkk, hkhalf⟩ := hk
  obtain ⟨hs, hT⟩ := Hg r hr h hh hhg'
  have hs1 : r - h ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans D.q_mem.2.le⟩
  obtain ⟨H₂, H₃, Hw⟩ := Hf r hr h hh hhf'
  let x₂ := fun N => cornerAverage β α r h N (fun z => jet β α 2 (r - h) z ^ 2)
  let x₃ := fun N => cornerAverage β α r h N (fun z => jet β α 2 (r - h) z ^ 3)
  let xw := fun N => cornerAverage β α r h N (fun z => jet β α 3 (r - h) z ^ 2)
  let e₂ := scalarLaw β α (r - h) (fun z => jet β α 2 (r - h) z ^ 2)
  let e₃ := scalarLaw β α (r - h) (fun z => jet β α 2 (r - h) z ^ 3)
  let ew := scalarLaw β α (r - h) (fun z => jet β α 3 (r - h) z ^ 2)
  let a := α (r - h)
  have hzero : Tendsto (fun N => OW.trialValue β α α r (h / 2) 0 N) atTop
      (𝓝 (3 * finiteParisiInf β)) := by
    have H := zeroTiltParisiLimit_of_monotone (β := β) hα hm α hα hm r (h / 2)
      (by positivity) (by linarith [hs.1]) (by linarith [hT.2]) (fun _ _ => rfl)
    simpa only [α, D.minimizer] using H
  by_cases hkzero : k = 0
  · filter_upwards [(tendsto_order.mp hzero).2 (3 * finiteParisiInf β + ε)
      (by linarith)] with N hN
    simpa [hkzero, pressurePolynomial] using hN.le
  let err := fun N : ℕ => |OW.trialValue β α α r (h / 2) 0 N - 3 * finiteParisiInf β| +
    |(β ^ 2) ^ 2 / 4| * P * h ^ 2 * |x₂ N - e₂| +
    h ^ 3 * 3 * (|a ^ 2 * (β ^ 2) ^ 3| * |x₃ N - e₃| +
      |a * (β ^ 2) ^ 3| * |xw N - ew|)
  have herr : Tendsto err atTop (𝓝 0) := by
    have H := ((hzero.sub_const (3 * finiteParisiInf β)).abs.add
      (((H₂.sub_const e₂).abs).const_mul (|(β ^ 2) ^ 2 / 4| * P * h ^ 2))).add
      (((((H₃.sub_const e₃).abs).const_mul |a ^ 2 * (β ^ 2) ^ 3|).add
        (((Hw.sub_const ew).abs).const_mul |a * (β ^ 2) ^ 3|)).const_mul (h ^ 3 * 3))
    simpa only [err, x₂, x₃, xw, e₂, e₃, ew, α, sub_self, abs_zero, mul_zero,
      add_zero, zero_add] using H
  let η : ℝ := min (ε / 2) (h ^ 2 * k ^ 2)
  have hη : 0 < η := lt_min (by positivity) (mul_pos (sq_pos_of_pos hh) (sq_pos_of_ne_zero hkzero))
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hηv : η ≤ h ^ 2 * k ^ 2 := min_le_right _ _
  have hc₁ : β ^ 2 * e₂ = 1 := D.contact₁ (r - h) hs
  have hc₂ : ew = 2 * a * e₃ := D.contact₂ (r - h) hs
  filter_upwards [(tendsto_order.mp herr).2 (ε / 2) (by positivity),
    Hc r hr h hh hhc' k hkk η hη, eventually_ge_atTop 1] with N heN hcore hN
  have hk2 := (half_jet_bounds hkhalf).1
  have hpN := Hp r hr h hh hhp' k hkhalf N hN
  have hpN' : |cornerPenalty α r h k N| ≤ P * h ^ 2 :=
    hpN.trans (mul_le_of_le_one_right (by positivity) hk2)
  have hV (z : ℝ) : |cornerV β α r h k N z| ≤ B * h ^ 2 * k ^ 2 := by
    obtain ⟨hq, _, hg', _⟩ := HA (r - h) hs1 k hkhalf z
    have HM := coefficient_sum_bound hA hP hh hh1 hq hg' hpN
    have HT := abs_add_le (cornerV β α r h k N z -
      (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
        h ^ 3 * cornerCubic β α (r - h) k z))
      (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
        h ^ 3 * cornerCubic β α (r - h) k z)
    rw [sub_add_cancel] at HT
    have HR := mul_le_mul_of_nonneg_left (value_error_le hh hh1 hkhalf) hC.le
    dsimp only [B]
    nlinarith only [HM, HT, HR, hcore z, hηv]
  have HF := prefix_core_bound D hh hs1 hT (by positivity) hB hV hcore
  have HE := contact_error_bound a (β ^ 2) e₂ e₃ ew (x₂ N) (x₃ N) (xw N)
    (cornerPenalty α r h k N) h k P hh.le hP hkhalf hc₁ hc₂ hpN'
  have HQ : (B * h ^ 2 * k ^ 2) ^ 2 / 2 ≤
      B ^ 2 / 2 * (Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3) := by
    have hsqrt : h ≤ Real.sqrt h := by
      nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h]
    have H₁ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (sq_nonneg k) hk2) (show 0 ≤ B ^ 2 * h ^ 4 / 2 by positivity)
    have H₂ := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ B ^ 2 / 2 * h ^ 3 * k ^ 2 by positivity)
    have H₃ : 0 ≤ B ^ 2 / 2 * h ^ 3 * |k| ^ 3 := by positivity
    nlinarith only [H₁, H₂, H₃]
  have HZ := le_abs_self (OW.trialValue β α α r (h / 2) 0 N - 3 * finiteParisiInf β)
  dsimp only [α, a, x₂, x₃, xw, e₂, e₃, ew] at HE
  dsimp only [err, a, x₂, x₃, xw, e₂, e₃, ew, α] at heN
  dsimp only [cornerMass]
  dsimp only [α] at HF HZ
  linear_combination HF + HE + HQ + HZ + heN + hηε

private theorem crude_original_scale {B d δ : ℝ} (hd : 0 < d) :
    B * (2 * d) * (δ / (2 * d)) ^ 2 = (B / 2) * δ ^ 2 / d := by
  field_simp

theorem localBoundaryControl_of_crudeC1 {β q l u : ℝ} {α : ℝ → ℝ}
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (hl : 0 < l) (hu : u < q) (hq : q < 1)
    (hcrude : CrudeC1 β α (Icc l u)) :
    LocalBoundaryControl β α (Icc l u) := by
  obtain ⟨B, hc, hB, hhc, H⟩ := hcrude
  obtain ⟨hg, hhg, Hg⟩ := interval_room hl hu hq
  refine ⟨min (hc / 2) (hg / 2), B / 2, 3, 3,
    lt_min (by positivity) (by positivity), by positivity, ?_⟩
  intro r hr d δ hd hd₀ hδ N hN
  obtain ⟨hdc, hdg⟩ := le_min_iff.mp hd₀
  have hdc' : 2 * d ≤ hc := by linarith
  have hdg' : 2 * d ≤ hg := by linarith
  obtain ⟨_, hT⟩ := Hg r hr (2 * d) (by positivity) hdg'
  obtain ⟨hL, hL'⟩ := corner_zero_boundary_lipschitz hα hm (r - 2 * d) (2 * d) N hT
  refine ⟨hL, hL', ?_⟩
  intro z
  have hk : |δ / (2 * d)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * d)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
    linarith
  have HV := (H r hr (2 * d) (by positivity) hdc' _ hk N hN z).1
  rw [crude_original_scale hd] at HV
  exact HV

theorem localCubicGap_of_cornerExpansion' {β l u : ℝ} {α : ℝ → ℝ}
    (hexp : CornerExpansion' β α (Icc l u))
    (hmass : UniformCornerMass β α (Icc l u))
    (hcrude : CrudeC1 β α (Icc l u)) : LocalCubicGap β α (Icc l u) := by
  obtain ⟨C, he, κ, hC, hhe, hκ, He⟩ := hexp
  obtain ⟨m₀, hm, hm₀, hhm, Hm⟩ := hmass
  obtain ⟨B, hc, hB, hhc, Hc⟩ := hcrude
  let t : ℝ := m₀ / (40 * (C + 1))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hCt : C * t ≤ m₀ / 40 := by
    have H : t * (40 * (C + 1)) = m₀ := div_mul_cancel₀ _ (by positivity)
    nlinarith only [H, ht.le]
  let κ₀ : ℝ := min (1 / 2) (min κ t)
  have hκ₀ : 0 < κ₀ := lt_min (by norm_num) (lt_min hκ ht)
  refine ⟨min (he / 2) (min (hm / 2) (min (hc / 2) (t ^ 2 / 2))), κ₀,
    m₀ / 10, B / 2, by positivity, hκ₀, by positivity, by positivity, ?_⟩
  intro r hr d δ hd hd₀ hδ₀ hδ
  simp only [le_min_iff] at hd₀
  obtain ⟨hde, hdm, hdc, hdt⟩ := hd₀
  let h : ℝ := 2 * d
  let k : ℝ := δ / (2 * d)
  have hh : 0 < h := by dsimp only [h]; positivity
  have he' : h ≤ he := by dsimp only [h]; linarith
  have hm' : h ≤ hm := by dsimp only [h]; linarith
  have hc' : h ≤ hc := by dsimp only [h]; linarith
  have ht' : h ≤ t ^ 2 := by dsimp only [h]; linarith
  have hkκ₀ : |k| ≤ κ₀ := by
    dsimp only [k]
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).mpr
    dsimp only [h]
    nlinarith only [hδ, mul_nonneg hκ₀.le hd.le]
  have hk : |k| ≤ 1 / 2 := hkκ₀.trans (min_le_left _ _)
  have hkκ : |k| ≤ κ := hkκ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkt : |k| ≤ t := hkκ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hk0 : k ≠ 0 := div_ne_zero (abs_pos.mp hδ₀) (by positivity)
  have hmass' : m₀ ≤ cornerMass β α (r - h) := Hm r hr h hh hm'
  have hmp : 0 < cornerMass β α (r - h) := hm₀.trans_le hmass'
  have hsqrt : C * Real.sqrt h ≤ cornerMass β α (r - h) / 40 := by
    have H := mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨ht.le, ht'⟩) hC
    linarith
  have htilt : C * |k| ≤ cornerMass β α (r - h) / 40 := by
    have H := mul_le_mul_of_nonneg_left hkt hC
    linarith
  have herror : C * (Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3) ≤
      cornerMass β α (r - h) * h ^ 3 * k ^ 2 / 20 := by
    have H₁ := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ h ^ 3 * k ^ 2 by positivity)
    have H₂ := mul_le_mul_of_nonneg_right htilt (show 0 ≤ h ^ 3 * k ^ 2 by positivity)
    have heq : |k| ^ 3 = |k| * k ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [heq]
    nlinarith only [H₁, H₂]
  have hδeq : δ = h * k := by dsimp only [h, k]; field_simp
  have hdeq : d = h / 2 := by dsimp only [h]; ring
  let ε : ℝ := cornerMass β α (r - h) * h ^ 3 * k ^ 2 / 20
  have hε : 0 < ε := by dsimp only [ε]; positivity
  constructor
  · filter_upwards [He r hr h hh he' k hkκ ε hε] with N hN
    have HP := mul_le_mul_of_nonneg_left (half_polynomial_bound hk)
      (show 0 ≤ cornerMass β α (r - h) * h ^ 3 by positivity)
    have hscale : h ^ 3 * k ^ 2 = 2 * (δ ^ 2 * d) := by rw [hδeq, hdeq]; ring
    have HM := mul_le_mul_of_nonneg_right hmass' (show 0 ≤ δ ^ 2 * d by positivity)
    rw [← hdeq, ← hδeq] at hN
    dsimp only [ε] at hN
    nlinarith only [hN, HP, herror, hscale, HM, hmp,
      mul_nonneg hm₀.le (show 0 ≤ δ ^ 2 * d by positivity)]
  · intro N hN z
    have HV := (Hc r hr h hh hc' k hk N hN z).2
    change |deriv (cornerV β α r (2 * d) (δ / (2 * d)) N) z| ≤ _
    exact HV.trans_eq (crude_original_scale hd)

theorem penaltyBound_of_scalarData {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    PenaltyBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let H : ℝ := min (l / 2) ((D.q - u) / 2)
  have hH : 0 < H := lt_min (by positivity) (by positivity)
  have hleft : 0 < l - H := by
    have HH := min_le_left (l / 2) ((D.q - u) / 2)
    dsimp only [H]
    linarith
  have hright : u + H < D.q := by
    have HH := min_le_right (l / 2) ((D.q - u) / 2)
    dsimp only [H]
    linarith
  obtain ⟨K, hK⟩ := D.cdf_lipschitzOn hleft hright
  exact Corner.penaltyBound_of_monotone_lipschitz β _ l u H K hl hH (cdf _).mono
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) hK

theorem cornerInputs_of_crude_value {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q)
    (hcrude : CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hvalue : CoreValue β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    LocalCubicGap β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      LocalBoundaryControl β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  have hpen := penaltyBound_of_scalarData D hl hu
  exact ⟨localCubicGap_of_cornerExpansion' (cornerExpansion_of_coreValue D hl hu hvalue hpen)
      (uniformCornerMass_of_scalarData D hl hlu hu) hcrude,
    localBoundaryControl_of_crudeC1 (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
      (cdf _).mono hl hu D.q_mem.2 hcrude⟩

end SKBarriers2
