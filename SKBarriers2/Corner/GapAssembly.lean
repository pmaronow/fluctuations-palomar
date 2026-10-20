module

public import SKBarriers2.Corner.CoreIdentity
public import SKBarriers2.Overshoot.Prefix
public import SKBarriers2.Static.LocalFractional
public import SKBarriers2.Bridge.ScalarLaw
public import OAI.Probability.SKBarriers.Parisi.CDFCramer

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

private theorem mesh_error_le {C h k : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hh : 0 < h) (h1 : h ≤ 1) (hN : 1 ≤ N) :
    C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2 ≤ 2 * C * h ^ 2 * k ^ 2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hn
  have hd : h ^ 2 / (N : ℝ) ≤ h ^ 2 := (div_le_iff₀ hnpos).mpr (by
    nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg h)])
  have H := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show h ^ 4 + h ^ 2 / (N : ℝ) ≤ 2 * h ^ 2 by
      linarith [(small_powers hh h1).2]) hC) (sq_nonneg k)
  nlinarith only [H]

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

theorem corner_C1_of_coreIdentity {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hcore : CoreIdentity β α I) (hpen : PenaltyBound β α I)
    (hcoeff : CoreCoefficientControl β α) :
    ∃ B h₀ : ℝ, 0 ≤ B ∧ 0 < h₀ ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → r - h ∈ Icc (0 : ℝ) 1 →
        ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ N : ℕ, 1 ≤ N → ∀ z : ℝ,
          |cornerV β α r h k N z| ≤ B * h ^ 2 * k ^ 2 ∧
          |deriv (cornerV β α r h k N) z| ≤ B * h ^ 2 * k ^ 2 := by
  obtain ⟨C, hc, hC, hhc, Hc⟩ := hcore
  obtain ⟨P, hp, hP, hhp, Hp⟩ := hpen
  obtain ⟨B, hB, HB⟩ := hcoeff
  refine ⟨B * P + B + 2 * C, min 1 (min hc hp), by positivity,
    lt_min zero_lt_one (lt_min hhc hhp), ?_⟩
  intro r hr h hh hh₀ hs k hk N hN z
  have h1 : h ≤ 1 := hh₀.trans (min_le_left _ _)
  have hhc' : h ≤ hc := hh₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhp' : h ≤ hp := hh₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hv, hd⟩ := Hc r hr h hh hhc' k hk N hN z
  obtain ⟨hq, hq', hg, hg'⟩ := HB (r - h) hs k hk z
  have hpen' := Hp r hr h hh hhp' k hk N hN
  have he := mesh_error_le hC.le hh h1 hN (k := k)
  constructor
  · have H := coefficient_sum_bound hB hP hh h1 hq hg hpen'
    have Ht := abs_add_le (cornerV β α r h k N z -
      (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
        h ^ 3 * cornerCubic β α (r - h) k z))
      (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
        h ^ 3 * cornerCubic β α (r - h) k z)
    rw [sub_add_cancel] at Ht
    nlinarith only [H, Ht, hv, he]
  · have H := coefficient_sum_bound hB hP hh h1 hq' hg' hpen'
    have Ht := abs_add_le (deriv (cornerV β α r h k N) z -
      (deriv (cornerQuadratic β α (r - h)) z * cornerPenalty α r h k N +
        h ^ 3 * deriv (cornerCubic β α (r - h) k) z))
      (deriv (cornerQuadratic β α (r - h)) z * cornerPenalty α r h k N +
        h ^ 3 * deriv (cornerCubic β α (r - h) k) z)
    rw [sub_add_cancel] at Ht
    nlinarith only [H, Ht, hd, he]

private theorem chain_spinConvex {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hc : ScalarSpinConvex f) (l : List (ℝ × ℝ))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1) :
    ScalarSpinConvex (scalarIncrementChain l f) := by
  induction l with
  | nil => exact hc
  | cons p l ih =>
    exact (ih (fun u hu => hm u (List.mem_cons_of_mem _ hu))).scalarStep
      (scalarIncrementChain_regular l hf) (hm p (List.mem_cons_self)) p.2

private theorem spin_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hc : ScalarSpinConvex f) :
    LipschitzWith 1 f ∧ LipschitzWith 1 (deriv f) := by
  have hd (z : ℝ) : HasDerivAt f (rootGradient 0 f z) z := by
    simpa only [parameterAxis, smul_eq_mul, mul_one, zero_add] using
      rootLine_hasDerivAt 0 hf 0 z
  have hd' (z : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f z) z := by
    simpa only [parameterAxis, smul_eq_mul, mul_one, zero_add] using
      rootGradientLine_hasDerivAt 0 hf 0 z
  have he : deriv f = rootGradient 0 f := funext (fun z => (hd z).deriv)
  constructor
  · apply lipschitzWith_of_nnnorm_deriv_le (fun z => (hd z).differentiableAt)
    intro z
    rw [(hd z).deriv]
    exact_mod_cast (hc.bounds z).1
  · rw [he]
    apply lipschitzWith_of_nnnorm_deriv_le (fun z => (hd' z).differentiableAt)
    intro z
    rw [(hd' z).deriv]
    exact_mod_cast (hc.bounds z).2

theorem corner_zero_boundary_lipschitz {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s h : ℝ) (N : ℕ) (hT : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    LipschitzWith 3 (OW.boundary β α (1 / 2) s h 0 N) ∧
    LipschitzWith 3 (deriv (OW.boundary β α (1 / 2) s h 0 N)) := by
  have ht : Real.toNNReal (1 - (s + 4 * h)) ≤ 1 :=
    Real.toNNReal_le_one.mpr (by linarith [hT.1])
  have hf : BoundedDerivs (Phi β α (s + 4 * h)) :=
    scalarCDFValue_regular β hα hm _ _ ht
  have hc : ScalarSpinConvex (Phi β α (s + 4 * h)) :=
    scalarCDFValue_spinConvex β hα hm _ _ ht
  let f := scalarIncrementChain (OW.scalarWindow β α (1 / 2) s h N)
    (Phi β α (s + 4 * h))
  have hfr : BoundedDerivs f := scalarIncrementChain_regular _ hf
  obtain ⟨hL, hL'⟩ := spin_lipschitz hfr
    (chain_spinConvex hf hc _ (OW.scalarWindow_mass_mem β α hα _ _ _ N))
  have he : OW.boundary β α (1 / 2) s h 0 N = fun z => 3 * f z :=
    funext (OW.boundary_zero_factorization β α _ _ _ _ hf)
  rw [he]
  have hd : deriv (fun z => 3 * f z) = fun z => 3 * deriv f z := by
    funext z
    exact ((hfr.1.differentiable (by norm_num) z).hasDerivAt.const_mul 3).deriv
  rw [hd]
  constructor
  · simpa using lipschitz_const_mul hL (3 : ℝ)
  · simpa using lipschitz_const_mul hL' (3 : ℝ)

private theorem interval_room {q l u : ℝ} (hl : 0 < l) (hu : u < q) (hq : q < 1) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      r - h ∈ Ioo (0 : ℝ) q ∧ r - h + 4 * h ∈ Icc (0 : ℝ) 1 := by
  refine ⟨min (l / 2) ((q - u) / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro r hr h hh hh₀
  have hhl := hh₀.trans (min_le_left _ _)
  have hhu := hh₀.trans (min_le_right _ _)
  constructor <;> constructor <;> linarith [hr.1, hr.2]

private theorem original_scale {B d δ : ℝ} (hB : 0 ≤ B) (hd : 0 < d) (hd1 : d ≤ 1) :
    B * (2 * d) ^ 2 * (δ / (2 * d)) ^ 2 ≤ B * δ ^ 2 / d := by
  have he : (2 * d) ^ 2 * (δ / (2 * d)) ^ 2 = δ ^ 2 := by field_simp
  rw [mul_assoc B, he]
  apply (le_div_iff₀ hd).mpr
  exact mul_le_of_le_one_right (mul_nonneg hB (sq_nonneg δ)) hd1

theorem localBoundaryControl_of_coreIdentity {β q l u : ℝ} {α : ℝ → ℝ}
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (hl : 0 < l) (hu : u < q) (hq : q < 1)
    (hcore : CoreIdentity β α (Icc l u)) (hpen : PenaltyBound β α (Icc l u))
    (hcoeff : CoreCoefficientControl β α) :
    LocalBoundaryControl β α (Icc l u) := by
  obtain ⟨B, hc, hB, hhc, H⟩ := corner_C1_of_coreIdentity hcore hpen hcoeff
  obtain ⟨hg, hhg, Hg⟩ := interval_room hl hu hq
  refine ⟨min 1 (min (hc / 2) (hg / 2)), B, 3, 3,
    lt_min zero_lt_one (lt_min (by positivity) (by positivity)), hB, ?_⟩
  intro r hr d δ hd hd₀ hδ N hN
  have hd1 := hd₀.trans (min_le_left _ _)
  have hdc : 2 * d ≤ hc := by
    have HH := hd₀.trans ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hdg : 2 * d ≤ hg := by
    have HH := hd₀.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
  obtain ⟨hs, hT⟩ := Hg r hr (2 * d) (by positivity) hdg
  obtain ⟨hL, hL'⟩ := corner_zero_boundary_lipschitz hα hm (r - 2 * d) (2 * d) N hT
  refine ⟨hL, hL', ?_⟩
  intro z
  have hk : |δ / (2 * d)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * d)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
    linarith
  exact (H r hr (2 * d) (by positivity) hdc ⟨hs.1.le, hs.2.le.trans hq.le⟩
    _ hk N hN z).1.trans (original_scale hB hd hd1)

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
    {r h k C B : ℝ} {N : ℕ}
    (hh : 0 < h) (hs : r - h ∈ Icc (0 : ℝ) 1)
    (hT : r - h + 4 * h ∈ Icc (0 : ℝ) 1)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hV : ∀ z, |cornerV β (cdf (D.μ : Measure ℝ)) r h k N z| ≤ B * h ^ 2 * k ^ 2)
    (hcore : ∀ z,
      |cornerV β (cdf (D.μ : Measure ℝ)) r h k N z -
        (cornerQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) z *
            cornerPenalty (cdf (D.μ : Measure ℝ)) r h k N +
          h ^ 3 * cornerCubic β (cdf (D.μ : Measure ℝ)) (r - h) k z)| ≤
          C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2) :
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
      C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2 + (B * h ^ 2 * k ^ 2) ^ 2 / 2 := by
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
    (B := vB) hV hBM (by positivity : 0 ≤ C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2)
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

theorem cornerExpansion_of_coreIdentity {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q)
    (hcore : CoreIdentity β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpen : PenaltyBound β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hcoeff : CoreCoefficientControl β (cdf (D.μ : Measure ℝ)))
    (hprefix : PrefixMomentConvergence β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CornerExpansion β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  have hα : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hm : Monotone α := (cdf _).mono
  obtain ⟨B, hv, hB, hhv, Hv⟩ := corner_C1_of_coreIdentity hcore hpen hcoeff
  obtain ⟨C, hc, hC, hhc, Hc⟩ := hcore
  obtain ⟨P, hp, hP, hhp, Hp⟩ := hpen
  obtain ⟨hf, hhf, Hf⟩ := hprefix
  obtain ⟨hg, hhg, Hg⟩ := interval_room hl hu D.q_mem.2
  refine ⟨C + B ^ 2 / 2, min hc (min hp (min hv (min hf hg))), by positivity,
    lt_min hhc (lt_min hhp (lt_min hhv (lt_min hhf hhg))), ?_⟩
  intro r hr h hh hh₀ ε hε
  simp only [le_min_iff] at hh₀
  obtain ⟨hhc', hhp', hhv', hhf', hhg'⟩ := hh₀
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
  let err := fun N : ℕ => |OW.trialValue β α α r (h / 2) 0 N - 3 * finiteParisiInf β| +
    |(β ^ 2) ^ 2 / 4| * P * h ^ 2 * |x₂ N - e₂| +
    h ^ 3 * 3 * (|a ^ 2 * (β ^ 2) ^ 3| * |x₃ N - e₃| +
      |a * (β ^ 2) ^ 3| * |xw N - ew|) + C * h ^ 2 / (N : ℝ)
  have hmesh : Tendsto (fun N : ℕ => C * h ^ 2 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have herr : Tendsto err atTop (𝓝 0) := by
    have H := (((hzero.sub_const (3 * finiteParisiInf β)).abs.add
      (((H₂.sub_const e₂).abs).const_mul (|(β ^ 2) ^ 2 / 4| * P * h ^ 2))).add
      (((((H₃.sub_const e₃).abs).const_mul |a ^ 2 * (β ^ 2) ^ 3|).add
        (((Hw.sub_const ew).abs).const_mul |a * (β ^ 2) ^ 3|)).const_mul (h ^ 3 * 3))).add hmesh
    simpa only [err, x₂, x₃, xw, e₂, e₃, ew, α, sub_self, abs_zero, mul_zero,
      add_zero, zero_add] using H
  have hc₁ : β ^ 2 * e₂ = 1 := D.contact₁ (r - h) hs
  have hc₂ : ew = 2 * a * e₃ := D.contact₂ (r - h) hs
  filter_upwards [(tendsto_order.mp herr).2 ε hε, eventually_ge_atTop 1] with N heN hN k hk
  have hk2 := (half_jet_bounds hk).1
  have hpN := Hp r hr h hh hhp' k hk N hN
  have hpN' : |cornerPenalty α r h k N| ≤ P * h ^ 2 :=
    hpN.trans (mul_le_of_le_one_right (by positivity) hk2)
  have HF := prefix_core_bound D hh hs1 hT hC.le hB
    (fun z => (Hv r hr h hh hhv' hs1 k hk N hN z).1)
    (fun z => (Hc r hr h hh hhc' k hk N hN z).1)
  have HE := contact_error_bound a (β ^ 2) e₂ e₃ ew (x₂ N) (x₃ N) (xw N)
    (cornerPenalty α r h k N) h k P hh.le hP hk hc₁ hc₂ hpN'
  have HR : C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2 ≤
      C * h ^ 4 * k ^ 2 + C * h ^ 2 / (N : ℝ) := by
    have H : (C * h ^ 2 / (N : ℝ)) * k ^ 2 ≤ C * h ^ 2 / (N : ℝ) :=
      mul_le_of_le_one_right (by positivity) hk2
    calc
      C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2 =
          C * h ^ 4 * k ^ 2 + (C * h ^ 2 / (N : ℝ)) * k ^ 2 := by ring
      _ ≤ C * h ^ 4 * k ^ 2 + C * h ^ 2 / (N : ℝ) := add_le_add le_rfl H
  have HQ : (B * h ^ 2 * k ^ 2) ^ 2 / 2 ≤ B ^ 2 / 2 * h ^ 4 * k ^ 2 := by
    have H := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (sq_nonneg k) hk2) (show 0 ≤ B ^ 2 * h ^ 4 / 2 by positivity)
    nlinarith only [H]
  have HZ := le_abs_self (OW.trialValue β α α r (h / 2) 0 N - 3 * finiteParisiInf β)
  dsimp only [α, a, x₂, x₃, xw, e₂, e₃, ew] at HE
  dsimp only [err, a, x₂, x₃, xw, e₂, e₃, ew, α] at heN
  dsimp only [cornerMass]
  dsimp only [α] at HF HZ
  linear_combination HF + HE + HR + HQ + HZ + heN

theorem localCubicGap_of_cornerExpansion {β q l u : ℝ} {α : ℝ → ℝ}
    (hl : 0 < l) (hu : u < q) (hq : q < 1)
    (hexp : CornerExpansion β α (Icc l u))
    (hmass : UniformCornerMass β α (Icc l u))
    (hcore : CoreIdentity β α (Icc l u)) (hpen : PenaltyBound β α (Icc l u))
    (hcoeff : CoreCoefficientControl β α) : LocalCubicGap β α (Icc l u) := by
  obtain ⟨C, he, hC, hhe, He⟩ := hexp
  obtain ⟨m₀, hm, hm₀, hhm, Hm⟩ := hmass
  obtain ⟨B, hc, hB, hhc, Hc⟩ := corner_C1_of_coreIdentity hcore hpen hcoeff
  obtain ⟨hg, hhg, Hg⟩ := interval_room hl hu hq
  obtain ⟨ht, hht, Ht⟩ := exists_pos_mul_lt (show 0 < m₀ / 10 by positivity) C
  refine ⟨min 1 (min (he / 2) (min (hm / 2) (min (hc / 2)
    (min (hg / 2) (ht / 2))))), 1, m₀ / 10, B,
    lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))),
    zero_lt_one, by positivity, hB, ?_⟩
  intro r hr d δ hd hd₀ hδ₀ hδ
  simp only [le_min_iff] at hd₀
  obtain ⟨hd1, hde, hdm, hdc, hdg, hdt⟩ := hd₀
  let h : ℝ := 2 * d
  let k : ℝ := δ / (2 * d)
  have hh : 0 < h := by dsimp only [h]; positivity
  have he' : h ≤ he := by dsimp only [h]; linarith
  have hm' : h ≤ hm := by dsimp only [h]; linarith
  have hc' : h ≤ hc := by dsimp only [h]; linarith
  have hg' : h ≤ hg := by dsimp only [h]; linarith
  have ht' : h ≤ ht := by dsimp only [h]; linarith
  have hk : |k| ≤ 1 / 2 := by
    dsimp only [k]
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).mpr
    linarith
  have hk0 : k ≠ 0 := div_ne_zero (abs_pos.mp hδ₀) (by positivity)
  have hmass' : m₀ ≤ cornerMass β α (r - h) := Hm r hr h hh hm'
  have hmp : 0 < cornerMass β α (r - h) := hm₀.trans_le hmass'
  have hsmall : C * h ≤ cornerMass β α (r - h) / 10 := by
    have H := mul_le_mul_of_nonneg_left ht' hC
    linarith
  have hδeq : δ = h * k := by dsimp only [h, k]; field_simp
  have hdeq : d = h / 2 := by dsimp only [h]; ring
  let ε : ℝ := cornerMass β α (r - h) * h ^ 3 * k ^ 2 / 20
  have hε : 0 < ε := by dsimp only [ε]; positivity
  constructor
  · filter_upwards [He r hr h hh he' ε hε] with N hN
    have H := local_gain_in_original_variables
      (OW.trialValue β α α r (h / 2) (h * k) N - ε)
      (3 * finiteParisiInf β) (cornerMass β α (r - h)) C h k δ d
      hmp hC hh hk hsmall (by linarith [hN k hk]) hδeq hdeq
    rw [← hdeq, ← hδeq] at H
    have hscale : h ^ 3 * k ^ 2 = 2 * (δ ^ 2 * d) := by rw [hδeq, hdeq]; ring
    have heps : ε = cornerMass β α (r - h) * (δ ^ 2 * d) / 10 := by
      dsimp only [ε]
      rw [mul_assoc, hscale]
      ring
    have Hm' := mul_le_mul_of_nonneg_right hmass'
      (mul_nonneg (sq_nonneg δ) hd.le)
    nlinarith only [H, heps, Hm']
  · intro N hN z
    obtain ⟨hs, _⟩ := Hg r hr h hh hg'
    exact (Hc r hr h hh hc' ⟨hs.1.le, hs.2.le.trans hq.le⟩ k hk N hN z).2.trans
      (original_scale hB hd hd1)

private theorem jet_hasDerivAt {β : ℝ} (D : ScalarData β) (j : ℕ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    HasDerivAt (jet β (cdf (D.μ : Measure ℝ)) (j + 1) s)
      (jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z) z := by
  let μ := Bridge.overlapMeasure D.μ D.mass_one
  have he (i : ℕ) : jet β (cdf (D.μ : Measure ℝ)) (i + 1) s =
      FRSB.parisiSpatialJet β μ (i + 1) s := by
    funext x
    simpa only [μ, Bridge.realMeasure_overlapMeasure] using
      Bridge.jet_succ_eq_parisiSpatialJet β μ i s hs x
  rw [he j, show j + 2 = (j + 1) + 1 by omega, he (j + 1)]
  exact FRSB.hasDerivAt_parisiSpatialJet_succ β μ j s z

private theorem uniform_power_C1 {β : ℝ} (D : ScalarData β) (j n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ,
      DifferentiableAt ℝ (fun y => jet β (cdf (D.μ : Measure ℝ)) (j + 1) s y ^ n) z ∧
      |jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z ^ n| ≤ B ∧
      |deriv (fun y => jet β (cdf (D.μ : Measure ℝ)) (j + 1) s y ^ n) z| ≤ B := by
  obtain ⟨K, hK⟩ := D.jets j
  obtain ⟨L, hL⟩ := D.jets (j + 1)
  refine ⟨|K| ^ n + (n : ℝ) * |K| ^ (n - 1) * |L|, by positivity, ?_⟩
  intro s hs z
  have hkd : |jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z| ≤ |K| :=
    (hK s hs z).trans (le_abs_self K)
  have hld : |jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z| ≤ |L| :=
    (hL s hs z).trans (le_abs_self L)
  have hd : HasDerivAt (fun y => jet β (cdf (D.μ : Measure ℝ)) (j + 1) s y ^ n)
      ((n : ℝ) * jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z ^ (n - 1) *
        jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z) z :=
    (jet_hasDerivAt D j s hs z).pow n
  refine ⟨hd.differentiableAt, ?_, ?_⟩
  · rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) hkd n).trans
      (le_add_of_nonneg_right (by positivity))
  · rw [hd.deriv, abs_mul, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have H : (n : ℝ) * |jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z| ^ (n - 1) *
        |jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z| ≤
          (n : ℝ) * |K| ^ (n - 1) * |L| := by gcongr
    exact H.trans (le_add_of_nonneg_left (by positivity))

private theorem half_jet_quadratic_bounds {k : ℝ} (hk : |k| ≤ 1 / 2) :
    |riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0| ≤ 3 * k ^ 2 ∧
      |wickJet (1 / 2) k - wickJet (1 / 2) 0| ≤ 3 * k ^ 2 := by
  have h2 := (half_jet_bounds hk).1
  have h4 : k ^ 4 ≤ k ^ 2 := by
    nlinarith only [mul_le_of_le_one_right (sq_nonneg k) h2]
  have h6 : k ^ 6 ≤ k ^ 2 := by
    have H := mul_le_mul_of_nonneg_right h4 (sq_nonneg k)
    nlinarith only [H, h4]
  constructor
  · rw [riccati_jet_evaluation _ _ (by norm_num)]
    norm_num only [riccati2, riccati4, c6]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg k, pow_nonneg (sq_nonneg k) 2,
      pow_nonneg (sq_nonneg k) 3]
  · rw [wick_jet_evaluation _ _ (by norm_num)]
    norm_num only [wick2, wick4]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg k, pow_nonneg (sq_nonneg k) 2]

private theorem cubic_linear_bound {A X Y cr cw x y R W k : ℝ}
    (hA : 0 ≤ A) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hcr : |cr| ≤ A) (hcw : |cw| ≤ A) (hx : |x| ≤ X) (hy : |y| ≤ Y)
    (hR : |R| ≤ 3 * k ^ 2) (hW : |W| ≤ 3 * k ^ 2) :
    |cr * x * R + cw * y * W| ≤ 3 * A * (X + Y) * k ^ 2 := by
  calc
    _ ≤ |cr| * |x| * |R| + |cw| * |y| * |W| := by
      simpa only [abs_mul] using abs_add_le (cr * x * R) (cw * y * W)
    _ ≤ A * X * (3 * k ^ 2) + A * Y * (3 * k ^ 2) := by gcongr
    _ = _ := by ring

theorem coreCoefficientControl_of_scalarData {β : ℝ} (D : ScalarData β) :
    CoreCoefficientControl β (cdf (D.μ : Measure ℝ)) := by
  obtain ⟨Q, hQ, HQ⟩ := uniform_power_C1 D 1 2
  obtain ⟨R, hR, HR⟩ := uniform_power_C1 D 1 3
  obtain ⟨W, hW, HW⟩ := uniform_power_C1 D 2 2
  let A : ℝ := (β ^ 2) ^ 3
  let c : ℝ := β ^ 4 / 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  refine ⟨c * Q + 3 * A * (R + W), by positivity, ?_⟩
  intro s hs k hk z
  obtain ⟨hdQ, hbQ, hbQ'⟩ := HQ s hs z
  obtain ⟨hdR, hbR, hbR'⟩ := HR s hs z
  obtain ⟨hdW, hbW, hbW'⟩ := HW s hs z
  obtain ⟨hkR, hkW⟩ := half_jet_quadratic_bounds hk
  let a := cdf (D.μ : Measure ℝ) s
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hcr : |a ^ 2 * A| ≤ A := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg hA]
    have hsq : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
    exact mul_le_of_le_one_left hA hsq
  have hcw : |a * A| ≤ A := by
    rw [abs_mul, abs_of_nonneg ha.1, abs_of_nonneg hA]
    exact mul_le_of_le_one_left hA ha.2
  have hqeq : cornerQuadratic β (cdf (D.μ : Measure ℝ)) s =
      fun y => c * jet β (cdf (D.μ : Measure ℝ)) 2 s y ^ 2 := by
    funext y
    dsimp only [cornerQuadratic, c]
    ring
  have hqd := hdQ.hasDerivAt.const_mul c
  have hgd : HasDerivAt (fun y => a ^ 2 * A * jet β (cdf (D.μ : Measure ℝ)) 2 s y ^ 3 *
      (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
      a * A * jet β (cdf (D.μ : Measure ℝ)) 3 s y ^ 2 *
      (wickJet (1 / 2) k - wickJet (1 / 2) 0))
      (a ^ 2 * A * deriv (fun y => jet β (cdf (D.μ : Measure ℝ)) 2 s y ^ 3) z *
        (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
      a * A * deriv (fun y => jet β (cdf (D.μ : Measure ℝ)) 3 s y ^ 2) z *
        (wickJet (1 / 2) k - wickJet (1 / 2) 0)) z :=
    ((hdR.hasDerivAt.const_mul (a ^ 2 * A)).mul_const
    (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0)).add
      ((hdW.hasDerivAt.const_mul (a * A)).mul_const
        (wickJet (1 / 2) k - wickJet (1 / 2) 0))
  have hq : |cornerQuadratic β (cdf (D.μ : Measure ℝ)) s z| ≤ c * Q := by
    rw [hqeq, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hbQ hc
  have hq' : |deriv (cornerQuadratic β (cdf (D.μ : Measure ℝ)) s) z| ≤ c * Q := by
    rw [hqeq, hqd.deriv, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hbQ' hc
  have hg : |cornerCubic β (cdf (D.μ : Measure ℝ)) s k z| ≤ 3 * A * (R + W) * k ^ 2 :=
    cubic_linear_bound hA hR hW hcr hcw hbR hbW hkR hkW
  have hg' : |deriv (cornerCubic β (cdf (D.μ : Measure ℝ)) s k) z| ≤
      3 * A * (R + W) * k ^ 2 := by
    change |deriv (fun y => a ^ 2 * A * jet β (cdf (D.μ : Measure ℝ)) 2 s y ^ 3 *
      (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0) +
      a * A * jet β (cdf (D.μ : Measure ℝ)) 3 s y ^ 2 *
      (wickJet (1 / 2) k - wickJet (1 / 2) 0)) z| ≤ _
    rw [hgd.deriv]
    exact cubic_linear_bound hA hR hW hcr hcw hbR' hbW' hkR hkW
  refine ⟨hq.trans (le_add_of_nonneg_right (by positivity)),
    hq'.trans (le_add_of_nonneg_right (by positivity)),
    hg.trans ?_, hg'.trans ?_⟩ <;> nlinarith [mul_nonneg (mul_nonneg hc hQ) (sq_nonneg k)]

private theorem cubic_moment_eq_denominator {β : ℝ} (D : ScalarData β)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    scalarLaw β (cdf (D.μ : Measure ℝ)) s
        (fun z => jet β (cdf (D.μ : Measure ℝ)) 2 s z ^ 3) =
      FRSB.quotientDenominator β (Bridge.overlapMeasure D.μ D.mass_one) s := by
  have H := Bridge.scalarLaw_jet_power_eq β (Bridge.overlapMeasure D.μ D.mass_one) 1 3 s hs
  simpa only [Bridge.realMeasure_overlapMeasure, FRSB.quotientDenominator,
    FRSB.quotientDenominatorPolynomial, FRSB.moment_X_pow] using H

theorem uniformCornerMass_of_scalarData {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    UniformCornerMass β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  have hβ : β ≠ 0 := by
    intro he
    have H := D.contact₁ (D.q / 2) ⟨by linarith [D.q_mem.1], by linarith [D.q_mem.1]⟩
    have hz : β ^ 2 = 0 := by simp only [he, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [hz, zero_mul] at H
    norm_num at H
  let μ := Bridge.overlapMeasure D.μ D.mass_one
  have hJ : Icc (l / 2) u ⊆ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], ht.2.trans (hu.le.trans D.q_mem.2.le)⟩
  have hcont := (FRSB.continuousOn_quotientDenominator β hβ μ).mono hJ
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (l / 2) u).Nonempty from ⟨l / 2, le_rfl, by linarith⟩) hcont
  have ht₀pos := FRSB.quotientDenominator_pos β hβ μ t₀ (hJ ht₀)
  obtain ⟨c, T, hc, hT, Hc⟩ := D.lin_lower
  let t₁ : ℝ := min T (l / 2)
  have ht₁ : 0 < t₁ := lt_min hT (by positivity)
  have hlin := Hc t₁ ⟨ht₁.le, min_le_left _ _⟩
  let A := c * t₁
  have hA : 0 < A := mul_pos hc ht₁
  refine ⟨A ^ 2 * (β ^ 2) ^ 3 * FRSB.quotientDenominator β μ t₀, l / 2,
    mul_pos (mul_pos (sq_pos_of_pos hA) (pow_pos (sq_pos_of_ne_zero hβ) 3)) ht₀pos,
    by positivity, ?_⟩
  intro r hr h hh hh₀
  have hsJ : r - h ∈ Icc (l / 2) u := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hAl : A ≤ cdf (D.μ : Measure ℝ) (r - h) := hlin.trans
    ((cdf (D.μ : Measure ℝ)).mono (show t₁ ≤ r - h from
      (min_le_right _ _).trans hsJ.1))
  have hAsq : A ^ 2 ≤ cdf (D.μ : Measure ℝ) (r - h) ^ 2 :=
    pow_le_pow_left₀ hA.le hAl 2
  rw [cornerMass, cubic_moment_eq_denominator D _ (hJ hsJ)]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAsq (by positivity : 0 ≤ (β ^ 2) ^ 3)) ht₀pos.le).trans
      (mul_le_mul_of_nonneg_left (hmin hsJ) (by positivity))

theorem corner_moments_of_step_path_average {β : ℝ} (D : ScalarData β)
    (r h : ℝ) (hs : r - h ∈ Icc (0 : ℝ) 1)
    (αn : ℕ → ℝ → ℝ) (F : ℕ → ℝ → ℝ) (l : ℕ → List (ℝ × ℝ≥0))
    (hn : ∀ n z, αn n z ∈ Icc (0 : ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) (cdf (D.μ : Measure ℝ))) atTop (𝓝 0))
    (hF : ∀ n, BoundedDerivs (F n)) (K : ℝ≥0) (hFK : ∀ n, LipschitzWith K (F n))
    (hFf : TendstoUniformly F (Phi β (cdf (D.μ : Measure ℝ)) (r - h)) atTop)
    (hm : ∀ n p, p ∈ l n → p.1 ∈ Icc (0 : ℝ) 1)
    (hdur : ∀ n, chainDuration (l n) = Real.toNNReal (r - h))
    (hmodel : ∀ n, TimeChainModels (αn n) 0 (l n))
    (hrep : ∀ N g, cornerAverage β (cdf (D.μ : Measure ℝ)) r h N g =
      scalarTimeChainAverage β (l N) (F N) g 0) :
    (Tendsto (fun N => cornerAverage β (cdf (D.μ : Measure ℝ)) r h N
      (fun z => jet β (cdf (D.μ : Measure ℝ)) 2 (r - h) z ^ 2)) atTop
      (𝓝 (scalarLaw β (cdf (D.μ : Measure ℝ)) (r - h)
        (fun z => jet β (cdf (D.μ : Measure ℝ)) 2 (r - h) z ^ 2)))) ∧
    (Tendsto (fun N => cornerAverage β (cdf (D.μ : Measure ℝ)) r h N
      (fun z => jet β (cdf (D.μ : Measure ℝ)) 2 (r - h) z ^ 3)) atTop
      (𝓝 (scalarLaw β (cdf (D.μ : Measure ℝ)) (r - h)
        (fun z => jet β (cdf (D.μ : Measure ℝ)) 2 (r - h) z ^ 3)))) ∧
    (Tendsto (fun N => cornerAverage β (cdf (D.μ : Measure ℝ)) r h N
      (fun z => jet β (cdf (D.μ : Measure ℝ)) 3 (r - h) z ^ 2)) atTop
      (𝓝 (scalarLaw β (cdf (D.μ : Measure ℝ)) (r - h)
        (fun z => jet β (cdf (D.μ : Measure ℝ)) 3 (r - h) z ^ 2)))) := by
  have hα : ∀ z, cdf (D.μ : Measure ℝ) z ∈ Icc (0 : ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have ht : Real.toNNReal (r - h) ≤ 1 := Real.toNNReal_le_one.mpr hs.2
  have hf : BoundedDerivs (Phi β (cdf (D.μ : Measure ℝ)) (r - h)) :=
    scalarCDFValue_regular β hα (cdf _).mono _ _
      (Real.toNNReal_le_one.mpr (by linarith [hs.1]))
  have hfK : LipschitzWith 1 (Phi β (cdf (D.μ : Measure ℝ)) (r - h)) :=
    scalarCDFValue_lipschitz β hα (cdf _).mono _ _
      (Real.toNNReal_le_one.mpr (by linarith [hs.1]))
  have hFK' : ∀ n, LipschitzWith (max K 1) (F n) :=
    fun n => (hFK n).weaken (le_max_left _ _)
  have hfK' : LipschitzWith (max K 1) (Phi β (cdf (D.μ : Measure ℝ)) (r - h)) :=
    hfK.weaken (le_max_right _ _)
  have H (g : ℝ → ℝ) (hg : BLTest g) :
      Tendsto (fun N => cornerAverage β (cdf (D.μ : Measure ℝ)) r h N g) atTop
        (𝓝 (scalarLaw β (cdf (D.μ : Measure ℝ)) (r - h) g)) := by
    obtain ⟨L, B, hL, hB⟩ := hg
    have He := Prefix.step_path_average_tendsto β hα (cdf _).mono hn hnm hD
      hF hf hFK' hfK' hL hB hFf l hm 0 _ ht le_rfl
      (by rw [zero_add, Real.coe_toNNReal _ hs.1]; exact hs.2)
      hdur hmodel 0
    simpa only [← hrep, scalarLaw] using He
  exact ⟨H _ (jet_power_test D 1 2 _ hs), H _ (jet_power_test D 1 3 _ hs),
    H _ (jet_power_test D 2 2 _ hs)⟩

theorem cornerInputs_of_coreIdentity {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q)
    (hcore : CoreIdentity β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpen : PenaltyBound β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hprefix : PrefixMomentConvergence β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    LocalCubicGap β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      LocalBoundaryControl β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  have hcoeff := coreCoefficientControl_of_scalarData D
  have hexp := cornerExpansion_of_coreIdentity D hl hu hcore hpen hcoeff hprefix
  have hmass := uniformCornerMass_of_scalarData D hl hlu hu
  refine ⟨localCubicGap_of_cornerExpansion hl hu D.q_mem.2 hexp hmass hcore hpen hcoeff, ?_⟩
  exact localBoundaryControl_of_coreIdentity
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (cdf _).mono
    hl hu D.q_mem.2 hcore hpen hcoeff

end SKBarriers2
