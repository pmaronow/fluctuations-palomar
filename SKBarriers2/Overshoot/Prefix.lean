module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Hierarchy.HierarchySandwich
public import OAI.Probability.SKBarriers.Gaussian.LipschitzTerminalStability
public import OAI.Probability.SKBarriers.Parisi.CDFUniformAverage
public import OAI.Probability.SKBarriers.Hierarchy.TimeChainRepresentation
public import OAI.Probability.SKBarriers.Gaussian.LipschitzChainRepresentation

@[expose] public section

/-!
Prefix estimates for memo L6 and manuscript `lem:os-prefix`.

All operators and averages below are the upstream objects. Bounds are expressed by
pointwise majorants `B` (hence apply with any available supremum norm). `BoundedDerivs`
is upstream's C² regularity condition, with bounded first and second derivatives.
No all-lean modules are used.

Scope: the sharp remainder is proved for regular terminals; terminal-law
stability and path-average convergence are proved for bounded Lipschitz tests.
The extension to all bounded continuous tests is not established here.

The manuscript floor response concerns the *difference of increments*
`(Op_γ(F+V)-Op_γ(F)) - (Op_α(F+V)-Op_α(F))`, rather than `Op_γ(f)-Op_α(f)`.
The final theorem records the upstream value/gradient estimates that are
available as inputs. They do not establish the linear L¹ floor response:
the gradient estimate has the form `2*C*D/η + 2*η`.
-/

noncomputable section
open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2.Prefix

private theorem uniform_const (g : ℝ → ℝ) :
    TendstoUniformly (fun _ : ℕ => g) g atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  exact Eventually.of_forall (fun _ _ => by simpa only [dist_self] using hε)

private theorem regular_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨C, D, hC, _, hb, _⟩ := hf.2
  refine ⟨⟨C, hC⟩, lipschitzWith_of_nnnorm_fderiv_le
    (hf.1.differentiable (by norm_num)) (fun x => ?_)⟩
  exact_mod_cast hb x

private theorem log_integral_exp_le_mean_add_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : Ω → ℝ} (hV : AEMeasurable V μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ z ∂μ, |V z| ≤ B) :
    Real.log (∫ z, Real.exp (V z) ∂μ) ≤ (∫ z, V z ∂μ) + B ^ 2 / 2 := by
  have hmem : ∀ᵐ z ∂μ, V z ∈ Icc (-B) B := by
    filter_upwards [hb] with z hz using abs_le.mp hz
  have hs := hasSubgaussianMGF_of_mem_Icc hV hmem
  have H := hs.mgf_le 1
  have hnorm : (‖B - -B‖₊ : ℝ) = 2 * B := by
    rw [coe_nnnorm, Real.norm_eq_abs]
    rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (mul_nonneg (by norm_num) hB)]
  have he : (∫ z, Real.exp (V z - ∫ y, V y ∂μ) ∂μ) =
      Real.exp (-(∫ y, V y ∂μ)) * (∫ z, Real.exp (V z) ∂μ) := by
    simp_rw [Real.exp_sub, div_eq_mul_inv]
    rw [integral_mul_const, Real.exp_neg]
    exact mul_comm _ _
  simp only [mgf, one_mul, one_pow, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, hnorm] at H
  rw [he] at H
  have H' : (∫ z, Real.exp (V z) ∂μ) ≤
      Real.exp ((∫ z, V z ∂μ) + B ^ 2 / 2) := by
    have HH := mul_le_mul_of_nonneg_left H (Real.exp_nonneg (∫ z, V z ∂μ))
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul,
      ← Real.exp_add] at HH
    calc
      _ ≤ Real.exp ((∫ z, V z ∂μ) + (2 * B / 2) ^ 2 * 1 / 2) := HH
      _ = _ := congrArg Real.exp (by ring)
  have hiE : Integrable (fun z => Real.exp (V z)) μ := by
    simpa only [one_mul] using integrable_exp_mul_of_mem_Icc hV hmem (t := 1)
  exact (Real.log_le_iff_le_exp (integral_exp_pos hiE)).mpr H'

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

/-- The finite hierarchy estimate, independent of its number of levels.
The upstream exponential sandwich and Hoeffding's lemma give the sharp `1/2`.
No ordering of the masses is required. -/
theorem hierarchy_remainder (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F G : ParameterSpace n → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |G z - F z| ≤ B) (x : ℝ) :
    |hierarchyPressure n m G x - hierarchyPressure n m F x -
      ∫ z, (G z - F z) ∂hierarchyPathLaw n m F x| ≤ B ^ 2 / 2 := by
  let : IsProbabilityMeasure (hierarchyPathLaw n m F x) :=
    hierarchyPathLaw_probability n m F hF x
  have hs := hierarchyPressure_increment_integral_sandwich n m hm hF hG x
  have H := log_integral_exp_le_mean_add_sq (hierarchyPathLaw n m F x)
    (V := fun z => G z - F z)
    (hG.1.continuous.sub hF.1.continuous).measurable.aemeasurable hB
    (ae_of_all _ hb)
  rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
  linarith [hs.2]

/-- Scalar finite-chain form, with the exact upstream tilted path average. -/
theorem scalarHierarchy_remainder (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |G z - F z| ≤ B) (x : ℝ) :
    |scalarHierarchy n m v G x - scalarHierarchy n m v F x -
      scalarHierarchyAverage n m v F (fun z => G z - F z) x| ≤ B ^ 2 / 2 := by
  have H := hierarchy_remainder n m hm
    ((hF.translate x).compCLM (coordinateLinear n v))
    ((hG.translate x).compCLM (coordinateLinear n v)) hB
    (fun z => hb (x + coordinateLinear n v z)) 0
  rw [← scalarHierarchyAverage_eq_integral n m v (g := fun z => G z - F z) hF
    (hG.1.continuous.sub hF.1.continuous) hB hb x] at H
  have hrep (f : ℝ → ℝ) :
      hierarchyPressure n m (fun z => f (x + coordinateLinear n v z)) 0 =
        scalarHierarchy n m v f x := by
    exact hierarchyPressure_scalarParameterTerminal n m v (fun _ => f) x 0
  rw [hrep G, hrep F] at H
  exact H

/-- `lem:os-prefix`, on the upstream continuum scalar operator.
The perturbation is `G - F`; thus `G = F + V` gives the memo's formula.
Regularity is stated explicitly because the upstream limit theorems require it. -/
theorem scalarCDFOperator_remainder (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K L B : ℝ≥0} (hFK : LipschitzWith K F) (hGL : LipschitzWith L G)
    (hb : ∀ z, |G z - F z| ≤ B)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFOperator β α s t G x - scalarCDFOperator β α s t F x -
      scalarCDFAverage β α s t F (fun z => G z - F z) x| ≤ (B : ℝ) ^ 2 / 2 := by
  have hGlim := (dyadicScalar_general_uniform hG hGL β hα hmono s t ht).tendsto_at x
  have hFlim := (dyadicScalar_general_uniform hF hFK β hα hmono s t ht).tendsto_at x
  have hAv := dyadicScalarAverage_tendsto_lipschitz β hα hmono hF hFK
    (hGL.sub hFK) hb s t ht x
  apply le_of_tendsto ((hGlim.sub hFlim).sub hAv).abs
  apply Eventually.of_forall
  intro n
  simp only [dyadicScalar, scalarTimeChain_eq_hierarchy, dyadicScalarAverage]
  exact scalarHierarchy_remainder _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i))
    hF hG B.coe_nonneg hb x

/-- The literal `F + V` form of the prefix estimate. -/
theorem scalarCDFOperator_add_remainder (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {F V : ℝ → ℝ} (hF : BoundedDerivs F) (hV : BoundedDerivs V)
    {B : ℝ≥0} (hb : ∀ z, |V z| ≤ B)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFOperator β α s t (fun z => F z + V z) x -
      scalarCDFOperator β α s t F x - scalarCDFAverage β α s t F V x| ≤
        (B : ℝ) ^ 2 / 2 := by
  obtain ⟨K, hFK⟩ := regular_lipschitz hF
  obtain ⟨L, hVL⟩ := regular_lipschitz hV
  simpa only [add_sub_cancel_left] using
    scalarCDFOperator_remainder β hα hmono hF (hF.add hV) hFK (hFK.add hVL)
      (fun z => by simpa only [add_sub_cancel_left] using hb z) s t ht x

private theorem scalarHierarchy_support (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G) (x : ℝ) :
    scalarHierarchyAverage n m v F (fun z => G z - F z) x ≤
      scalarHierarchy n m v G x - scalarHierarchy n m v F x := by
  have H := (hierarchyPressure_increment_sandwich n m hm
    (primitiveParameterTerminal_regular n v hF hF x)
    (primitiveParameterTerminal_regular n v hG hG x) 0).1
  have ha : hierarchyAverage n m
      (scalarParameterTerminal n v (primitivePerturbation F F) x)
      (fun z => scalarParameterTerminal n v (primitivePerturbation G G) x z -
        scalarParameterTerminal n v (primitivePerturbation F F) x z) 0 =
      scalarHierarchyAverage n m v F (fun z => G z - F z) x := by
    change hierarchyAverage n m
      (scalarParameterTerminal n v (primitivePerturbation F F) x)
      (scalarParameterTerminal n v
        (fun a z => primitivePerturbation G G a z - primitivePerturbation F F a z) x) 0 = _
    rw [hierarchyAverage_scalarParameterTerminal]
    simp only [primitivePerturbation_zero]
  rw [ha, hierarchyPressure_scalarParameterTerminal,
    hierarchyPressure_scalarParameterTerminal, primitivePerturbation_zero,
    primitivePerturbation_zero] at H
  exact H

private theorem scalarHierarchyAverage_terminal_le (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F₁ F₂ g : ℝ → ℝ} (hF₁ : BoundedDerivs F₁) (hF₂ : BoundedDerivs F₂)
    (hg : BoundedDerivs g) {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B)
    (hF : ∀ z, |F₁ z - F₂ z| ≤ ε) (hgb : ∀ z, |g z| ≤ B) (x : ℝ) :
    scalarHierarchyAverage n m v F₁ g x - scalarHierarchyAverage n m v F₂ g x ≤ B * ε := by
  let τ : ℝ := ε / B
  have hτ : 0 < τ := div_pos hε hB
  have hτB : τ * B = ε := div_mul_cancel₀ ε hB.ne'
  let H : ℝ → ℝ := fun z => F₁ z - τ * g z
  have hH : BoundedDerivs H := by
    simpa only [neg_mul, ← sub_eq_add_neg] using hF₁.add (hg.const_mul (-τ))
  have hHg : ∀ z, |H z - F₁ z| ≤ ε := by
    intro z
    dsimp only [H]
    rw [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos hτ]
    exact (mul_le_mul_of_nonneg_left (hgb z) hτ.le).trans_eq hτB
  have hδ : BoundedScalar (fun z => F₁ z - F₂ z) :=
    ⟨hF₁.1.continuous.sub hF₂.1.continuous, ε, hε.le, hF⟩
  have hbg : BoundedScalar g := ⟨hg.1.continuous, B, hB.le, hgb⟩
  have hlow := scalarHierarchy_support n m v hm hF₂ hH x
  have hR := (abs_le.mp (scalarHierarchy_remainder n m v hm hF₂ hF₁ hε.le hF x)).2
  have hT := (abs_le.mp (scalarHierarchy_remainder n m v hm hF₁ hH hε.le hHg x)).2
  have hobs : (fun z => H z - F₂ z) =
      fun z => (F₁ z - F₂ z) - τ * g z := by
    funext z
    dsimp only [H]
    ring
  have hobs' : (fun z => H z - F₁ z) = fun z => (-τ) * g z := by
    funext z
    dsimp only [H]
    ring
  rw [hobs, scalarHierarchyAverage_sub hF₂ hδ (hbg.const_mul τ),
    scalarHierarchyAverage_const_mul hF₂ hbg] at hlow
  rw [hobs', scalarHierarchyAverage_const_mul hF₁ hbg] at hT
  have hprod : τ * (scalarHierarchyAverage n m v F₁ g x -
      scalarHierarchyAverage n m v F₂ g x) ≤ ε ^ 2 := by
    linarith
  apply (mul_le_mul_iff_right₀ hτ).mp
  calc
    _ ≤ ε ^ 2 := hprod
    _ = τ * (B * ε) := by rw [← mul_assoc, hτB]; ring

/-- Sharp finite terminal stability. This is also a consequence of the sharp
quadratic prefix estimate and the supporting-hyperplane inequality. -/
theorem scalarHierarchyAverage_terminal_stability_regular (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F₁ F₂ g : ℝ → ℝ} (hF₁ : BoundedDerivs F₁) (hF₂ : BoundedDerivs F₂)
    (hg : BoundedDerivs g) {ε B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hF : ∀ z, |F₁ z - F₂ z| ≤ ε) (hgb : ∀ z, |g z| ≤ B) (x : ℝ) :
    |scalarHierarchyAverage n m v F₁ g x - scalarHierarchyAverage n m v F₂ g x| ≤ B * ε := by
  rcases hε.eq_or_lt with heq | hεpos
  · have he : F₁ = F₂ := funext (fun z => sub_eq_zero.mp
      (abs_eq_zero.mp (le_antisymm (heq ▸ hF z) (abs_nonneg _))))
    rw [he, sub_self, abs_zero]
    exact mul_nonneg hB hε
  rcases hB.eq_or_lt with heq | hBpos
  · have he : g = fun _ => 0 := funext (fun z =>
      abs_eq_zero.mp (le_antisymm (heq ▸ hgb z) (abs_nonneg _)))
    have hz (f : ℝ → ℝ) (hf : BoundedDerivs f) :
        scalarHierarchyAverage n m v f g x = 0 := by
      rw [he, scalarHierarchyAverage_eq_integral n m v hf continuous_const
        (B := 0) le_rfl (fun _ => by norm_num)]
      simp only [integral_zero]
    rw [hz F₁ hF₁, hz F₂ hF₂, sub_self, abs_zero]
    exact mul_nonneg hB hε
  apply abs_sub_le_iff.mpr
  exact ⟨scalarHierarchyAverage_terminal_le n m v hm hF₁ hF₂ hg hεpos hBpos hF hgb x,
    scalarHierarchyAverage_terminal_le n m v hm hF₂ hF₁ hg hεpos hBpos
      (fun z => (abs_sub_comm (F₂ z) (F₁ z)) ▸ hF z) hgb x⟩

private theorem doubleWindow_regular {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0 < h) :
    BoundedDerivs (scalarWindow (scalarWindow g h) h) := by
  have hS : Continuous (scalarWindow g h) := (scalarWindow_lipschitz hg hh).continuous
  have hd (x : ℝ) : HasDerivAt (scalarWindowDerivative (scalarWindow g h) h)
      (scalarWindowDerivative (scalarWindowDerivative g h) h x) x := by
    convert (((scalarWindow_hasDerivAt hg.continuous h (x + h)).comp x
      ((hasDerivAt_id x).add_const h)).sub
        (scalarWindow_hasDerivAt hg.continuous h x)).div_const h using 1
    · rfl
    · simp only [scalarWindowDerivative, mul_one]
  have hC : 0 ≤ 2 * (L : ℝ) / h := div_nonneg (by positivity) hh.le
  exact boundedDerivs_of_derivatives (scalarWindow_hasDerivAt hS h) hd
    (scalarWindowDerivative_continuous (scalarWindowDerivative_continuous hg.continuous h) h)
    (B := L) (C := ⟨2 * (L : ℝ) / h, hC⟩)
    (scalarWindowDerivative_lipschitz_bound (scalarWindow_lipschitz hg hh) hh)
    (scalarWindowDerivative_bound (scalarWindowDerivative_lipschitz_bound hg hh) hh)

private theorem doubleWindow_approx {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |scalarWindow (scalarWindow g h) h x - g x| ≤ 2 * (L : ℝ) * h := by
  have h₁ := scalarWindow_approx (scalarWindow_lipschitz hg hh) hh x
  have h₂ := scalarWindow_approx hg hh x
  exact (abs_sub_le _ (scalarWindow g h x) _).trans (by linarith)

/-- Sharp finite terminal stability for any bounded Lipschitz observable.
Double averaging removes the C² hypothesis on the observable. -/
theorem scalarHierarchyAverage_terminal_stability (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F₁ F₂ g : ℝ → ℝ} (hF₁ : BoundedDerivs F₁) (hF₂ : BoundedDerivs F₂)
    {L B : ℝ≥0} (hg : LipschitzWith L g) {ε : ℝ} (hε : 0 ≤ ε)
    (hF : ∀ z, |F₁ z - F₂ z| ≤ ε) (hgb : ∀ z, |g z| ≤ B) (x : ℝ) :
    |scalarHierarchyAverage n m v F₁ g x - scalarHierarchyAverage n m v F₂ g x| ≤ (B : ℝ) * ε := by
  apply le_of_forall_pos_le_add
  intro η hη
  let h : ℝ := η / (8 * ((L : ℝ) + 1))
  have hh : 0 < h := by dsimp only [h]; positivity
  let a : ℝ → ℝ := scalarWindow (scalarWindow g h) h
  have haB : ∀ z, |a z| ≤ B :=
    scalarWindow_bound (scalarWindow_lipschitz hg hh).continuous
      (scalarWindow_bound hg.continuous hgb hh) hh
  have happrox : ∀ z, |g z - a z| ≤ 2 * (L : ℝ) * h := by
    intro z
    rw [abs_sub_comm]
    exact doubleWindow_approx hg hh z
  have hA (f : ℝ → ℝ) (hf : BoundedDerivs f) :
      |scalarHierarchyAverage n m v f g x - scalarHierarchyAverage n m v f a x| ≤
        2 * (L : ℝ) * h :=
    scalarHierarchyAverage_observable_distance hf
      ⟨hg.continuous, B, B.coe_nonneg, hgb⟩
      ⟨(scalarWindow_lipschitz (scalarWindow_lipschitz hg hh) hh).continuous,
        B, B.coe_nonneg, haB⟩ (by positivity) happrox n m v x
  have H := scalarHierarchyAverage_terminal_stability_regular n m v hm hF₁ hF₂
    (doubleWindow_regular hg hh) hε B.coe_nonneg hF haB x
  have herr : 4 * (L : ℝ) * h ≤ η := by
    have he : 8 * ((L : ℝ) + 1) * h = η := by dsimp only [h]; field_simp
    nlinarith [L.coe_nonneg]
  calc
    _ ≤ |scalarHierarchyAverage n m v F₁ g x - scalarHierarchyAverage n m v F₁ a x| +
        |scalarHierarchyAverage n m v F₁ a x - scalarHierarchyAverage n m v F₂ g x| :=
      abs_sub_le _ _ _
    _ ≤ |scalarHierarchyAverage n m v F₁ g x - scalarHierarchyAverage n m v F₁ a x| +
        (|scalarHierarchyAverage n m v F₁ a x - scalarHierarchyAverage n m v F₂ a x| +
          |scalarHierarchyAverage n m v F₂ a x - scalarHierarchyAverage n m v F₂ g x|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ 2 * (L : ℝ) * h + ((B : ℝ) * ε + 2 * (L : ℝ) * h) := by
      rw [abs_sub_comm (scalarHierarchyAverage n m v F₂ a x)]
      exact add_le_add (hA F₁ hF₁) (add_le_add H (hA F₂ hF₂))
    _ ≤ (B : ℝ) * ε + η := by linarith

/-- Memo L6's sharp terminal-law estimate for bounded Lipschitz test functions. -/
theorem scalarCDFAverage_terminal_stability (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {F₁ F₂ g : ℝ → ℝ} (hF₁ : BoundedDerivs F₁) (hF₂ : BoundedDerivs F₂)
    {A B : ℝ≥0} (hgA : LipschitzWith A g)
    {ε : ℝ} (hε : 0 ≤ ε) (hF : ∀ z, |F₁ z - F₂ z| ≤ ε)
    (hgb : ∀ z, |g z| ≤ B) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFAverage β α s t F₁ g x - scalarCDFAverage β α s t F₂ g x| ≤ (B : ℝ) * ε := by
  obtain ⟨K, hF₁K⟩ := regular_lipschitz hF₁
  obtain ⟨L, hF₂L⟩ := regular_lipschitz hF₂
  have h₁ := dyadicScalarAverage_tendsto_lipschitz β hα hmono hF₁ hF₁K hgA hgb s t ht x
  have h₂ := dyadicScalarAverage_tendsto_lipschitz β hα hmono hF₂ hF₂L hgA hgb s t ht x
  apply le_of_tendsto (h₁.sub h₂).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i))
    hF₁ hF₂ hgA hε hF hgb x)

/-- Convergence of the upstream dyadic step-profile path averages on bounded
Lipschitz tests. The test need not be differentiable. -/
theorem dyadic_path_average_tendsto (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {F g : ℝ → ℝ} (hF : BoundedDerivs F) {K L B : ℝ≥0}
    (hFK : LipschitzWith K F) (hgL : LipschitzWith L g) (hgB : ∀ z, |g z| ≤ B)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t F g x) atTop
      (𝓝 (scalarCDFAverage β α s t F g x)) :=
  dyadicScalarAverage_tendsto_lipschitz β hα hmono hF hFK hgL hgB s t ht x

/-- Varying baseline terminals in the dyadic path law, as needed for `ν_N`.
Terminal convergence is an explicit input to be supplied by the zero-tent
factorization. No uniform derivative bound on the varying terminals is needed. -/
theorem dyadic_path_average_varying_terminal (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF : ∀ n, BoundedDerivs (F n)) (hf : BoundedDerivs f)
    {K L B : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hgB : ∀ z, |g z| ≤ B)
    (hFf : TendstoUniformly F f atTop)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t (F n) g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  have hd : Tendsto (fun n => dyadicScalarAverage β α n s t (F n) g x -
      dyadicScalarAverage β α n s t f g x) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let η : ℝ := ε / ((B : ℝ) + 1)
    have hη : 0 < η := by dsimp only [η]; positivity
    filter_upwards [Metric.tendstoUniformly_iff.mp hFf η hη] with n hn
    have H := scalarHierarchyAverage_terminal_stability
      (dyadicIntervals α n s t).length
      (fun i => ((dyadicIntervals α n s t).get i).1)
      (fun i => β * Real.sqrt (((dyadicIntervals α n s t).get i).2 : ℝ))
      (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i))
      (hF n) hf hgL hη.le
      (fun z => by simpa only [Real.dist_eq, abs_sub_comm] using (hn z).le) hgB x
    change |dyadicScalarAverage β α n s t (F n) g x -
      dyadicScalarAverage β α n s t f g x| ≤ (B : ℝ) * η at H
    rw [Real.dist_eq, sub_zero]
    apply H.trans_lt
    have he : ((B : ℝ) + 1) * η = ε := by dsimp only [η]; field_simp
    linarith
  have H := hd.add (dyadic_path_average_tendsto β hα hmono hf hfK hgL hgB s t ht x)
  simpa only [sub_add_cancel, zero_add] using H

/-- Step-profile version with the exact upstream time-chain models. Both
profile convergence and baseline-terminal convergence are visible inputs. -/
theorem step_path_average_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    (hn : ∀ n z, αn n z ∈ Icc (0 : ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF : ∀ n, BoundedDerivs (F n)) (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hFK : ∀ n, LipschitzWith K (F n)) (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (hgB : ∀ z, |g z| ≤ B)
    (hFf : TendstoUniformly F f atTop)
    (l : ℕ → List (ℝ × ℝ≥0)) (hm : ∀ n p, p ∈ l n → p.1 ∈ Icc (0 : ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (hs : 0 ≤ s) (hst : s + t ≤ 1)
    (hdur : ∀ n, chainDuration (l n) = t) (hmodel : ∀ n, TimeChainModels (αn n) s (l n))
    (x : ℝ) :
    Tendsto (fun n => scalarTimeChainAverage β (l n) (F n) g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  have H := (scalarCDFAverage_tendstoUniformly_varying β hα hmono hn hnm hD
    hf hF hfK hFK hgL (fun _ => hgL) hgB (fun _ => hgB)
    hFf (uniform_const g) s t ht hs hst).tendsto_at x
  simpa only [scalarCDFAverage_eq_chainAverage_lipschitz
    (hF _) (hFK _) hgL hgB β (hn _) (hnm _) (l _) (hm _) s t ht (hdur _) (hmodel _)] using H

/-- The exact upstream profile-stability inputs. The second bound is a
finite-difference modulus, and is not the manuscript's linear floor response. -/
theorem scalar_profile_stability_inputs (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x η : ℝ) (hη : 0 < η) :
    |scalarCDFValue β α s t x - scalarCDFValue β γ s t x| ≤
        scalarTimeMassConstant β * (∫ z in s..s+t, |α z - γ z|) ∧
    |scalarCDFGradient β α s t x - scalarCDFGradient β γ s t x| ≤
        2 * (scalarTimeMassConstant β * (∫ z in s..s+t, |α z - γ z|)) / η + 2 * η := by
  exact ⟨scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm s t ht x,
    scalarCDFGradient_cdf_stability β hα hαm hγ hγm s t ht x η hη⟩

end SKBarriers2.Prefix
