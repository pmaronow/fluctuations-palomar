module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set

namespace SKBarriers2

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def parameterVerticalDerivative (F : P × ℝ → ℝ) (x : P × ℝ) : ℝ :=
  fderiv ℝ F x (0, 1)

theorem parameterVerticalDerivative_contDiffOn {F : P × ℝ → ℝ}
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (parameterVerticalDerivative F) U :=
  (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem parameterVerticalDerivative_hasDerivAt {F : P × ℝ → ℝ}
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {p : P} {k : ℝ} (hx : (p, k) ∈ U) :
    HasDerivAt (fun t => F (p, t)) (parameterVerticalDerivative F (p, k)) k := by
  have hline : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) k :=
    (hasDerivAt_const k p).prodMk (hasDerivAt_id k)
  exact ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline

theorem compact_parameter_vertical_bounds {F : P × ℝ → ℝ}
    {K U : Set (P × ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hKU : K ⊆ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K,
      |F x| ≤ B ∧ |parameterVerticalDerivative F x| ≤ B ∧
        |parameterVerticalDerivative (parameterVerticalDerivative F) x| ≤ B ∧
        HasDerivAt (fun t => F (x.1, t)) (parameterVerticalDerivative F x) x.2 ∧
        HasDerivAt (fun t => parameterVerticalDerivative F (x.1, t))
          (parameterVerticalDerivative (parameterVerticalDerivative F) x) x.2 := by
  have hF₁ := parameterVerticalDerivative_contDiffOn hU hF
  have hF₂ := parameterVerticalDerivative_contDiffOn hU hF₁
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn (hF.continuousOn.mono hKU)
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn (hF₁.continuousOn.mono hKU)
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn (hF₂.continuousOn.mono hKU)
  refine ⟨1 + |B₀| + |B₁| + |B₂|, by positivity, ?_⟩
  intro x hx
  have h₀ : |F x| ≤ B₀ := hB₀ x hx
  have h₁ : |parameterVerticalDerivative F x| ≤ B₁ := hB₁ x hx
  have h₂ : |parameterVerticalDerivative (parameterVerticalDerivative F) x| ≤ B₂ := hB₂ x hx
  refine ⟨?_, ?_, ?_, parameterVerticalDerivative_hasDerivAt hU hF (hKU hx),
    parameterVerticalDerivative_hasDerivAt hU hF₁ (hKU hx)⟩ <;>
    linarith [le_abs_self B₀, le_abs_self B₁, le_abs_self B₂,
      abs_nonneg B₀, abs_nonneg B₁, abs_nonneg B₂]

omit [NormedSpace ℝ P] in
theorem compact_zero_slice_rectangle {K : Set P} {U : Set (P × ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hzero : K ×ˢ ({0} : Set ℝ) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ K ×ˢ Icc (-δ) δ ⊆ U := by
  obtain ⟨A, B, _, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hzero
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp
    (hB.mem_nhds (h0B (show (0 : ℝ) ∈ ({0} : Set ℝ) from rfl)))
  refine ⟨ε / 2, by positivity, ?_⟩
  rintro ⟨p, ρ⟩ ⟨hp, hρ⟩
  apply hAB
  refine ⟨hKA hp, hεB ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  have hρabs := abs_le.mpr hρ
  linarith

end SKBarriers2
