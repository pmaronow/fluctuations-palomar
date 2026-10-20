module

public import SKBarriers2.Static.LocalFractional
public import SKBarriers2.Overshoot.FloorResponse

@[expose] public section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2

theorem homogeneousFloorResponse (β : ℝ) : HomogeneousFloorResponse β := by
  intro K H
  refine ⟨FloorResponse.floorResponseConstant β (K + 1),
    FloorResponse.floorResponseConstant_nonneg β (K + 1), ?_⟩
  intro α γ hα hαm hγ hγm F V hF hV hFK hdF ε L hε hL hsmall hVB hVL t ht
  let epsBound : ℝ≥0 := NNReal.mk ε hε
  let lipBound : ℝ≥0 := NNReal.mk L hL
  have hepsBound : epsBound ≤ 1 := by
    change ε ≤ 1
    linarith only [hsmall, hL]
  have hlipBound : lipBound ≤ 1 := by
    change L ≤ 1
    linarith only [hsmall, hε]
  have hdiv (f : ℝ → ℝ) (hf : ∀ z, f z ∈ Icc (0 : ℝ) 1) :
      ∀ z, f z / 3 ∈ Icc (0 : ℝ) 1 := by
    intro z
    constructor
    · exact div_nonneg (hf z).1 (by norm_num)
    · linarith [(hf z).2]
  have hdivm (f : ℝ → ℝ) (hf : Monotone f) : Monotone (fun z => f z / 3) := by
    intro z w hzw
    exact div_le_div_of_nonneg_right (hf hzw) (by norm_num)
  have hresponse := FloorResponse.scalarCDFOperator_add_homogeneous_response_of_deriv_le
    β (hdiv α hα) (hdivm α hαm) (hdiv γ hγ) (hdivm γ hγm) hF hV
    (ε := epsBound) (L := lipBound) hFK hdF hVL hVB hepsBound hlipBound 0 t ht 0
  simp only [zero_add] at hresponse
  have he : (∫ z in (0 : ℝ)..t, |γ z / 3 - α z / 3|) =
      (∫ z in Icc (0 : ℝ) (t : ℝ), |γ z - α z|) / 3 := by
    simp_rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_of_le t.coe_nonneg,
      ← integral_Icc_eq_integral_Ioc]
  have hI : 0 ≤ ∫ z in Icc (0 : ℝ) (t : ℝ), |γ z - α z| :=
    integral_nonneg (fun z => abs_nonneg (γ z - α z))
  have hdist : (∫ z in (0 : ℝ)..t, |γ z / 3 - α z / 3|) ≤
      ∫ z in Icc (0 : ℝ) (t : ℝ), |γ z - α z| :=
    he.trans_le (div_le_self hI (by norm_num))
  exact hresponse.trans (mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (FloorResponse.floorResponseConstant_nonneg β (K + 1))
      (add_nonneg hε hL)))

theorem localFractionalGap_of_cubicGap' {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    {ρ : ℕ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    (hcubic : LocalCubicGap β α I) (hfloor : FloorTrial β α 3)
    (hgeometry : LocalWindowGeometry α I)
    (hboundary : LocalBoundaryControl β α I)
    (hρlim : Tendsto ρ atTop (𝓝 0)) (hρpos : ∀ᶠ n : ℕ in atTop, 0 < ρ n) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E ∈ Ioc (0 : ℝ) E₀,
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g ∈ Ioo (0 : ℝ) g₀,
        ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S ∈ Ioc (0 : ℝ) S₀,
          LocalFractionalGap β I ρ S E g := by
  exact localFractionalGap_of_cubicGap hα hαm hmin hcubic hfloor
    (homogeneousFloorResponse β) hgeometry hboundary hρlim hρpos

theorem localFractionalGap_of_cubicGap_uniform' {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    (hcubic : LocalCubicGap β α I) (hfloor : FloorTrial β α 3)
    (hgeometry : LocalWindowGeometry α I)
    (hboundary : LocalBoundaryControl β α I) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E ∈ Ioc (0 : ℝ) E₀,
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g ∈ Ioo (0 : ℝ) g₀,
        ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S ∈ Ioc (0 : ℝ) S₀,
          ∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) →
            (∀ᶠ n : ℕ in atTop, 0 < ρ n) → LocalFractionalGap β I ρ S E g := by
  exact localFractionalGap_of_cubicGap_uniform hα hαm hmin hcubic hfloor
    (homogeneousFloorResponse β) hgeometry hboundary

end SKBarriers2
