module

public import SKBarriers2.Corner.FrozenRowsPotential19
public import SKBarriers2.Corner.FrozenRowsPotential21
public import SKBarriers2.Corner.FrozenRowsAffineGeometry4
public import SKBarriers2.Corner.FrozenRowsMixed22

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

def frozenCompletedFineLogInput (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (q j : Fin 12) (k g t : ℝ) (y : Vec3) : ℝ :=
  frozenCompletedHeadLogInput β α a s h z ε q k t
    (y + (Real.sqrt h)⁻¹ • (g • (frozenRowsHead β a h j.val k).2))

def frozenCompletedFineEndpoint (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (q j : Fin 12) (g k t : ℝ) (y : Vec3) : Vec3 :=
  let A := frozenScoreMatrix β α a s h z ε q k
  let b := frozenScoreMean β α a s h z ε q k
  let c := (frozenRowsHead β a h j.val k).2
  let χ := (1 - ε) * jet β α 2 (s + 4 * h) z
  Real.sqrt h • A y + b + g • A c + t • frozenCompletedDirection β a χ h q k

theorem scalarData_frozenCompletedFineLogInput_eq_pureChain {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ q j : Fin 12, ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ g t : ℝ, ∀ y : Vec3,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
      let f := centeredFrozenRowsTerminal β α (r - h) h z ε
      frozenCompletedFineLogInput β α a (r - h) h z ε q j k g t y =
        (a * frozenUnitMass q) * frozenCompletedSuffixChain β a χ h f q k
          (frozenCompletedFineEndpoint β α a (r - h) h z ε q j g k t y) := by
  obtain ⟨h₀,hh₀,H⟩ := scalarData_frozenCompletedHeadLogInput_eq_pureChain D hl hu
  refine ⟨h₀,hh₀,?_⟩
  intro r hr h hh hhsmall z ε hε q j k hk g t y
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let ρ := Real.sqrt h
  let R := centeredFrozenRowsQuadratic β α (r - h) h z ε
  let tail := (frozenSchedule β a (1 / 2) h k).drop q.val
  let c := (frozenRowsHead β a h j.val k).2
  let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
  have hρ : ρ ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hshift : ρ • (y + ρ⁻¹ • (g • c)) = ρ • y + g • c := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hρ,one_smul]
  have hpoint : gaussianPathMean tail R (ρ • (y + ρ⁻¹ • (g • c))) +
      t • frozenCompletedDirection β a χ h q k =
      frozenCompletedFineEndpoint β α a (r - h) h z ε q j g k t y := by
    rw [hshift,gaussianPathMean_shift,frozenScore_path_mean_linear]
    simp only [frozenCompletedFineEndpoint,frozenScoreMatrix,frozenScoreMean,
      smul_apply,gaussianPathLinearCLM_apply]
    rfl
  have HE := H r hr h hh hhsmall z ε hε q k hk t (y + ρ⁻¹ • (g • c))
  dsimp only at HE
  rw [frozenRowsHead_mass_eq β a h k hh.le q,hpoint] at HE
  exact HE

end SKBarriers2.Corner
