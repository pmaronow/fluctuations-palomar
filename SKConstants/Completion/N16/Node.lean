module

public import SKConstants.Completion.N16.Counterexample

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.N16
open Blueprint

theorem AuxRotationStatement_holds : AuxRotationStatement := by
  intro Ω _ W δ r₀ q c s hcs
  exact replayAux_rotation W δ r₀ q c s hcs

theorem perAngleLawStatement_incompatible_with_brownianSystemExists
    (hBM : BrownianSystemExistsStatement) : ¬ PerAngleLawStatement := by
  obtain ⟨Ω, m, hW⟩ := hBM
  let := m
  obtain ⟨W⟩ := hW
  exact not_PerAngleLawStatement W

def PerAngleLawNonnegativeExponentStatement : Prop :=
  ∀ (p : Parameters), 0 ≤ p.D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω),
      ∀ᶠ n : ℕ in atTop, ∀ (θ : ℝ) (k : ℕ),
        (experimentLaw W p n).map (fun z => (z.1.1, angleInput p n θ k z)) =
          (angleLaw W p n).map (regressionInput p n) ∧
        (experimentLaw W p n).map (angleInput p n θ k) = runLaw W p n

theorem PerAngleLawNonnegativeExponentStatement_holds :
    PerAngleLawNonnegativeExponentStatement := by
  intro p hD Ω _ W
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  intro θ k
  have hδ : (smoothing p n : ℝ) ≤ 1 := by
    rw [smoothing, Real.coe_toNNReal _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  exact ⟨angle_joint_law W p n θ k hδ, angle_run_law W p n θ k hδ⟩

theorem perAngleLaw_one_twentieth_holds {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) :
    ∀ᶠ n : ℕ in atTop, ∀ (θ : ℝ) (k : ℕ),
      (experimentLaw W g0Parameters n).map
        (fun z => (z.1.1, angleInput g0Parameters n θ k z)) =
          (angleLaw W g0Parameters n).map (regressionInput g0Parameters n) ∧
      (experimentLaw W g0Parameters n).map (angleInput g0Parameters n θ k) =
        runLaw W g0Parameters n :=
  PerAngleLawNonnegativeExponentStatement_holds g0Parameters (by norm_num [g0Parameters]) W

end SKConstants.N16
