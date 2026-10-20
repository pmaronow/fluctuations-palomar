module

public import SKBarriers2.Corner.KStability
public import SKBarriers2.Analysis.ParamChain

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

private theorem deriv_chain_diagonal (ps : List (ℝ × E)) {f : E → ℝ}
    (hf : BoundedDerivs f) (z : ℝ) :
    deriv (fun y : ℝ => vectorIncrementChain ps f (fun _ => y)) z =
      fderiv ℝ (vectorIncrementChain ps f) (fun _ => z) (fun _ => 1) := by
  have hdiag : HasDerivAt (fun y : ℝ => (fun _ : Fin 3 => y)) (fun _ => 1) z := by
    apply hasDerivAt_pi.mpr
    intro i
    exact hasDerivAt_id z
  exact (((vectorIncrementChain_regular ps hf).1.differentiable (by norm_num)
    (fun _ => z)).hasFDerivAt.comp_hasDerivAt z hdiag).deriv

theorem scalarData_boundary_parameter_regular {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ z k : ℝ, |k| ≤ 1 / 2 →
        ContDiffAt ℝ 2 (fun t => OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N z) k ∧
        ContDiffAt ℝ 2 (fun t => deriv (OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N) z) k := by
  obtain ⟨C, h₁, _, hh₁, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a₀, h₂, ha₀, hh₂, hmass⟩ := scalarData_window_mass_floor D hl hu
  let h₃ := kStabilityInteriorRadius D.q l u
  have hh₃ : 0 < h₃ := kStabilityInteriorRadius_pos hl hu
  refine ⟨min (min h₁ h₂) h₃, lt_min (lt_min hh₁ hh₂) hh₃, ?_⟩
  intro r hr h hh hh0 N hN z k hk
  have hh1 : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : h ≤ h₃ := hh0.trans (min_le_right _ _)
  have htime := kStability_time_mem hr hh.le hh3
    (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  have ht : r - h + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [htime.1, htime.2, D.q_mem.2]
  let f : E → ℝ := cornerTerminal β (cdf (D.μ : Measure ℝ)) r h
  let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
  have hf : QPotential 3 (terminalJetBound D 3) f :=
    scalarData_terminal_qPotential D 3 ht
  have hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k :=
    fun p hp => (hparam r hr h hh hh1 N hN p hp k hk).1
  have hpos : ∀ p ∈ ps, 0 < (p k).1 :=
    fun p hp => ha₀.trans_le (hmass r hr h hh hh2 N hN p hp k hk).1
  have hvalue := ParamChain.contDiffAt_curveChain ps hf (by norm_num) hreg hpos (fun _ => z)
  have hgradient := ParamChain.contDiffAt_curveChain_spatial ps hf le_rfl hreg hpos
    (fun _ => z) (fun _ => 1)
  have hv : ContDiffAt ℝ 2 (fun t => vectorIncrementChain (ps.map (fun p => p t)) f
      (fun _ => z)) k := hvalue.comp k (contDiff_id.prodMk contDiff_const).contDiffAt
  have hg : ContDiffAt ℝ 2 (fun t => fderiv ℝ
      (vectorIncrementChain (ps.map (fun p => p t)) f) (fun _ => z) (fun _ => 1)) k :=
    hgradient.comp k (contDiff_id.prodMk contDiff_const).contDiffAt
  have hboundary (t : ℝ) :
      OW.boundary β (cdf (D.μ : Measure ℝ)) (1 / 2) (r - h) h t N =
        fun y => vectorIncrementChain (ps.map (fun p => p t)) f (fun _ => y) := by
    funext y
    dsimp only [ps]
    rw [windowKCurves_apply β (cdf (D.μ : Measure ℝ)) (r - h) h t N hh.le]
    rfl
  constructor
  · convert hv using 1
    funext t
    exact congrFun (hboundary t) z
  · convert hg using 1
    funext t
    rw [hboundary t]
    exact deriv_chain_diagonal _ (hf.boundedDerivs (by norm_num)) z

end SKBarriers2.Corner
