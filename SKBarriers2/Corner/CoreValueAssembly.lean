module

public import SKBarriers2.Corner.CoreValue
public import SKBarriers2.Corner.FrozenCore
public import SKBarriers2.Corner.FrozenTransport
public import SKBarriers2.Corner.MassVariationAnalytic

@[expose] public section

noncomputable section
open scoped Topology
open Filter Set MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

private theorem interpolatedBoundary_zero_eq_frozenBoundary
    (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) (z : ℝ) :
    interpolatedBoundary β α a 0 p s h k N z = frozenBoundary β α a p s h k N z := by
  rw [frozenBoundary_eq_lambda_zero]
  rfl

theorem scalarData_coreValue_of_frozenRemainder_massVariation {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hfr : FrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hmv : MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CoreValue β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  obtain ⟨Cfr, Hfr, κfr, hCfr, hHfr, hκfr, hκhalf, hfr⟩ :=
    frozenCore_finite_of_remainder hfr
  obtain ⟨Cmv, Hmv, κmv, hCmv, hHmv, hκmv, hmv⟩ := hmv
  refine ⟨Cfr + Cmv, min Hfr (min Hmv ((D.q - u) / 3)), min κfr κmv,
    add_pos_of_pos_of_nonneg hCfr hCmv,
    lt_min hHfr (lt_min hHmv (by positivity)), lt_min hκfr hκmv, ?_⟩
  intro r hr h hh hhsmall k hk ε hε
  have hhfr : h ≤ Hfr := hhsmall.trans (min_le_left _ _)
  have hhmv : h ≤ Hmv := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hht : h ≤ (D.q - u) / 3 := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hkfr : |k| ≤ κfr := hk.trans (min_le_left _ _)
  have hkmv : |k| ≤ κmv := hk.trans (min_le_right _ _)
  have hkhalf : |k| ≤ 1 / 2 := hkfr.trans hκhalf
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hr.1, hr.2, D.q_mem.2]
  have hPhi : BoundedDerivs (Phi β α ((r - h) + 4 * h)) := scalarData_phi_regular D ht
  filter_upwards [hmv r hr h hh hhmv k hkmv ε hε, eventually_gt_atTop (0 : ℕ)] with N hmvN hN z
  have hfrN := hfr r hr h hh hhfr k hkfr N hN hPhi z
  rw [frozenPenalty_eq α (r - h) h k hN hh.le hkhalf] at hfrN
  have hfrN' :
      |(interpolatedBoundary β α (α (r - h)) 0 (1 / 2) (r - h) h k N z -
          interpolatedBoundary β α (α (r - h)) 0 (1 / 2) (r - h) h 0 N z) -
        (cornerQuadratic β α (r - h) z *
            (h ^ 2 * α (r - h) * penaltyPolynomial (1 / 2) k) +
          h ^ 3 * cornerCubic β α (r - h) k z)| ≤ Cfr * frozenError h k := by
    simpa only [interpolatedBoundary_zero_eq_frozenBoundary] using hfrN
  have hsplit : cornerV β α r h k N z -
      (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
        h ^ 3 * cornerCubic β α (r - h) k z) =
      ((interpolatedBoundary β α (α (r - h)) 0 (1 / 2) (r - h) h k N z -
          interpolatedBoundary β α (α (r - h)) 0 (1 / 2) (r - h) h 0 N z) -
        (cornerQuadratic β α (r - h) z *
            (h ^ 2 * α (r - h) * penaltyPolynomial (1 / 2) k) +
          h ^ 3 * cornerCubic β α (r - h) k z)) +
      (cornerMassVariation β α r h k N z -
        cornerQuadratic β α (r - h) z * cornerMassVariationPenalty α r h k N) := by
    rw [cornerV_massVariation_split, cornerPenalty_massVariation_split α r h k hN hh.le
      (OW.repairLength_mem (by norm_num) hkhalf)]
    ring
  change |cornerV β α r h k N z -
    (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
      h ^ 3 * cornerCubic β α (r - h) k z)| ≤
    (Cfr + Cmv) * (Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3) + ε
  rw [hsplit]
  calc
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hfrN' (hmvN z))
    _ = (Cfr + Cmv) * (Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3) + ε := by
      rw [frozenError]
      ring

theorem scalarData_coreValue_of_terminal_massVariation {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hterminal : TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hmv : MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CoreValue β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact scalarData_coreValue_of_frozenRemainder_massVariation D hl hu
    (scalarData_frozenRemainderBound_of_terminal D hl hu hterminal) hmv

end SKBarriers2.Corner
