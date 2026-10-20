module

public import SKBarriers2.Corner.FrozenRowsPotential10

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.Corner

theorem scalarData_frozenRowsPotentialKBounds {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) : FrozenRowsPotentialKBounds D (Icc l u) := by
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity)
  let B := terminalJetBound D 5 + scalarTerminalJetBound D 5 + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [terminalJetBound_nonneg D 5, scalarTerminalJetBound_nonneg D 5]
  have hBt : terminalJetBound D 5 ≤ B := by
    dsimp only [B]
    linarith [scalarTerminalJetBound_nonneg D 5]
  have hBs : scalarTerminalJetBound D 5 ≤ B := by
    dsimp only [B]
    linarith [terminalJetBound_nonneg D 5]
  obtain ⟨ρ₀, L, hρ₀, hL, H⟩ := frozenCenteredModelPotential_uniform_kBounds β a₀ B ha₀ hB
  obtain ⟨hC, hhC, HC⟩ := scalarData_frozenRowsNoiseKJet_zero_centered D hl hu
  let h₀ := min hC (min (ρ₀ ^ 2) (min (l / 2) ((D.q - u) / 6)))
  have hh₀ : 0 < h₀ := lt_min hhC (lt_min (sq_pos_of_pos hρ₀)
    (lt_min (by positivity) (by positivity)))
  refine ⟨h₀, L, hh₀, hL, ?_⟩
  intro r hr h hh hhsmall z ε hε j hj k hk g
  have hhC' : h ≤ hC := hhsmall.trans (min_le_left _ _)
  have hhρ : h ≤ ρ₀ ^ 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hr.1], by linarith [hr.2, D.q_mem.2]⟩
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Icc a₀ 1 :=
    ⟨monotone_cdf _ (by linarith [hr.1]), cdf_le_one _ _⟩
  have hρsmall : Real.sqrt h ≤ ρ₀ := by
    nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h]
  have he : |ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
  have hLambda : |1 - ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have hjet (i : ℕ) (hi : 1 ≤ i) (hi5 : i ≤ 5) :
      |(1 - ε) * jet β (cdf (D.μ : Measure ℝ)) i ((r - h) + 4 * h) z| ≤ B := by
    rw [abs_mul]
    exact ((mul_le_mul hLambda (scalarData_jet_le D hi hi5 htime z)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)).trans hBs
  have hf : QPotential 5 B
      (centeredFrozenRowsTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h z ε) := by
    have HF := ((scalarData_frozenTerminal_qPotential D 5 htime).const_mul ε).translate (fun _ => z)
    apply HF.mono
    exact ((mul_le_mul_of_nonneg_right he (terminalJetBound_nonneg D 5)).trans_eq
      (one_mul _)).trans hBt
  let q : Fin 12 := ⟨j, by omega⟩
  have HB := H (cdf (D.μ : Measure ℝ) (r - h)) ha
    ((1 - ε) * jet β (cdf (D.μ : Measure ℝ)) 1 ((r - h) + 4 * h) z)
    ((1 - ε) * jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z)
    (hjet 1 le_rfl (by norm_num)) (hjet 2 (by norm_num) (by norm_num))
    (Real.sqrt h) (Real.sqrt_pos.mpr hh) hρsmall _ hf q k hk g
  have HJ := HC r hr h hh hhC' z ε
    ⟨by linarith [hε.1], by linarith [hε.2]⟩ j k hk g
  have heq : (fun t => centeredFrozenRowsPotential β (cdf (D.μ : Measure ℝ))
      (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j t g) =
      fun t => frozenCenteredModelPotential β (cdf (D.μ : Measure ℝ) (r - h))
        ((1 - ε) * jet β (cdf (D.μ : Measure ℝ)) 1 ((r - h) + 4 * h) z)
        ((1 - ε) * jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z)
        (Real.sqrt h) (centeredFrozenRowsTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h z ε)
        q t g := by
    funext t
    exact centeredFrozenRowsPotential_eq_model β (cdf (D.μ : Measure ℝ)) _ _ _ _ _ hh.le q t g
  rw [heq] at HJ
  exact ⟨HJ.1.symm ▸ HB.1, HJ.2.symm ▸ HB.2⟩

end SKBarriers2.Corner
