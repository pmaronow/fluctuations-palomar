module

public import SKBarriers2.Corner.MassSensitivityC2Proof2
public import SKBarriers2.Corner.PathEnergyGenerator2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem generator12_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
      ∀ c : ℕ, c ≤ 2 →
        ‖iteratedDeriv c (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk c hc
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  have H := (hbound β h hh N i k hk).2
  interval_cases c
  · exact H.1
  · simpa only [iteratedDeriv_one] using H.2.1
  · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H.2.2

theorem scalarData_window_terminalGradientSquare_jets {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C₀ h0 kap : ℝ, 0 < C₀ ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      ∀ p ∈ windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N,
      ∀ c : Fin 3, QBoundedJets 8 (C₀*h/(N:ℝ)) (fun x =>
        iteratedDeriv c.val (fun t =>
          (fderiv ℝ (massVariationTerminal β α (r-h) h) x (p t).2)^2) k) := by
  by_cases hlu : l ≤ u
  · obtain ⟨hV,hhV,hregular⟩ :=
      scalarData_interpolated_window_curve_regular D hl hlu hu
    obtain ⟨L,hL,hdir⟩ := generator12_window_direction_bound β
    let B := terminalJetBound D 9
    let K := 1024*B^2*L^2
    let C₀ := 1+K
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hC₀ : 0 < C₀ := by dsimp only [C₀]; linarith
    refine ⟨C₀,min hV (kStabilityInteriorRadius D.q l u),1/2,hC₀,
      lt_min hhV (kStabilityInteriorRadius_pos hl hu),(by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam k hk
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let f := massVariationTerminal β α (r-h) h
    have hhV' := hh0.trans (min_le_left _ _)
    have hhI := hh0.trans (min_le_right _ _)
    have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
      have H := kStability_time_mem hr hh.le hhI
        (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
      constructor <;> linarith [H.1,H.2,D.q_mem.2]
    have hf : QPotential 9 B f := scalarData_massVariationTerminal_qPotential D 9 ht
    intro p hp c
    let w := fun t => (p t).2
    have hw : ContDiffAt ℝ 2 w k :=
      (hregular r hr h hh hhV' N hN lam hlam p hp k hk).1.snd
    have hb := hdir _ _ _ hh.le N p hp k hk
    have hw₀ : ‖w k‖ ≤ L*Real.sqrt (h/(N:ℝ)) := by
      simpa only [iteratedDeriv_zero] using hb 0 (by norm_num)
    have hw₁ : ‖deriv w k‖ ≤ L*Real.sqrt (h/(N:ℝ)) := by
      simpa only [iteratedDeriv_one] using hb 1 (by norm_num)
    have hw₂ : ‖deriv (deriv w) k‖ ≤ L*Real.sqrt (h/(N:ℝ)) := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb 2 (by norm_num)
    have H := qBoundedJets_terminalGradientSquareJet hf (w k) (deriv w k)
      (deriv (deriv w) k) hw₀ hw₁ hw₂ c
    have hscale : 1024*B^2*(L*Real.sqrt (h/(N:ℝ)))^2 ≤ C₀*h/(N:ℝ) := by
      have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
      calc
        _ = K*h/(N:ℝ) := by
          rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le hn)]
          dsimp only [K]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show K ≤ C₀ by dsimp only [C₀]; linarith) hh.le) hn
    convert H.mono hscale using 1
    funext x
    exact (terminalGradientSquareJet_eq_iteratedDeriv hw c x).symm
  · refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
