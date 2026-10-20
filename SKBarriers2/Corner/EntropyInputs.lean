module

public import SKBarriers2.Corner.KStability
public import SKBarriers2.Corner.MassVariationAnalytic
public import SKBarriers2.Analysis.ChainJets
public import SKBarriers2.Main.Final

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory ProbabilityTheory OAI.SK.Analytic
open SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

private theorem sample_divisor_bounds (p s h k : ℝ) (N : ℕ)
    (q : ℝ × ℝ × E) (hq : q ∈ windowMassSamples p s h k N) :
    q.2.1 ∈ Icc (1 : ℝ) 3 := by
  simp only [windowMassSamples, List.mem_append] at hq
  rcases hq with ((((hq | hq) | hq) | hq) | hq) | hq
  all_goals
    obtain ⟨j, _, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
    norm_num

private theorem frozen_entry_bounds {β a A p s h k : ℝ} {α : ℝ → ℝ}
    {N : ℕ} (hA : 0 ≤ A) (ha : A ≤ a) (ha1 : a ≤ 1)
    (q : MassPathEntry E) (hq : q ∈ windowMassPath β α a p s h k N) :
    q.1 ∈ Icc (A / 3) 1 := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
  have hc := sample_divisor_bounds p s h k N v hv
  have hcp : 0 < v.2.1 := by linarith [hc.1]
  constructor
  · apply (le_div_iff₀ hcp).mpr
    calc
      A / 3 * v.2.1 ≤ A / 3 * 3 :=
        mul_le_mul_of_nonneg_left hc.2 (by positivity)
      _ = A := by ring
      _ ≤ a := ha
  · exact (div_le_self (hA.trans ha) hc.1).trans ha1

private theorem entry_mem_true_window (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    (N : ℕ) (q : MassPathEntry E) (hq : q ∈ windowMassPath β α a p s h k N) :
    (q.1 + q.2.1, q.2.2) ∈
      (OW.window α p s h k N).map (fun v => (v.1, β • v.2)) := by
  have H : (q.1 + q.2.1, q.2.2) ∈
      massPath (windowMassPath β α a p s h k N) 1 := by
    exact List.mem_map.mpr ⟨q, hq, by simp only [one_mul]⟩
  rw [massPath_window_eq] at H
  have hprofile : interpolatedProfile α a 1 = α := by
    funext t
    dsimp only [interpolatedProfile]
    ring
  simpa only [hprofile] using H

private theorem window_inner_jets {β B a s h k lam : ℝ} {α : ℝ → ℝ} {N : ℕ}
    (hf : QPotential 10 B (massVariationTerminal β α s h))
    (hm : ∀ q ∈ massPath (windowMassPath β α a (1/2) s h k N) lam,
      q.1 ∈ Icc (0 : ℝ) 1)
    (hN : 0 < N) (hh : 0 ≤ h)
    (hh0 : h ≤ windowJetRadius 10 B β) (hk : |k| ≤ 1/2) :
    WindowInnerJets β α a (1/2) s h k N lam (B+1) := by
  let l := massPath (windowMassPath β α a (1/2) s h k N) lam
  have hB : 0 ≤ B := hf.nonneg
  have hK := stepStabilityCoefficient_nonneg 10 (by linarith : 0 ≤ B+1)
  have hE : chainEnergy l ≤ 12*β^2*h := by
    dsimp only [l]
    rw [massPath_window_eq]
    exact window_chainEnergy_le β _ s h k hN hh hk
  have hh1 : h ≤ (12*β^2*(stepStabilityCoefficient 10 (B+1)+1)+1)⁻¹ :=
    hh0.trans (min_le_left _ _)
  have hh2 : h ≤ (24*β^2*(B+1)+1)⁻¹ := hh0.trans (min_le_right _ _)
  have h1 : h*(12*β^2*(stepStabilityCoefficient 10 (B+1)+1)+1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (by simpa only [one_div] using hh1)
  have h2 : h*(24*β^2*(B+1)+1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (by simpa only [one_div] using hh2)
  have hbudget : (stepStabilityCoefficient 10 (B+1)+1)*chainEnergy l ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left hE
      (show 0 ≤ stepStabilityCoefficient 10 (B+1)+1 by positivity)
    nlinarith
  have hcurv : (B+1)*chainEnergy l ≤ 1/2 := by
    have H := mul_le_mul_of_nonneg_left hE (show 0 ≤ B+1 by positivity)
    nlinarith
  intro j _
  apply qPotential_chain_tail (l.take (j+1)) (l.drop (j+1)) hf (by norm_num)
  all_goals rw [List.take_append_drop]
  · exact hm
  · exact hbudget
  · exact hcurv

theorem scalarData_uniformWindowEntropyInputs {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    UniformWindowEntropyInputs β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  by_cases hlu : l ≤ u
  swap
  · refine ⟨0, 1, 0, 1, 1, le_rfl, by norm_num, le_rfl,
      by norm_num, by norm_num, ?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim
  obtain ⟨C, h1, hC, hh1, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a1, h2, ha1, hh2, hfloor⟩ := scalarData_window_mass_floor D hl hu
  let A := cdf (D.μ : Measure ℝ) (l/2)
  have hA : 0 < A := D.cdf_pos (by positivity)
  let B := terminalJetBound D 10
  have hB : 0 ≤ B := terminalJetBound_nonneg D 10
  let h3 := kStabilityInteriorRadius D.q l u
  let h4 := windowJetRadius 10 B β
  let h0 := min (min h1 h2) (min h3 h4)
  have hh0pos : 0 < h0 := lt_min (lt_min hh1 hh2)
    (lt_min (kStabilityInteriorRadius_pos hl hu) (windowJetRadius_pos 10 hB β))
  refine ⟨B+1, min a1 (A/3), C^2*β^2, h0, 1/2, by positivity,
    lt_min ha1 (by positivity), by positivity, hh0pos, by norm_num, ?_⟩
  intro r hr h hh hh0 k hk N hN
  have hhP : h ≤ h1 := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhF : h ≤ h2 := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhI : h ≤ h3 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhJ : h ≤ h4 := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have htime := kStability_time_mem hr hh.le hhI
    (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  have ht : (r-h)+4*h ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [htime.1, htime.2, D.q_mem.2]
  have hstart := kStability_time_mem hr hh.le hhI
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  have hAs : A ≤ cdf (D.μ : Measure ℝ) (r-h) :=
    (cdf (D.μ : Measure ℝ)).mono (by simpa only [mul_zero, add_zero] using hstart.1)
  have htrue (q : MassPathEntry E)
      (hq : q ∈ windowMassPath β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h k N) :
      q.1+q.2.1 ∈ Icc a1 1 ∧ ‖q.2.2‖^2 ≤ C^2*β^2*h/(N:ℝ) := by
    have H := entry_mem_true_window β _ _ _ _ _ _ N q hq
    rw [← windowKCurves_apply β _ (r-h) h k N hh.le] at H
    obtain ⟨p, hp, he⟩ := List.mem_map.mp H
    have hm := hfloor r hr h hh hhF N hN p hp k hk
    have hv := (hparam r hr h hh hhP N hN p hp k hk).2.2.2.1
    have hv' : ‖q.2.2‖ ≤ C * |β| * Real.sqrt (h/(N:ℝ)) := by
      simpa only [he, Prod.snd] using hv
    refine ⟨by simpa only [he, Prod.fst] using hm, ?_⟩
    have Hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hv'
    rw [mul_pow, mul_pow, sq_abs,
      Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))] at Hsq
    exact Hsq.trans_eq (by ring)
  have hentry (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
      (q : MassPathEntry E)
      (hq : q ∈ windowMassPath β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h k N) :
      q.1+lam*q.2.1 ∈ Icc (min a1 (A/3)) 1 ∧
        ‖q.2.2‖^2 ≤ C^2*β^2*h/(N:ℝ) := by
    have hf := frozen_entry_bounds hA.le hAs (cdf_le_one _ _) q hq
    obtain ⟨hm, hv⟩ := htrue q hq
    have hf0 : min a1 (A/3) ≤ q.1 := (min_le_right _ _).trans hf.1
    have hm0 : min a1 (A/3) ≤ q.1+q.2.1 := (min_le_left _ _).trans hm.1
    refine ⟨⟨?_, ?_⟩, hv⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr hf0),
        mul_nonneg hlam.1 (sub_nonneg.mpr hm0)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr hf.2),
        mul_nonneg hlam.1 (sub_nonneg.mpr hm.2)]
  refine ⟨scalarData_massVariationTerminal_regular D ht, ?_⟩
  intro lam hlam
  constructor
  · apply window_inner_jets (scalarData_massVariationTerminal_qPotential D 10 ht)
      _ (by omega) hh.le hhJ hk
    intro q hq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    have H := (hentry lam hlam v hv).1
    exact ⟨(le_of_lt (lt_min ha1 (by positivity))).trans H.1, H.2⟩
  · intro j
    exact hentry lam hlam _ (List.get_mem _ j)

end SKBarriers2.Corner
