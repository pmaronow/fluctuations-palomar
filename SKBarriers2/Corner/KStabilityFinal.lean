module

public import SKBarriers2.Analysis.ParamStep4
public import SKBarriers2.Corner.KStabilityChain
public import SKBarriers2.Corner.KStabilityDischarge

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem curveFirstMajorant_hfirst (K k : ℝ) (ps : List (ℝ → ℝ × E))
    (front : List (ℝ → ℝ × E)) (p : ℝ → ℝ × E) (tail : List (ℝ → ℝ × E))
    (_hsplit : ps = front ++ p :: tail) :
    curveFirstMajorant K k (p :: tail) ≤
      (1 + K * ‖(p k).2‖ ^ 2) * curveFirstMajorant K k tail +
        K * windowFirstVariationSource k p := by
  exact le_rfl

theorem windowSecondVariationSource_eq (k A : ℝ) (p : ℝ → ℝ × E) :
    windowSecondVariationSource k p A =
      secondVariationSource A (deriv (fun t => (p t).1) k)
        (deriv (deriv (fun t => (p t).1)) k)
        (p k).2 (deriv (fun t => (p t).2) k) (deriv (deriv (fun t => (p t).2)) k) := by
  rfl

theorem window_second_variation_bound {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℝ → ℝ × E) (k A H : ℝ),
      0 ≤ A → 0 ≤ H → 0 < (p k).1 → ((p k).1)⁻¹ ≤ R →
      secondVariationBound B A H (p k).1 (deriv (fun t => (p t).1) k)
        (deriv (deriv (fun t => (p t).1)) k)
        (p k).2 (deriv (fun t => (p t).2) k) (deriv (deriv (fun t => (p t).2)) k) ≤
          (1 + K * ‖(p k).2‖ ^ 2) * H + K * windowSecondVariationSource k p A := by
  obtain ⟨K, hK, hbound⟩ := secondVariationBound_le_source hB hR
  refine ⟨K, hK, ?_⟩
  intro p k A H hA hH hm hinv
  rw [windowSecondVariationSource_eq]
  exact hbound A H (p k).1 _ _ hA hH hm hinv _ _ _

theorem curveFirstMajorant_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hm : ∀ p ∈ ps, |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1)
    (hsmall : 8 * K * variationEnergy (windowVariationEnergy k) ps ≤ 1) :
    curveFirstMajorant K k ps ≤ 8 * K * variationEnergy (windowVariationEnergy k) ps := by
  have H := window_two_level_recursion_le ps k hK (curveFirstMajorant K k) (fun _ => 0)
    (curveFirstMajorant_nonneg hK k) (fun _ => le_rfl) le_rfl le_rfl hm
    (fun _ _ _ _ => le_rfl) (by
      intro front p tail hsplit
      have ha := curveFirstMajorant_nonneg hK k tail
      unfold windowSecondVariationSource
      positivity) hsmall
  exact H.1

private theorem chainEnergy_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ) :
    chainEnergy (ps.map (fun p => p k)) ≤ variationEnergy (windowVariationEnergy k) ps := by
  rw [windowVariationEnergy_sum]
  have he1 : 0 ≤ (ps.map fun p => ‖deriv (fun t => (p t).2) k‖ ^ 2).sum :=
    List.sum_nonneg (fun a ha => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _)
  have he2 : 0 ≤ (ps.map fun p => ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2).sum :=
    List.sum_nonneg (fun a ha => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _)
  simp only [chainEnergy, List.map_map, Function.comp_def]
  linarith

private theorem direction_square_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ)
    (p : ℝ → ℝ × E) (hp : p ∈ ps) :
    ‖(p k).2‖ ^ 2 ≤ variationEnergy (windowVariationEnergy k) ps := by
  apply le_trans _ (chainEnergy_le_variation ps k)
  simp only [chainEnergy, List.map_map, Function.comp_def]
  exact List.single_le_sum (fun a ha => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
    exact sq_nonneg _) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem scalarData_window_first_variation {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ K C h₀ : ℝ, 0 < K ∧ 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ k : ℝ, |k| ≤ 1 / 2 →
      let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
      ∀ front tail, ps = front ++ tail →
        QBoundedJets 3 (curveFirstMajorant K k tail)
          (fun x => deriv (fun t => vectorIncrementChain (tail.map (fun p => p t))
            (cornerTerminal β (cdf (D.μ : Measure ℝ)) r h) x) k) ∧
        curveFirstMajorant K k tail ≤ C * h := by
  obtain ⟨A, h₁, hA, hh₁, hvariation⟩ := scalarData_window_variation_budget D hl hlu hu
  obtain ⟨P, h₂, _, hh₂, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a₀, h₃, ha₀, hh₃, hmass⟩ := scalarData_window_mass_floor D hl hu
  let B := terminalJetBound D 5
  have hB : 0 ≤ B := terminalJetBound_nonneg D 5
  let K := |tiltedStabilityCoefficient 3 (B + 1)| +
    |massSensitivityJetCoefficient 2 (B + 1)| +
    |directionSensitivityCoefficient 3 (B + 1)| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hTilt : tiltedStabilityCoefficient 3 (B + 1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (massSensitivityJetCoefficient 2 (B + 1)),
      abs_nonneg (directionSensitivityCoefficient 3 (B + 1))]
  have hMass : massSensitivityJetCoefficient 2 (B + 1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (massSensitivityJetCoefficient 2 (B + 1)),
      abs_nonneg (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (directionSensitivityCoefficient 3 (B + 1))]
  have hDir : directionSensitivityCoefficient 3 (B + 1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (directionSensitivityCoefficient 3 (B + 1)),
      abs_nonneg (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (massSensitivityJetCoefficient 2 (B + 1))]
  have hS : 0 ≤ stepStabilityCoefficient 5 (B + 1) :=
    stepStabilityCoefficient_nonneg 5 (by positivity)
  let L := stepStabilityCoefficient 5 (B + 1) + 1 + 2 * (B + 1) + 8 * K + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  let h₄ := kStabilityInteriorRadius D.q l u
  have hh₄ : 0 < h₄ := kStabilityInteriorRadius_pos hl hu
  refine ⟨K, 8 * K * A, min (min h₁ h₂) (min h₃ (min h₄ (A * L + 1)⁻¹)),
    hK, by positivity, lt_min (lt_min hh₁ hh₂)
      (lt_min hh₃ (lt_min hh₄ (inv_pos.mpr (by positivity)))), ?_⟩
  intro r hr h hh hh0 N hN k hk
  have hh1 : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : h ≤ h₃ := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : h ≤ h₄ := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhinv : h ≤ (A * L + 1)⁻¹ := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
  dsimp only
  obtain ⟨henergy, hmder⟩ := hvariation r hr h hh hh1 N hN k hk
  have he : 0 ≤ variationEnergy (windowVariationEnergy k) ps :=
    variationEnergy_nonneg (fun p _ => windowVariationEnergy_nonneg k p)
  have hLE : L * variationEnergy (windowVariationEnergy k) ps ≤ 1 := by
    have hinv : h * (A * L + 1) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < A * L + 1)).mp (by simpa only [one_div] using hhinv)
    have H := mul_le_mul_of_nonneg_left henergy hL.le
    nlinarith
  have hbudget : (stepStabilityCoefficient 5 (B + 1) + 1) *
      chainEnergy (ps.map (fun p => p k)) ≤ 1 := by
    apply le_trans (mul_le_mul_of_nonneg_left (chainEnergy_le_variation ps k) (by positivity))
    apply le_trans (mul_le_mul_of_nonneg_right (show stepStabilityCoefficient 5 (B + 1) + 1 ≤ L by
      dsimp only [L]; linarith) he) hLE
  have hcurv : (B + 1) * chainEnergy (ps.map (fun p => p k)) ≤ 1 / 2 := by
    have H := mul_le_mul_of_nonneg_right (show 2 * (B + 1) ≤ L by
      dsimp only [L]; linarith) he
    have H' := mul_le_mul_of_nonneg_left (chainEnergy_le_variation ps k)
      (show 0 ≤ B + 1 by positivity)
    nlinarith
  have hsmall : 8 * K * variationEnergy (windowVariationEnergy k) ps ≤ 1 :=
    (mul_le_mul_of_nonneg_right (show 8 * K ≤ L by dsimp only [L]; linarith) he).trans hLE
  have he1 : variationEnergy (windowVariationEnergy k) ps ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right (show 1 ≤ L by dsimp only [L]; linarith) he
    nlinarith
  have hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k :=
    fun p hp => (hparam r hr h hh hh2 N hN p hp k hk).1
  have hpos : ∀ p ∈ ps, 0 < (p k).1 :=
    fun p hp => ha₀.trans_le (hmass r hr h hh hh3 N hN p hp k hk).1
  have hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B + 1) * ‖(p k).2‖ ^ 2 ≤ 1 / 2 := by
    intro p hp
    have hv2 := direction_square_le_variation ps k p hp
    have hsingle : ‖(p k).2‖ ^ 2 ≤ chainEnergy (ps.map (fun p => p k)) := by
      simp only [chainEnergy, List.map_map, Function.comp_def]
      exact List.single_le_sum (fun a ha => by
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
        exact sq_nonneg _) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    refine ⟨(hmass r hr h hh hh3 N hN p hp k hk).2, ?_, ?_⟩
    · nlinarith [norm_nonneg ((p k).2)]
    · exact (mul_le_mul_of_nonneg_left hsingle (by positivity)).trans hcurv
  have ht := kStability_time_mem hr hh.le hh4 (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  have hterminal : QPotential 5 B (cornerTerminal β (cdf (D.μ : Measure ℝ)) r h) :=
    scalarData_terminal_qPotential D 5 (by
      constructor <;> linarith [ht.1, ht.2, D.q_mem.2])
  have hwhole := curveFirstMajorant_le_variation ps k hK.le hmder hsmall
  intro front tail hsplit
  refine ⟨qBoundedJets_first_curveChain_tail (n := 2) ps hterminal hreg hpos hK.le
    hTilt hMass hDir hgeometry hbudget hcurv front tail hsplit, ?_⟩
  calc
    curveFirstMajorant K k tail ≤ curveFirstMajorant K k ps := by
      have H := curveFirstMajorant_tail_le hK.le k front tail
      rw [← hsplit] at H
      exact H
    _ ≤ 8 * K * variationEnergy (windowVariationEnergy k) ps := hwhole
    _ ≤ 8 * K * A * h := by nlinarith [mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 8 * K)]

theorem scalarData_boundaryKSecondBound_of_quantitative {β : ℝ} (D : ScalarData β)
    {l u C h₁ : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) (hh₁ : 0 < h₁)
    (hquant : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ N : ℕ, 1 ≤ N →
      ∀ z k : ℝ, |k| ≤ 1 / 2 →
        |deriv (deriv (fun t => OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N z)) k| ≤ C * h ∧
        |deriv (deriv (fun t => deriv (OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N) z)) k| ≤ C * h) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ h₁ ∧
      BoundaryKSecondBound β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ := by
  obtain ⟨h₂, hh₂, hregular⟩ := scalarData_boundary_parameter_regular D hl hlu hu
  obtain ⟨h₃, hh₃, hspatial⟩ := scalarData_boundary_spatial_uniform D hl hu
  refine ⟨min h₁ (min h₂ h₃), lt_min hh₁ (lt_min hh₂ hh₃), min_le_left _ _, ?_⟩
  intro r hr h hh hh0 N hN
  have hh1 : h ≤ h₁ := hh0.trans (min_le_left _ _)
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh3 : h ≤ h₃ := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨fun k _ z => hspatial r hr h hh hh3 N k z, ?_⟩
  intro z k hk
  obtain ⟨hv, hd⟩ := hregular r hr h hh hh2 N hN z k hk
  exact ⟨hv, hd, hquant r hr h hh hh1 N hN z k hk⟩

theorem scalarData_crudeC1_of_quantitative {β : ℝ} (D : ScalarData β)
    {l u C h₁ : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q)
    (hC : 0 ≤ C) (hh₁ : 0 < h₁)
    (hquant : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ N : ℕ, 1 ≤ N →
      ∀ z k : ℝ, |k| ≤ 1 / 2 →
        |deriv (deriv (fun t => OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N z)) k| ≤ C * h ∧
        |deriv (deriv (fun t => deriv (OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N) z)) k| ≤ C * h) :
    CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨h₂, hh₂, _, hbound⟩ :=
    scalarData_boundaryKSecondBound_of_quantitative D hl hlu hu hh₁ hquant
  let h₃ := kStabilityInteriorRadius D.q l u
  have hh₃ : 0 < h₃ := kStabilityInteriorRadius_pos hl hu
  apply crudeC1_of_second_parameter_bound (B := terminalJetBound D 2) hC (lt_min hh₂ hh₃)
  · intro r hr h hh hh0
    have ht := kStability_time_mem hr hh.le (hh0.trans (min_le_right _ _))
      (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
    exact scalarData_terminal_qPotential D 2 (by
      constructor <;> linarith [ht.1, ht.2, D.q_mem.2])
  · intro r hr h hh hh0 N hN
    exact hbound r hr h hh (hh0.trans (min_le_left _ _)) N hN

end SKBarriers2.Corner
