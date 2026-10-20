module

public import SKBarriers2.Corner.FrozenRowsPotential5
public import SKBarriers2.Corner.FrozenRowsPotential12
public import SKBarriers2.Corner.FrozenRowsPotential8

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

def frozenCompletedSuffixChain (β a χ h : ℝ) (f : Vec3 → ℝ)
    (j : Fin 12) (k : ℝ) (y : Vec3) : ℝ :=
  let n := 12 - (j.val + 1)
  vectorIncrementChain (List.ofFn (fun i : Fin n =>
    let q : Fin 12 := ⟨j.val + 1 + i.val, by omega⟩
    (a * frozenUnitMass q, frozenCompletedDirection β a χ h q k))) f y

theorem frozenCompletedSuffixChain_eq_actual (β a c u χ h z k : ℝ) (hh : 0 ≤ h)
    (f : Vec3 → ℝ) (j : Fin 12) (y : Vec3) :
    vectorIncrementChain
      (completedSquareSchedule ((frozenSchedule β a (1 / 2) h k).drop (j.val + 1))
        (separableTaylorQuadratic c u χ z)) f y =
      frozenCompletedSuffixChain β a χ h f j k y := by
  rw [frozenCompletedSuffixChain, completedSquareSchedule_drop,
    completedSquareSchedule_frozen β a c u χ h z k hh, list_drop_ofFn]

private theorem unitMass_pos_le (j : Fin 12) :
    0 < frozenUnitMass j ∧ frozenUnitMass j ≤ 1 := by
  fin_cases j <;> norm_num [frozenUnitMass]

set_option maxHeartbeats 0 in
theorem frozenCompletedSuffixChain_uniform_regular_kJets_order (s : ℕ) (hs : 1 ≤ s)
    (β B : ℝ) (hB : 0 < B) :
    ∃ ρ₀ L : ℝ, 0 < ρ₀ ∧ 0 ≤ L ∧
      ∀ a ∈ Ioc (0 : ℝ) 1, ∀ χ : ℝ, |χ| ≤ B →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ f : Vec3 → ℝ, QPotential (s + 4) B f →
      ∀ j : Fin 12, ∀ k ∈ frozenRowsKDomain,
      QPotential (s + 4) (B + 1) (frozenCompletedSuffixChain β a χ (ρ ^ 2) f j k) ∧
      QBoundedJets (s + 2) L
        (fun y => deriv (fun t => frozenCompletedSuffixChain β a χ (ρ ^ 2) f j t y) k) ∧
      QBoundedJets s L
        (fun y => deriv (deriv (fun t => frozenCompletedSuffixChain β a χ (ρ ^ 2) f j t y)) k) := by
  obtain ⟨M, δV, hM, hδV, HV⟩ := frozenCompletedDirection_uniform_control β
  obtain ⟨K₀, hK₀, HK₀⟩ := fixedMassSecondVariationBound_le_source s (by linarith : 0 ≤ B + 1)
  let KT := tiltedStabilityCoefficient (s + 2) (B + 1)
  let KM := massSensitivityJetCoefficient (s + 1) (B + 1)
  let KD := directionSensitivityCoefficient (s + 2) (B + 1)
  let K := 1 + K₀ + |KT| + |KM| + |KD|
  have hK : 0 < K := by dsimp only [K]; positivity
  have hK₀K : K₀ ≤ K := by dsimp only [K]; linarith [abs_nonneg KT, abs_nonneg KM, abs_nonneg KD]
  have hKT : KT ≤ K := by dsimp only [K]; linarith [le_abs_self KT, abs_nonneg KM, abs_nonneg KD]
  have hKM : KM ≤ K := by dsimp only [K]; linarith [le_abs_self KM, abs_nonneg KT, abs_nonneg KD]
  have hKD : KD ≤ K := by dsimp only [K]; linarith [le_abs_self KD, abs_nonneg KT, abs_nonneg KM]
  have hsource : ∀ A H : ℝ, 0 ≤ A → 0 ≤ H → ∀ v w b : Vec3,
      fixedMassSecondVariationBound s (B + 1) A H v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * fixedMassSecondVariationSource A v w b := by
    intro A H hA hH v w b
    apply (HK₀ A H hA hH v w b).trans
    have hn : 0 ≤ fixedMassSecondVariationSource A v w b := by
      dsimp only [fixedMassSecondVariationSource]
      positivity
    gcongr
  let S₀ := stepStabilityCoefficient (s + 4) (B + 1) + 1
  have hS₀ : 0 < S₀ := by
    dsimp only [S₀]
    linarith [stepStabilityCoefficient_nonneg (s + 4) (by linarith : 0 ≤ B + 1)]
  let S := 1 + M ^ 2 + 12 * M ^ 2 * S₀ + 24 * M ^ 2 * (B + 1)
  have hS : 0 < S := by dsimp only [S]; positivity
  let ρ₀ := min 1 (min (δV / (B + 1)) S⁻¹)
  let L := (1 + 6 * K) ^ 24
  refine ⟨ρ₀, L, lt_min (by norm_num) (lt_min (by positivity) (inv_pos.mpr hS)), by positivity, ?_⟩
  intro a ha χ hχ ρ hρ hρsmall f hf j k hk
  have hρ₁ : ρ ≤ 1 := hρsmall.trans (min_le_left _ _)
  have hρV : ρ ≤ δV / (B + 1) := (hρsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρS : ρ ≤ S⁻¹ := (hρsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hρ₂ : ρ ^ 2 ≤ ρ := by nlinarith
  have hSρ : S * ρ ≤ 1 := (mul_le_mul_of_nonneg_left hρS hS.le).trans_eq
    (mul_inv_cancel₀ hS.ne')
  have hscale : |a * χ * ρ ^ 2| ≤ δV := by
    have haabs : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2
    have H := (le_div_iff₀ (by linarith : 0 < B + 1)).mp hρV
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ)]
    calc
      _ ≤ 1 * B * ρ ^ 2 := by gcongr
      _ = B * ρ ^ 2 := by ring
      _ ≤ B * ρ := mul_le_mul_of_nonneg_left hρ₂ hB.le
      _ ≤ δV := by nlinarith
  have hsqrt : Real.sqrt (ρ ^ 2) = ρ := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  let U : Set ℝ := Ioo (-(1 / 2) : ℝ) (1 / 2)
  have hkU : k ∈ U := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  let n := 12 - (j.val + 1)
  let q : Fin n → Fin 12 := fun i => ⟨j.val + 1 + i.val, by dsimp only [n] at i; omega⟩
  let m := fun i : Fin n => a * frozenUnitMass (q i)
  let V := fun t => fun i : Fin n => frozenCompletedDirection β a χ (ρ ^ 2) (q i) t
  let V₁ := fun t => fun i : Fin n => frozenCompletedDirectionFirst β a χ (ρ ^ 2) (q i) t
  let V₂ := fun t => fun i : Fin n => frozenCompletedDirectionSecond β a χ (ρ ^ 2) (q i) t
  have Hdir (t : ℝ) (ht : t ∈ U) (i : Fin n) := HV a χ (ρ ^ 2) t hscale
    (abs_le.mpr ⟨ht.1.le, ht.2.le⟩) (q i)
  have hVjets (t : ℝ) (ht : t ∈ U) : HasDerivAt V (V₁ t) t ∧ HasDerivAt V₁ (V₂ t) t :=
    ⟨hasDerivAt_pi.mpr (fun i => (Hdir t ht i).2.2.2.1),
      hasDerivAt_pi.mpr (fun i => (Hdir t ht i).2.2.2.2.1)⟩
  have hVd : deriv V k = V₁ k ∧ deriv (deriv V) k = V₂ k := by
    have hnear : deriv V =ᶠ[𝓝 k] V₁ := by
      filter_upwards [isOpen_Ioo.mem_nhds hkU] with t ht
      exact (hVjets t ht).1.deriv
    exact ⟨(hVjets k hkU).1.deriv, hnear.deriv_eq.trans (hVjets k hkU).2.deriv⟩
  have hVc : ContDiffAt ℝ 2 V k := contDiffAt_pi.mpr (fun i => (Hdir k hkU i).2.2.2.2.2)
  have hVB (i : Fin n) : ‖V k i‖ ≤ M * ρ ∧ ‖deriv V k i‖ ≤ M * ρ ∧
      ‖deriv (deriv V) k i‖ ≤ M * ρ := by
    rw [hVd.1, hVd.2]
    simpa only [hsqrt] using
      And.intro (Hdir k hkU i).1 (And.intro (Hdir k hkU i).2.1 (Hdir k hkU i).2.2.1)
  have hMρ : M * ρ ≤ 1 := by
    have hMS : M ^ 2 ≤ S := by
      dsimp only [S]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 12 * M ^ 2) hS₀.le,
        mul_nonneg (by positivity : 0 ≤ 24 * M ^ 2) (by linarith : 0 ≤ B + 1)]
    have H := (mul_le_mul_of_nonneg_right hMS hρ.le).trans hSρ
    have HH := mul_le_mul_of_nonneg_left hρ₂ (sq_nonneg M)
    nlinarith [mul_nonneg hM.le hρ.le]
  let E := StepCalculus.chainEnergy (List.ofFn (fun i : Fin n => (m i, V k i)))
  have hE : E ≤ 12 * M ^ 2 * ρ := by
    have hsum : E ≤ (n : ℝ) * (M * ρ) ^ 2 := by
      simp only [E, StepCalculus.chainEnergy, List.map_ofFn, List.sum_ofFn]
      calc
        _ ≤ ∑ _ : Fin n, (M * ρ) ^ 2 := Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hVB i).1 2)
        _ = _ := by simp
    calc
      _ ≤ (n : ℝ) * (M * ρ) ^ 2 := hsum
      _ ≤ 12 * (M * ρ) ^ 2 := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Nat.sub_le 12 (j.val + 1))) (sq_nonneg _)
      _ = 12 * M ^ 2 * ρ ^ 2 := by ring
      _ ≤ 12 * M ^ 2 * ρ := mul_le_mul_of_nonneg_left hρ₂ (by positivity)
  have hbudget : S₀ * E ≤ 1 := by
    have hES : 12 * M ^ 2 * S₀ ≤ S := by
      dsimp only [S]
      nlinarith [sq_nonneg M,
        mul_nonneg (by positivity : 0 ≤ 24 * M ^ 2) (by linarith : 0 ≤ B + 1)]
    calc
      _ ≤ S₀ * (12 * M ^ 2 * ρ) := mul_le_mul_of_nonneg_left hE hS₀.le
      _ = (12 * M ^ 2 * S₀) * ρ := by ring
      _ ≤ S * ρ := mul_le_mul_of_nonneg_right hES hρ.le
      _ ≤ 1 := hSρ
  have hcurv : (B + 1) * E ≤ 1 / 2 := by
    have hES : 24 * M ^ 2 * (B + 1) ≤ S := by
      dsimp only [S]
      nlinarith [sq_nonneg M, mul_nonneg (by positivity : 0 ≤ 12 * M ^ 2) hS₀.le]
    have H := (mul_le_mul_of_nonneg_right hES hρ.le).trans hSρ
    have HE := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ B + 1)
    nlinarith
  have hgeo (i : Fin n) : ‖V k i‖ ≤ 1 ∧ ‖deriv V k i‖ ≤ 1 ∧
      ‖deriv (deriv V) k i‖ ≤ 1 ∧ (B + 1) * ‖V k i‖ ^ 2 ≤ 1 / 2 := by
    have hi : ‖V k i‖ ^ 2 ≤ E := by
      dsimp only [E, StepCalculus.chainEnergy]
      simp only [List.map_ofFn, List.sum_ofFn]
      exact Finset.single_le_sum (fun i _ => sq_nonneg ‖V k i‖) (Finset.mem_univ i)
    exact ⟨(hVB i).1.trans hMρ, (hVB i).2.1.trans hMρ, (hVB i).2.2.trans hMρ,
      (mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ B + 1)).trans hcurv⟩
  have hm (i : Fin n) : 0 < m i ∧ m i ≤ 1 := by
    have hi := unitMass_pos_le (q i)
    exact ⟨mul_pos ha.1 hi.1, (mul_le_mul ha.2 hi.2 hi.1.le (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
      (by ring)⟩
  have hpotential : QPotential (s + 4) (B + 1)
      (frozenCompletedSuffixChain β a χ (ρ ^ 2) f j k) := by
    have HP := qPotential_chain_uniform (List.ofFn (fun i : Fin n => (m i, V k i))) hf
      (by omega : 2 ≤ s + 4)
      (by
        intro c hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        exact ⟨(hm i).1.le, (hm i).2⟩) hbudget hcurv
    change QPotential (s + 4) (B + 1) (vectorIncrementChain
      (List.ofFn (fun i : Fin n => (m i,V k i))) f)
    exact HP
  have H := fixedMassChain_moving_endpoint_jets_order hs m hf hVc
    (x := fun _ : ℝ => (0 : Vec3)) contDiffAt_const hm hK.le hKT hKM hKD hsource hgeo hbudget hcurv
  have hfirst : QBoundedJets (s + 2) ((1 + 6 * K) ^ n)
      (fun y => deriv (fun t => frozenCompletedSuffixChain β a χ (ρ ^ 2) f j t y) k) := by
    simpa [frozenCompletedSuffixChain, m, V, q, n] using H.1
  have hsecond : QBoundedJets s ((1 + 6 * K) ^ (2 * n))
      (fun y => deriv (deriv (fun t => frozenCompletedSuffixChain β a χ (ρ ^ 2) f j t y)) k) := by
    simpa [frozenCompletedSuffixChain, m, V, q, n] using H.2
  exact ⟨hpotential, hfirst.mono (pow_le_pow_right₀ (by linarith) (by dsimp only [n]; omega)),
    hsecond.mono (pow_le_pow_right₀ (by linarith) (by dsimp only [n]; omega))⟩

theorem frozenCompletedSuffixChain_uniform_kJets_order (s : ℕ) (hs : 1 ≤ s)
    (β B : ℝ) (hB : 0 < B) :
    ∃ ρ₀ L : ℝ, 0 < ρ₀ ∧ 0 ≤ L ∧
      ∀ a ∈ Ioc (0 : ℝ) 1, ∀ χ : ℝ, |χ| ≤ B →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ f : Vec3 → ℝ, QPotential (s + 4) B f →
      ∀ j : Fin 12, ∀ k ∈ frozenRowsKDomain,
      QBoundedJets (s + 2) L
        (fun y => deriv (fun t => frozenCompletedSuffixChain β a χ (ρ ^ 2) f j t y) k) ∧
      QBoundedJets s L
        (fun y => deriv (deriv (fun t => frozenCompletedSuffixChain β a χ (ρ ^ 2) f j t y)) k) := by
  obtain ⟨ρ₀, L, hρ₀, hL, H⟩ :=
    frozenCompletedSuffixChain_uniform_regular_kJets_order s hs β B hB
  refine ⟨ρ₀, L, hρ₀, hL, ?_⟩
  intro a ha χ hχ ρ hρ hρsmall f hf j k hk
  exact (H a ha χ hχ ρ hρ hρsmall f hf j k hk).2

theorem scalarData_frozenCompletedSuffixChain_regular_kJets_order {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (s : ℕ) (hs : 1 ≤ s) :
    ∃ h₀ L : ℝ, 0 < h₀ ∧ 1 ≤ L ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : Fin 12, ∀ k ∈ frozenRowsKDomain,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
      let f := centeredFrozenRowsTerminal β α (r - h) h z ε
      QPotential (s + 4) L (frozenCompletedSuffixChain β a χ h f j k) ∧
      QBoundedJets (s + 2) L (fun y => deriv (fun t => frozenCompletedSuffixChain β a χ h f j t y) k) ∧
        QBoundedJets s L (fun y => deriv (deriv (fun t => frozenCompletedSuffixChain β a χ h f j t y)) k) := by
  let B := terminalJetBound D (s + 4) + scalarTerminalJetBound D (s + 4) + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [terminalJetBound_nonneg D (s + 4), scalarTerminalJetBound_nonneg D (s + 4)]
  have hBt : terminalJetBound D (s + 4) ≤ B := by
    dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D (s + 4)]
  have hBs : scalarTerminalJetBound D (s + 4) ≤ B := by
    dsimp only [B]; linarith [terminalJetBound_nonneg D (s + 4)]
  obtain ⟨ρ₀, L, hρ₀, hL, H⟩ := frozenCompletedSuffixChain_uniform_regular_kJets_order s hs β B hB
  let C := B + 1 + L
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  let h₀ := min (ρ₀ ^ 2) (min (l / 2) ((D.q - u) / 6))
  refine ⟨h₀, C, lt_min (sq_pos_of_pos hρ₀) (lt_min (by positivity) (by positivity)), hC, ?_⟩
  intro r hr h hh hhsmall z ε hε j k hk
  have hhρ : h ≤ ρ₀ ^ 2 := hhsmall.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hr.1], by linarith [hr.2, D.q_mem.2]⟩
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Ioc (0 : ℝ) 1 :=
    ⟨scalarData_cdf_pos_of_pos D (by linarith [hr.1]), cdf_le_one _ _⟩
  have hρsmall : Real.sqrt h ≤ ρ₀ := by nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h]
  have he : |ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
  have hLambda : |1 - ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have hχ : |(1 - ε) * jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z| ≤ B := by
    rw [abs_mul]
    exact ((mul_le_mul hLambda (scalarData_jet_le D (r := s + 4) (by omega) (by omega) htime z)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)).trans hBs
  have hf : QPotential (s + 4) B
      (centeredFrozenRowsTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h z ε) := by
    apply (((scalarData_frozenTerminal_qPotential D (s + 4) htime).const_mul ε).translate
      (fun _ => z)).mono
    exact ((mul_le_mul_of_nonneg_right he (terminalJetBound_nonneg D (s + 4))).trans_eq
      (one_mul _)).trans hBt
  have HB := H _ ha _ hχ (Real.sqrt h) (Real.sqrt_pos.mpr hh) hρsmall _ hf j k hk
  simp only [Real.sq_sqrt hh.le] at HB
  exact ⟨HB.1.mono (by dsimp only [C]; linarith),
    HB.2.1.mono (by dsimp only [C]; linarith), HB.2.2.mono (by dsimp only [C]; linarith)⟩

theorem scalarData_frozenCompletedSuffixChain_kJets_order {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (s : ℕ) (hs : 1 ≤ s) :
    ∃ h₀ L : ℝ, 0 < h₀ ∧ 0 ≤ L ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : Fin 12, ∀ k ∈ frozenRowsKDomain,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
      let f := centeredFrozenRowsTerminal β α (r - h) h z ε
      QBoundedJets (s + 2) L (fun y => deriv (fun t => frozenCompletedSuffixChain β a χ h f j t y) k) ∧
        QBoundedJets s L (fun y => deriv (deriv (fun t => frozenCompletedSuffixChain β a χ h f j t y)) k) := by
  obtain ⟨h₀, L, hh₀, hL, H⟩ :=
    scalarData_frozenCompletedSuffixChain_regular_kJets_order D hl hu s hs
  refine ⟨h₀, L, hh₀, by linarith, ?_⟩
  intro r hr h hh hhsmall z ε hε j k hk
  exact (H r hr h hh hhsmall z ε hε j k hk).2

end SKBarriers2.Corner
