module

public import SKBarriers2.Corner.FrozenRowsPotential18

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

def frozenScoreMatrix (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ) (q : Fin 12)
    (k : ℝ) : Vec3 →L[ℝ] Vec3 :=
  gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h k).drop q.val)
    (centeredFrozenRowsQuadratic β α s h z ε)

def frozenScoreMean (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ) (q : Fin 12)
    (k : ℝ) : Vec3 :=
  gaussianPathMean ((frozenSchedule β a (1 / 2) h k).drop q.val)
    (centeredFrozenRowsQuadratic β α s h z ε) 0

structure FrozenCompletedScoreControl (d : ℕ) (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) (k C : ℝ) : Prop where
  mass : 0 < a ∧ a ≤ 1
  scale : Real.sqrt h ≤ 1
  terminal : QPotential 2 C (centeredFrozenRowsTerminal β α s h z ε)
  primal : QPotential (d + 4) C
    (frozenCompletedSuffixChain β a ((1 - ε) * jet β α 2 (s + 4 * h) z) h
      (centeredFrozenRowsTerminal β α s h z ε) q k)
  first : QBoundedJets (d + 2) C (fun y => deriv (fun κ =>
    frozenCompletedSuffixChain β a ((1 - ε) * jet β α 2 (s + 4 * h) z) h
      (centeredFrozenRowsTerminal β α s h z ε) q κ y) k)
  second : QBoundedJets d C (fun y => deriv (deriv (fun κ =>
    frozenCompletedSuffixChain β a ((1 - ε) * jet β α 2 (s + 4 * h) z) h
      (centeredFrozenRowsTerminal β α s h z ε) q κ y)) k)
  directions_regular : ∀ j : Fin 12, ContDiffAt ℝ 2
    (frozenCompletedDirection β a ((1 - ε) * jet β α 2 (s + 4 * h) z) h j) k
  directions : ∀ j : Fin 12, ∀ i : Fin 3,
    ‖iteratedDeriv i.val
      (frozenCompletedDirection β a ((1 - ε) * jet β α 2 (s + 4 * h) z) h j) k‖ ≤ C * Real.sqrt h
  mean_regular : ContDiffAt ℝ 2 (frozenScoreMean β α a s h z ε q) k
  matrix_regular : ContDiffAt ℝ 2 (frozenScoreMatrix β α a s h z ε q) k
  mean : ∀ i : Fin 3, ‖iteratedDeriv i.val (frozenScoreMean β α a s h z ε q) k‖ ≤ C
  matrix : ‖frozenScoreMatrix β α a s h z ε q k‖ ≤ C
  matrix_jets : ∀ i : Fin 2,
    ‖iteratedDeriv (i.val + 1) (frozenScoreMatrix β α a s h z ε q) k‖ ≤ C * h

set_option maxHeartbeats 0 in
theorem scalarData_frozenCompletedScore_control {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) (hd : 1 ≤ d) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 1 ≤ C ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ q : Fin 12, ∀ k ∈ frozenRowsKDomain,
      FrozenCompletedScoreControl d β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε q k C := by
  obtain ⟨hF, LF, hhF, hLF, HF⟩ :=
    scalarData_frozenCompletedSuffixChain_regular_kJets_order D hl hu d hd
  obtain ⟨hR, hhR, _HR⟩ := scalarData_frozenCompletedHeadLogInput_eq_pureChain D hl hu
  obtain ⟨hA, CA, hhA, hCA, HA⟩ := scalarData_frozenRows_path_linear_geometry D hl hu
  obtain ⟨hb, Cb, hhb, hCb, Hb⟩ := scalarData_frozenRows_path_mean_regular_geometry D hl hu
  obtain ⟨M, δ, hM, hδ, HV⟩ := frozenCompletedDirection_uniform_control β
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let C := 1 + LF + CA + Cb + M + terminalJetBound D 2
  have hC : 1 ≤ C := by dsimp only [C]; linarith [terminalJetBound_nonneg D 2]
  let h₀ := min hF (min hR (min hA (min hb (min 1
    (min (δ / (B + 1)) (min (l / 2) ((D.q - u) / 6)))))))
  have hh₀ : 0 < h₀ := lt_min hhF (lt_min hhR (lt_min hhA (lt_min hhb
    (lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  refine ⟨h₀,C,hh₀,hC,?_⟩
  intro r hr h hh hhsmall z ε hε q k hk
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have _hhR' : h ≤ hR := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhA' : h ≤ hA := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhb' : h ≤ hb := (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hhrest : h ≤ min 1 (min (δ / (B + 1)) (min (l / 2) ((D.q - u) / 6))) :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  have hh₁ : h ≤ 1 := hhrest.trans (min_le_left _ _)
  have hhδ : h ≤ δ / (B + 1) := (hhrest.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := ((hhrest.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := ((hhrest.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let ρ := Real.sqrt h
  let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
  let R := centeredFrozenRowsQuadratic β α (r - h) h z ε
  let f := centeredFrozenRowsTerminal β α (r - h) h z ε
  let A := fun κ => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h κ).drop q.val) R
  let b := fun κ => gaussianPathMean ((frozenSchedule β a (1 / 2) h κ).drop q.val) R 0
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₁ : ρ ≤ 1 := (Real.sqrt_le_one).mpr hh₁
  have hk' : |k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hr.1],by linarith [hr.2,D.q_mem.2]⟩
  have ha : 0 < a ∧ a ≤ 1 :=
    ⟨scalarData_cdf_pos_of_pos D (by linarith [hr.1]),cdf_le_one _ _⟩
  have hχ : |χ| ≤ B := by
    dsimp only [χ]
    rw [abs_mul]
    have hε' : |1 - ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.2],by linarith [hε.1]⟩
    apply ((mul_le_mul hε' (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)).trans
    dsimp only [B]
    linarith
  have hscale : |a * χ * h| ≤ δ := by
    rw [abs_mul,abs_mul,abs_of_pos ha.1,abs_of_pos hh]
    have H := (le_div_iff₀ (by linarith : 0 < B + 1)).mp hhδ
    calc
      _ ≤ 1 * B * h := by gcongr; exact ha.2
      _ ≤ δ := by nlinarith
  have HVk (j : Fin 12) := HV a χ h k hscale hk' j
  let nq : Fin 13 := ⟨q.val,by omega⟩
  have Hmean := Hb r hr h hh hhb' z ε hε nq k hk'
  have hbc : ContDiffAt ℝ 2 b k := Hmean.1.of_le (by simp)
  have hAc : ContDiffAt ℝ 2 A k := Hmean.2.1.of_le (by simp)
  have hAe : A = fun κ => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h κ).drop q.val)
      ((terminalTaylorQuadratic β α (r - h) h z).scale (1 - ε)) := by
    funext κ
    exact centeredFrozenRows_path_linear_eq β α a (r - h) h z ε κ q.val
  have HAq := HA r hr h hh hhA' z ε hε nq k hk'
  have hAB : ‖A k‖ ≤ CA := by rw [hAe]; exact HAq.1
  have HFq := HF r hr h hh hhF' z ε hε q k hk
  have hFC : LF ≤ C := by dsimp only [C]; linarith [terminalJetBound_nonneg D 2]
  have hAC : CA ≤ C := by dsimp only [C]; linarith [terminalJetBound_nonneg D 2]
  have hbC : Cb ≤ C := by dsimp only [C]; linarith [terminalJetBound_nonneg D 2]
  have hMC : M ≤ C := by dsimp only [C]; linarith [terminalJetBound_nonneg D 2]
  have hterminal : QPotential 2 C f := by
    apply (((scalarData_frozenTerminal_qPotential D 2 htime).const_mul ε).translate
      (fun _ => z)).mono
    have he : |ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.1],hε.2⟩
    apply ((mul_le_mul_of_nonneg_right he (terminalJetBound_nonneg D 2)).trans_eq (one_mul _)).trans
    dsimp only [C]
    linarith [terminalJetBound_nonneg D 2]
  refine ⟨ha,hρ₁,hterminal,HFq.1.mono hFC,HFq.2.1.mono hFC,HFq.2.2.mono hFC,
    (fun j => (HVk j).2.2.2.2.2),?_,hbc,hAc,?_,hAB.trans hAC,?_⟩
  · intro j i
    have hD₁ : deriv (frozenCompletedDirection β a χ h j) k =
        frozenCompletedDirectionFirst β a χ h j k := (HVk j).2.2.2.1.deriv
    have hnear : deriv (frozenCompletedDirection β a χ h j) =ᶠ[𝓝 k]
        frozenCompletedDirectionFirst β a χ h j := by
      have hku : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1],by linarith [hk.2]⟩
      filter_upwards [isOpen_Ioo.mem_nhds hku] with κ hκ
      exact (HV a χ h κ hscale (abs_le.mpr ⟨hκ.1.le,hκ.2.le⟩) j).2.2.2.1.deriv
    have hD₂ : deriv (deriv (frozenCompletedDirection β a χ h j)) k =
        frozenCompletedDirectionSecond β a χ h j k :=
      hnear.deriv_eq.trans (HVk j).2.2.2.2.1.deriv
    have hMρ : M * ρ ≤ C * ρ := mul_le_mul_of_nonneg_right hMC hρ.le
    fin_cases i
    · exact (HVk j).1.trans hMρ
    · change ‖iteratedDeriv 1 (frozenCompletedDirection β a χ h j) k‖ ≤ C * ρ
      simpa only [iteratedDeriv_one,hD₁] using (HVk j).2.1.trans hMρ
    · change ‖iteratedDeriv 2 (frozenCompletedDirection β a χ h j) k‖ ≤ C * ρ
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero,hD₂] using (HVk j).2.2.1.trans hMρ
  · intro i
    exact (Hmean.2.2 i).trans hbC
  · intro i
    rw [show frozenScoreMatrix β α a (r - h) h z ε q = A from rfl,hAe]
    exact (HAq.2 i).trans (mul_le_mul_of_nonneg_right hAC hh.le)

end SKBarriers2.Corner
