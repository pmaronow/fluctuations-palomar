module

public import SKBarriers2.Corner.FrozenRowsPotential22
public import SKBarriers2.Corner.FrozenRowsPotential23

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

private theorem three_ordinary_norm_bounds {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} {k B : ℝ} (H : ∀ i : Fin 3, ‖iteratedDeriv i.val f k‖ ≤ B) :
    ‖f k‖ ≤ B ∧ ‖deriv f k‖ ≤ B ∧ ‖deriv (deriv f) k‖ ≤ B := by
  refine ⟨?_,?_,?_⟩
  · have H₀ : ‖iteratedDeriv 0 f k‖ ≤ B := H (0 : Fin 3)
    simpa only [iteratedDeriv_zero] using H₀
  · have H₁ : ‖iteratedDeriv 1 f k‖ ≤ B := H (1 : Fin 3)
    simpa only [iteratedDeriv_one] using H₁
  · have H₂ : ‖iteratedDeriv 2 f k‖ ≤ B := H (2 : Fin 3)
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H₂

set_option maxHeartbeats 0 in
theorem scalarData_frozenCompletedFineLogInput_score_profiles {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ L : ℝ, 0 < h₀ ∧ 1 ≤ L ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ q j : Fin 12, ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      let σ := Real.sqrt h / (1 + |g|)
      let δ := (Real.sqrt h) ^ 3 / (1 + |g|)
      ∃ s₀ s₁ t₀ t₁ t₂ : ℝ → Vec3 → ℝ,
      (ContDiff ℝ d (Function.uncurry s₀) ∧ ContDiff ℝ d (Function.uncurry s₁) ∧
        ContDiff ℝ d (Function.uncurry t₀) ∧ ContDiff ℝ d (Function.uncurry t₁) ∧
        ContDiff ℝ d (Function.uncurry t₂)) ∧
      (∀ t, WJets d (L * (1 + |t|) ^ 3) 0 (s₀ t) ∧
        WJets d (L * (1 + |t|) ^ 3) 1 (s₁ t) ∧
        WJets d (L * (1 + |t|) ^ 3) 0 (t₀ t) ∧
        WJets d (L * (1 + |t|) ^ 3) 1 (t₁ t) ∧
        WJets d (L * (1 + |t|) ^ 3) 2 (t₂ t)) ∧
      (∀ t y, σ * deriv (fun κ => frozenCompletedFineLogInput β α a (r - h) h z ε q j κ g t y) k =
        s₀ t y + δ * s₁ t y) ∧
      (∀ t y, σ ^ 2 * deriv (deriv
        (fun κ => frozenCompletedFineLogInput β α a (r - h) h z ε q j κ g t y)) k =
        t₀ t y + δ * t₁ t y + δ ^ 2 * t₂ t y) := by
  obtain ⟨hControl,C,hhControl,hC,HC⟩ := scalarData_frozenCompletedScore_control D hl hu (d + 1) (by omega)
  obtain ⟨hR,hhR,HR⟩ := scalarData_frozenCompletedFineLogInput_eq_pureChain D hl hu
  obtain ⟨CH,hCH,HH⟩ := frozenRowsHead_direction_uniform_jets β
  let LG := 1 + 3 * C + 4 * C * CH
  let B₀ := 1 + C * max 1 LG ^ d + LG
  let L := movingScoreProfileBudget d B₀
  have hC₀ : 0 ≤ C := by linarith
  have hCH₀ : 0 ≤ CH := by linarith
  have hLG : 0 ≤ LG := by dsimp only [LG]; positivity
  have hCLG : C ≤ LG := by dsimp only [LG]; nlinarith [mul_nonneg hC₀ hCH₀]
  have hGLG : 2 * C + 4 * C * CH ≤ LG := by dsimp only [LG]; linarith
  have hL : 1 ≤ L := by
    have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
    have h₂ : 0 ≤ 4 * (2 : ℝ) ^ d * B₀ ^ 2 := by positivity
    have h₃ : 0 ≤ 3 * ((2 : ℝ) ^ d) ^ 2 * B₀ ^ 3 := by positivity
    dsimp only [L,movingScoreProfileBudget]
    linarith
  refine ⟨min hControl hR,L,lt_min hhControl hhR,hL,?_⟩
  intro r hr h hh hhsmall z ε hε q j k hk g
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let ρ := Real.sqrt h
  let W := 1 + |g|
  let σ := ρ / W
  let δ := ρ ^ 3 / W
  let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
  let f := centeredFrozenRowsTerminal β α (r - h) h z ε
  let F := frozenCompletedSuffixChain β a χ h f q
  let G := fun y => deriv (fun κ => F κ y) k
  let H := fun y => deriv (deriv (fun κ => F κ y)) k
  let A := frozenScoreMatrix β α a (r - h) h z ε q
  let b := frozenScoreMean β α a (r - h) h z ε q
  let c := fun κ => (frozenRowsHead β a h j.val κ).2
  let v := frozenCompletedDirection β a χ h q
  let X := fun (κ t : ℝ) (y : Vec3) => ρ • A κ y + b κ + g • A κ (c κ) + t • v κ
  have hctl := HC r hr h hh (hhsmall.trans (min_le_left _ _)) z ε hε q k hk
  have hk' : |k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₁ : ρ ≤ 1 := hctl.scale
  have hρsq : ρ ^ 2 = h := Real.sq_sqrt hh.le
  have hW : 0 < W := by dsimp only [W]; positivity
  have hW₁ : 1 ≤ W := by dsimp only [W]; linarith [abs_nonneg g]
  have hσ : |σ| ≤ 1 := by
    rw [abs_of_pos (div_pos hρ hW)]
    exact (div_le_one₀ hW).mpr (hρ₁.trans hW₁)
  have hbjets := three_ordinary_norm_bounds hctl.mean
  have hvjets := three_ordinary_norm_bounds (hctl.directions q)
  have hhead := HH a h hh.le j k hk'
  have hcjets := three_ordinary_norm_bounds hhead.2
  have hCCρ : C * ρ ≤ C := mul_le_of_le_one_right hC₀ hρ₁
  have hCHρ : CH * ρ ≤ CH := mul_le_of_le_one_right hCH₀ hρ₁
  have hA₁ : ‖deriv A k‖ ≤ C * ρ ^ 2 := by
    rw [hρsq]
    have H₁ : ‖iteratedDeriv 1 A k‖ ≤ C * h := hctl.matrix_jets (0 : Fin 2)
    simpa only [iteratedDeriv_one] using H₁
  have hA₂ : ‖deriv (deriv A) k‖ ≤ C * ρ ^ 2 := by
    rw [hρsq]
    have H₂ : ‖iteratedDeriv 2 A k‖ ≤ C * h := hctl.matrix_jets (1 : Fin 2)
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H₂
  obtain ⟨u₀,a₀,U,V,hu₀,ha₀,hAendpoint,hU,hV,hnoise,hXc,hvel,hacc⟩ :=
    affine_endpoint_small_score_geometry hρ hρ₁ hC₀ hCH₀
      hctl.matrix_regular hctl.mean_regular (hhead.1.of_le (by simp))
      (hctl.directions_regular q) hctl.matrix hA₁ hA₂ hbjets.2.1 hbjets.2.2
      (hvjets.2.1.trans hCCρ) (hvjets.2.2.trans hCCρ)
      (hcjets.1.trans hCHρ) (hcjets.2.1.trans hCHρ) (hcjets.2.2.trans hCHρ) g
  let B := fun t : ℝ => b k + g • A k (c k) + t • v k
  have hB : ContDiff ℝ d B := by dsimp only [B]; fun_prop
  have hf : QPotential (d + 2) C (F k) := hctl.primal.of_le (by omega)
  have hG : QBoundedJets (d + 1) C G := hctl.first.of_le (by omega)
  have hH : QBoundedJets d C H := hctl.second.of_le (Nat.le_succ d)
  obtain ⟨s₀,s₁,t₀,t₁,t₂,hsmooth,hweighted,hs₁,hs₂⟩ :=
    joint_affine_fine_score_profiles hf hG hH hLG hσ (ρ • A k) U V B u₀ a₀ hB
      (hu₀.of_le (by simp)) (ha₀.of_le (by simp)) (hAendpoint.trans hCLG)
      (hU.trans hCLG) (hV.trans hCLG)
      (fun t => (hnoise t).1.trans (mul_le_mul_of_nonneg_right hGLG (by positivity)))
      (fun t => (hnoise t).2.trans (mul_le_mul_of_nonneg_right hGLG (by positivity)))
  have hpoint (t : ℝ) (y : Vec3) : X k t y = (ρ • A k) y + B t := by
    dsimp only [X,B]
    simp only [smul_apply]
    module
  let n := 12 - (q.val + 1)
  let labels : Fin n → Fin 12 := fun i => ⟨q.val + 1 + i.val,by dsimp only [n] at i; omega⟩
  let m := fun i : Fin n => a * frozenUnitMass (labels i)
  let Vtail := fun κ => fun i : Fin n => frozenCompletedDirection β a χ h (labels i) κ
  have hVtail : ContDiffAt ℝ 2 Vtail k :=
    contDiffAt_pi.mpr (fun i => hctl.directions_regular (labels i))
  have hunit (i : Fin 12) : 0 < frozenUnitMass i ∧ frozenUnitMass i ≤ 1 := by
    fin_cases i <;> norm_num [frozenUnitMass]
  have hm (i : Fin n) : 0 < m i := mul_pos hctl.mass.1 (hunit (labels i)).1
  have hF : F = fun κ y => vectorIncrementChain
      (List.ofFn (fun i : Fin n => (m i, Vtail κ i))) f y := by
    funext κ y
    rfl
  have htotal (t : ℝ) (y : Vec3) :=
    fixedMassChain_moving_endpoint_jets_identity m hctl.terminal hVtail (hXc t y) hm
  have htotal₁ (t : ℝ) (y : Vec3) : deriv (fun κ => F κ (X κ t y)) k =
      G (X k t y) + fderiv ℝ (F k) (X k t y) (deriv (fun κ => X κ t y) k) := by
    simpa only [G,hF] using (htotal t y).1
  have htotal₂ (t : ℝ) (y : Vec3) : deriv (deriv (fun κ => F κ (X κ t y))) k =
      H (X k t y) + 2 * fderiv ℝ G (X k t y) (deriv (fun κ => X κ t y) k) +
      fderiv ℝ (fderiv ℝ (F k)) (X k t y)
        (deriv (fun κ => X κ t y) k) (deriv (fun κ => X κ t y) k) +
      fderiv ℝ (F k) (X k t y) (deriv (deriv (fun κ => X κ t y)) k) := by
    simpa only [H,G,hF] using (htotal t y).2
  have hp₁ (t : ℝ) (y : Vec3) : σ * deriv (fun κ => F κ (X κ t y)) k = s₀ t y + δ * s₁ t y := by
    have HS := hs₁ t y
    rw [← hpoint t y,← hvel t y] at HS
    simp only [map_smul,smul_eq_mul] at HS
    calc
      _ = σ * G (X k t y) + σ * fderiv ℝ (F k) (X k t y) (deriv (fun κ => X κ t y) k) := by
        rw [htotal₁]
        ring
      _ = _ := HS
  have hp₂ (t : ℝ) (y : Vec3) : σ ^ 2 * deriv (deriv (fun κ => F κ (X κ t y))) k =
      t₀ t y + δ * t₁ t y + δ ^ 2 * t₂ t y := by
    have HS := hs₂ t y
    rw [← hpoint t y,← hvel t y,← hacc t y] at HS
    simp only [map_smul,smul_apply,smul_eq_mul] at HS
    rw [htotal₂]
    convert HS using 1
    ring
  let μ := a * frozenUnitMass q
  have hμ : 0 < μ ∧ μ ≤ 1 := ⟨mul_pos hctl.mass.1 (hunit q).1,
    (mul_le_mul hctl.mass.2 (hunit q).2 (hunit q).1.le (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)⟩
  have hμabs : |μ| ≤ 1 := by rw [abs_of_pos hμ.1]; exact hμ.2
  have hnear (t : ℝ) (y : Vec3) :
      (fun κ => frozenCompletedFineLogInput β α a (r - h) h z ε q j κ g t y) =ᶠ[𝓝 k]
        fun κ => μ * F κ (X κ t y) := by
    have hkU : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1],by linarith [hk.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds hkU] with κ hκ
    exact HR r hr h hh (hhsmall.trans (min_le_right _ _)) z ε hε q j κ
      (abs_le.mpr ⟨hκ.1.le,hκ.2.le⟩) g t y
  refine ⟨(fun t y => μ * s₀ t y),(fun t y => μ * s₁ t y),
    (fun t y => μ * t₀ t y),(fun t y => μ * t₁ t y),(fun t y => μ * t₂ t y),?_,?_,?_,?_⟩
  · exact ⟨contDiff_const.mul hsmooth.1,contDiff_const.mul hsmooth.2.1,
      contDiff_const.mul hsmooth.2.2.1,contDiff_const.mul hsmooth.2.2.2.1,
      contDiff_const.mul hsmooth.2.2.2.2⟩
  · intro t
    have hscale {p : ℕ} {S : Vec3 → ℝ} (HS : WJets d (L * (1 + |t|) ^ 3) p S) :
        WJets d (L * (1 + |t|) ^ 3) p (fun y => μ * S y) := by
      exact (HS.const_smul μ).mono (mul_le_of_le_one_left HS.nonneg hμabs) le_rfl
    have HW := hweighted t
    exact ⟨hscale HW.1,hscale HW.2.1,hscale HW.2.2.1,hscale HW.2.2.2.1,hscale HW.2.2.2.2⟩
  · intro t y
    rw [(hnear t y).deriv_eq,deriv_const_mul_field]
    calc
      σ * (μ * deriv (fun κ => F κ (X κ t y)) k) =
          μ * (σ * deriv (fun κ => F κ (X κ t y)) k) := by ring
      _ = _ := by rw [hp₁]; ring
  · intro t y
    rw [(hnear t y).deriv.deriv_eq,deriv_const_mul_field',deriv_const_mul_field]
    calc
      σ ^ 2 * (μ * deriv (deriv (fun κ => F κ (X κ t y))) k) =
          μ * (σ ^ 2 * deriv (deriv (fun κ => F κ (X κ t y))) k) := by ring
      _ = _ := by rw [hp₂]; ring

end SKBarriers2.Corner
