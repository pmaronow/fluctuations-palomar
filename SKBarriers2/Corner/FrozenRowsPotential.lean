module

public import SKBarriers2.Corner.FrozenRowsWeighted

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def completedSquareSchedule : List (ℝ × Vec3) → QuadraticTerminal → List (ℝ × Vec3)
  | [], _ => []
  | u :: t, Q =>
      (u.1, gaussianPathLinear t Q
        ((Real.sqrt ((riccatiRecursion t Q).precision u.1 u.2)⁻¹) • u.2)) ::
          completedSquareSchedule t Q

@[simp] theorem completedSquareSchedule_length (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) : (completedSquareSchedule l Q).length = l.length := by
  induction l with
  | nil => rfl
  | cons u t ih => simp only [completedSquareSchedule, List.length_cons, ih]

theorem completedSquareSchedule_drop (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (j : ℕ) :
    completedSquareSchedule (l.drop j) Q = (completedSquareSchedule l Q).drop j := by
  induction l generalizing j with
  | nil => simp only [List.drop_nil, completedSquareSchedule]
  | cons u t ih =>
    cases j with
    | zero => rfl
    | succ j => simpa only [List.drop_succ_cons, completedSquareSchedule] using ih j

theorem vectorStep_gaussianPathMean (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (m : ℝ) (v x : Vec3) (f : Vec3 → ℝ) :
    vectorStep m v (fun y => f (gaussianPathMean l Q y)) x =
      vectorStep m (gaussianPathLinear l Q v) f (gaussianPathMean l Q x) := by
  simp only [vectorStep, gaussianStep, positiveGaussianLogStep,
    gaussianPathMean_shift]

theorem epsilonFrameResidual_eq_completedSquareChain
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (ε : ℝ)
    (H : ∀ u t, u :: t <:+ l →
      u.1 ≠ 0 ∧ 0 < (riccatiRecursion t (Q.scale (1 - ε))).precision u.1 u.2 ∧
        ∃ B : ℝ, QPotential 2 B (epsilonFrameResidual t Q G ε)) (x : Vec3) :
    epsilonFrameResidual l Q G ε x =
      vectorIncrementChain (completedSquareSchedule l (Q.scale (1 - ε)))
        (fun y => ε * G y) (gaussianPathMean l (Q.scale (1 - ε)) x) := by
  induction l generalizing x with
  | nil => exact epsilonFrameResidual_nil Q G ε x
  | cons u t ih =>
    have ht := fun (v : ℝ × Vec3) (s : List (ℝ × Vec3)) (hs : v :: s <:+ t) =>
      H v s (hs.trans (List.suffix_cons u t))
    rcases H u t (List.suffix_refl _) with ⟨hm, hD, B, hB⟩
    let P := riccatiRecursion t (Q.scale (1 - ε))
    let w := (Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2
    have hLip (y z : Vec3) : |epsilonFrameResidual t Q G ε y -
        epsilonFrameResidual t Q G ε z| ≤ B * ‖y - z‖ :=
      (hB.lipschitzWith (by norm_num)).norm_sub_le y z
    have hpos : 0 < quadraticAverage P u.1 u.2
        (fun y => Real.exp (u.1 * epsilonFrameResidual t Q G ε y)) x := by
      rw [quadraticAverage_eq_standard P u.1 u.2 x hD
        (g := fun y => Real.exp (u.1 * epsilonFrameResidual t Q G ε y))
        (Real.continuous_exp.comp
          ((continuous_const : Continuous (fun _ : Vec3 => u.1)).mul hB.smooth.continuous))]
      exact integral_exp_pos (integrable_exp_lipschitz_line hB.smooth.continuous hLip
        u.1 (quadraticMeanTransition P u.1 u.2 x) w)
    rw [epsilonFrameResidual_cons t Q G ε u x hB.smooth.continuous hm hD hpos]
    change vectorStep u.1 w (epsilonFrameResidual t Q G ε)
        (quadraticMeanLinear P u.1 u.2 x + quadraticNoiseConstant P u.1 u.2) = _
    have he : epsilonFrameResidual t Q G ε = fun y =>
        vectorIncrementChain (completedSquareSchedule t (Q.scale (1 - ε)))
          (fun z => ε * G z) (gaussianPathMean t (Q.scale (1 - ε)) y) :=
      funext (ih ht)
    rw [he, vectorStep_gaussianPathMean, ← quadraticMeanTransition_eq_affine]
    rfl

theorem epsilonChain_eq_completedSquareChain
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (ε : ℝ)
    (H : ∀ u t, u :: t <:+ l →
      u.1 ≠ 0 ∧ 0 < (riccatiRecursion t (Q.scale (1 - ε))).precision u.1 u.2 ∧
        ∃ B : ℝ, QPotential 2 B (epsilonFrameResidual t Q G ε)) (x : Vec3) :
    epsilonChain l Q (fun y => G y - Q.value y) ε x =
      (riccatiRecursion l (Q.scale (1 - ε))).value x +
        vectorIncrementChain (completedSquareSchedule l (Q.scale (1 - ε)))
          (fun y => ε * G y) (gaussianPathMean l (Q.scale (1 - ε)) x) := by
  have h := epsilonFrameResidual_eq_completedSquareChain l Q G ε H x
  rw [epsilonFrameResidual_eq_actual] at h
  linarith

theorem scalarData_frozen_suffix_completedSquareChain {β l u : ℝ}
    (D : ScalarData β) (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ z : ℝ, ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ t : List (ℝ × Vec3),
      t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ x : Vec3,
      let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z
      let P := Q.scale (1 - ε)
      epsilonChain t Q (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) ε x =
        (riccatiRecursion t P).value x +
          vectorIncrementChain (completedSquareSchedule t P)
            (fun y => ε * frozenTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h y)
              (gaussianPathMean t P x) := by
  obtain ⟨C, hR, _, hhR, HR⟩ :=
    scalarData_epsilonFrameResidual_spatial_qPotential D hl hu 2 le_rfl
  obtain ⟨hP, _, hhP, _, HP⟩ := scalarData_frozen_suffix_lipschitz_frames D hl hu
  refine ⟨min hR hP, lt_min hhR hhP, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε t ht x
  apply epsilonChain_eq_completedSquareChain
  intro v s hs
  have hvs := hs.trans ht
  have hA := (HP r hr h hh (hhsmall.trans (min_le_right _ _)) k hk z ε hε _ hvs).1
  refine ⟨hA.2.1, hA.2.2, C, ?_⟩
  exact HR r hr h hh (hhsmall.trans (min_le_left _ _)) k hk z ε hε s
    ((List.suffix_cons v s).trans hvs)

end SKBarriers2.Corner
