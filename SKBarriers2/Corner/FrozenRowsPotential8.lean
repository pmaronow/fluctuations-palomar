module

public import SKBarriers2.Corner.FrozenRowsPotential4
public import SKBarriers2.Corner.FrozenRowsAssembly

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def centeredFrozenRowsQuadratic (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ) : QuadraticTerminal :=
  separableTaylorQuadratic 0 ((1 - ε) * jet β α 1 (s + 4 * h) z)
    ((1 - ε) * jet β α 2 (s + 4 * h) z) 0

def centeredFrozenRowsTerminal (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ) (y : Vec3) : ℝ :=
  ε * frozenTerminal β α s h (y + (fun _ => z))

def centeredFrozenRowsPotential (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (k g : ℝ) : ℝ :=
  let t := (frozenSchedule β a (1 / 2) h k).drop (j + 1)
  let Q := centeredFrozenRowsQuadratic β α s h z ε
  let x := g • (frozenRowsHead β a h j k).2
  (riccatiRecursion t Q).value x +
    vectorIncrementChain (completedSquareSchedule t Q)
      (centeredFrozenRowsTerminal β α s h z ε) (gaussianPathMean t Q x)

theorem scalarData_frozenRowsNoise_zero_centered {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z ε : ℝ,
      ε ∈ Icc (-1 : ℝ) 2 → ∀ j : ℕ, ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ g : ℝ,
      frozenRowsNoise β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j 0 k g =
        3 * (1 - ε) * Phi β (cdf (D.μ : Measure ℝ)) ((r - h) + 4 * h) z +
          centeredFrozenRowsPotential β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j k g := by
  obtain ⟨h₀, hh₀, H⟩ := scalarData_frozen_suffix_completedSquareChain D hl hu
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall z ε hε j k hk g
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let t := (frozenSchedule β a (1 / 2) h k).drop (j + 1)
  let Q := (terminalTaylorQuadratic β α (r - h) h z).scale (1 - ε)
  let R := centeredFrozenRowsQuadratic β α (r - h) h z ε
  let c : Vec3 := fun _ => z
  let x := g • (frozenRowsHead β a h j k).2
  let C := 3 * (1 - ε) * Phi β α ((r - h) + 4 * h) z
  have hQR : Q.translate c = R.addConstant C :=
    separableTaylorQuadratic_scale_translate _ _ _ _ _
  have hstep := H r hr h hh hhsmall k hk z ε hε t (List.drop_suffix _ _) (x + c)
  have hcenter := completedSquareExpression_center t Q R c C hQR
    (fun y => ε * frozenTerminal β α (r - h) h y) x
  change epsilonChain t (terminalTaylorQuadratic β α (r - h) h z)
    (terminalResidual β α (r - h) h z) ε (x + c) =
      (riccatiRecursion t Q).value (x + c) +
        vectorIncrementChain (completedSquareSchedule t Q)
          (fun y => ε * frozenTerminal β α (r - h) h y) (gaussianPathMean t Q (x + c)) at hstep
  rw [hcenter] at hstep
  simp only [frozenRowsNoise, epsilonSuffixNoiseJet, Fin.val_zero, iteratedDeriv_zero]
  change epsilonChain t (terminalTaylorQuadratic β α (r - h) h z)
      (terminalResidual β α (r - h) h z) ε (c + x) = _
  rw [add_comm c x]
  exact hstep.trans (add_assoc C _ _)

theorem scalarData_frozenRowsNoiseKJet_zero_centered {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z ε : ℝ,
      ε ∈ Icc (-1 : ℝ) 2 → ∀ j : ℕ, ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ,
      let f := fun k => centeredFrozenRowsPotential β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j k g
      let J := frozenRowsNoiseKJet β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j 0 k g
      J.first = deriv f k ∧ J.second = deriv (deriv f) k := by
  obtain ⟨h₀, hh₀, H⟩ := scalarData_frozenRowsNoise_zero_centered D hl hu
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall z ε hε j k hk g
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let C := 3 * (1 - ε) * Phi β α ((r - h) + 4 * h) z
  let f := fun t => centeredFrozenRowsPotential β α a (r - h) h z ε j t g
  have hnear : (fun t => frozenRowsNoise β α a (r - h) h z ε j 0 t g) =ᶠ[𝓝 k]
      fun t => C + f t := by
    have hmem : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := by
      exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with t ht
    exact H r hr h hh hhsmall z ε hε j t
      (abs_le.mpr ⟨ht.1.le, ht.2.le⟩) g
  constructor
  · change deriv (fun t => frozenRowsNoise β α a (r - h) h z ε j 0 t g) k = _
    rw [hnear.deriv_eq, deriv_const_add]
  · change deriv (deriv (fun t => frozenRowsNoise β α a (r - h) h z ε j 0 t g)) k = _
    have hadd : deriv (fun t => C + f t) = deriv f := by
      funext t
      exact deriv_const_add C
    exact hnear.deriv.deriv_eq.trans
      (congrArg (fun H : ℝ → ℝ => deriv H k) hadd)

end SKBarriers2.Corner
