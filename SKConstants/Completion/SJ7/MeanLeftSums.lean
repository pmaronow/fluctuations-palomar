module

public import SKConstants.Completion.SJ7.FrozenIntegral
public import SKConstants.Completion.SJ7.LinkedL2
public import SKConstants.Completion.LM4b.ActualZetaMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem energyReference_eq_beta_pr (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) :
    actualParisiEnergyReference W β V = β * (∫ s in (0 : ℝ)..V,
      actualParisiFullSusceptibilityExpected W β s * actualParisiFullSusceptibilitySquareExpected W β s) := by
  rw [← intervalIntegral.integral_const_mul]
  unfold actualParisiEnergyReference
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le V.coe_nonneg] at hs
  dsimp only
  rw [LQ.actual_rho_eq W β hβ s hs.1]
  calc
    _ = β * actualParisiFullSusceptibilityExpected W β s *
        (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β s).1]; ring

theorem measurable_jointRowLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    Measurable (jointRowLeftSum W Z β hβ V l) := by
  apply Finset.measurable_fun_sum
  intro k _
  have hp (S : ℝ≥0) : Measurable (fun u : (Bool × Ω) × A => LJ.actualRowPotential W β S u.1) :=
    (LJ.measurable_actualRowPotential W β S).comp measurable_fst
  have hm : Measurable (fun u : (Bool × Ω) × A =>
      actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k) u.1.2) :=
    (measurable_actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k)).comp
    (measurable_snd.comp measurable_fst)
  have hs : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  have hB (S : ℝ≥0) : Measurable (fun u : (Bool × Ω) × A =>
      (actualParisiQueryBrownianSystem W Z β hβ).B S (u.1.2, u.2)) :=
    ((actualParisiQueryBrownianSystem W Z β hβ).measurable S).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact ((hp _).sub (hp _)).const_mul _ |>.add
    (((hs.sub hm).const_mul _).mul ((hB _).sub (hB _)))

theorem integrable_jointRowLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    Integrable (jointRowLeftSum W Z β hβ V l) (actualParisiFullQuerySpinLaw W Z β V) := by
  have hp (S : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A => LJ.actualRowPotential W β S u.1)
      (actualParisiFullQuerySpinLaw W Z β V) :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).integrable_comp
      (LJ.integrable_actualRowPotential W β S V)
  apply integrable_finsetSum
  intro k _
  refine ((((hp ((brownianDyadicGrid V).time l (k + 1))).sub (hp ((brownianDyadicGrid V).time l k))).const_mul
    (β * actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k))).add
    ((LM4b.integrable_actualRowQueryDefect W Z β hβ
      ((brownianDyadicGrid V).time l k) ((brownianDyadicGrid V).time l (k + 1)) V).const_mul
      (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β ((brownianDyadicGrid V).time l k))))).congr
        (ae_of_all _ (fun u => ?_))
  dsimp only [Pi.add_apply, Pi.sub_apply, actualParisiMagnetizationObservable,
    actualParisiFullPosteriorMean, LM4b.actualRowQueryIncrement]
  ring

theorem jointRowLeftSum_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    (∫ u, jointRowLeftSum W Z β hβ V l u ∂actualParisiFullQuerySpinLaw W Z β V) =
      ∑ k ∈ Finset.range (2 ^ l),
        (β / 2 * actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k) *
            (∫ s in ((brownianDyadicGrid V).time l k : ℝ)..
              ((brownianDyadicGrid V).time l (k + 1) : ℝ),
              actualParisiFullSusceptibilitySquareExpected W β s) +
          Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β ((brownianDyadicGrid V).time l k)) *
            ∫ s in ((brownianDyadicGrid V).time l k : ℝ)..
              ((brownianDyadicGrid V).time l (k + 1) : ℝ),
              actualParisiQueryRho W β s * actualParisiFullSusceptibilityExpected W β s) := by
  let G := brownianDyadicGrid V
  let ν := actualParisiFullQuerySpinLaw W Z β V
  have hp (S : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A => LJ.actualRowPotential W β S u.1) ν :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).integrable_comp
      (LJ.integrable_actualRowPotential W β S V)
  have hpm (S : ℝ≥0) (hS : S ≤ V) :
      (∫ u : (Bool × Ω) × A, LJ.actualRowPotential W β S u.1 ∂ν) =
        actualParisiFullOverlap W β S / 2 :=
    ((actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).integral_comp
      (LJ.measurable_actualRowPotential W β S).aestronglyMeasurable).trans
      (LJ.actualRowPotential_mean W β hβ S V hS)
  have hB (k : ℕ) := LM4b.integrable_actualRowQueryDefect W Z β hβ (G.time l k) (G.time l (k + 1)) V
  unfold jointRowLeftSum
  have hi (k : ℕ) : Integrable (fun u : (Bool × Ω) × A =>
      β * actualParisiFullSusceptibilityExpected W β (G.time l k) *
        (LJ.actualRowPotential W β (G.time l (k + 1)) u.1 - LJ.actualRowPotential W β (G.time l k) u.1) +
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k)) *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (G.time l k) u.1.2) *
        LM4b.actualRowQueryIncrement W Z β hβ (G.time l k) (G.time l (k + 1)) u) ν := by
    refine ((((hp (G.time l (k + 1))).sub (hp (G.time l k))).const_mul
      (β * actualParisiFullSusceptibilityExpected W β (G.time l k))).add
      ((hB k).const_mul (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k))))).congr
        (ae_of_all _ (fun u => ?_))
    dsimp only [Pi.add_apply, Pi.sub_apply, actualParisiMagnetizationObservable,
      actualParisiFullPosteriorMean, LM4b.actualRowQueryIncrement]
    ring
  dsimp only [G, ν, LM4b.actualRowQueryIncrement] at hi
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  have hend : G.time l (2 ^ l) = V := by simp [G, brownianDyadicGrid]
  have hnext : G.time l (k + 1) ≤ V := (G.monotone l (by omega)).trans_eq hend
  have hcur := G.monotone l (Nat.le_succ k)
  have hA : Integrable (fun u : (Bool × Ω) × A =>
      β * actualParisiFullSusceptibilityExpected W β (G.time l k) *
        (LJ.actualRowPotential W β (G.time l (k + 1)) u.1 - LJ.actualRowPotential W β (G.time l k) u.1)) ν := by
    refine (((hp (G.time l (k + 1))).sub (hp (G.time l k))).const_mul
      (β * actualParisiFullSusceptibilityExpected W β (G.time l k))).congr
      (ae_of_all _ (fun u => ?_))
    rfl
  have heq : (∫ u, β * actualParisiFullSusceptibilityExpected W β (G.time l k) *
      (LJ.actualRowPotential W β (G.time l (k + 1)) u.1 - LJ.actualRowPotential W β (G.time l k) u.1) +
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k)) *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (G.time l k) u.1.2) *
        LM4b.actualRowQueryIncrement W Z β hβ (G.time l k) (G.time l (k + 1)) u ∂ν) =
      (∫ u, β * actualParisiFullSusceptibilityExpected W β (G.time l k) *
        (LJ.actualRowPotential W β (G.time l (k + 1)) u.1 - LJ.actualRowPotential W β (G.time l k) u.1) ∂ν) +
      (∫ u, Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k)) *
        ((scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β (G.time l k) u.1.2) *
          LM4b.actualRowQueryIncrement W Z β hβ (G.time l k) (G.time l (k + 1)) u) ∂ν) := by
    rw [← integral_add hA
      ((hB k).const_mul (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k))))]
    apply integral_congr_ae (ae_of_all _ (fun u => ?_))
    dsimp only [Pi.add_apply, Pi.sub_apply, actualParisiMagnetizationObservable,
      actualParisiFullPosteriorMean]
    ring
  change (∫ u, β * actualParisiFullSusceptibilityExpected W β (G.time l k) *
      (LJ.actualRowPotential W β (G.time l (k + 1)) u.1 - LJ.actualRowPotential W β (G.time l k) u.1) +
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k)) *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (G.time l k) u.1.2) *
        LM4b.actualRowQueryIncrement W Z β hβ (G.time l k) (G.time l (k + 1)) u ∂ν) = _
  rw [heq, integral_const_mul, integral_sub (hp _) (hp _), hpm _ hnext, hpm _ (hcur.trans hnext)]
  have hq := LM4b.actualRowQueryDefect_mean W Z β hβ (G.time l k) (G.time l (k + 1)) V hcur hnext
  change _ + (∫ u, Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (G.time l k)) *
    ((scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β (G.time l k) u.1.2) *
      LM4b.actualRowQueryIncrement W Z β hβ (G.time l k) (G.time l (k + 1)) u) ∂ν) = _
  rw [integral_const_mul, hq,
    actualParisiFullSusceptibilitySquareExpected_interval W β hβ _ _ hcur]
  dsimp only [LM4b.actualQueryCellMean]
  ring

theorem jointRowLeftSum_mean_tendsto (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    Tendsto (fun l => ∫ u, jointRowLeftSum W Z β hβ V l u
      ∂actualParisiFullQuerySpinLaw W Z β V) atTop
      (𝓝 (3 / 2 * actualParisiEnergyReference W β V)) := by
  let p := actualParisiFullSusceptibilityExpected W β
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let ρ := actualParisiQueryRho W β
  have h1 := frozen_integral_dyadic_tendsto p r
    (continuous_actualParisiFullSusceptibilityExpected W β)
    (continuous_actualParisiFullSusceptibilitySquareExpected W β) V (fun s _ => by
      rw [abs_of_nonneg (actualParisiFullSusceptibilitySquareExpected_bounds W β s).1]
      exact (actualParisiFullSusceptibilitySquareExpected_bounds W β s).2)
  have h2 := frozen_integral_dyadic_tendsto (fun s => Real.sqrt (r s)) (fun s => ρ s * p s)
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt
    ((continuous_actualParisiQueryRho W β).mul (continuous_actualParisiFullSusceptibilityExpected W β))
    V (fun s hs => by
      have hb := LQ.actual_query_integrand_bounds W β hβ s
      rw [mul_comm, abs_of_nonneg hb.1]
      exact hb.2.trans (by
        simpa using Real.sqrt_le_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β s).2))
  have he : actualParisiEnergyReference W β V = β * (∫ s in (0 : ℝ)..V, p s * r s) := by
    exact energyReference_eq_beta_pr W β hβ V
  have he1 : β / 2 * (∫ s in (0 : ℝ)..V, p s * r s) =
      actualParisiEnergyReference W β V / 2 := by
    rw [he]
    ring
  have he2 : (∫ s in (0 : ℝ)..V, Real.sqrt (r s) * (ρ s * p s)) =
      actualParisiEnergyReference W β V := by
    unfold actualParisiEnergyReference
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [r, p, ρ]
    ring
  have hlim := (h1.const_mul (β / 2)).add h2
  rw [he1, he2] at hlim
  have he : actualParisiEnergyReference W β V / 2 + actualParisiEnergyReference W β V =
      3 / 2 * actualParisiEnergyReference W β V := by ring
  rw [he] at hlim
  convert hlim using 1
  funext l
  rw [jointRowLeftSum_mean, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    dsimp only [p, r]
    ring
  · rfl

end SKConstants.Completion.SJ7
