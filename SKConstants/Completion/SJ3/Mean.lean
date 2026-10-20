module

public import SKConstants.Completion.SJ3.Versions
public import SKConstants.Completion.SJ3.PotentialIntegral
public import SKConstants.Completion.N7.IntegralMean
public import SKConstants.Completion.N7.Quadrature
public import SKConstants.ParisiFullVarianceIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ3
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance mean_W_isProbability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance mean_Z_isProbability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability
attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization

theorem energyReference_eq_beta_integral_pr (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) : actualParisiEnergyReference W β V =
      β * ∫ t in (0 : ℝ)..(V : ℝ), actualParisiFullSusceptibilityExpected W β t *
        actualParisiFullSusceptibilitySquareExpected W β t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le V.coe_nonneg] at ht
  change Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t) *
    actualParisiFullSusceptibilityExpected W β t * actualParisiQueryRho W β t = _
  rw [LQ.actual_rho_eq W β hβ t ht.1]
  calc
    _ = β * actualParisiFullSusceptibilityExpected W β t *
        (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1]; ring

theorem integrable_jointRowLeftSum_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V H : ℝ≥0) (l : ℕ) :
    Integrable (jointRowLeftSum W Z β hβ V l) (actualParisiFullQuerySpinLaw W Z β H) := by
  have hp (t : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A => LJ.actualRowPotential W β t u.1)
      (actualParisiFullQuerySpinLaw W Z β H) :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integrable_comp
      (LJ.integrable_actualRowPotential W β t H)
  apply integrable_finsetSum
  intro k _
  apply Integrable.add
  · exact ((hp _).sub (hp _)).const_mul _
  · convert (LM4b.integrable_actualRowQueryDefect W Z β hβ
      ((brownianDyadicGrid V).time l k) ((brownianDyadicGrid V).time l (k + 1)) H).const_mul
      (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β ((brownianDyadicGrid V).time l k))) using 1
    funext u
    dsimp only [LM4b.actualRowQueryIncrement]
    change _ = Real.sqrt _ * ((scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β _ u.1.2) * _)
    ring

theorem jointRowLeftSum_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    (∫ u, jointRowLeftSum W Z β hβ V l u ∂actualParisiFullQuerySpinLaw W Z β V) =
      (β / 2) * (∑ k ∈ Finset.range (2 ^ l),
        actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k) *
          (∫ t in ((brownianDyadicGrid V).time l k : ℝ)..((brownianDyadicGrid V).time l (k + 1) : ℝ),
            actualParisiFullSusceptibilitySquareExpected W β t)) +
      ∑ k ∈ Finset.range (2 ^ l),
        Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β ((brownianDyadicGrid V).time l k)) *
          (∫ t in ((brownianDyadicGrid V).time l k : ℝ)..((brownianDyadicGrid V).time l (k + 1) : ℝ),
            actualParisiQueryRho W β t * actualParisiFullSusceptibilityExpected W β t) := by
  have hpi (t : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A => LJ.actualRowPotential W β t u.1)
      (actualParisiFullQuerySpinLaw W Z β V) :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).integrable_comp
      (LJ.integrable_actualRowPotential W β t V)
  have hpm (t : ℝ≥0) (ht : t ≤ V) :
      (∫ u : (Bool × Ω) × A, LJ.actualRowPotential W β t u.1
        ∂actualParisiFullQuerySpinLaw W Z β V) = actualParisiFullOverlap W β t / 2 :=
    LM4b.actualRowPotential_mean W Z β hβ t V ht
  have hq (s t : ℝ≥0) (c : ℝ) :
      Integrable (fun u : (Bool × Ω) × A =>
        c * (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) *
          ((actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
            (actualParisiQueryBrownianSystem W Z β hβ).B s (u.1.2, u.2)))
        (actualParisiFullQuerySpinLaw W Z β V) := by
    convert (LM4b.integrable_actualRowQueryDefect W Z β hβ s t V).const_mul c using 1
    funext u
    dsimp only [LM4b.actualRowQueryIncrement]
    change _ = c * ((scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) * _)
    ring
  have hAi (s t : ℝ≥0) : Integrable (fun u : (Bool × Ω) × A =>
      LJ.actualRowPotential W β t u.1 - LJ.actualRowPotential W β s u.1)
      (actualParisiFullQuerySpinLaw W Z β V) := by
    exact ((hpi t).sub (hpi s)).congr (ae_of_all _ (fun _ => rfl))
  have hint (k : ℕ) : Integrable (fun u : (Bool × Ω) × A =>
      β * actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k) *
        (LJ.actualRowPotential W β ((brownianDyadicGrid V).time l (k + 1)) u.1 -
          LJ.actualRowPotential W β ((brownianDyadicGrid V).time l k) u.1) +
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β ((brownianDyadicGrid V).time l k)) *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k) u.1.2) *
          ((actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l (k + 1)) (u.1.2, u.2) -
            (actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l k) (u.1.2, u.2)))
      (actualParisiFullQuerySpinLaw W Z β V) := by
    exact (((hAi ((brownianDyadicGrid V).time l k) ((brownianDyadicGrid V).time l (k + 1))).const_mul
        (β * actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k))).add
        (hq _ _ _)).congr (ae_of_all _ (fun _ => rfl))
  unfold jointRowLeftSum
  rw [integral_finsetSum _ (fun k _ => hint k)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  let s := (brownianDyadicGrid V).time l k
  let t := (brownianDyadicGrid V).time l (k + 1)
  have hst : s ≤ t := (brownianDyadicGrid V).monotone l (Nat.le_succ k)
  have htV : t ≤ V := LM3.dyadic_time_le_horizon V l (k + 1) (Finset.mem_range.mp hk)
  have hsV : s ≤ V := hst.trans htV
  have hA : (∫ u : (Bool × Ω) × A,
      (LJ.actualRowPotential W β t u.1 - LJ.actualRowPotential W β s u.1)
      ∂actualParisiFullQuerySpinLaw W Z β V) =
      (∫ r in (s : ℝ)..(t : ℝ), actualParisiFullSusceptibilitySquareExpected W β r) / 2 := by
    rw [integral_sub (hpi t) (hpi s), hpm t htV, hpm s hsV,
      actualParisiFullSusceptibilitySquareExpected_interval W β hβ s t hst]
    ring
  rw [integral_add ((hAi s t).const_mul _) (hq s t _)]
  have hmul (u : (Bool × Ω) × A) :
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) *
          ((actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
            (actualParisiQueryBrownianSystem W Z β hβ).B s (u.1.2, u.2)) =
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) *
        ((scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β s u.1.2) *
          LM4b.actualRowQueryIncrement W Z β hβ s t u) := by
    change _ = Real.sqrt _ * ((scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) * _)
    dsimp only [LM4b.actualRowQueryIncrement]
    ring
  change (∫ u, β * actualParisiFullSusceptibilityExpected W β s *
      (LJ.actualRowPotential W β t u.1 - LJ.actualRowPotential W β s u.1)
      ∂actualParisiFullQuerySpinLaw W Z β V) +
    (∫ u, Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β s) *
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β s u.1.2) *
        ((actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) -
          (actualParisiQueryBrownianSystem W Z β hβ).B s (u.1.2, u.2))
      ∂actualParisiFullQuerySpinLaw W Z β V) = _
  simp_rw [hmul]
  rw [integral_const_mul, hA,
    integral_const_mul, LM4b.actualRowQueryDefect_mean W Z β hβ s t V hst htV]
  change _ + Real.sqrt _ * (∫ r in (s : ℝ)..(t : ℝ),
    actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r) = _
  ring

theorem jointRowLeftSum_mean_tendsto (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    Tendsto (fun l => ∫ u, jointRowLeftSum W Z β hβ V l u
      ∂actualParisiFullQuerySpinLaw W Z β V) atTop (𝓝 (3 / 2 * actualParisiEnergyReference W β V)) := by
  have hp1 (t : ℝ) : |actualParisiFullSusceptibilityExpected W β t| ≤ 1 := by
    rw [abs_of_nonneg (actualParisiFullSusceptibilityExpected_nonneg W β t)]
    exact LBase.actual_susceptibility_le_one W β t
  have hr1 (t : ℝ) : |actualParisiFullSusceptibilitySquareExpected W β t| ≤ 1 := by
    rw [abs_of_nonneg (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1]
    exact (actualParisiFullSusceptibilitySquareExpected_bounds W β t).2
  have hg1 (t : ℝ) : |actualParisiQueryRho W β t * actualParisiFullSusceptibilityExpected W β t| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (actualParisiQueryRho_bounds W β hβ t).1]
    exact (mul_le_mul (actualParisiQueryRho_bounds W β hβ t).2 (hp1 t) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have h1 := N7.left_integrated_quadrature_tendsto
    (actualParisiFullSusceptibilityExpected W β) (actualParisiFullSusceptibilitySquareExpected W β)
    (continuous_actualParisiFullSusceptibilityExpected W β)
    (continuous_actualParisiFullSusceptibilitySquareExpected W β) hr1
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l i _ => brownianDyadicGrid_width_le V l i)
  have h2 := N7.left_integrated_quadrature_tendsto
    (fun t => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t))
    (fun t => actualParisiQueryRho W β t * actualParisiFullSusceptibilityExpected W β t)
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt
    ((continuous_actualParisiQueryRho W β).mul (continuous_actualParisiFullSusceptibilityExpected W β)) hg1
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l i _ => brownianDyadicGrid_width_le V l i)
  simp only [one_mul, brownianDyadicGrid_horizon] at h1 h2
  have he : (∫ t in (0 : ℝ)..(V : ℝ), Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t) *
      (actualParisiQueryRho W β t * actualParisiFullSusceptibilityExpected W β t)) =
      actualParisiEnergyReference W β V := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he] at h2
  have hh := (h1.const_mul (β / 2)).add h2
  have he' : β / 2 * (∫ t in (0 : ℝ)..(V : ℝ), actualParisiFullSusceptibilityExpected W β t *
      actualParisiFullSusceptibilitySquareExpected W β t) + actualParisiEnergyReference W β V =
      3 / 2 * actualParisiEnergyReference W β V := by
    rw [energyReference_eq_beta_integral_pr W β hβ V]
    ring
  rw [he'] at hh
  simpa only [jointRowLeftSum_mean W Z β hβ V] using hh

theorem jointRowIntegral_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    (∫ u, Zv u ∂actualParisiFullQuerySpinLaw W Z β V) = 3 / 2 * actualParisiEnergyReference W β V := by
  let μ := LM4.actualRowBaseLaw W Z
  let L := LM4.actualRowLink (A := A) β W V
  have hL : MemLp L 2 μ := (memLp_const (2 : ℝ)).mono'
    (LM4.measurable_actualRowLink β W V).aestronglyMeasurable
    (ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (LM4.actualRowLink_bounds β W V u).1]
      exact (LM4.actualRowLink_bounds β W V u).2))
  have hS (l : ℕ) : MemLp (jointRowLeftSum W Z β hβ V l) 2 μ := by
    have hi : MemLp (fun u => jointRowLeftSum W Z β hβ V l u - Zv u) 2 μ :=
      (memLp_two_iff_integrable_sq
        (((measurable_jointRowLeftSum W Z β hβ V l).aemeasurable.sub hZv.2.1.aemeasurable).aestronglyMeasurable)).mpr
        (hZv.2.2.1 l)
    convert hi.add hZv.2.1 using 1
    funext u
    simp only [Pi.add_apply, sub_add_cancel]
  have hlim := N7.integral_mul_tendsto_of_meanSquare hS hZv.2.1 hL hZv.2.2.2
  have he (f : (Bool × Ω) × A → ℝ) :
      (∫ u, f u ∂actualParisiFullQuerySpinLaw W Z β V) = ∫ u, L u * f u ∂μ := by
    rw [← LM4.actual_linkedRowLaw_eq]
    exact LM4.integral_linkedRowLaw (LM4.measurable_actualRowLink β W V)
      (ae_of_all _ (fun u => (LM4.actualRowLink_bounds β W V u).1.le))
  simp_rw [← he] at hlim
  exact tendsto_nhds_unique hlim (jointRowLeftSum_mean_tendsto W Z β hβ V)

end SKConstants.Completion.SJ3
