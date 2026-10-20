module

public import SKConstants.Completion.N9.ScalarBounds
public import SKConstants.Completion.N9.MomentAssembly
public import SKConstants.Completion.N9.FrozenQuery
public import SKConstants.Completion.N9.InitializedGeometry
public import SKConstants.Completion.LFine.EmpiricalCovariance
public import SKConstants.Completion.LFine.EmpiricalNormMoments
public import SKConstants.Completion.LM5.EnergyExpectation
public import SKConstants.Completion.Blueprint.NodesLower
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem fineEnergy_frozenQuery_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (a h f : ℝ≥0)
    (n m j : ℕ) (hn : 0 < n) (hdim : m+j=n)
    (s d L M b : ℝ) (hs : 0 < s) (hd : 0 ≤ d) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (E : Ξ → Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Ξ → Fin n → ℝ)
    (Bpast Dpast : Ξ → Fin n → ScalarContinuousPath a)
    (hE : ∀ p i k, dot (E p i) (E p k) = if i=k then 1 else 0)
    (hm₀ : ∀ p, E p *ᵥ m₀ p = 0)
    (hposterior : ∀ p, FreshPosteriorMeanStatement W β hβ a h f n (Bpast p) (Dpast p)) :
    let T := fun p => frozenQueryTarget W β hβ a s (m₀ p) (Bpast p) (Dpast p)
    let ζ := fun p => frozenQueryMixedMean W β hβ a h f (Bpast p) (Dpast p)
    let Y := fun p => queryRemovedSquare n (E p) (T p)
    let z := fun p => (n : ℝ)⁻¹ * ∑ i, ζ p i
    (∀ p i, 0 ≤ ζ p i ∧ ζ p i ≤ L*s) →
    (∀ i, Measurable (fun p => (ζ p i,T p i))) →
    iIndepFun (fun i p => (ζ p i,T p i)) μ →
    (∀ i, MemLp (fun p => T p i) 4 μ) →
    (∀ i, (∫ p, (T p i)^2 ∂μ) = 1) →
    (∀ i, (∫ p, (T p i)^4 ∂μ) ≤ M*d/s^2) →
    (∫ p, z p ∂μ) = b →
    Integrable Y μ → Integrable (fun p => (Y p)^2) μ →
    (∫ p, Y p ∂μ) ≤ (j : ℝ)*d/((n : ℝ)*s^2) →
    (∫ p, (Y p)^2 ∂μ) ≤ 3*((j : ℝ)^2+j)*d^2/((n : ℝ)^2*s^4) →
    Integrable (fun p => frozenQueryExpectation W β hβ a h f s
      (E p) (m₀ p) (Bpast p) (Dpast p)) μ →
    s*b - ((M+4)*L)*fineCellError n j s d ≤
      ∫ p, frozenQueryExpectation W β hβ a h f s (E p) (m₀ p) (Bpast p) (Dpast p) ∂μ := by
  dsimp only
  intro hζ hrow hind hT hunit hfourth hzmean hYi hy₂i hEY hEY₂ hki
  let T := fun p => frozenQueryTarget W β hβ a s (m₀ p) (Bpast p) (Dpast p)
  let ζ := fun p => frozenQueryMixedMean W β hβ a h f (Bpast p) (Dpast p)
  let Q := fun p => queryTotalSquare n (T p)
  let Y := fun p => queryRemovedSquare n (E p) (T p)
  let z := fun p => (n : ℝ)⁻¹ * ∑ i, ζ p i
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrank : (n : ℝ)-(m : ℝ) = (j : ℝ) := by
    have he : (m : ℝ)+(j : ℝ) = (n : ℝ) := by exact_mod_cast hdim
    linarith
  have hQeq (p : Ξ) : Q p = (n : ℝ)⁻¹*∑ i, (T p i)^2 := by
    simp only [Q, queryTotalSquare, dot, pow_two]
  have hT₂ (i : Fin n) : MemLp (fun p => T p i) 2 μ :=
    (hT i).mono_exponent (by norm_num)
  have hQmem : MemLp Q 2 μ := by
    convert (memLp_finsetSum Finset.univ
      (fun i _ => memLp_square_of_four μ (fun p => T p i) (hT i))).const_mul ((n : ℝ)⁻¹) using 1
    ext p
    exact hQeq p
  have hQi : Integrable Q μ := hQmem.integrable (by norm_num)
  have hQmean : (∫ p, Q p ∂μ) = 1 := by
    simp_rw [hQeq]
    exact empirical_norm_square_mean μ n hn (fun i p => T p i) hT₂ hunit
  have hqi : Integrable (fun p => (Q p-1)^2) μ :=
    (hQmem.sub (memLp_const 1)).integrable_sq
  have hindT : iIndepFun (fun i p => T p i) μ :=
    hind.comp (fun _ x => x.2) (fun _ => measurable_snd)
  have hEQ : (∫ p, (Q p-1)^2 ∂μ) ≤ M*d/((n : ℝ)*s^2) := by
    have hfluct := empirical_norm_square_fluctuation_le μ n hn (fun i p => T p i)
      hT hindT hunit (M*d/s^2) hfourth
    simp_rw [← hQeq] at hfluct
    calc
      _ ≤ (M*d/s^2)/(n : ℝ) := hfluct
      _ = _ := by ring
  have hzbounds (p : Ξ) : 0 ≤ z p ∧ z p ≤ L*s := by
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hnR.le)
        (Finset.sum_nonneg (fun i _ => (hζ p i).1))
    · calc
        _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, L*s := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => (hζ p i).2)) (inv_nonneg.mpr hnR.le)
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hnR.ne']
  have hzm : Measurable z :=
    (Finset.measurable_sum _ (fun i _ => (hrow i).fst)).const_mul ((n : ℝ)⁻¹)
  have hzi : Integrable z μ := Integrable.of_bound hzm.aestronglyMeasurable (L*s)
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hzbounds p).1]
      exact (hzbounds p).2)
  have hci : Integrable (fun p => z p*(Q p-1)) μ :=
    (hQi.sub (integrable_const 1)).bdd_mul hzm.aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hzbounds p).1]
        exact (hzbounds p).2)
  let R := fun i p => (ζ p i,(T p i)^2)
  have hmR (i : Fin n) : Measurable (R i) :=
    (hrow i).fst.prodMk ((hrow i).snd.pow_const 2)
  have hiR : iIndepFun R μ :=
    hind.comp (fun _ x => (x.1,x.2^2)) (fun _ => by fun_prop)
  have hcov : -(L*s)/(n : ℝ) ≤ ∫ p, z p*(Q p-1) ∂μ := by
    have hc := empirical_covariance_lower μ n hn R hmR hiR (L*s)
      (fun i p => hζ p i) (fun i p => sq_nonneg (T p i))
      (fun i => (hT₂ i).integrable_sq) hunit
    change -(L*s)/(n : ℝ) ≤ ∫ p, z p*((n : ℝ)⁻¹*∑ i, (T p i)^2-1) ∂μ at hc
    simpa only [← hQeq] using hc
  have hx : ∀ᵐ p ∂μ, 0 ≤ Q p-Y p := ae_of_all _ fun p =>
    sub_nonneg.mpr (queryRemovedSquare_le_total n hnR (E p) (T p) (hE p))
  have hy : ∀ᵐ p ∂μ, 0 ≤ Y p := ae_of_all _ fun p =>
    queryRemovedSquare_nonneg n hnR.le (E p) (T p)
  have hCi := integrable_residual_sqrt μ Q Y hQi hYi hx hy
  have hEi : Integrable (fun p => s*z p*Real.sqrt (Q p-Y p)) μ := by
    convert (hCi.bdd_mul hzm.aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hzbounds p).1]
        exact (hzbounds p).2)).const_mul s using 1
    ext p
    ring
  have hres := expected_fineQueryLowerIntegrand_cell μ Q Y z n j hn s d L M b hs hd hL hM
    hx hy (ae_of_all _ hzbounds) hQi hYi hzi hci hqi hy₂i hCi hEi hQmean hzmean hcov hEY hEQ hEY₂
  have hlowi : Integrable (fun p => fineQueryLowerIntegrand n j s L (Q p) (Y p) (z p)) μ := by
    have hdiag : Integrable (fun p => L*s^2*Real.sqrt (Q p-Y p)*j/n) μ := by
      convert hCi.const_mul (L*s^2*j/n) using 1
      ext p
      ring
    exact (hEi.sub hdiag).sub (integrable_const (2*L*s/n))
  apply hres.trans
  apply integral_mono_ae hlowi hki
  apply ae_of_all
  intro p
  have hbound := freshRows_oneQuery_lower W β hβ a h f n m hn (Bpast p) (Dpast p)
    s hs L hL (E p) (m₀ p) (hE p) (hm₀ p) (hposterior p)
    (fun i => by
      change |ζ p i| ≤ L*s
      rw [abs_of_nonneg (hζ p i).1]
      exact (hζ p i).2)
  dsimp only at hbound
  change s*queryResidualNorm n (E p) (T p)*(z p) -
    L*s^2*queryResidualNorm n (E p) (T p)*((n : ℝ)-(m : ℝ))/n - 2*L*s/n ≤
      frozenQueryExpectation W β hβ a h f s (E p) (m₀ p) (Bpast p) (Dpast p) at hbound
  rw [queryResidualNorm_eq_sqrt_difference n hnR (E p) (T p) (hE p), hrank] at hbound
  convert hbound using 1
  dsimp only [fineQueryLowerIntegrand,Q,Y]
  ring

theorem fineEnergy_source_zeroQueries_mean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r : ℕ) (hr : 0 < r) :
    (∫ z, LM5.growingSourceEnergy W β hβ δ r 0 z ∂M1.SourceLinkedLaw W β hβ δ r 0) = 0 := by
  rw [LM5.growingSource_energy_integral_eq_query W β hβ δ r 0 (by omega)]
  simp only [LM5.growingSourceQueryEnergy, LC5.paperQueryEnergy, Finset.univ_eq_empty,
    Finset.sum_empty, integral_zero]

theorem fineEnergy_source_zeroQueries_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (hsmall : (δ : ℝ) ≤ 1) (r : ℕ) (hr : 0 < r) :
    actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ 0) -
      fineEnergyQuadratureConstant β*(δ : ℝ) ≤
      ∫ z, LM5.growingSourceEnergy W β hβ δ r 0 z ∂M1.SourceLinkedLaw W β hβ δ r 0 := by
  rw [fineEnergy_source_zeroQueries_mean W β hβ δ r hr]
  have hquad := LQ.actual_growing_energy_error W β hβ δ hδ 0 (fun i hi => by
    have hi0 : i=0 := by omega
    subst i
    have hd0 : (growingQueryDuration δ 0 : ℝ) = (δ : ℝ) := by
      simp only [growingQueryDuration_coe, growingQueryTime_zero, NNReal.coe_zero,
        zero_div, Real.exp_zero, mul_one]
    exact_mod_cast (hd0.trans_le hsmall))
  simp only [LQ.actualParisiGrowingEnergySum, Finset.range_zero, Finset.sum_empty] at hquad
  change |0-actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ 0)| ≤
    fineEnergyQuadratureConstant β*(δ : ℝ) at hquad
  linarith [(abs_le.mp hquad).1]

end SKConstants.Completion.N9
