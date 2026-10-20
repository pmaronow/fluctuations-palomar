module

public import SKConstants.Completion.LM4b.ZetaBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SKConstants.Completion.LM4b
open LM4 Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def psiMomentConstant (β : ℝ) : ℝ := 2^14 * (1 + β)^2

def psiOfParts (ell J Q A N : Ω → ℝ) (β e : ℝ) (u : Ω) : ℝ :=
  rowInformation ell J Q u - β * zetaOfParts A N e u

theorem psiOfParts_centered_moments [IsProbabilityMeasure μ]
    {ell J Q A N : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hAm : Measurable A) (hNm : Measurable N)
    (hlink : ∀ᵐ u ∂μ, 0 ≤ ell u ∧ ell u ≤ 2) (hnorm : ∫ u, ell u ∂μ = 1)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ u ∂μ, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ))
    (e : ℝ) (he : |e| ≤ 1)
    (hA : ∀ᵐ u ∂μ, |A u| ≤ 33 * (1 + β) * (1 + (V : ℝ)))
    (hN : HasSubgaussianMGF N 4 μ) :
    let ν := linkedRowLaw μ ell
    let X := centeredObservable ν (psiOfParts ell J Q A N β e)
    (∀ p : ℕ, Integrable (fun u => X u ^ p) ν) ∧
    (∫ u, X u ∂ν = 0) ∧
    (∀ p : ℕ, 2 ≤ p → (∫ u, |X u| ^ p ∂ν) ≤
      (p.factorial : ℝ) * (psiMomentConstant β * (1 + (V : ℝ))) ^ p) := by
  let ν := linkedRowLaw μ ell
  let I := rowInformation ell J Q
  let ζ := zetaOfParts A N e
  let U := centeredObservable ν I
  let Z := centeredObservable ν ζ
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have hν : IsProbabilityMeasure ν := linkedRowLaw_isProbability hell hlink hnorm
  let := hν
  have hI := rowInformation_centered_moments hell hJm hQm hlink hnorm V hJ hQ
  have hZ := zetaOfParts_centered_moments hell hAm hNm hlink hnorm β hβ0.le V e he hA hN
  have hIm : Measurable I := measurable_rowInformation hell hJm hQm
  have hZm : Measurable ζ := (hAm.add hNm).sub_const _
  have hUm : Measurable U := hIm.sub_const _
  have hZm' : Measurable Z := hZm.sub_const _
  have hIi : Integrable I ν := by
    have hh := (hI.1 1).add (integrable_const (∫ u, I u ∂ν))
    exact hh.congr (ae_of_all _ (fun u => by simp [centeredObservable, I, ν]))
  have hZi : Integrable ζ ν := by
    have hh := (hZ.1 1).add (integrable_const (∫ u, ζ u ∂ν))
    exact hh.congr (ae_of_all _ (fun u => by simp [centeredObservable, ζ, ν]))
  have hEq (u : Ω) : centeredObservable ν (psiOfParts ell J Q A N β e) u = U u + (-β * Z u) := by
    unfold centeredObservable psiOfParts
    rw [integral_sub hIi (hZi.const_mul β), integral_const_mul]
    dsimp [U,Z,centeredObservable,I,ζ]
    ring
  have hUI (p : ℕ) : Integrable (fun u => |U u|^p) ν := by
    simpa only [Real.norm_eq_abs, norm_pow] using (hI.1 p).norm
  have hZI (p : ℕ) : Integrable (fun u => |-β * Z u|^p) ν := by
    simpa only [abs_mul, mul_pow] using
      ((show Integrable (fun u => |Z u|^p) ν by
        simpa only [Real.norm_eq_abs, norm_pow] using (hZ.1 p).norm).const_mul (|-β|^p))
  have hPI (p : ℕ) : Integrable (fun u => |centeredObservable ν (psiOfParts ell J Q A N β e) u|^p) ν := by
    simp_rw [hEq]
    exact integrable_abs_add_pow hUm (hZm'.const_mul (-β)) p (hUI p) (hZI p)
  refine ⟨fun p => (hPI p).mono'
    (((hIm.sub (hZm.const_mul β)).sub_const _).pow_const p).aestronglyMeasurable
    (ae_of_all _ (fun _ => by simp only [Real.norm_eq_abs, abs_pow]; rfl)), ?_, fun p hp => ?_⟩
  · change ∫ u, centeredObservable ν (psiOfParts ell J Q A N β e) u ∂ν = 0
    simp_rw [hEq]
    rw [integral_add (by simpa using hI.1 1) ((by simpa using hZ.1 1 : Integrable Z ν).const_mul (-β)),
      integral_const_mul]
    change (∫ u, U u ∂ν) + -β * (∫ u, Z u ∂ν) = 0
    rw [hI.2.1, hZ.2.1]
    ring
  · have hZM : (∫ u, |-β * Z u|^p ∂ν) ≤
        (p.factorial : ℝ) * (β * (512 * (1 + β) * (1 + (V : ℝ))))^p := by
      simp only [abs_mul, abs_neg, abs_of_pos hβ0, mul_pow, integral_const_mul]
      calc
        _ ≤ β^p * ((p.factorial : ℝ) * (512 * (1+β) * (1+(V:ℝ)))^p) :=
          mul_le_mul_of_nonneg_left (hZ.2.2 p hp) (pow_nonneg hβ0.le p)
        _ = _ := by simp only [mul_pow]; ring
    have hh := integral_abs_add_pow_le hUm (hZm'.const_mul (-β))
      (by positivity : 0 < 16 * (1 + (V:ℝ)))
      (by positivity : 0 < β * (512 * (1 + β) * (1 + (V:ℝ))))
      (hUI p) (hZI p) (hI.2.2 p hp) hZM
    have hh' : (∫ u, |centeredObservable ν (psiOfParts ell J Q A N β e) u|^p ∂ν) ≤
        (p.factorial : ℝ) * (16*(1+(V:ℝ)) + β*(512*(1+β)*(1+(V:ℝ))))^p := by
      simpa only [hEq] using hh.2
    change (∫ u, |centeredObservable ν (psiOfParts ell J Q A N β e) u|^p ∂ν) ≤ _
    apply hh'.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    unfold psiMomentConstant
    have hscale : 16 + β * (512 * (1+β)) ≤ 2^14 * (1+β)^2 := by
      nlinarith [sq_nonneg β]
    nlinarith [mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ 1+(V:ℝ))]

theorem psiOfParts_iid_abs [IsProbabilityMeasure μ]
    {ell J Q A N : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J) (hQm : Measurable Q)
    (hAm : Measurable A) (hNm : Measurable N)
    (hlink : ∀ᵐ u ∂μ, 0 ≤ ell u ∧ ell u ≤ 2) (hnorm : ∫ u, ell u ∂μ = 1)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ)
    (hQ : ∀ᵐ u ∂μ, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ)) (e : ℝ) (he : |e| ≤ 1)
    (hA : ∀ᵐ u ∂μ, |A u| ≤ 33 * (1 + β) * (1 + (V : ℝ)))
    (hN : HasSubgaussianMGF N 4 μ) {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := linkedRowLaw μ ell
    (Measure.pi (fun _ : Fin n => ν)).real
      {u | (n : ℝ) * η ≤ |∑ i : Fin n, centeredObservable ν (psiOfParts ell J Q A N β e) (u i)|} ≤
      2 * Real.exp (-(n : ℝ) * min
        (η^2 / (8 * (psiMomentConstant β * (1+(V:ℝ)))^2))
        (η / (4 * (psiMomentConstant β * (1+(V:ℝ)))))) := by
  let ν := linkedRowLaw μ ell
  have : IsProbabilityMeasure ν := linkedRowLaw_isProbability hell hlink hnorm
  have hm := psiOfParts_centered_moments hell hJm hQm hAm hNm hlink hnorm β hβ V hJ hQ e he hA hN
  have hXp : Measurable (centeredObservable ν (psiOfParts ell J Q A N β e)) :=
    (((measurable_rowInformation hell hJm hQm).sub
      (((hAm.add hNm).sub_const (e/2)).const_mul β)).sub_const _)
  have hK : 0 < psiMomentConstant β * (1+(V:ℝ)) := by
    unfold psiMomentConstant
    positivity
  have hmgf := localMGF_of_centered_factorial hXp hK hm.1 hm.2.1 hm.2.2
  simpa only [show 4 * (2 * (psiMomentConstant β * (1+(V:ℝ)))^2) =
      8 * (psiMomentConstant β * (1+(V:ℝ)))^2 by ring,
    show (1 / (2 * (psiMomentConstant β * (1+(V:ℝ))))) * η / 2 =
      η / (4 * (psiMomentConstant β * (1+(V:ℝ)))) by field_simp; ring] using
    iid_sum_abs_of_localMGF ν hXp hmgf (by positivity) (by positivity) hn hη

end SKConstants.Completion.LM4b
