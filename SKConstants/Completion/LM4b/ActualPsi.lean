module

public import SKConstants.Completion.LM4b.QueryPredictability
public import SKConstants.Completion.LM4b.PsiConcentration
public import SKConstants.Completion.LM4b.ActualZetaMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK LM4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualZetaDeterministic (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (w : ℕ → ℝ) (k : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  ∑ j ∈ Finset.range k, w j *
    (actualRowPotential W β (t (j+1)) u - actualRowPotential W β (t j) u)

theorem measurable_actualZetaDeterministic (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (w : ℕ → ℝ) (k : ℕ) : Measurable (actualZetaDeterministic (A:=A) W β t w k) :=
  Finset.measurable_fun_sum _ (fun j _ =>
    ((measurable_actualRowPotential W β (t (j+1))).sub (measurable_actualRowPotential W β (t j))).const_mul (w j))

theorem actualZeta_eq_parts (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (w c : ℕ → ℝ) (k : ℕ) (e : ℝ) :
    actualZeta W Z β hβ t w c k e =
      zetaOfParts (actualZetaDeterministic W β t w k)
        (actualNoise W Z β hβ (fun j => t (j+1)) c k) e := by
  funext u
  unfold actualZeta zetaOfParts actualZetaDeterministic actualNoise
  rw [predictableGaussianSum_eq_range_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  simp only [actualNoiseCoefficient, actualNoiseIncrement, actualRowQueryIncrement,
    brownianMeshIncrement]
  ring

omit [MeasurableSpace A] in
theorem actualZetaDeterministic_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (w v : ℕ → ℝ) (k : ℕ) (V : ℝ≥0)
    (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j) (hstart : v 0 ≤ β)
    (herror : ∑ j ∈ Finset.range k, |w j-v j| ≤ 10*β*(V:ℝ)) (u : (Bool × Ω) × A) :
    |actualZetaDeterministic W β t w k u| ≤ 33 * (1+β) * (1+(V:ℝ)) := by
  apply potential_weighted_increment_abs_le w v
    (fun j => actualParisiMagnetizationObservable W β (t j) u.1.2) k (scalarHiddenSign u.1.1) β (V:ℝ)
    _ (fun j => actualParisiMagnetizationObservable_abs_le W β (t j) u.1.2)
    hv hv0 hstart (by linarith) V.coe_nonneg herror
  cases u.1.1 <;> norm_num [scalarHiddenSign]

def actualPsi (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (J : (Bool × Ω) × A → ℝ) (t : ℕ → ℝ≥0) (w c : ℕ → ℝ) (k : ℕ) (e : ℝ)
    (u : (Bool × Ω) × A) : ℝ :=
  actualRowInformation β W V J (actualRowDBracket W β V) u - β * actualZeta W Z β hβ t w c k e u

theorem actualPsi_centered_moments_of_primitives
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks q V i)
    (J : (Bool × Ω) × A → ℝ) (hJm : Measurable J) (hJ : IsActualRowDIntegral W Z β hβ V J)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (w v c : ℕ → ℝ) (k : ℕ) (e : ℝ) (he : |e| ≤ 1)
    (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j) (hstart : v 0 ≤ β)
    (herror : ∑ j ∈ Finset.range k, |w j-v j| ≤ 10*β*(V:ℝ))
    (hbudget : ∑ j ∈ Finset.range k, (c j)^2 * (brownianMeshVariance (fun j => t (j+1)) j : ℝ) ≤ 1) :
    let ν := actualParisiFullQuerySpinLaw W Z β V
    let X := Concentration.centeredObservable ν (actualPsi W Z β hβ V J t w c k e)
    (∀ p : ℕ, Integrable (fun u => X u^p) ν) ∧ (∫ u, X u ∂ν = 0) ∧
      (∀ p : ℕ, 2 ≤ p → (∫ u, |X u|^p ∂ν) ≤
        (p.factorial:ℝ) * (psiMomentConstant β * (1+(V:ℝ)))^p) := by
  have hpredictable := actualQueryPredictableState W Z β hβ (fun j => t (j+1))
    (fun a b hab => ht (by omega)) c
  have hn := actualNoise_hasSubgaussianMGF_of_predictable W Z β hβ (fun j => t (j+1))
    (fun a b hab => ht (by omega)) c k hpredictable hbudget
  have hm := psiOfParts_centered_moments (measurable_actualRowLink β W V) hJm
    (measurable_actualRowDBracket W β V) (measurable_actualZetaDeterministic W β t w k)
    (measurable_actualNoise W Z β hβ (fun j => t (j+1)) c k)
    (ae_of_all _ (fun u => ⟨(actualRowLink_bounds β W V u).1.le, (actualRowLink_bounds β W V u).2⟩))
    (actualRowLink_integral β W Z V) β hβ V
    (actualRowDIntegral_hasSubgaussianMGF_of_transport W Z β hβ δ hδ ranks q V i htransport J hJ)
    (ae_of_all _ (actualRowDBracket_bounds W β hβ V)) e he
    (ae_of_all _ (actualZetaDeterministic_bound W β hβ t w v k V hv hv0 hstart herror)) hn
  have heq : actualPsi W Z β hβ V J t w c k e =
      psiOfParts (actualRowLink β W V) J (actualRowDBracket W β V)
        (actualZetaDeterministic W β t w k) (actualNoise W Z β hβ (fun j => t (j+1)) c k) β e := by
    funext u
    rw [actualPsi, actualZeta_eq_parts]
    rfl
  rw [heq]
  simpa only [actual_linkedRowLaw_eq] using hm

theorem actualPsi_iid_abs_of_primitives
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks q V i)
    (J : (Bool × Ω) × A → ℝ) (hJm : Measurable J) (hJ : IsActualRowDIntegral W Z β hβ V J)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (w v c : ℕ → ℝ) (k : ℕ) (e : ℝ) (he : |e| ≤ 1)
    (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j) (hstart : v 0 ≤ β)
    (herror : ∑ j ∈ Finset.range k, |w j-v j| ≤ 10*β*(V:ℝ))
    (hbudget : ∑ j ∈ Finset.range k, (c j)^2 * (brownianMeshVariance (fun j => t (j+1)) j : ℝ) ≤ 1)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := actualParisiFullQuerySpinLaw W Z β V
    (actualParisiFullMixedRowsLaw W Z β V n).real {u | (n:ℝ)*η ≤
      |∑ j : Fin n, Concentration.centeredObservable ν (actualPsi W Z β hβ V J t w c k e) (u j)|} ≤
      2 * Real.exp (-(n:ℝ) * min
        (η^2 / (8*(psiMomentConstant β*(1+(V:ℝ)))^2))
        (η / (4*(psiMomentConstant β*(1+(V:ℝ)))))) := by
  have hpredictable := actualQueryPredictableState W Z β hβ (fun j => t (j+1))
    (fun a b hab => ht (by omega)) c
  have hnmgf := actualNoise_hasSubgaussianMGF_of_predictable W Z β hβ (fun j => t (j+1))
    (fun a b hab => ht (by omega)) c k hpredictable hbudget
  have hm := psiOfParts_iid_abs (measurable_actualRowLink β W V) hJm
    (measurable_actualRowDBracket W β V) (measurable_actualZetaDeterministic W β t w k)
    (measurable_actualNoise W Z β hβ (fun j => t (j+1)) c k)
    (ae_of_all _ (fun u => ⟨(actualRowLink_bounds β W V u).1.le, (actualRowLink_bounds β W V u).2⟩))
    (actualRowLink_integral β W Z V) β hβ V
    (actualRowDIntegral_hasSubgaussianMGF_of_transport W Z β hβ δ hδ ranks q V i htransport J hJ)
    (ae_of_all _ (actualRowDBracket_bounds W β hβ V)) e he
    (ae_of_all _ (actualZetaDeterministic_bound W β hβ t w v k V hv hv0 hstart herror)) hnmgf hn hη
  have heq : actualPsi W Z β hβ V J t w c k e =
      psiOfParts (actualRowLink β W V) J (actualRowDBracket W β V)
        (actualZetaDeterministic W β t w k) (actualNoise W Z β hβ (fun j => t (j+1)) c k) β e := by
    funext u
    rw [actualPsi, actualZeta_eq_parts]
    rfl
  rw [heq]
  simpa only [actual_linkedRowLaw_eq, actualParisiFullMixedRowsLaw] using hm

end SKConstants.Completion.LM4b
