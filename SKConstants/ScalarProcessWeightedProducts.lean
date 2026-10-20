module

public import SKConstants.ScalarProcessMixedRowCovariances
public import SKConstants.SubGaussianProductsSecondMoment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
namespace SKConstants
open Concentration
set_option backward.isDefEq.respectTransparency true
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem scalarContinuousPosteriorIncrement_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) (hST : S ≤ T) :
    HasSubgaussianMGF (scalarContinuousPosteriorIncrement z B S T) (T-S)
      (scalarHiddenBrownianLaw z P) := by
  let t : ℕ → ℝ≥0 := fun i => if i=0 then S else T
  have ht : Monotone t := by
    intro i j hij
    by_cases hi : i=0
    · subst i
      by_cases hj : j=0
      · subst j; exact le_rfl
      · simpa only [t,ite_eq_left rfl,ite_eq_right hj] using hST
    · have hj : j ≠ 0 := by omega
      simp only [t,ite_eq_right hi,ite_eq_right hj,le_refl]
  have h := scalarContinuousPosterior_linearForm_hasSubgaussianMGF P z B hB t ht (fun _ => 1) 1
  simpa only [Finset.range_one,Finset.sum_singleton,t,ite_eq_left rfl,ite_eq_right (by decide : (1:ℕ)≠0),
    one_mul,nnnorm_one,one_pow,ite_true] using h

def scalarDurationNormalizedPosteriorIncrement (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (S T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  scalarContinuousPosteriorIncrement z B S T u / Real.sqrt ((T:ℝ)-(S:ℝ))

theorem measurable_scalarDurationNormalizedPosteriorIncrement
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ v, Measurable (B v)) (S T : ℝ≥0) :
    Measurable (scalarDurationNormalizedPosteriorIncrement z B S T) := by
  have hY (v : ℝ≥0) : Measurable (scalarHiddenContinuousField z B v) :=
    (measurable_const.add (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul_const _)).add
      ((hBm v).comp measurable_snd)
  exact ((measurable_scalarTanh.comp (hY T)).sub (measurable_scalarTanh.comp (hY S))).div_const _

theorem scalarDurationNormalizedPosteriorIncrement_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) (hST : S < T) :
    HasSubgaussianMGF (scalarDurationNormalizedPosteriorIncrement z B S T) 1
      (scalarHiddenBrownianLaw z P) := by
  have hd : 0 < (T:ℝ)-(S:ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr hST)
  have hs := Real.sq_sqrt hd.le
  have h := (scalarContinuousPosteriorIncrement_hasSubgaussianMGF P z B hB S T hST.le).const_mul
    (Real.sqrt ((T:ℝ)-(S:ℝ)))⁻¹
  convert h using 1
  · ext u
    simp only [scalarDurationNormalizedPosteriorIncrement,div_eq_mul_inv,mul_comm]
  · apply NNReal.eq
    change (1:ℝ) = ((Real.sqrt ((T:ℝ)-(S:ℝ)))⁻¹)^2*(T-S:ℝ≥0)
    rw [NNReal.coe_sub hST.le,inv_pow,hs]
    field_simp

def scalarWeightedProductMGFProxy (R : ℝ) (V : ℝ≥0) : ℝ≥0 :=
  max 1 (scalarPosteriorRowMGFProxy R V)

def scalarPosteriorDurationProduct (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (a : EuclideanSpace ℝ (Fin d)) (S T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  ⟪scalarNormalizedPosteriorRow z B t
    (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ *
    scalarDurationNormalizedPosteriorIncrement z B S T u

theorem measurable_scalarPosteriorDurationProduct
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ v, Measurable (B v)) (t : ℕ → ℝ≥0)
    (a : EuclideanSpace ℝ (Fin d)) (S T : ℝ≥0) :
    Measurable (scalarPosteriorDurationProduct z B t a S T) := by
  have hm := measurable_scalarNormalizedPosteriorRow (d := d) z B hBm t
    (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1)))
  have hI : Measurable (fun u => ⟪scalarNormalizedPosteriorRow z B t
    (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ) := by fun_prop
  exact hI.mul (measurable_scalarDurationNormalizedPosteriorIncrement z B hBm S T)

theorem scalarActualPosterior_durationProduct_secondMoment_le
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hBm : ∀ v, Measurable (B v))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0:ℝ)) (htV : t d ≤ V)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1)
    (S T : ℝ≥0) (hST : S < T) :
    (∫ u, (⟪scalarNormalizedPosteriorRow z B t
        (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ *
      scalarDurationNormalizedPosteriorIncrement z B S T u)^2
      ∂scalarHiddenBrownianLaw z P) ≤
      correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ) := by
  have hX := scalarActualNormalizedPosteriorRow_unit_hasSubgaussianMGF P z B hB R hR hz t ht V ht1 htV a ha
  have hXm : Measurable (fun u => ⟪scalarNormalizedPosteriorRow z B t
      (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ) := by
    have hm := measurable_scalarNormalizedPosteriorRow (d := d) z B hBm t
      (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1)))
    fun_prop
  have hYm := measurable_scalarDurationNormalizedPosteriorIncrement z B hBm S T
  have hY := scalarDurationNormalizedPosteriorIncrement_hasSubgaussianMGF P z B hB S T hST
  have hs := subGaussian_correlated_product_secondMoment (scalarHiddenBrownianLaw z P) _ _ hXm hYm
    (scalarWeightedProductMGFProxy R V) 1 (le_max_left _ _) (by norm_num)
    (hasSubgaussianMGF_of_proxy_le hX (le_max_right _ _)) hY
    (scalarActualNormalizedPosteriorRow_unit_secondMoment_le_one P z B hB R hR hz t ht V ht1 htV a ha)
  simpa only [NNReal.coe_one,one_mul] using hs

theorem scalarActualPosterior_durationProduct_localMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hBm : ∀ v, Measurable (B v))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0:ℝ)) (htV : t d ≤ V)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1)
    (S T : ℝ≥0) (hST : S < T) :
    LocalQuadraticMGF (centeredObservable (scalarHiddenBrownianLaw z P)
      (fun u => ⟪scalarNormalizedPosteriorRow z B t
          (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ *
        scalarDurationNormalizedPosteriorIncrement z B S T u))
      (scalarHiddenBrownianLaw z P)
      (16*correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ))
      (1/(4*productVarianceScale (Real.sqrt (scalarWeightedProductMGFProxy R V:ℝ))
        (correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ)))) := by
  have hX := scalarActualNormalizedPosteriorRow_unit_hasSubgaussianMGF P z B hB R hR hz t ht V ht1 htV a ha
  have hXm : Measurable (fun u => ⟪scalarNormalizedPosteriorRow z B t
      (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ) := by
    have hm := measurable_scalarNormalizedPosteriorRow (d := d) z B hBm t
      (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1)))
    fun_prop
  have hYm := measurable_scalarDurationNormalizedPosteriorIncrement z B hBm S T
  exact subGaussian_correlated_product_balanced_localMGF (scalarHiddenBrownianLaw z P) _ _ hXm hYm
    (scalarWeightedProductMGFProxy R V) (le_max_left _ _)
    (hasSubgaussianMGF_of_proxy_le hX (le_max_right _ _))
    (scalarDurationNormalizedPosteriorIncrement_hasSubgaussianMGF P z B hB S T hST)
    (scalarActualNormalizedPosteriorRow_unit_secondMoment_le_one P z B hB R hR hz t ht V ht1 htV a ha)

private theorem scalarLocalQuadraticMGF_productCopy {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ) (v r : ℝ)
    (h : LocalQuadraticMGF F μ v r) {n : ℕ} (i : Fin n) :
    LocalQuadraticMGF (fun ω : Fin n → A => F (ω i))
      (Measure.pi (fun _ : Fin n => μ)) v r where
  integrable_exp_mul θ hθ :=
    (measurePreserving_eval (fun _ : Fin n => μ) i).hasLaw.integrable_comp (h.integrable_exp_mul θ hθ)
  mgf_le θ hθ := by
    have hl := (measurePreserving_eval (fun _ : Fin n => μ) i).hasLaw
    have he := hl.integral_comp (h.integrable_exp_mul θ hθ).aestronglyMeasurable
    change (∫ ω : Fin n → A, Real.exp (θ*F (ω i)) ∂Measure.pi (fun _ => μ)) =
      mgf F μ θ at he
    rw [show mgf (fun ω : Fin n → A => F (ω i)) (Measure.pi (fun _ => μ)) θ = mgf F μ θ from he]
    exact h.mgf_le θ hθ

theorem scalarActualPosterior_durationProduct_average_tail
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hBm : ∀ v, Measurable (B v))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0:ℝ)) (htV : t d ≤ V)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1)
    (S T : ℝ≥0) (hST : S < T) (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    (scalarPosteriorRowsLaw P z n).real {ω | η ≤
      |(∑ i : Fin n, centeredObservable (scalarHiddenBrownianLaw z P)
        (scalarPosteriorDurationProduct z B t a S T) (ω i))/(n:ℝ)|} ≤
      2*Real.exp (-(n:ℝ)*min
        (η^2/(64*correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ)))
        (η/(8*productVarianceScale (Real.sqrt (scalarWeightedProductMGFProxy R V:ℝ))
          (correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ))))) := by
  let F := centeredObservable (scalarHiddenBrownianLaw z P) (scalarPosteriorDurationProduct z B t a S T)
  have hF : Measurable F := (measurable_scalarPosteriorDurationProduct z B hBm t a S T).sub_const _
  have hLocal := scalarActualPosterior_durationProduct_localMGF P z B hB hBm R hR hz
    t ht V ht1 htV a ha S T hST
  change LocalQuadraticMGF F (scalarHiddenBrownianLaw z P) _ _ at hLocal
  have hK : 1 ≤ (scalarWeightedProductMGFProxy R V:ℝ) := le_max_left _ _
  have hkp : 0 < Real.sqrt (scalarWeightedProductMGFProxy R V:ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs := correlatedProductVarianceFactor_pos hK
  have hb := productVarianceScale_pos (s := correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ)) hkp
  have hi := iIndepFun_pi (μ := fun _ : Fin n => scalarHiddenBrownianLaw z P)
    (X := fun _ => F) (fun _ => hF.aemeasurable)
  have hh := independent_average_bernstein hn hi (fun i => hF.comp (measurable_pi_apply i))
    (fun i => scalarLocalQuadraticMGF_productCopy _ F _ _ hLocal i)
    (by positivity) (by positivity) hη
  convert hh using 1 <;> simp only [scalarPosteriorRowsLaw,F,div_eq_mul_inv,mul_comm] <;> ring

def scalarWeightedPosteriorForm (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (q : ℕ → ℝ≥0)
    (w : ℕ → ℝ) (m : ℕ) (D : ℝ≥0) (u : Bool × Ω) : ℝ :=
  (∑ j ∈ Finset.range m, w j*scalarContinuousPosteriorIncrement z B (q j) (q (j+1)) u)/
    Real.sqrt (D:ℝ)

theorem measurable_scalarWeightedPosteriorForm
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ v, Measurable (B v))
    (q : ℕ → ℝ≥0) (w : ℕ → ℝ) (m : ℕ) (D : ℝ≥0) :
    Measurable (scalarWeightedPosteriorForm z B q w m D) := by
  have hY (v : ℝ≥0) : Measurable (scalarHiddenContinuousField z B v) :=
    (measurable_const.add (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul_const _)).add
      ((hBm v).comp measurable_snd)
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j hj
  exact (((measurable_scalarTanh.comp (hY (q (j+1)))).sub
    (measurable_scalarTanh.comp (hY (q j)))).const_mul _)

theorem scalarWeightedPosteriorForm_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : Monotone q)
    (w : ℕ → ℝ) (m : ℕ) (D : ℝ≥0) (hD : 0 < D)
    (hbudget : ∑ j ∈ Finset.range m, ‖w j‖₊^2*(q (j+1)-q j) ≤ D) :
    HasSubgaussianMGF (scalarWeightedPosteriorForm z B q w m D) 1
      (scalarHiddenBrownianLaw z P) :=
  hasSubgaussianMGF_div_sqrt_proxy hD (hasSubgaussianMGF_of_proxy_le
    (scalarContinuousPosterior_linearForm_hasSubgaussianMGF P z B hB q hq w m) hbudget)

theorem scalarActualPosterior_weightedProduct_localMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hBm : ∀ v, Measurable (B v))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0:ℝ)) (htV : t d ≤ V)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (w : ℕ → ℝ) (m : ℕ)
    (D : ℝ≥0) (hD : 0 < D)
    (hbudget : ∑ j ∈ Finset.range m, ‖w j‖₊^2*(q (j+1)-q j) ≤ D) :
    LocalQuadraticMGF (centeredObservable (scalarHiddenBrownianLaw z P)
      (fun u => ⟪scalarNormalizedPosteriorRow z B t
          (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ *
        scalarWeightedPosteriorForm z B q w m D u))
      (scalarHiddenBrownianLaw z P)
      (16*correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ))
      (1/(4*productVarianceScale (Real.sqrt (scalarWeightedProductMGFProxy R V:ℝ))
        (correlatedProductVarianceFactor (scalarWeightedProductMGFProxy R V:ℝ)))) := by
  have hX := scalarActualNormalizedPosteriorRow_unit_hasSubgaussianMGF P z B hB R hR hz t ht V ht1 htV a ha
  have hXm : Measurable (fun u => ⟪scalarNormalizedPosteriorRow z B t
      (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ) := by
    have hm := measurable_scalarNormalizedPosteriorRow (d := d) z B hBm t
      (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1)))
    fun_prop
  exact subGaussian_correlated_product_balanced_localMGF (scalarHiddenBrownianLaw z P) _ _ hXm
    (measurable_scalarWeightedPosteriorForm z B hBm q w m D)
    (scalarWeightedProductMGFProxy R V) (le_max_left _ _)
    (hasSubgaussianMGF_of_proxy_le hX (le_max_right _ _))
    (scalarWeightedPosteriorForm_hasSubgaussianMGF P z B hB q hq w m D hD hbudget)
    (scalarActualNormalizedPosteriorRow_unit_secondMoment_le_one P z B hB R hR hz t ht V ht1 htV a ha)

end SKConstants
