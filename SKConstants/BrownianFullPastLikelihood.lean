module
public import SKConstants.BrownianContinuousLikelihood
public import SKConstants.GaussianStaticLikelihoodLimit

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianFullPastExponential {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t)
    (θ : ℝ) (n : ℕ) (u : A × Ω) : ℝ :=
  Real.exp (θ*brownianStaticPredictableSum D t H n u-
    θ^2*brownianStaticPredictableVariation D t H n u/2)

lemma measurable_brownianFullPastExponential {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    Measurable (brownianFullPastExponential D t H θ n) := by
  let Φ := fun u : A × (Iic (t n) → ℝ) =>
    Real.exp (θ*brownianStaticPastSum t ht H n u-θ^2*brownianStaticPastVariation t ht H n u/2)
  have hΦ : Measurable Φ :=
    (((measurable_brownianStaticPastSum t ht H hH n).const_mul θ).sub
      (((measurable_brownianStaticPastVariation t ht H hH n).const_mul (θ^2)).div_const 2)).exp
  convert hΦ.comp (measurable_fst.prodMk
    ((Measurable.of_eval (fun s : Iic (t n) => hmD s)).comp measurable_snd)) using 1
  funext u
  rw [brownianFullPastExponential,brownianStaticPredictableSum,predictableGaussianSum_eq_fin_sum,
    brownianStaticPredictableVariation,predictableGaussianVariation_eq_fin_sum]
  rfl

lemma brownianFullPastExponential_integral {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    Integrable (brownianFullPastExponential D t H θ n) (P.prod Q) ∧
      (∫ u, brownianFullPastExponential D t H θ n u ∂P.prod Q) = 1 :=
  brownianStaticPredictableExponential_integral P Q D hD hmD t ht H hH θ n

lemma brownianFullPastExponential_conditional_mean_one {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) (a : A) :
    (∫⁻ ω, ENNReal.ofReal (brownianFullPastExponential D t H θ n (a,ω)) ∂Q) = 1 := by
  have hm := (measurable_brownianFullPastExponential D hmD t ht H hH θ n).ennreal_ofReal
  have hi := brownianFullPastExponential_integral (Measure.dirac a) Q D hD hmD t ht H hH θ n
  have he : (∫⁻ u, ENNReal.ofReal (brownianFullPastExponential D t H θ n u)
      ∂(Measure.dirac a).prod Q) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun _ => (Real.exp_pos _).le)),hi.2]
    norm_num
  rw [lintegral_prod _ hm.aemeasurable] at he
  have hu : Measurable (Function.uncurry (fun a ω =>
    ENNReal.ofReal (brownianFullPastExponential D t H θ n (a,ω)))) := hm
  rw [lintegral_dirac' a hu.lintegral_prod_right] at he
  exact he

theorem brownianFullPastExponential_preserves_static_marginal {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    ((P.prod Q).withDensity (fun u => ENNReal.ofReal
      (brownianFullPastExponential D t H θ n u))).map Prod.fst = P := by
  let f : A × Ω → ℝ≥0∞ := fun u => ENNReal.ofReal (brownianFullPastExponential D t H θ n u)
  have hm : Measurable f := (measurable_brownianFullPastExponential D hmD t ht H hH θ n).ennreal_ofReal
  let κ : Kernel A Ω := (Kernel.const A Q).withDensity (fun a ω => f (a,ω))
  have hk : IsMarkovKernel κ := by
    constructor
    intro a
    constructor
    dsimp only [κ]
    rw [Kernel.withDensity_apply _ hm,Kernel.const_apply,withDensity_apply _
      MeasurableSet.univ,Measure.restrict_univ]
    exact brownianFullPastExponential_conditional_mean_one Q D hD hmD t ht H hH θ n a
  let := hk
  have he : P ⊗ₘ κ = (P.prod Q).withDensity f := by
    dsimp only [κ]
    rw [Measure.compProd_withDensity hm,Measure.compProd_const]
  rw [← he]
  exact Measure.fst_compProd P κ

lemma brownianFullPastExponential_square {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t) (n : ℕ) (u : A × Ω) :
    brownianFullPastExponential D t H 1 n u ^ 2 =
      brownianFullPastExponential D t H 2 n u *
        Real.exp (brownianStaticPredictableVariation D t H n u) := by
  rw [brownianFullPastExponential,brownianFullPastExponential,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

lemma eLpNorm_brownianFullPastExponential_two_le {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) (V : ℝ)
    (hV : ∀ u, brownianStaticPredictableVariation D t H n u ≤ V) :
    eLpNorm (brownianFullPastExponential D t H 1 n) 2 (P.prod Q) ≤
      ENNReal.ofReal (Real.exp V) ^ (1/(2 : ℝ)) := by
  have hm := measurable_brownianFullPastExponential D hmD t ht H hH 1 n
  have hp (u : A × Ω) : 0 ≤ brownianFullPastExponential D t H 1 n u := (Real.exp_pos _).le
  have htwo := brownianFullPastExponential_integral P Q D hD hmD t ht H hH 2 n
  have hbound : ∀ u, brownianFullPastExponential D t H 1 n u ^ 2 ≤
      Real.exp V * brownianFullPastExponential D t H 2 n u := by
    intro u
    rw [brownianFullPastExponential_square]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hV u)) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hi : Integrable (fun u => brownianFullPastExponential D t H 1 n u ^ 2) (P.prod Q) :=
    (htwo.1.const_mul (Real.exp V)).mono' (hm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (brownianFullPastExponential D t H 1 n u))]
        exact hbound u))
  have hs : (∫ u, brownianFullPastExponential D t H 1 n u ^ 2 ∂P.prod Q) ≤ Real.exp V := by
    have hh := integral_mono hi (htwo.1.const_mul (Real.exp V)) hbound
    rwa [integral_const_mul,htwo.2,mul_one] at hh
  have hl : (∫⁻ u, ENNReal.ofReal (brownianFullPastExponential D t H 1 n u ^ 2) ∂P.prod Q) ≤
      ENNReal.ofReal (Real.exp V) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [Real.enorm_eq_ofReal (hp _),ENNReal.rpow_two,← ENNReal.ofReal_pow (hp _) 2]
  exact ENNReal.rpow_le_rpow hl (by norm_num)

theorem brownianFullPast_density_limit {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j)) (N : ℕ → ℕ)
    (H : (j : ℕ) → BrownianStaticPredictableCoefficient A (t j))
    (hH : ∀ j k, Measurable (H j k)) (V : ℝ)
    (hV : ∀ j u, brownianStaticPredictableVariation D (t j) (H j) (N j) u ≤ V)
    (Y : A × Ω → ℝ) (hlim : TendstoInMeasure (P.prod Q)
      (fun j => brownianFullPastExponential D (t j) (H j) 1 (N j)) atTop Y) :
    Integrable Y (P.prod Q) ∧ (∀ᵐ u ∂P.prod Q, 0 ≤ Y u) ∧
      (∫ u, Y u ∂P.prod Q) = 1 ∧
      IsProbabilityMeasure ((P.prod Q).withDensity (fun u => ENNReal.ofReal (Y u))) ∧
      (((P.prod Q).withDensity (fun u => ENNReal.ofReal (Y u))).map Prod.fst = P) ∧
      Tendsto (fun j => eLpNorm (brownianFullPastExponential D (t j) (H j) 1 (N j)-Y) 1
        (P.prod Q)) atTop (𝓝 0) := by
  let X : ℕ → A × Ω → ℝ := fun j => brownianFullPastExponential D (t j) (H j) 1 (N j)
  let C : ℝ≥0 := ⟨(Real.exp V)^(1/(2 : ℝ)),Real.rpow_nonneg (Real.exp_pos V).le _⟩
  have hm (j : ℕ) : Measurable (X j) := measurable_brownianFullPastExponential D hmD
    (t j) (ht j) (H j) (hH j) 1 (N j)
  have hcap (j : ℕ) : eLpNorm (X j) 2 (P.prod Q) ≤ C := by
    have hb := eLpNorm_brownianFullPastExponential_two_le P Q D hD hmD
      (t j) (ht j) (H j) (hH j) (N j) V (hV j)
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (X j) 2 (P.prod Q) ≤ ENNReal.ofReal ((Real.exp V)^(1/(2 : ℝ)))
    simpa only [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos V).le (by norm_num : 0 ≤ 1/(2 : ℝ))] using hb
  have hi (j : ℕ) : Integrable (X j) (P.prod Q) :=
    (brownianFullPastExponential_integral P Q D hD hmD (t j) (ht j) (H j) (hH j) 1 (N j)).1
  have hmean (j : ℕ) : ∫ u, X j u ∂P.prod Q = 1 :=
    (brownianFullPastExponential_integral P Q D hD hmD (t j) (ht j) (H j) (hH j) 1 (N j)).2
  have hpos (j : ℕ) (u : A × Ω) : 0 ≤ X j u := (Real.exp_pos _).le
  obtain ⟨hYi,hYpos,hYmean,hYprob,hL1⟩ :=
    probability_density_of_tendstoInMeasure_of_eLpNorm_two_le (P.prod Q) X Y
      (fun j => (hm j).aestronglyMeasurable) (fun j => ae_of_all _ (hpos j)) hmean C hcap hlim
  have hstatic := density_limit_preserves_marginal (P.prod Q) P Prod.fst measurable_fst X Y hi hYi
    (fun j => ae_of_all _ (hpos j)) hYpos (fun j => brownianFullPastExponential_preserves_static_marginal
      P Q D hD hmD (t j) (ht j) (H j) (hH j) 1 (N j)) hL1
  exact ⟨hYi,hYpos,hYmean,hYprob,hstatic,hL1⟩

lemma tendstoInMeasure_continuous_two_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : ℕ → Ω → ℝ} {x y : Ω → ℝ}
    (hXm : ∀ n, AEStronglyMeasurable (X n) P) (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hX : TendstoInMeasure P X atTop x) (hY : TendstoInMeasure P Y atTop y)
    (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    TendstoInMeasure P (fun n ω => f (X n ω,Y n ω)) atTop (fun ω => f (x ω,y ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n =>
    (hf.measurable.comp_aemeasurable ((hXm n).aemeasurable.prodMk
      (hYm n).aemeasurable)).aestronglyMeasurable)).2
  intro ns hns
  obtain ⟨ms,hms,hXX⟩ := (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ls,hls,hYY⟩ := (hY.comp (hns.comp hms).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms ∘ ls,hms.comp hls,?_⟩
  filter_upwards [hXX,hYY] with ω hωX hωY
  exact (hf.tendsto (x ω,y ω)).comp ((hωX.comp hls.tendsto_atTop).prodMk_nhds hωY)

end SKConstants
