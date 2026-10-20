module
public import SKConstants.PredictableGaussianVectorSums

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianVectorPastRestrict {ι : Type*} {s T : ℝ≥0} (hs : s ≤ T)
    (w : Iic T → ι → ℝ) : Iic s → ι → ℝ := fun t => w ⟨t,t.property.trans hs⟩

lemma measurable_brownianVectorPastRestrict {ι : Type*} {s T : ℝ≥0} (hs : s ≤ T) :
    Measurable (brownianVectorPastRestrict (ι := ι) hs) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

abbrev BrownianVectorPredictableCoefficient (A ι : Type*) (t : ℕ → ℝ≥0) :=
  (k : ℕ) → A × (Iic (t k) → ι → ℝ) → ι → ℝ

def brownianVectorStaticCoefficient {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t)
    (k : ℕ) (u : A × (ι → Ω)) : ι → ℝ := H k (u.1,brownianVectorFullPast D (t k) u.2)

def brownianVectorPredictableSum {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t) :=
  predictableGaussianVectorSum (fun k u => brownianVectorMeshIncrement D t k u.2)
    (brownianVectorStaticCoefficient D t H)

def brownianVectorPredictableVariation {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t) :=
  predictableGaussianVectorVariation (brownianMeshVariance t) (brownianVectorStaticCoefficient D t H)

def brownianVectorPastSum {A ι : Type*} [Fintype ι] (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianVectorPredictableCoefficient A ι t) (n : ℕ)
    (u : A × (Iic (t n) → ι → ℝ)) : ℝ :=
  ∑ k : Fin n,∑ i,H k (u.1,brownianVectorPastRestrict (ht (Nat.le_of_lt k.isLt)) u.2) i*
    (u.2 ⟨t (k+1),ht (by omega)⟩ i-u.2 ⟨t k,ht (Nat.le_of_lt k.isLt)⟩ i)

def brownianVectorPastVariation {A ι : Type*} [Fintype ι] (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianVectorPredictableCoefficient A ι t) (n : ℕ)
    (u : A × (Iic (t n) → ι → ℝ)) : ℝ :=
  ∑ k : Fin n,(brownianMeshVariance t k : ℝ)*
    ∑ i,H k (u.1,brownianVectorPastRestrict (ht (Nat.le_of_lt k.isLt)) u.2) i^2

lemma measurable_brownianVectorPastSum {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) : Measurable (brownianVectorPastSum t ht H n) := by
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro i _
  apply Measurable.mul
  · exact (measurable_pi_apply i).comp ((hH k).comp (measurable_fst.prodMk
      ((measurable_brownianVectorPastRestrict _).comp measurable_snd)))
  · fun_prop

lemma measurable_brownianVectorPastVariation {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) : Measurable (brownianVectorPastVariation t ht H n) := by
  apply Finset.measurable_sum
  intro k _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp ((hH k).comp (measurable_fst.prodMk
    ((measurable_brownianVectorPastRestrict _).comp measurable_snd)))).pow_const 2

lemma measurable_brownianVectorStaticCoefficient {A ι Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (k : ℕ) : Measurable (brownianVectorStaticCoefficient D t H k) :=
  (hH k).comp (measurable_fst.prodMk ((show Measurable (brownianVectorFullPast (ι := ι) D (t k)) from
    Measurable.of_eval (fun s : Iic (t k) => Measurable.of_eval (fun i : ι =>
      (hmD s).comp (measurable_pi_apply i)))).comp measurable_snd))

theorem brownianVectorPredictable_state_indep_increment {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    IndepFun (fun u => (brownianVectorPredictableSum D t H n u,
      brownianVectorStaticCoefficient D t H n u,brownianVectorPredictableVariation D t H n u))
      (fun u : A × (ι → Ω) => brownianVectorMeshIncrement D t n u.2)
      (P.prod (Measure.pi (fun _ : ι => Q))) := by
  let Φ := fun u : A × (Iic (t n) → ι → ℝ) =>
    (brownianVectorPastSum t ht H n u,H n u,brownianVectorPastVariation t ht H n u)
  have hΦ : Measurable Φ := (measurable_brownianVectorPastSum t ht H hH n).prodMk
    ((hH n).prodMk (measurable_brownianVectorPastVariation t ht H hH n))
  have hi := brownianVectorStaticPast_indep_increment (ι := ι) P Q D hD hmD t ht n
  convert hi.comp hΦ measurable_id using 1
  · funext u
    rw [brownianVectorPredictableSum,predictableGaussianVectorSum_eq_fin_sum,
      brownianVectorPredictableVariation,predictableGaussianVectorVariation_eq_fin_sum]
    rfl
  · rfl

def brownianVectorFullPastExponential {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t)
    (θ : ℝ) (n : ℕ) (u : A × (ι → Ω)) : ℝ :=
  Real.exp (θ*brownianVectorPredictableSum D t H n u-
    θ^2*brownianVectorPredictableVariation D t H n u/2)

theorem brownianVectorFullPastExponential_integral {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    Integrable (brownianVectorFullPastExponential D t H θ n) (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∫ u, brownianVectorFullPastExponential D t H θ n u ∂P.prod (Measure.pi (fun _ : ι => Q))) = 1 := by
  have hsnd : HasLaw (Prod.snd : A × (ι → Ω) → (ι → Ω))
      (Measure.pi (fun _ : ι => Q)) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  exact predictableGaussianVectorExponential_integral _ _ _ _
    (fun k => (brownianVectorMeshIncrement_hasLaw (ι := ι) Q D hD t ht k).comp hsnd)
    (fun k => (measurable_brownianVectorStaticCoefficient D hmD t H hH k).aemeasurable)
    (brownianVectorPredictable_state_indep_increment P Q D hD hmD t ht H hH) θ n

lemma measurable_brownianVectorFullPastExponential {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    Measurable (brownianVectorFullPastExponential D t H θ n) := by
  let Φ := fun u : A × (Iic (t n) → ι → ℝ) =>
    Real.exp (θ*brownianVectorPastSum t ht H n u-θ^2*brownianVectorPastVariation t ht H n u/2)
  have hΦ : Measurable Φ :=
    (((measurable_brownianVectorPastSum t ht H hH n).const_mul θ).sub
      (((measurable_brownianVectorPastVariation t ht H hH n).const_mul (θ^2)).div_const 2)).exp
  convert hΦ.comp (measurable_fst.prodMk ((show Measurable (brownianVectorFullPast (ι := ι) D (t n)) from
    Measurable.of_eval (fun s : Iic (t n) => Measurable.of_eval (fun i : ι =>
      (hmD s).comp (measurable_pi_apply i)))).comp measurable_snd)) using 1
  funext u
  rw [brownianVectorFullPastExponential,brownianVectorPredictableSum,predictableGaussianVectorSum_eq_fin_sum,
    brownianVectorPredictableVariation,predictableGaussianVectorVariation_eq_fin_sum]
  rfl

theorem brownianVectorFullPastExponential_conditional_mean_one {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) (a : A) :
    (∫⁻ ω, ENNReal.ofReal (brownianVectorFullPastExponential D t H θ n (a,ω))
      ∂Measure.pi (fun _ : ι => Q)) = 1 := by
  have hm := (measurable_brownianVectorFullPastExponential D hmD t ht H hH θ n).ennreal_ofReal
  have hi := brownianVectorFullPastExponential_integral (Measure.dirac a) Q D hD hmD t ht H hH θ n
  have he : (∫⁻ u, ENNReal.ofReal (brownianVectorFullPastExponential D t H θ n u)
      ∂(Measure.dirac a).prod (Measure.pi (fun _ : ι => Q))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun _ => (Real.exp_pos _).le)),hi.2]
    norm_num
  rw [lintegral_prod _ hm.aemeasurable] at he
  have hu : Measurable (Function.uncurry (fun a ω =>
    ENNReal.ofReal (brownianVectorFullPastExponential D t H θ n (a,ω)))) := hm
  rw [lintegral_dirac' a hu.lintegral_prod_right] at he
  exact he

theorem brownianVectorFullPastExponential_preserves_static_marginal {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    ((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u => ENNReal.ofReal
      (brownianVectorFullPastExponential D t H θ n u))).map Prod.fst = P := by
  let f : A × (ι → Ω) → ℝ≥0∞ := fun u => ENNReal.ofReal (brownianVectorFullPastExponential D t H θ n u)
  have hm : Measurable f := (measurable_brownianVectorFullPastExponential D hmD t ht H hH θ n).ennreal_ofReal
  let κ : Kernel A (ι → Ω) := (Kernel.const A (Measure.pi (fun _ : ι => Q))).withDensity (fun a ω => f (a,ω))
  have hk : IsMarkovKernel κ := by
    constructor
    intro a
    constructor
    dsimp only [κ]
    rw [Kernel.withDensity_apply _ hm,Kernel.const_apply,withDensity_apply _
      MeasurableSet.univ,Measure.restrict_univ]
    exact brownianVectorFullPastExponential_conditional_mean_one Q D hD hmD t ht H hH θ n a
  let := hk
  have he : P ⊗ₘ κ = (P.prod (Measure.pi (fun _ : ι => Q))).withDensity f := by
    dsimp only [κ]
    rw [Measure.compProd_withDensity hm,Measure.compProd_const]
  rw [← he]
  exact Measure.fst_compProd P κ

lemma brownianVectorFullPastExponential_square {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianVectorPredictableCoefficient A ι t) (n : ℕ) (u : A × (ι → Ω)) :
    brownianVectorFullPastExponential D t H 1 n u ^ 2 =
      brownianVectorFullPastExponential D t H 2 n u *
        Real.exp (brownianVectorPredictableVariation D t H n u) := by
  rw [brownianVectorFullPastExponential,brownianVectorFullPastExponential,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

lemma eLpNorm_brownianVectorFullPastExponential_two_le {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorPredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) (V : ℝ)
    (hV : ∀ u, brownianVectorPredictableVariation D t H n u ≤ V) :
    eLpNorm (brownianVectorFullPastExponential D t H 1 n) 2 (P.prod (Measure.pi (fun _ : ι => Q))) ≤
      ENNReal.ofReal (Real.exp V) ^ (1/(2 : ℝ)) := by
  have hm := measurable_brownianVectorFullPastExponential D hmD t ht H hH 1 n
  have hp (u : A × (ι → Ω)) : 0 ≤ brownianVectorFullPastExponential D t H 1 n u := (Real.exp_pos _).le
  have htwo := brownianVectorFullPastExponential_integral P Q D hD hmD t ht H hH 2 n
  have hbound : ∀ u, brownianVectorFullPastExponential D t H 1 n u ^ 2 ≤
      Real.exp V * brownianVectorFullPastExponential D t H 2 n u := by
    intro u
    rw [brownianVectorFullPastExponential_square]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hV u)) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hi : Integrable (fun u => brownianVectorFullPastExponential D t H 1 n u ^ 2) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (htwo.1.const_mul (Real.exp V)).mono' (hm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (brownianVectorFullPastExponential D t H 1 n u))]
        exact hbound u))
  have hs : (∫ u, brownianVectorFullPastExponential D t H 1 n u ^ 2 ∂P.prod (Measure.pi (fun _ : ι => Q))) ≤ Real.exp V := by
    have hh := integral_mono hi (htwo.1.const_mul (Real.exp V)) hbound
    rwa [integral_const_mul,htwo.2,mul_one] at hh
  have hl : (∫⁻ u, ENNReal.ofReal (brownianVectorFullPastExponential D t H 1 n u ^ 2) ∂P.prod (Measure.pi (fun _ : ι => Q))) ≤
      ENNReal.ofReal (Real.exp V) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [Real.enorm_eq_ofReal (hp _),ENNReal.rpow_two,← ENNReal.ofReal_pow (hp _) 2]
  exact ENNReal.rpow_le_rpow hl (by norm_num)

theorem brownianVectorFullPast_density_limit {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j)) (N : ℕ → ℕ)
    (H : (j : ℕ) → BrownianVectorPredictableCoefficient A ι (t j))
    (hH : ∀ j k, Measurable (H j k)) (V : ℝ)
    (hV : ∀ j u, brownianVectorPredictableVariation D (t j) (H j) (N j) u ≤ V)
    (Y : A × (ι → Ω) → ℝ) (hlim : TendstoInMeasure (P.prod (Measure.pi (fun _ : ι => Q)))
      (fun j => brownianVectorFullPastExponential D (t j) (H j) 1 (N j)) atTop Y) :
    Integrable Y (P.prod (Measure.pi (fun _ : ι => Q))) ∧ (∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), 0 ≤ Y u) ∧
      (∫ u, Y u ∂P.prod (Measure.pi (fun _ : ι => Q))) = 1 ∧
      IsProbabilityMeasure ((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u => ENNReal.ofReal (Y u))) ∧
      (((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u => ENNReal.ofReal (Y u))).map Prod.fst = P) ∧
      Tendsto (fun j => eLpNorm (brownianVectorFullPastExponential D (t j) (H j) 1 (N j)-Y) 1
        (P.prod (Measure.pi (fun _ : ι => Q)))) atTop (𝓝 0) := by
  let X : ℕ → A × (ι → Ω) → ℝ := fun j => brownianVectorFullPastExponential D (t j) (H j) 1 (N j)
  let C : ℝ≥0 := ⟨(Real.exp V)^(1/(2 : ℝ)),Real.rpow_nonneg (Real.exp_pos V).le _⟩
  have hm (j : ℕ) : Measurable (X j) := measurable_brownianVectorFullPastExponential D hmD
    (t j) (ht j) (H j) (hH j) 1 (N j)
  have hcap (j : ℕ) : eLpNorm (X j) 2 (P.prod (Measure.pi (fun _ : ι => Q))) ≤ C := by
    have hb := eLpNorm_brownianVectorFullPastExponential_two_le P Q D hD hmD
      (t j) (ht j) (H j) (hH j) (N j) V (hV j)
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (X j) 2 (P.prod (Measure.pi (fun _ : ι => Q))) ≤ ENNReal.ofReal ((Real.exp V)^(1/(2 : ℝ)))
    simpa only [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos V).le (by norm_num : 0 ≤ 1/(2 : ℝ))] using hb
  have hi (j : ℕ) : Integrable (X j) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (brownianVectorFullPastExponential_integral P Q D hD hmD (t j) (ht j) (H j) (hH j) 1 (N j)).1
  have hmean (j : ℕ) : ∫ u, X j u ∂P.prod (Measure.pi (fun _ : ι => Q)) = 1 :=
    (brownianVectorFullPastExponential_integral P Q D hD hmD (t j) (ht j) (H j) (hH j) 1 (N j)).2
  have hpos (j : ℕ) (u : A × (ι → Ω)) : 0 ≤ X j u := (Real.exp_pos _).le
  obtain ⟨hYi,hYpos,hYmean,hYprob,hL1⟩ :=
    probability_density_of_tendstoInMeasure_of_eLpNorm_two_le (P.prod (Measure.pi (fun _ : ι => Q))) X Y
      (fun j => (hm j).aestronglyMeasurable) (fun j => ae_of_all _ (hpos j)) hmean C hcap hlim
  have hstatic := density_limit_preserves_marginal (P.prod (Measure.pi (fun _ : ι => Q))) P Prod.fst measurable_fst X Y hi hYi
    (fun j => ae_of_all _ (hpos j)) hYpos (fun j => brownianVectorFullPastExponential_preserves_static_marginal
      P Q D hD hmD (t j) (ht j) (H j) (hH j) 1 (N j)) hL1
  exact ⟨hYi,hYpos,hYmean,hYprob,hstatic,hL1⟩

end SKConstants
