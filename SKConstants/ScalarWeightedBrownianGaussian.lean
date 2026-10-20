module

public import SKConstants.ScalarStieltjesRiemann
public import SKConstants.BrownianGaussianHistory
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem scalarHasLaw_of_ae_tendsto
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (hX : ∀ l, HasLaw (X l) ν P)
    (hYm : AEMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun l => X l ω) atTop (𝓝 (Y ω))) :
    HasLaw Y ν P := by
  refine ⟨hYm, ?_⟩
  have : IsProbabilityMeasure (P.map Y) := (Measure.isProbabilityMeasure_map_iff hYm).mpr inferInstance
  apply Measure.ext_of_charFun
  ext θ
  let e : ℝ → ℂ := fun x => Complex.exp ((θ*x : ℝ)*Complex.I)
  have he : Continuous e := by dsimp [e]; fun_prop
  have hl : Tendsto (fun l => ∫ ω, e (X l ω) ∂P) atTop (𝓝 (∫ ω, e (Y ω) ∂P)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun l => (he.measurable.comp_aemeasurable (hX l).aemeasurable).aestronglyMeasurable)
      (integrable_const 1)
      (fun l => ae_of_all _ (fun ω => by
        exact (Complex.norm_exp_ofReal_mul_I (θ*X l ω)).le))
      (hlim.mono (fun ω hω => (he.tendsto _).comp hω))
  have hx (l : ℕ) : (∫ ω, e (X l ω) ∂P) = charFun ν θ := by
    change (∫ ω, (e ∘ X l) ω ∂P) = _
    rw [(hX l).integral_comp he.measurable.aestronglyMeasurable]
    simpa only [e, Complex.ofReal_mul] using (charFun_apply_real θ).symm
  have hy : charFun (P.map Y) θ = ∫ ω, e (Y ω) ∂P := by
    rw [charFun_apply_real]
    simpa only [e, Complex.ofReal_mul] using integral_map hYm he.measurable.aestronglyMeasurable
  rw [hy]
  exact tendsto_nhds_unique hl (by simpa only [hx] using tendsto_const_nhds)

def scalarBrownianWeightedMeshSum (B : ℝ≥0 → Ω → ℝ) (q : ℕ → ℝ≥0)
    (w : ℕ → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, w i*brownianMeshIncrement B q i ω

def scalarBrownianWeightedMeshVariance (q : ℕ → ℝ≥0) (w : ℕ → ℝ) (m : ℕ) : ℝ≥0 :=
  ∑ i : Fin m, NNReal.mk ((w i)^2) (sq_nonneg _)*brownianMeshVariance q i

theorem scalarBrownianWeightedMeshSum_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (q : ℕ → ℝ≥0) (hq : Monotone q)
    (w : ℕ → ℝ) (m : ℕ) :
    HasLaw (scalarBrownianWeightedMeshSum B q w m)
      (gaussianReal 0 (scalarBrownianWeightedMeshVariance q w m)) P := by
  let X : Fin m → Ω → ℝ := fun i ω => w i*brownianMeshIncrement B q i ω
  have hl (i : Fin m) : HasLaw (X i)
      (gaussianReal 0 (NNReal.mk ((w i)^2) (sq_nonneg _)*brownianMeshVariance q i)) P := by
    simpa only [mul_zero] using gaussianReal_const_mul (brownianMeshIncrement_hasLaw hB q hq i) (w i)
  have hind : iIndepFun X P :=
    ((brownianMeshIncrement_iIndepFun hB q hq).precomp Fin.val_injective).comp
      (fun i x => w i*x) (fun _ => measurable_const.mul measurable_id)
  have hg := hind.hasGaussianLaw_fun_sum (fun i => (hl i).hasGaussianLaw)
  have hmean : (∫ ω, (∑ i, X i ω) ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hl i).hasGaussianLaw.integrable)]
    simp_rw [(hl _).integral_eq, integral_id_gaussianReal]
    simp
  have hlp (i : Fin m) : MemLp (X i) 2 P := (hl i).hasGaussianLaw.memLp_two
  have hvar : variance (fun ω => ∑ i, X i ω) P =
      (scalarBrownianWeightedMeshVariance q w m : ℝ) := by
    have hh := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hlp i)
      (fun i _ j _ hij => hind.indepFun hij)
    have he : (∑ i, X i) = fun ω => ∑ i, X i ω := by ext ω; simp
    rw [he] at hh
    rw [hh]
    simp only [scalarBrownianWeightedMeshVariance, NNReal.coe_sum, (hl _).variance_eq,
      variance_id_gaussianReal]
  refine ⟨hg.aemeasurable, ?_⟩
  change P.map (fun ω => ∑ i, X i ω) = _
  rw [hg.map_eq_gaussianReal, hmean, hvar, Real.toNNReal_coe]

variable {A : Type*} [MeasurableSpace A]

def scalarTwoBrownianWeightedMeshSum (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (q : ℕ → ℝ≥0) (w z : ℕ → ℝ) (m : ℕ) (u : Ω × A) : ℝ :=
  scalarBrownianWeightedMeshSum B q w m u.1+scalarBrownianWeightedMeshSum C q z m u.2

theorem scalarTwoBrownianWeightedMeshSum_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (w z : ℕ → ℝ) (m : ℕ) :
    HasLaw (scalarTwoBrownianWeightedMeshSum B C q w z m)
      (gaussianReal 0 (scalarBrownianWeightedMeshVariance q w m+
        scalarBrownianWeightedMeshVariance q z m)) (P.prod Q) := by
  have h1 := scalarBrownianWeightedMeshSum_hasLaw P B hB q hq w m
  have h2 := scalarBrownianWeightedMeshSum_hasLaw Q C hC q hq z m
  have hi := indepFun_prod₀ h1.aemeasurable h2.aemeasurable
  have hh := hi.hasLaw_fun_add (h1.comp (measurePreserving_fst (μ := P) (ν := Q)).hasLaw)
    (h2.comp (measurePreserving_snd (μ := P) (ν := Q)).hasLaw)
  change HasLaw (fun ω : Ω × A => scalarBrownianWeightedMeshSum B q w m ω.1+
    scalarBrownianWeightedMeshSum C q z m ω.2) _ _
  simpa only [gaussianReal_conv_gaussianReal, zero_add, Function.comp_def] using hh

theorem scalarTwoBrownianWeightedMeshVariance_of_unit
    (q : ℕ → ℝ≥0) (hq : Monotone q) (w z : ℕ → ℝ) (m : ℕ)
    (hwz : ∀ i < m, (w i)^2+(z i)^2=1) :
    scalarBrownianWeightedMeshVariance q w m+scalarBrownianWeightedMeshVariance q z m =
      q m-q 0 := by
  apply NNReal.eq
  simp only [scalarBrownianWeightedMeshVariance, NNReal.coe_add, NNReal.coe_sum,
    NNReal.coe_mul, NNReal.coe_mk]
  rw [NNReal.coe_sub (hq (by omega)), ← Finset.sum_add_distrib]
  have he (i : Fin m) : (w i)^2*(brownianMeshVariance q i : ℝ)+
      (z i)^2*(brownianMeshVariance q i : ℝ) = (q (i+1) : ℝ)-(q i : ℝ) := by
    rw [← add_mul, hwz i i.isLt, one_mul, brownianMeshVariance,
      NNReal.coe_sub (hq (by omega))]
  simp_rw [he]
  change (∑ x : Fin m, (fun i : ℕ => (q (i+1) : ℝ)-(q i : ℝ)) x) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (q (i+1) : ℝ)-(q i : ℝ))]
  exact Finset.sum_range_sub (fun i => (q i : ℝ)) m

def scalarBrownianDyadicTime (u : ℝ≥0) (l i : ℕ) : ℝ≥0 :=
  u*(i : ℝ≥0)/(2 : ℝ≥0)^l

theorem scalarBrownianDyadicTime_coe (u : ℝ≥0) (l i : ℕ) :
    (scalarBrownianDyadicTime u l i : ℝ) = scalarStieltjesDyadicTime u l i := by
  simp [scalarBrownianDyadicTime, scalarStieltjesDyadicTime]

theorem scalarBrownianDyadicTime_mono (u : ℝ≥0) (l : ℕ) :
    Monotone (scalarBrownianDyadicTime u l) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) u.coe_nonneg) (by positivity)

theorem scalarBrownianDyadicTime_zero (u : ℝ≥0) (l : ℕ) :
    scalarBrownianDyadicTime u l 0 = 0 := by simp [scalarBrownianDyadicTime]

theorem scalarBrownianDyadicTime_end (u : ℝ≥0) (l : ℕ) :
    scalarBrownianDyadicTime u l (2^l) = u := by simp [scalarBrownianDyadicTime]

omit [MeasurableSpace Ω] in
theorem scalarBrownianWeightedMeshSum_neg (B : ℝ≥0 → Ω → ℝ) (q : ℕ → ℝ≥0)
    (w : ℕ → ℝ) (m : ℕ) (ω : Ω) :
    scalarBrownianWeightedMeshSum B q (fun i => -w i) m ω =
      -scalarBrownianWeightedMeshSum B q w m ω := by
  simp [scalarBrownianWeightedMeshSum, neg_mul]

omit [MeasurableSpace Ω] in
theorem scalarBrownianWeightedMeshSum_eq_dyadic
    (f : StieltjesFunction ℝ) (B : ℝ≥0 → Ω → ℝ) (T u : ℝ≥0) (hu : u ≤ T)
    (F : ScalarContinuousPath T) (ω : Ω)
    (hF : ∀ t : Icc (0 : ℝ) (T : ℝ), F t = B ⟨t,t.property.1⟩ ω) (l : ℕ) :
    scalarBrownianWeightedMeshSum B (scalarBrownianDyadicTime u l)
      (fun i => f (scalarBrownianDyadicTime u l i : ℝ)) (2^l) ω =
      scalarStieltjesDyadicSumAt f T F u l := by
  unfold scalarBrownianWeightedMeshSum scalarStieltjesDyadicSumAt scalarStieltjesMeshSum
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    f (scalarBrownianDyadicTime u l i : ℝ)*brownianMeshIncrement B (scalarBrownianDyadicTime u l) i ω)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [brownianMeshIncrement, scalarBrownianDyadicTime_coe]
  have he (j : ℕ) (hj : j ≤ 2^l) :
      IccExtend T.coe_nonneg F (scalarStieltjesDyadicTime u l j) =
        B (scalarBrownianDyadicTime u l j) ω := by
    have hm := scalarStieltjesDyadicTime_mem u l j hj
    have hmT : scalarStieltjesDyadicTime u l j ∈ Icc (0 : ℝ) (T : ℝ) :=
      ⟨hm.1, hm.2.trans (show (u : ℝ) ≤ T from hu)⟩
    simp only [IccExtend, Function.comp_apply, projIcc_of_mem _ hmT]
    have hq : (⟨scalarStieltjesDyadicTime u l j,hmT.1⟩ : ℝ≥0) =
        scalarBrownianDyadicTime u l j := by
      apply NNReal.eq
      exact (scalarBrownianDyadicTime_coe u l j).symm
    simpa only [hq] using hF ⟨_,hmT⟩
  rw [he i (Finset.mem_range.mp hi).le, he (i+1) (Finset.mem_range.mp hi)]

theorem scalarTwoDriverWeightedPath_eval_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (T u : ℝ≥0) (hu : u ≤ T)
    (hunit : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), (f s)^2+(g s)^2=1)
    (F : Ω → ScalarContinuousPath T) (G : A → ScalarContinuousPath T)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ), F ω t = B ⟨t,t.property.1⟩ ω)
    (hG : ∀ᵐ ω ∂Q, ∀ t : Icc (0 : ℝ) (T : ℝ), G ω t = C ⟨t,t.property.1⟩ ω) :
    HasLaw (fun ω : Ω × A =>
      scalarTwoDriverWeightedPath f g hf hg T (F ω.1,G ω.2) ⟨u,u.coe_nonneg,hu⟩)
      (gaussianReal 0 u) (P.prod Q) := by
  let X : ℕ → Ω × A → ℝ := fun l => scalarTwoBrownianWeightedMeshSum B C
    (scalarBrownianDyadicTime u l)
    (fun i => -f (scalarBrownianDyadicTime u l i : ℝ))
    (fun i => g (scalarBrownianDyadicTime u l i : ℝ)) (2^l)
  have hl (l : ℕ) : HasLaw (X l) (gaussianReal 0 u) (P.prod Q) := by
    have h := scalarTwoBrownianWeightedMeshSum_hasLaw P Q B C hB hC _
      (scalarBrownianDyadicTime_mono u l)
      (fun i => -f (scalarBrownianDyadicTime u l i : ℝ))
      (fun i => g (scalarBrownianDyadicTime u l i : ℝ)) (2^l)
    have hv := scalarTwoBrownianWeightedMeshVariance_of_unit
      (scalarBrownianDyadicTime u l) (scalarBrownianDyadicTime_mono u l)
      (fun i => -f (scalarBrownianDyadicTime u l i : ℝ))
      (fun i => g (scalarBrownianDyadicTime u l i : ℝ)) (2^l) (by
        intro i hi
        have hm := scalarStieltjesDyadicTime_mem u l i hi.le
        simpa only [neg_sq, scalarBrownianDyadicTime_coe] using
          hunit _ ⟨hm.1,hm.2.trans (show (u : ℝ) ≤ T from hu)⟩)
    rw [scalarBrownianDyadicTime_zero,scalarBrownianDyadicTime_end,tsub_zero] at hv
    simpa only [hv] using h
  have hm : Measurable (fun ω : Ω × A =>
      scalarTwoDriverWeightedPath f g hf hg T (F ω.1,G ω.2) ⟨u,u.coe_nonneg,hu⟩) :=
    (ContinuousMap.measurable_eval _).comp
      ((measurable_scalarTwoDriverWeightedPath f g hf hg T).comp (hFm.prodMap hGm))
  apply scalarHasLaw_of_ae_tendsto (P.prod Q) (gaussianReal 0 u) X _ hl hm.aemeasurable
  have hF' : ∀ᵐ ω ∂P, (∀ t : Icc (0 : ℝ) (T : ℝ), F ω t = B ⟨t,t.property.1⟩ ω) ∧ B 0 ω=0 :=
    hF.and hB.eval_zero_ae_eq_zero
  have hG' : ∀ᵐ ω ∂Q, (∀ t : Icc (0 : ℝ) (T : ℝ), G ω t = C ⟨t,t.property.1⟩ ω) ∧ C 0 ω=0 :=
    hG.and hC.eval_zero_ae_eq_zero
  filter_upwards [(measurePreserving_fst (μ := P) (ν := Q)).quasiMeasurePreserving.ae hF',
    (measurePreserving_snd (μ := P) (ν := Q)).quasiMeasurePreserving.ae hG'] with ω hωF hωG
  have he (l : ℕ) : X l ω = -scalarStieltjesDyadicSumAt f T (F ω.1) u l+
      scalarStieltjesDyadicSumAt g T (G ω.2) u l := by
    dsimp [X,scalarTwoBrownianWeightedMeshSum]
    rw [scalarBrownianWeightedMeshSum_neg,
      scalarBrownianWeightedMeshSum_eq_dyadic f B T u hu (F ω.1) ω.1 hωF.1,
      scalarBrownianWeightedMeshSum_eq_dyadic g C T u hu (G ω.2) ω.2 hωG.1]
  simp_rw [he]
  apply scalarTwoDriverWeightedPath_dyadic_tendsto f g hf hg T u hu
  · rw [hωF.1 ⟨0,le_rfl,T.coe_nonneg⟩]
    exact hωF.2
  · rw [hωG.1 ⟨0,le_rfl,T.coe_nonneg⟩]
    exact hωG.2

end SKConstants
