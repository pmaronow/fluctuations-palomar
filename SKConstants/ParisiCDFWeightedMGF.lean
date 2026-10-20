module

public import SKConstants.ParisiCDFConditionalMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def preCDFWeightedIncrements {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (T : ℝ)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, c i * (preCDFGradientProcess W β α ha h1 T (t (i+1)) w -
    preCDFGradientProcess W β α ha h1 T (t i) w)

def preCDFWeightedProxy (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) : ℝ≥0 :=
  ∑ i ∈ Finset.range n, NNReal.mk ((c i)^2) (sq_nonneg _) * (t (i+1)-t i)

def preCDFWeightedPast (β : ℝ) (α : StieltjesFunction ℝ) (T : ℝ)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (p : ScalarContinuousPath a) : ℝ :=
  ∑ i ∈ Finset.range n, c i *
    (compactCDFJet β α T 0 ((t (i+1) : ℝ)/β^2)
      (p (projIcc 0 (a : ℝ) a.coe_nonneg (t (i+1)))) -
    compactCDFJet β α T 0 ((t i : ℝ)/β^2)
      (p (projIcc 0 (a : ℝ) a.coe_nonneg (t i))))

lemma abs_weighted_differences (f g : ℕ → ℝ) (c : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |∑ i ∈ Finset.range n, c i * (f i-g i)| ≤ 2*∑ i ∈ Finset.range n, |c i| := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |c i*(f i-g i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, 2*|c i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hD : |f i-g i| ≤ 2 :=
        abs_le.mpr ⟨by have h := abs_le.mp (hf i); have k := abs_le.mp (hg i); linarith,
          by have h := abs_le.mp (hf i); have k := abs_le.mp (hg i); linarith⟩
      nlinarith [abs_nonneg (c i),mul_le_mul_of_nonneg_left hD (abs_nonneg (c i))]
    _ = _ := by rw [Finset.mul_sum]

lemma measurable_preCDFWeightedPast (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    Measurable (preCDFWeightedPast β α T t c n a) := by
  have hg (r : ℝ) : Measurable (compactCDFJet β α T 0 r) :=
    ((compactCDFJetField β α ha h1 hβ hT0 hT1 0).smooth.regular r).smooth.continuous.measurable
  exact Finset.measurable_fun_sum _ fun i hi => measurable_const.mul
    ((hg _ |>.comp (ContinuousMap.measurable_eval _)).sub
      (hg _ |>.comp (ContinuousMap.measurable_eval _)))

lemma preCDFWeightedPast_abs_le (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (p : ScalarContinuousPath a) :
    |preCDFWeightedPast β α T t c n a p| ≤ 2*∑ i ∈ Finset.range n, |c i| :=
  abs_weighted_differences _ _ c n
    (fun _i => compactCDFJet_zero_abs_le_one β α ha hT0 hT1 _ _)
    (fun _i => compactCDFJet_zero_abs_le_one β α ha hT0 hT1 _ _)

lemma preCDFWeightedPast_version {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (T : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (n : ℕ) :
    (fun w => preCDFWeightedPast β α T t c n (t n)
      (boundedDriftPastPath W (finiteTemperatureCDFDrift β α ha h1) (t n) w)) =ᵐ[W.law]
        preCDFWeightedIncrements W β α ha h1 T t c n := by
  filter_upwards [boundedDriftPastPath_version W (finiteTemperatureCDFDrift β α ha h1) (t n)]
    with w hw
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have h0 : (t i : ℝ) ∈ Icc (0:ℝ) (t n : ℝ) := ⟨(t i).coe_nonneg,ht (by omega)⟩
  have h1' : (t (i+1) : ℝ) ∈ Icc (0:ℝ) (t n : ℝ) :=
    ⟨(t (i+1)).coe_nonneg,ht (by omega)⟩
  simp only [projIcc_of_mem (t n).coe_nonneg h0,projIcc_of_mem (t n).coe_nonneg h1',hw,
    preCDFGradientProcess,finiteTemperatureCDFProcess]
  rfl

theorem preCDFWeightedIncrements_mgf
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (n : ℕ)
    (hn : (t n : ℝ)/β^2 < T) (θ : ℝ) :
    (∫ w, Real.exp (θ*preCDFWeightedIncrements W β α ha h1 T t c n w) ∂W.law) ≤
      Real.exp ((preCDFWeightedProxy t c n : ℝ)*θ^2/2) := by
  let := W.isProbability
  induction n with
  | zero => simp [preCDFWeightedIncrements,preCDFWeightedProxy]
  | succ n ih =>
    have hn' : (t n : ℝ)/β^2 < T :=
      (div_le_div_of_nonneg_right (NNReal.coe_le_coe.mpr (ht (Nat.le_succ n)))
        (sq_nonneg β)).trans_lt hn
    have hd : t n+(t (n+1)-t n)=t (n+1) := add_tsub_cancel_of_le (ht (Nat.le_succ n))
    let F : ScalarContinuousPath (t n) → ℝ := fun p =>
      Real.exp (θ*preCDFWeightedPast β α T t c n (t n) p)
    have hFm : Measurable F := Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_preCDFWeightedPast β α ha h1 hβ hT0 hT1 t c n (t n)))
    have hFb (p : ScalarContinuousPath (t n)) : F p ≤ Real.exp (|θ| * (2*∑ i ∈ Finset.range n, |c i|)) := by
      apply Real.exp_le_exp.mpr
      calc θ*_ ≤ |θ*_| := le_abs_self _
        _ = |θ| * |_| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (preCDFWeightedPast_abs_le β α ha hT0 hT1.le t c n (t n) p) (abs_nonneg θ)
    have hv : ((t n : ℝ)+((t (n+1)-t n : ℝ≥0) : ℝ))/β^2 < T := by
      simpa only [←NNReal.coe_add,hd] using hn
    have hs := preCDFGradient_conditional_mgf_test W β α ha h1 hβ hT0 hT1
      (t n) (t (n+1)-t n) hv F hFm (fun p => (Real.exp_pos _).le) _ hFb (θ*c n)
    have hp := preCDFWeightedPast_version W β α ha h1 T t ht c n
    have hl : (∫ w, Real.exp (θ*preCDFWeightedIncrements W β α ha h1 T t c (n+1) w) ∂W.law) =
        ∫ w, F (boundedDriftPastPath W (finiteTemperatureCDFDrift β α ha h1) (t n) w) *
          Real.exp ((θ*c n)*(preCDFGradientProcess W β α ha h1 T
            (t n+(t (n+1)-t n)) w-preCDFGradientProcess W β α ha h1 T (t n) w)) ∂W.law := by
      apply integral_congr_ae
      filter_upwards [hp] with w hw
      simp only [F,hw,preCDFWeightedIncrements,Finset.sum_range_succ,hd]
      rw [←Real.exp_add]
      congr 1
      ring
    have hr : (∫ w, F (boundedDriftPastPath W (finiteTemperatureCDFDrift β α ha h1) (t n) w) ∂W.law) =
        ∫ w, Real.exp (θ*preCDFWeightedIncrements W β α ha h1 T t c n w) ∂W.law := by
      apply integral_congr_ae
      exact hp.mono (fun w hw => congrArg (fun x => Real.exp (θ*x)) hw)
    rw [hl]
    apply hs.trans
    rw [hr]
    calc
      _ ≤ Real.exp ((θ*c n)^2*((t (n+1)-t n : ℝ≥0) : ℝ)/2) *
          Real.exp ((preCDFWeightedProxy t c n : ℝ)*θ^2/2) :=
        mul_le_mul_of_nonneg_left (ih hn') (by positivity)
      _ = Real.exp ((preCDFWeightedProxy t c (n+1) : ℝ)*θ^2/2) := by
        rw [←Real.exp_add]
        congr 1
        simp only [preCDFWeightedProxy,Finset.sum_range_succ,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_mk]
        ring

theorem preCDFWeightedIncrements_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (n : ℕ)
    (hn : (t n : ℝ)/β^2 < T) :
    HasSubgaussianMGF (preCDFWeightedIncrements W β α ha h1 T t c n)
      (preCDFWeightedProxy t c n) W.law := by
  let := W.isProbability
  have hg (r : ℝ) : Measurable (compactCDFJet β α T 0 r) :=
    ((compactCDFJetField β α ha h1 hβ hT0 hT1 0).smooth.regular r).smooth.continuous.measurable
  have hm : Measurable (preCDFWeightedIncrements W β α ha h1 T t c n) :=
    Finset.measurable_fun_sum _ fun i hi => measurable_const.mul
      ((hg _ |>.comp (finiteTemperatureCDFProcess_measurable W β α ha h1 (t (i+1)))).sub
        (hg _ |>.comp (finiteTemperatureCDFProcess_measurable W β α ha h1 (t i))))
  have hb (w : Ω) : |preCDFWeightedIncrements W β α ha h1 T t c n w| ≤
      2*∑ i ∈ Finset.range n, |c i| :=
    abs_weighted_differences _ _ c n
      (fun _i => compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le _ _)
      (fun _i => compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le _ _)
  refine ⟨fun θ => integrable_exp_mul_of_mem_Icc
    (a := -(2*∑ i ∈ Finset.range n, |c i|)) (b := 2*∑ i ∈ Finset.range n, |c i|)
      hm.aemeasurable (ae_of_all _ fun w => abs_le.mp (hb w)), fun θ => ?_⟩
  exact preCDFWeightedIncrements_mgf W β α ha h1 hβ hT0 hT1 t ht c n hn θ

end SKConstants.ParisiFullSupport
