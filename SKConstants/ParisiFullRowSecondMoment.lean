module

public import SKConstants.ParisiFullMartingale
public import SKConstants.ScalarProcessParisiRDerivative
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullRowSecondMoment_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def actualParisiMagnetizationObservable (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiFullMagnetization β t (actualParisiFullScalarProcess W β t w)

lemma measurable_actualParisiMagnetizationObservable (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) :
    Measurable (actualParisiMagnetizationObservable W β t) := by
  exact ((continuous_actualParisiFullMagnetization β).comp
    ((continuous_const : Continuous (fun _ : ℝ => (t:ℝ))).prodMk continuous_id)).measurable.comp
      (measurable_actualParisiPreContinuationField W β t)

lemma actualParisiMagnetizationObservable_abs_le (W : BrownianSystem Ω) (β : ℝ)
    (t : ℝ≥0) (w : Ω) : |actualParisiMagnetizationObservable W β t w| ≤ 1 :=
  (actualParisiFullMagnetization_curvature_bounds β _ _).1

lemma integrable_actualParisiMagnetization_pair (W : BrownianSystem Ω) (β : ℝ) (S T : ℝ≥0) :
    Integrable (fun w => actualParisiMagnetizationObservable W β S w *
      actualParisiMagnetizationObservable W β T w) W.law := by
  apply Integrable.of_bound ((measurable_actualParisiMagnetizationObservable W β S).mul
    (measurable_actualParisiMagnetizationObservable W β T)).aestronglyMeasurable 1
  exact ae_of_all _ (fun w => by
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (actualParisiMagnetizationObservable_abs_le W β S w)
      (actualParisiMagnetizationObservable_abs_le W β T w) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul 1))

theorem actualParisiMagnetization_crossMoment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w,actualParisiMagnetizationObservable W β S w *
      actualParisiMagnetizationObservable W β T w ∂W.law) =
      ∫ w,(actualParisiMagnetizationObservable W β S w)^2 ∂W.law := by
  let F : ScalarContinuousPath S → ℝ := fun p =>
    actualParisiFullMagnetization β S (p ⟨S,S.coe_nonneg,le_rfl⟩)
  have hF : Measurable F := by
    exact ((continuous_actualParisiFullMagnetization β).comp
      ((continuous_const : Continuous (fun _ : ℝ => (S:ℝ))).prodMk continuous_id)).measurable.comp
        (ContinuousMap.measurable_eval _)
  have hB (p : ScalarContinuousPath S) : |F p| ≤ 1 :=
    (actualParisiFullMagnetization_curvature_bounds β _ _).1
  have H := actualParisiFullProcess_martingale_test W β hβ S (T-S) F hF 1 hB
  have he : S+(T-S)=T := add_tsub_cancel_of_le hST
  simp only [← NNReal.coe_add,he] at H
  have hiS : Integrable (fun w => (actualParisiMagnetizationObservable W β S w)^2) W.law := by
    simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β S S
  have H' : (∫ w,actualParisiMagnetizationObservable W β S w *
      (actualParisiMagnetizationObservable W β T w-actualParisiMagnetizationObservable W β S w)
        ∂W.law)=0 := by
    refine (integral_congr_ae ?_).trans H
    filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) S] with w hw
    rw [show F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w)=
      actualParisiMagnetizationObservable W β S w by
        dsimp only [F,actualParisiMagnetizationObservable]
        rw [hw ⟨S,S.coe_nonneg,le_rfl⟩]
        rfl]
    rfl
  have hiT := integrable_actualParisiMagnetization_pair W β S T
  simp_rw [mul_sub,← pow_two] at H'
  rw [integral_sub hiT hiS] at H'
  linarith

def actualParisiMagnetizationIncrement (W : BrownianSystem Ω) (β : ℝ)
    (S T : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiMagnetizationObservable W β T w-actualParisiMagnetizationObservable W β S w

lemma measurable_actualParisiMagnetizationIncrement (W : BrownianSystem Ω) (β : ℝ) (S T : ℝ≥0) :
    Measurable (actualParisiMagnetizationIncrement W β S T) :=
  (measurable_actualParisiMagnetizationObservable W β T).sub
    (measurable_actualParisiMagnetizationObservable W β S)

lemma actualParisiMagnetizationIncrement_abs_le (W : BrownianSystem Ω) (β : ℝ)
    (S T : ℝ≥0) (w : Ω) : |actualParisiMagnetizationIncrement W β S T w| ≤ 2 := by
  exact (abs_sub _ _).trans (by
    have H := add_le_add (actualParisiMagnetizationObservable_abs_le W β T w)
      (actualParisiMagnetizationObservable_abs_le W β S w)
    norm_num at H ⊢
    exact H)

lemma integrable_actualParisiIncrement_pair (W : BrownianSystem Ω) (β : ℝ) (A S T U : ℝ≥0) :
    Integrable (fun w => actualParisiMagnetizationIncrement W β A S w *
      actualParisiMagnetizationIncrement W β T U w) W.law := by
  apply Integrable.of_bound ((measurable_actualParisiMagnetizationIncrement W β A S).mul
    (measurable_actualParisiMagnetizationIncrement W β T U)).aestronglyMeasurable 4
  exact ae_of_all _ (fun w => by
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (actualParisiMagnetizationIncrement_abs_le W β A S w)
      (actualParisiMagnetizationIncrement_abs_le W β T U w) (abs_nonneg _) (by norm_num)).trans_eq
        (by norm_num))

theorem actualParisiIncrement_disjoint_crossMoment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (A S T U : ℝ≥0) (hAS : A ≤ S) (hST : S ≤ T) (hTU : T ≤ U) :
    (∫ w,actualParisiMagnetizationIncrement W β A S w *
      actualParisiMagnetizationIncrement W β T U w ∂W.law)=0 := by
  let M := actualParisiMagnetizationObservable W β
  have he (w : Ω) : (M S w-M A w)*(M U w-M T w)=
      (M S w*M U w-M S w*M T w)-(M A w*M U w-M A w*M T w) := by ring
  change (∫ w,(M S w-M A w)*(M U w-M T w) ∂W.law)=0
  simp_rw [he]
  have H := integral_sub
    ((integrable_actualParisiMagnetization_pair W β S U).sub
      (integrable_actualParisiMagnetization_pair W β S T))
    ((integrable_actualParisiMagnetization_pair W β A U).sub
      (integrable_actualParisiMagnetization_pair W β A T))
  have HS := integral_sub (integrable_actualParisiMagnetization_pair W β S U)
    (integrable_actualParisiMagnetization_pair W β S T)
  have HA := integral_sub (integrable_actualParisiMagnetization_pair W β A U)
    (integrable_actualParisiMagnetization_pair W β A T)
  simp only [Pi.sub_apply] at H HS HA
  dsimp only [M]
  rw [H,HS,HA]
  rw [actualParisiMagnetization_crossMoment W β hβ S U (hST.trans hTU),
    actualParisiMagnetization_crossMoment W β hβ S T hST,
    actualParisiMagnetization_crossMoment W β hβ A U ((hAS.trans hST).trans hTU),
    actualParisiMagnetization_crossMoment W β hβ A T (hAS.trans hST)]
  ring

theorem actualParisiIncrement_secondMoment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w,(actualParisiMagnetizationIncrement W β S T w)^2 ∂W.law)=
      (∫ w,(actualParisiMagnetizationObservable W β T w)^2 ∂W.law)-
        ∫ w,(actualParisiMagnetizationObservable W β S w)^2 ∂W.law := by
  let M := actualParisiMagnetizationObservable W β
  have he (w : Ω) : (M T w-M S w)^2=(M T w*M T w+M S w*M S w)-2*(M S w*M T w) := by ring
  change (∫ w,(M T w-M S w)^2 ∂W.law)=
    (∫ w,(M T w)^2 ∂W.law)-∫ w,(M S w)^2 ∂W.law
  simp_rw [he]
  have H := integral_sub
    ((integrable_actualParisiMagnetization_pair W β T T).add
      (integrable_actualParisiMagnetization_pair W β S S))
    ((integrable_actualParisiMagnetization_pair W β S T).const_mul 2)
  have HA := integral_add (integrable_actualParisiMagnetization_pair W β T T)
    (integrable_actualParisiMagnetization_pair W β S S)
  simp only [Pi.sub_apply,Pi.add_apply] at H HA
  dsimp only [M]
  rw [H,HA,integral_const_mul,actualParisiMagnetization_crossMoment W β hβ S T hST]
  simp only [←pow_two]
  ring

theorem actualParisiFullPosteriorForm_secondMoment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (c : ℕ → ℝ) (n : ℕ) :
    (∫ w,(∑ i ∈ Finset.range n,c i*actualParisiMagnetizationIncrement W β (t i) (t (i+1)) w)^2
      ∂W.law) = ∑ i ∈ Finset.range n,c i^2*
      ((∫ w,(actualParisiMagnetizationObservable W β (t (i+1)) w)^2 ∂W.law)-
        ∫ w,(actualParisiMagnetizationObservable W β (t i) w)^2 ∂W.law) := by
  classical
  let X := fun i => actualParisiMagnetizationIncrement W β (t i) (t (i+1))
  let V := fun i => (∫ w,(actualParisiMagnetizationObservable W β (t (i+1)) w)^2 ∂W.law)-
    ∫ w,(actualParisiMagnetizationObservable W β (t i) w)^2 ∂W.law
  have hcov (i j : ℕ) : (∫ w,X i w*X j w ∂W.law)=if i=j then V i else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [ite_true,←pow_two]
      exact actualParisiIncrement_secondMoment W β hβ _ _ (ht (Nat.le_succ i))
    rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hij|hji
    · exact actualParisiIncrement_disjoint_crossMoment W β hβ _ _ _ _
        (ht (Nat.le_succ i)) (ht (by omega)) (ht (Nat.le_succ j))
    · have H := actualParisiIncrement_disjoint_crossMoment W β hβ (t j) (t (j+1)) (t i) (t (i+1))
        (ht (Nat.le_succ j)) (ht (by omega)) (ht (Nat.le_succ i))
      simpa only [mul_comm] using H
  have hint (i j : ℕ) : Integrable (fun w => c i*c j*(X i w*X j w)) W.law :=
    (integrable_actualParisiIncrement_pair W β _ _ _ _).const_mul _
  have he (w : Ω) : (∑ i ∈ Finset.range n,c i*X i w)^2=
      ∑ i ∈ Finset.range n,∑ j ∈ Finset.range n,c i*c j*(X i w*X j w) := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change (∫ w,(∑ i ∈ Finset.range n,c i*X i w)^2 ∂W.law)=∑ i ∈ Finset.range n,c i^2*V i
  simp_rw [he]
  rw [integral_finsetSum (Finset.range n) (fun i hi =>
    integrable_finset_sum (Finset.range n) (fun j hj => hint i j))]
  simp_rw [integral_finsetSum (Finset.range n) (fun j hj => hint _ j),integral_const_mul,hcov]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,hi,ite_true]
  ring

end SKConstants
