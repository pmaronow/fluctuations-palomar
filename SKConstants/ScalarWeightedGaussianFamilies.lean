module

public import SKConstants.ScalarWeightedBrownianGaussian
public import SKConstants.GaussianProposalAmbientReconstruction
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem scalarHasLaw_borel_of_ae_tendsto {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E) (Y : Ω → E) (hX : ∀ l, HasLaw (X l) ν P)
    (hYm : AEMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun l => X l ω) Filter.atTop (nhds (Y ω))) :
    HasLaw Y ν P := by
  refine ⟨hYm, ?_⟩
  have : IsProbabilityMeasure (P.map Y) := (Measure.isProbabilityMeasure_map_iff hYm).mpr inferInstance
  have he : (⟨P.map Y,inferInstance⟩ : FiniteMeasure E) = ⟨ν,inferInstance⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    have hl : Filter.Tendsto (fun l => ∫ ω,f (X l ω) ∂P) Filter.atTop
        (nhds (∫ ω,f (Y ω) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun l => (f.continuous.measurable.comp_aemeasurable (hX l).aemeasurable).aestronglyMeasurable)
        (integrable_const ‖f‖) (fun l => ae_of_all _ (fun ω => f.norm_coe_le_norm _))
        (hlim.mono (fun ω hω => (f.continuous.tendsto _).comp hω))
    have hx (l : ℕ) : (∫ ω,f (X l ω) ∂P)=∫ y,f y ∂ν := by
      simpa only [Function.comp_def] using (hX l).integral_comp f.continuous.measurable.aestronglyMeasurable
    have hy := integral_map hYm f.continuous.measurable.aestronglyMeasurable
    exact hy.trans (tendsto_nhds_unique hl (by simp only [hx]; exact tendsto_const_nhds))
  exact congrArg (fun μ : FiniteMeasure E => (μ : Measure E)) he

theorem scalarIndependentGaussian_linear_covariance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P) (hi : iIndepFun X P)
    (a b : ι → ℝ) :
    cov[fun ω => ∑ i,a i*X i ω,fun ω => ∑ i,b i*X i ω;P] =
      ∑ i,a i*b i*(v i : ℝ) := by
  have hp (i : ι) : MemLp (X i) 2 P := (hX i).hasGaussianLaw.memLp_two
  have hc (i j : ι) : cov[X i,X j;P] = if i=j then (v i : ℝ) else 0 := by
    by_cases hij : i=j
    · subst j
      rw [covariance_self (hX i).aemeasurable,(hX i).variance_eq,variance_id_gaussianReal,ite_eq_left rfl]
    · rw [(hi.indepFun hij).covariance_eq_zero (hp i) (hp j),ite_eq_right hij]
  rw [covariance_fun_sum_fun_sum (fun i => (hp i).const_mul (a i))
    (fun i => (hp i).const_mul (b i))]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right,hc]
  simp [mul_ite]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarIndependentGaussian_linearForms_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P) (hi : iIndepFun X P)
    (a : κ → ι → ℝ)
    (ha : ∀ k l, k ≠ l → (∑ i,a k i*a l i*(v i : ℝ))=0) :
    HasLaw (fun ω k => ∑ i,a k i*X i ω)
      (Measure.pi (fun k => gaussianReal 0 (∑ i,(a k i)^2*(v i : ℝ)).toNNReal)) P := by
  let L : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x k := ∑ i,a k i*x i
      map_add' x y := by ext k; simp [mul_add,Finset.sum_add_distrib]
      map_smul' c x := by ext k; simp [Finset.mul_sum]; congr 1; ext i; ring
      cont := by fun_prop }
  have hg : HasGaussianLaw (fun ω k => ∑ i,a k i*X i ω) P :=
    (hi.hasGaussianLaw (fun i => (hX i).hasGaussianLaw)).map L
  have hind : iIndepFun (fun k ω => ∑ i,a k i*X i ω) P := by
    apply hg.iIndepFun_of_covariance_eq_zero
    intro k l hkl
    rw [scalarIndependentGaussian_linear_covariance P X v hX hi]
    exact ha k l hkl
  apply hind.hasLaw_pi
  intro k
  have hm : (∫ ω, (∑ i,a k i*X i ω) ∂P)=0 := by
    rw [integral_finsetSum _ (fun i _ => (hX i).hasGaussianLaw.integrable.const_mul (a k i))]
    simp_rw [integral_const_mul,(hX _).integral_eq,integral_id_gaussianReal,mul_zero]
    simp
  have hv : variance (fun ω => ∑ i,a k i*X i ω) P = ∑ i,(a k i)^2*(v i : ℝ) := by
    rw [← covariance_self (hg.eval k).aemeasurable,
      scalarIndependentGaussian_linear_covariance P X v hX hi]
    simp only [sq]
  exact ⟨(hg.eval k).aemeasurable, by rw [(hg.eval k).map_eq_gaussianReal,hm,hv]⟩

variable {A : Type*} [MeasurableSpace A]

def scalarTwoBrownianMeshFamily (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (q : ℕ → ℝ≥0) (m : ℕ) (u : Ω × A) : (Fin m ⊕ Fin m) → ℝ :=
  Sum.elim (fun i => brownianMeshIncrement B q i u.1)
    (fun i => brownianMeshIncrement C q i u.2)

theorem scalarTwoBrownianMeshFamily_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (m : ℕ) :
    HasLaw (scalarTwoBrownianMeshFamily B C q m)
      (Measure.pi (fun i : Fin m ⊕ Fin m => gaussianReal 0
        (Sum.elim (fun j : Fin m => brownianMeshVariance q j) (fun j : Fin m => brownianMeshVariance q j) i)))
      (P.prod Q) := by
  let X : Ω → Fin m → ℝ := fun ω i => brownianMeshIncrement B q i ω
  let Y : A → Fin m → ℝ := fun ω i => brownianMeshIncrement C q i ω
  have hx : HasLaw X (Measure.pi (fun i : Fin m => gaussianReal 0 (brownianMeshVariance q i))) P :=
    ((brownianMeshIncrement_iIndepFun hB q hq).precomp Fin.val_injective).hasLaw_pi
      (fun i => brownianMeshIncrement_hasLaw hB q hq i)
  have hy : HasLaw Y (Measure.pi (fun i : Fin m => gaussianReal 0 (brownianMeshVariance q i))) Q :=
    ((brownianMeshIncrement_iIndepFun hC q hq).precomp Fin.val_injective).hasLaw_pi
      (fun i => brownianMeshIncrement_hasLaw hC q hq i)
  have hp := (indepFun_prod₀ hx.aemeasurable hy.aemeasurable).hasLaw_prod
    (hx.comp (measurePreserving_fst (μ := P) (ν := Q)).hasLaw)
    (hy.comp (measurePreserving_snd (μ := P) (ν := Q)).hasLaw)
  exact (measurePreserving_sumPiEquivProdPi_symm
    (fun i : Fin m ⊕ Fin m => gaussianReal 0
      (Sum.elim (fun j : Fin m => brownianMeshVariance q j) (fun j : Fin m => brownianMeshVariance q j) i))).hasLaw.comp hp

theorem scalarTwoBrownianMeshFamily_linearForms_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (m : ℕ)
    (a : κ → (Fin m ⊕ Fin m) → ℝ)
    (ha : ∀ k l, k ≠ l → (∑ i, a k i*a l i*
      (Sum.elim (fun j : Fin m => (brownianMeshVariance q j : ℝ))
        (fun j : Fin m => (brownianMeshVariance q j : ℝ)) i))=0) :
    HasLaw (fun u k => ∑ i,a k i*scalarTwoBrownianMeshFamily B C q m u i)
      (Measure.pi (fun k => gaussianReal 0 (∑ i,(a k i)^2*
        (Sum.elim (fun j : Fin m => (brownianMeshVariance q j : ℝ))
          (fun j : Fin m => (brownianMeshVariance q j : ℝ)) i)).toNNReal)) (P.prod Q) := by
  let v : (Fin m ⊕ Fin m) → ℝ≥0 :=
    Sum.elim (fun j : Fin m => brownianMeshVariance q j) (fun j : Fin m => brownianMeshVariance q j)
  have hf := scalarTwoBrownianMeshFamily_hasLaw P Q B C hB hC q hq m
  have hm (i : Fin m ⊕ Fin m) : HasLaw
      (fun u => scalarTwoBrownianMeshFamily B C q m u i) (gaussianReal 0 (v i)) (P.prod Q) :=
    (measurePreserving_eval (fun i => gaussianReal 0 (v i)) i).hasLaw.comp hf
  have hi : iIndepFun (fun i u => scalarTwoBrownianMeshFamily B C q m u i) (P.prod Q) :=
    (iIndepFun_iff_hasLaw_pi_pi hm).mpr hf
  have hv (i : Fin m ⊕ Fin m) : (v i : ℝ) =
      Sum.elim (fun j : Fin m => (brownianMeshVariance q j : ℝ))
        (fun j : Fin m => (brownianMeshVariance q j : ℝ)) i := by cases i <;> rfl
  have hh := scalarIndependentGaussian_linearForms_hasLaw (P.prod Q) _ v hm hi a
    (fun k l hkl => by simpa only [hv] using ha k l hkl)
  simpa only [hv] using hh

end SKConstants
