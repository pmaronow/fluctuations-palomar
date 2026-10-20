module
public import SKConstants.ScalarProcessLagBlocks
public import SKConstants.ScalarProcessLagCanonical
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.MeasurableLIntegral

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace SKConstants

def scalarHistoryAppendEquiv (m : ℕ) : (n : ℕ) →
    (ScalarObservationHistory m × ScalarObservationHistory n) ≃ᵐ ScalarObservationHistory (m+n)
  | 0 => MeasurableEquiv.prodPUnit
  | n+1 => MeasurableEquiv.prodAssoc.symm.trans
      (MeasurableEquiv.prodCongr (scalarHistoryAppendEquiv m n) (MeasurableEquiv.refl ℝ))

lemma scalarHistoryAppend_lastField (z : ℝ) (m n : ℕ)
    (p : ScalarObservationHistory m) (q : ScalarObservationHistory n) :
    scalarLastField z (m+n) (scalarHistoryAppendEquiv m n (p,q)) =
      scalarLastField (scalarLastField z m p) n q := by
  cases n with
  | zero => rfl
  | succ n => rfl

lemma scalarHistoryAppend_lintegral (z : ℝ) (δ : ℝ≥0) (m n : ℕ)
    (f : ScalarObservationHistory (m+n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ h, f h ∂scalarObservationHistoryLaw z (fun _ => δ) (m+n)) =
    ∫⁻ p, ∫⁻ q, f (scalarHistoryAppendEquiv m n (p,q))
      ∂scalarObservationHistoryLaw (scalarLastField z m p) (fun _ => δ) n
      ∂scalarObservationHistoryLaw z (fun _ => δ) m := by
  induction n with
  | zero =>
    change _ = ∫⁻ p, ∫⁻ _q : PUnit, f p ∂Measure.dirac PUnit.unit
      ∂scalarObservationHistoryLaw z (fun _ => δ) m
    simp
  | succ n ih =>
    simp only [Nat.add_succ] at f hf ⊢
    let F : ScalarObservationHistory (m+n) → ℝ≥0∞ := fun h =>
      ∫⁻ y, f (h,y) ∂scalarObservationStepKernel z δ (m+n) h
    have hf' : Measurable (Function.uncurry (fun h : ScalarObservationHistory (m+n) =>
      fun y : ℝ => f (h,y))) := hf
    have hF : Measurable F := hf'.lintegral_kernel_prod_right
    change (∫⁻ h, f h ∂(scalarObservationHistoryLaw z (fun _ => δ) (m+n) ⊗ₘ
      scalarObservationStepKernel z δ (m+n))) = _
    rw [Measure.lintegral_compProd hf]
    change (∫⁻ h, F h ∂scalarObservationHistoryLaw z (fun _ => δ) (m+n)) = _
    rw [ih F hF]
    apply lintegral_congr
    intro p
    change _ = ∫⁻ q, f (scalarHistoryAppendEquiv m (n+1) (p,q))
      ∂(scalarObservationHistoryLaw (scalarLastField z m p) (fun _ => δ) n ⊗ₘ
        scalarObservationStepKernel (scalarLastField z m p) δ n)
    let g : ScalarObservationHistory n × ℝ → ℝ≥0∞ := fun q =>
      f (scalarHistoryAppendEquiv m (n+1) (p,q))
    have hg : Measurable g := hf.comp ((scalarHistoryAppendEquiv m (n+1)).measurable.comp
      (measurable_const.prodMk measurable_id))
    change _ = ∫⁻ q, g q ∂(scalarObservationHistoryLaw (scalarLastField z m p) (fun _ => δ) n ⊗ₘ
        scalarObservationStepKernel (scalarLastField z m p) δ n)
    rw [Measure.lintegral_compProd hg]
    apply lintegral_congr
    intro q
    dsimp [F, g]
    rw [scalarObservationStepKernel_apply, scalarObservationStepKernel_apply,
      scalarHistoryAppend_lastField]
    rfl

def scalarLagBlockLength (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => scalarLagBlockLength N k + N

def scalarLagBlockFlattenEquiv (N : ℕ) : (k : ℕ) →
    ScalarLagBlockHistory N k ≃ᵐ ScalarObservationHistory (scalarLagBlockLength N k)
  | 0 => MeasurableEquiv.refl _
  | k+1 => (MeasurableEquiv.prodCongr (scalarLagBlockFlattenEquiv N k)
      (MeasurableEquiv.refl _)).trans (scalarHistoryAppendEquiv (scalarLagBlockLength N k) N)

lemma scalarLagBlockFlatten_lastField (z : ℝ) (N k : ℕ) (p : ScalarLagBlockHistory N k) :
    scalarLastField z (scalarLagBlockLength N k) (scalarLagBlockFlattenEquiv N k p) =
      scalarLagBlockLastField z N k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change scalarLastField z (scalarLagBlockLength N k+N)
      (scalarHistoryAppendEquiv (scalarLagBlockLength N k) N
        (scalarLagBlockFlattenEquiv N k p.1, p.2)) = _
    rw [scalarHistoryAppend_lastField, ih]
    rfl

lemma scalarLagBlockFlatten_lintegral (z : ℝ) (δ : ℝ≥0) (N k : ℕ)
    (f : ScalarObservationHistory (scalarLagBlockLength N k) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f (scalarLagBlockFlattenEquiv N k p) ∂scalarLagBlockHistoryLaw z (fun _ => δ) N k) =
      ∫⁻ h, f h ∂scalarObservationHistoryLaw z (fun _ => δ) (scalarLagBlockLength N k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let K : Kernel (ScalarObservationHistory (scalarLagBlockLength N k)) (ScalarObservationHistory N) :=
      (scalarObservationHistoryKernel (fun _ => δ) N).comap
        (scalarLastField z (scalarLagBlockLength N k)) (measurable_scalarLastField z _)
    let g : ScalarObservationHistory (scalarLagBlockLength N k) → ℝ≥0∞ := fun h =>
      ∫⁻ q, f (scalarHistoryAppendEquiv (scalarLagBlockLength N k) N (h,q)) ∂K h
    have hg' : Measurable (Function.uncurry (fun h => fun q =>
        f (scalarHistoryAppendEquiv (scalarLagBlockLength N k) N (h,q)))) :=
      hf.comp (scalarHistoryAppendEquiv (scalarLagBlockLength N k) N).measurable
    have hg : Measurable g := hg'.lintegral_kernel_prod_right
    let F : ScalarLagBlockHistory N k × ScalarObservationHistory N → ℝ≥0∞ :=
      fun p => f (scalarLagBlockFlattenEquiv N (k+1) p)
    have hF : Measurable F := hf.comp (scalarLagBlockFlattenEquiv N (k+1)).measurable
    change (∫⁻ p, f (scalarLagBlockFlattenEquiv N (k+1) p)
      ∂(scalarLagBlockHistoryLaw z (fun _ => δ) N k ⊗ₘ scalarLagBlockStepKernel z (fun _ => δ) N k)) = _
    change (∫⁻ p, F p ∂(scalarLagBlockHistoryLaw z (fun _ => δ) N k ⊗ₘ
      scalarLagBlockStepKernel z (fun _ => δ) N k)) = _
    rw [Measure.lintegral_compProd hF]
    change (∫⁻ p, ∫⁻ q, f (scalarLagBlockFlattenEquiv N (k+1) (p,q))
      ∂scalarLagBlockStepKernel z (fun _ => δ) N k p ∂scalarLagBlockHistoryLaw z (fun _ => δ) N k) = _
    have he : (∫⁻ p, ∫⁻ q, f (scalarLagBlockFlattenEquiv N (k+1) (p,q))
        ∂scalarLagBlockStepKernel z (fun _ => δ) N k p ∂scalarLagBlockHistoryLaw z (fun _ => δ) N k) =
        ∫⁻ p, g (scalarLagBlockFlattenEquiv N k p) ∂scalarLagBlockHistoryLaw z (fun _ => δ) N k := by
      apply lintegral_congr
      intro p
      dsimp only [g, K]
      rw [Kernel.comap_apply, scalarObservationHistoryKernel_apply,
        scalarLagBlockStepKernel_apply, scalarLagBlockFlatten_lastField]
      rfl
    rw [he, ih g hg]
    change _ = ∫⁻ h : ScalarObservationHistory (scalarLagBlockLength N k+N),
      f h ∂scalarObservationHistoryLaw z (fun _ => δ) (scalarLagBlockLength N k+N)
    rw [scalarHistoryAppend_lintegral z δ (scalarLagBlockLength N k) N f hf]
    apply lintegral_congr
    intro p
    dsimp only [g, K]
    rw [Kernel.comap_apply, scalarObservationHistoryKernel_apply]

lemma scalarLagBlockFlatten_hasLaw (z : ℝ) (δ : ℝ≥0) (N k : ℕ) :
    HasLaw (scalarLagBlockFlattenEquiv N k)
      (scalarObservationHistoryLaw z (fun _ => δ) (scalarLagBlockLength N k))
      (scalarLagBlockHistoryLaw z (fun _ => δ) N k) where
  aemeasurable := (scalarLagBlockFlattenEquiv N k).measurable.aemeasurable
  map_eq := by
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    rw [lintegral_map hf (scalarLagBlockFlattenEquiv N k).measurable]
    exact scalarLagBlockFlatten_lintegral z δ N k f hf

lemma scalarLagBlockGroup_hasLaw (z : ℝ) (δ : ℝ≥0) (N k : ℕ) :
    HasLaw (scalarLagBlockFlattenEquiv N k).symm
      (scalarLagBlockHistoryLaw z (fun _ => δ) N k)
      (scalarObservationHistoryLaw z (fun _ => δ) (scalarLagBlockLength N k)) where
  aemeasurable := (scalarLagBlockFlattenEquiv N k).symm.measurable.aemeasurable
  map_eq := by
    rw [← (scalarLagBlockFlatten_hasLaw z δ N k).map_eq,
      Measure.map_map (scalarLagBlockFlattenEquiv N k).symm.measurable
        (scalarLagBlockFlattenEquiv N k).measurable]
    simp

def scalarUniformLagBlockHistory {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (n N k : ℕ) : Bool × Ω → ScalarLagBlockHistory N k :=
  (scalarLagBlockFlattenEquiv N k).symm ∘
    scalarUniformObservationHistory z B n (scalarLagBlockLength N k)

theorem scalarUniformLagBlockHistory_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (n N k : ℕ) :
    HasLaw (scalarUniformLagBlockHistory z B n N k)
      (scalarLagBlockHistoryLaw z (brownianMeshVariance (scalarUniformTime n)) N k)
      (scalarHiddenBrownianLaw z P) := by
  have hdt : brownianMeshVariance (scalarUniformTime n) =
      fun _ => 1 / ((n:ℝ≥0)+1) := funext (brownianMeshVariance_scalarUniformTime n)
  rw [hdt]
  apply (scalarLagBlockGroup_hasLaw z (1/((n:ℝ≥0)+1)) N k).comp
  have hh := scalarUniformObservationHistory_hasLaw hB z n (scalarLagBlockLength N k)
  rwa [hdt] at hh

theorem scalarUniformWeightedLagBlockSum_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (n N k : ℕ) (w : ℕ → ℝ)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hduration : (scalarUniformTime n N : ℝ) ≤ h)
    (A : ℝ) (hA : 0 < A) (hw : ∀ j < k, |w j| ≤ A) :
    Concentration.LocalQuadraticMGF
      (scalarWeightedLagBlockSum z (brownianMeshVariance (scalarUniformTime n)) N w k ∘
        scalarUniformLagBlockHistory z B n N k)
      (scalarHiddenBrownianLaw z P)
      ((2048*Real.exp 1*h^2)*∑ j ∈ Finset.range k, (w j)^2) (1/(32*h*A)) := by
  apply (scalarWeightedLagBlockSum_local_mgf z _ N h hh hh1
    (fun j _ => by exact_mod_cast scalarUniformMeshVariance_le_one n j)
    (by rw [scalarUniformMeshVariance_sum]; exact hduration) w A hA k hw).comp_hasLaw
  exact scalarUniformLagBlockHistory_hasLaw hB z n N k

end SKConstants
