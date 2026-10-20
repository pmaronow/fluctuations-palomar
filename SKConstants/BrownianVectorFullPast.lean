module
public import SKConstants.BrownianFullPastPredictable
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianVectorFullPast {ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : ι → Ω) : Iic T → ι → ℝ := fun s i => D s (ω i)

def brownianVectorMeshIncrement {ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (k : ℕ) (ω : ι → Ω) : ι → ℝ :=
  fun i => brownianMeshIncrement D t k (ω i)

theorem brownianVectorMeshIncrement_hasLaw {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    HasLaw (brownianVectorMeshIncrement (ι := ι) D t k)
      (Measure.pi (fun _ : ι => gaussianReal 0 (brownianMeshVariance t k)))
      (Measure.pi (fun _ : ι => Q)) := by
  have h := brownianMeshIncrement_hasLaw hD t ht k
  exact (iIndepFun_pi (fun _ : ι => h.aemeasurable)).hasLaw_pi
    (fun i => h.comp (measurePreserving_eval (fun _ : ι => Q) i).hasLaw)

theorem brownianVectorFullPast_indep_increment {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q)
    (hmD : ∀ s, Measurable (D s)) (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    IndepFun (brownianVectorFullPast (ι := ι) D (t k)) (brownianVectorMeshIncrement D t k)
      (Measure.pi (fun _ : ι => Q)) := by
  let f : Ω → (Iic (t k) → ℝ) := brownianFullPast D (t k)
  let g : Ω → ℝ := brownianMeshIncrement D t k
  have hf : Measurable f := Measurable.of_eval (fun s => hmD s)
  have hg : Measurable g := (hmD _).sub (hmD _)
  have hi : IndepFun f g Q := by
    have he : t k+brownianMeshVariance t k=t (k+1) := add_tsub_cancel_of_le (ht (by omega))
    change IndepFun (fun ω (s : Iic (t k)) => D s ω) (fun ω => D (t (k+1)) ω-D (t k) ω) Q
    simpa only [Function.comp_def,Function.id_def,he] using
      ((hD.indepFun_shift (t k)).comp (φ := fun w : ℝ≥0 → ℝ => w (brownianMeshVariance t k))
        (ψ := id) (measurable_pi_apply _) measurable_id).symm
  have hpair : HasLaw (fun ω => (f ω,g ω)) ((Q.map f).prod (Q.map g)) Q :=
    hi.hasLaw_prod ⟨hf.aemeasurable,rfl⟩ ⟨hg.aemeasurable,rfl⟩
  have hj := (iIndepFun_pi (fun _ : ι => hpair.aemeasurable)).hasLaw_pi
    (fun i => hpair.comp (measurePreserving_eval (fun _ : ι => Q) i).hasLaw)
  have hs := (measurePreserving_arrowProdEquivProdArrow (Iic (t k) → ℝ) ℝ ι
    (fun _ => Q.map f) (fun _ => Q.map g)).hasLaw.comp hj
  have hfl : HasLaw (fun ω : ι → Ω => fun i => f (ω i)) (Measure.pi (fun _ : ι => Q.map f))
      (Measure.pi (fun _ : ι => Q)) :=
    (iIndepFun_pi (fun _ : ι => hf.aemeasurable)).hasLaw_pi
      (fun i => (show HasLaw f (Q.map f) Q from ⟨hf.aemeasurable,rfl⟩).comp
        (measurePreserving_eval (fun _ : ι => Q) i).hasLaw)
  have hgl : HasLaw (fun ω : ι → Ω => fun i => g (ω i)) (Measure.pi (fun _ : ι => Q.map g))
      (Measure.pi (fun _ : ι => Q)) :=
    (iIndepFun_pi (fun _ : ι => hg.aemeasurable)).hasLaw_pi
      (fun i => (show HasLaw g (Q.map g) Q from ⟨hg.aemeasurable,rfl⟩).comp
        (measurePreserving_eval (fun _ : ι => Q) i).hasLaw)
  have hij : IndepFun (fun ω : ι → Ω => fun i => f (ω i))
      (fun ω : ι → Ω => fun i => g (ω i)) (Measure.pi (fun _ : ι => Q)) :=
    (indepFun_iff_hasLaw_prodMk_prod hfl hgl).2 hs
  exact hij.comp (Measurable.of_eval (fun s => Measurable.of_eval (fun i =>
    (measurable_pi_apply s).comp (measurable_pi_apply i)))) measurable_id

theorem brownianVectorStaticPast_indep_increment {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    IndepFun (fun u : A × (ι → Ω) => (u.1,brownianVectorFullPast D (t k) u.2))
      (fun u => brownianVectorMeshIncrement D t k u.2) (P.prod (Measure.pi (fun _ : ι => Q))) := by
  apply indepFun_static_prod_left P (Measure.pi (fun _ : ι => Q))
  · exact (show Measurable (brownianVectorFullPast (ι := ι) D (t k)) from
      Measurable.of_eval (fun s : Iic (t k) => Measurable.of_eval (fun i : ι =>
        (hmD s).comp (measurable_pi_apply i)))).aemeasurable
  · exact (show Measurable (brownianVectorMeshIncrement (ι := ι) D t k) from
      Measurable.of_eval (fun i : ι => ((hmD _).sub (hmD _)).comp
        (measurable_pi_apply i))).aemeasurable
  · exact brownianVectorFullPast_indep_increment Q D hD hmD t ht k

end SKConstants
