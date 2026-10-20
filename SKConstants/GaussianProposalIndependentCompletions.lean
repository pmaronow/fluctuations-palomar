module

public import SKConstants.GaussianProposalCompletionRotation
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

section Reorder
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]
  (μ : Measure A) (ν : Measure B) (ρ : Measure C) (η : Measure D)
  [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite η]

lemma prod_quad_shuffle :
    ((μ.prod ν).prod (ρ.prod η)).map
      (fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))) = (μ.prod ρ).prod (ν.prod η) := by
  have h1 := measurePreserving_prodAssoc μ ν (ρ.prod η)
  have h2 := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν ρ η).symm)
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id η))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ρ ν η)
  have h5 := (measurePreserving_prodAssoc μ ρ (ν.prod η)).symm
  exact (h5.comp (h4.comp (h3.comp (h2.comp h1)))).map_eq
end Reorder

@[expose] def PaperCompletionNoise (n : ℕ) : ℕ → Type
  | 0 => Unit
  | K+1 => EuclideanSpace ℝ (Fin n) × PaperCompletionNoise n K

instance paperCompletionNoiseMeasurableSpace (n : ℕ) :
    (K : ℕ) → MeasurableSpace (PaperCompletionNoise n K)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | K+1 => by
    letI := paperCompletionNoiseMeasurableSpace n K
    exact inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin n) × PaperCompletionNoise n K))

@[expose] def paperCompletionNoiseLaw (n : ℕ) :
    (K : ℕ) → Measure (PaperCompletionNoise n K)
  | 0 => Measure.dirac ()
  | K+1 => (primitiveGaussian (Fin n)).prod (paperCompletionNoiseLaw n K)

instance paperCompletionNoiseLaw_probability (n : ℕ) :
    (K : ℕ) → IsProbabilityMeasure (paperCompletionNoiseLaw n K)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | K+1 => by
    let := paperCompletionNoiseLaw_probability n K
    exact inferInstanceAs (IsProbabilityMeasure
      ((primitiveGaussian (Fin n)).prod (paperCompletionNoiseLaw n K)))

@[expose] def PaperAugmentedNoise (n : ℕ) : ℕ → Type
  | 0 => EuclideanSpace ℝ (Fin n × Fin n)
  | K+1 => (EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n)) ×
      PaperAugmentedNoise n K

instance paperAugmentedNoiseMeasurableSpace (n : ℕ) :
    (K : ℕ) → MeasurableSpace (PaperAugmentedNoise n K)
  | 0 => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin n × Fin n)))
  | K+1 => by
    letI := paperAugmentedNoiseMeasurableSpace n K
    exact inferInstanceAs (MeasurableSpace
      ((EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n)) × PaperAugmentedNoise n K))

@[expose] def paperAugmentedNoiseLaw (n : ℕ) :
    (K : ℕ) → Measure (PaperAugmentedNoise n K)
  | 0 => primitiveGaussian (Fin n × Fin n)
  | K+1 => ((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).prod
      (paperAugmentedNoiseLaw n K)

instance paperAugmentedNoiseLaw_probability (n : ℕ) :
    (K : ℕ) → IsProbabilityMeasure (paperAugmentedNoiseLaw n K)
  | 0 => inferInstanceAs (IsProbabilityMeasure (primitiveGaussian (Fin n × Fin n)))
  | K+1 => by
    let := paperAugmentedNoiseLaw_probability n K
    exact inferInstanceAs (IsProbabilityMeasure
      (((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).prod
        (paperAugmentedNoiseLaw n K)))

@[expose] def paperAugmentedOriginal (n : ℕ) :
    (K : ℕ) → PaperAugmentedNoise n K → StoppedNoise (Fin n) K
  | 0,z => z
  | K+1,z => (z.1.1,paperAugmentedOriginal n K z.2)

lemma paperAugmentedOriginal_measurable (n K : ℕ) : Measurable (paperAugmentedOriginal n K) := by
  induction K with
  | zero => exact measurable_id
  | succ K ih => exact measurable_fst.fst.prodMk (ih.comp measurable_snd)

lemma paperAugmentedOriginal_law (n K : ℕ) :
    (paperAugmentedNoiseLaw n K).map (paperAugmentedOriginal n K) =
      stoppedNoiseLaw (Fin n) K := by
  induction K with
  | zero => exact Measure.map_id
  | succ K ih =>
    change (((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).prod
      (paperAugmentedNoiseLaw n K)).map
      (Prod.map Prod.fst (paperAugmentedOriginal n K)) = _
    rw [← Measure.map_prod_map _ _ measurable_fst (paperAugmentedOriginal_measurable n K),ih]
    simp only [Measure.map_fst_prod,measure_univ,one_smul,stoppedNoiseLaw]

variable {Past : Type*} [MeasurableSpace Past]

@[expose] def paperIndependentCompletions (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → PaperAugmentedNoise n K → PaperCompletionNoise n K
  | 0,_,_ => ()
  | K+1,s,z =>
    let F := paperFrame s.2 (target K s.1)
    (paperIndependentCompletion F z.1,
      paperIndependentCompletions r n target update K (update K s.1 z.1.1,tailRows F) z.2)

@[expose] def paperAugmentedCausalOutput (r n : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : PaperAugmentedNoise n K) :
    (UpperPair (Fin (r+K)) → ℝ) × PaperCompletionNoise n K :=
  (paperCausalUpper r n σ target update K s (paperAugmentedOriginal n K z),
    paperIndependentCompletions r n target update K s z)

set_option backward.isDefEq.respectTransparency true in
lemma paperIndependentCompletions_measurable (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) : Measurable (Function.uncurry (paperIndependentCompletions r n target update K)) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    let F (s : PaperState r n (K+1) Past) : Matrix (Fin (r+K+1)) (Fin n) ℝ :=
      paperFrame s.2 (target K s.1)
    have hF (i : Fin (r+K+1)) (j : Fin n) : Measurable (fun s => F s i j) :=
      paperFrame_measurable (m := r+K) (n := n)
        (A := PaperState r n (K+1) Past) (fun s => s.2) (fun s => target K s.1)
        (fun _ _ => by fun_prop) (fun j => (htarget K j).comp measurable_fst) i j
    have hc : Measurable (fun x : PaperState r n (K+1) Past × PaperAugmentedNoise n (K+1) =>
        paperIndependentCompletion (F x.1) x.2.1) := by
      let X := PaperState r n (K+1) Past × PaperAugmentedNoise n (K+1)
      have hp (i j : Fin n) : Measurable (fun x : X => remainingProjection (F x.1) i j) := by
        simp only [remainingProjection,Matrix.mul_apply,Matrix.transpose_apply,tailRows]
        exact Finset.measurable_sum _ (fun k _ =>
          ((hF k.succ i).comp measurable_fst).mul ((hF k.succ j).comp measurable_fst))
      have hq (i j : Fin n) : Measurable (fun x : X => paperUsedProjection (F x.1) i j) :=
        measurable_const.sub (hp i j)
      have hm : Measurable (fun x : X =>
          paperUsedProjection (F x.1) *ᵥ (fun i => x.2.1.1 (.inl i))+
            remainingProjection (F x.1) *ᵥ x.2.1.2.ofLp) := by
        apply Measurable.of_eval
        intro i
        simp only [Pi.add_apply,Matrix.mulVec,dotProduct]
        apply Measurable.add
        · exact Finset.measurable_sum _ (fun j _ => (hq i j).mul
            ((EuclideanSpace.proj (Sum.inl j : Fin n ⊕ Unit)).continuous.measurable.comp
              measurable_snd.fst.fst))
        · exact Finset.measurable_sum _ (fun j _ => (hp i j).mul
            ((EuclideanSpace.proj j).continuous.measurable.comp measurable_snd.fst.snd))
      exact (WithLp.measurable_toLp 2 _).comp hm
    have hs : Measurable (fun x : PaperState r n (K+1) Past × PaperAugmentedNoise n (K+1) =>
        (update K x.1.1 x.2.1.1,tailRows (F x.1))) := by
      apply Measurable.prodMk
      · exact (hupdate K).comp (measurable_fst.fst.prodMk measurable_snd.fst.fst)
      · apply Measurable.of_eval
        intro i
        apply Measurable.of_eval
        intro j
        exact (hF i.succ j).comp measurable_fst
    change Measurable (fun x : PaperState r n (K+1) Past × PaperAugmentedNoise n (K+1) =>
      (paperIndependentCompletion (F x.1) x.2.1,
        paperIndependentCompletions r n target update K
          (update K x.1.1 x.2.1.1,tailRows (F x.1)) x.2.2))
    exact hc.prodMk (ih.comp (hs.prodMk measurable_snd.snd))

lemma paperAugmentedCausalOutput_measurable (r n : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) : Measurable (Function.uncurry (paperAugmentedCausalOutput r n σ target update K)) := by
  exact ((paperCausalUpper_measurable r n σ target update htarget hupdate K).comp
    (measurable_fst.prodMk ((paperAugmentedOriginal_measurable n K).comp measurable_snd))).prodMk
    (paperIndependentCompletions_measurable r n target update htarget hupdate K)

theorem paperAugmentedCausalOutput_joint_law (r n : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j,dot (s.2 i) (s.2 j)=if i=j then 1 else 0) :
    (paperAugmentedNoiseLaw n K).map (paperAugmentedCausalOutput r n σ target update K s) =
      (gaussianUpperLaw σ (Fin (r+K))).prod (paperCompletionNoiseLaw n K) := by
  induction K with
  | zero =>
    change (primitiveGaussian (Fin n × Fin n)).map
      (fun z => ((fun p => compressedEntry σ (fun i j => s.2 i j) p z),())) =
      (gaussianUpperLaw σ (Fin r)).prod (Measure.dirac ())
    have hm : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
        fun p => compressedEntry σ (fun i j => s.2 i j) p z) :=
      (compressedEntries_joint_measurable σ (fun _ : Unit => fun i j => s.2 i j)
        (fun _ _ => measurable_const)).comp
        ((show Measurable (fun _ : EuclideanSpace ℝ (Fin n × Fin n) => ()) from measurable_const).prodMk measurable_id)
    have hb : (primitiveGaussian (Fin n × Fin n)).map
        (fun z => fun p => compressedEntry σ (fun i j => s.2 i j) p z) =
        gaussianUpperLaw σ (Fin r) :=
      compressedEntries_joint_law σ (fun i j => s.2 i j) horth
    rw [Measure.prod_dirac,← hb]
    exact (Measure.map_map
      (show Measurable (fun x : UpperPair (Fin r) → ℝ => (x,())) from measurable_id.prodMk measurable_const) hm).symm
  | succ K ih =>
    let := paperCompletionNoiseLaw_probability n K
    let := paperAugmentedNoiseLaw_probability n K
    let B := completionFrame (0 : Fin (r+K+1)) (paperDirection s.2 (target K s.1))
    let frame := paperFrame s.2 (target K s.1)
    let C := fun p : EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n) =>
      (ambientColumn σ (r+K) frame p.1,paperIndependentCompletion frame p)
    let F := fun p : EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n) =>
      paperAugmentedCausalOutput r n σ target update K
        (update K s.1 p.1,tailRows frame)
    have hframe : ∀ i j,dot (frame i) (frame j)=if i=j then 1 else 0 :=
      paperFrame_orthogonal s.2 (target K s.1) horth
    have htail := tailRows_orthogonal frame hframe
    have hpast : Measurable (fun p : EuclideanSpace ℝ (Fin n ⊕ Unit) ×
        EuclideanSpace ℝ (Fin n) => update K s.1 p.1) :=
      (hupdate K).comp (measurable_const.prodMk measurable_fst)
    have hF : Measurable (Function.uncurry F) :=
      (paperAugmentedCausalOutput_measurable r n σ target update htarget hupdate K).comp
        (((hpast.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd)
    have hjoint := adaptiveStep_joint_law
      (μ := (primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n)))
      (ν := paperAugmentedNoiseLaw n K) hF
      (fun p => ih (update K s.1 p.1,tailRows frame) htail)
    have hC : Measurable C :=
      ((ambientColumn_measurable σ (r+K) frame).comp measurable_fst).prodMk
        (paperIndependentCompletion_measurable frame)
    have hproject :
        (((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).prod
          ((gaussianUpperLaw σ (Fin (r+K))).prod (paperCompletionNoiseLaw n K))).map
          (Prod.map C id) =
        ((gaussianColumnLaw σ (r+K)).prod (primitiveGaussian (Fin n))).prod
          ((gaussianUpperLaw σ (Fin (r+K))).prod (paperCompletionNoiseLaw n K)) := by
      rw [← Measure.map_prod_map _ _ hC measurable_id,Measure.map_id]
      exact congrArg (fun μ => μ.prod
        ((gaussianUpperLaw σ (Fin (r+K))).prod (paperCompletionNoiseLaw n K)))
        (paperColumnIndependentCompletion_joint_law σ frame hframe)
    let shuffle : ((Fin (r+K+1) → ℝ) × EuclideanSpace ℝ (Fin n)) ×
        ((UpperPair (Fin (r+K)) → ℝ) × PaperCompletionNoise n K) →
        ((Fin (r+K+1) → ℝ) × (UpperPair (Fin (r+K)) → ℝ)) ×
          PaperCompletionNoise n (K+1) :=
      fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))
    have hshuffle : Measurable shuffle :=
      (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
        (measurable_fst.snd.prodMk measurable_snd.snd)
    let A : (Fin (r+K+1) → ℝ) × (UpperPair (Fin (r+K)) → ℝ) →
        UpperPair (Fin (r+K+1)) → ℝ :=
      fun x => matrixUpper (basisAssembly B (joinUpper (r+K) x))
    have hA : Measurable A := (matrixUpper_measurable (r+K+1)).comp
      ((basisAssembly_measurable B).comp (joinUpper_measurable (r+K)))
    have hAlaw : ((gaussianColumnLaw σ (r+K)).prod
        (gaussianUpperLaw σ (Fin (r+K)))).map A =
        gaussianUpperLaw σ (Fin (r+K+1)) := by
      calc
        _ = (gaussianUpperLaw σ (Fin (r+K+1))).map
            (fun q => matrixUpper (basisAssembly B q)) := by
          rw [← joinUpper_law σ (r+K)]
          exact (Measure.map_map
            ((matrixUpper_measurable (r+K+1)).comp (basisAssembly_measurable B))
            (joinUpper_measurable (r+K))).symm
        _ = _ := assemblyUpper_law σ (r+K+1) B
          (completionFrame_orthogonal 0 (paperDirection s.2 (target K s.1)))
    have hshuffleLaw :
        (((gaussianColumnLaw σ (r+K)).prod (primitiveGaussian (Fin n))).prod
          ((gaussianUpperLaw σ (Fin (r+K))).prod (paperCompletionNoiseLaw n K))).map shuffle =
        ((gaussianColumnLaw σ (r+K)).prod (gaussianUpperLaw σ (Fin (r+K)))).prod
          ((primitiveGaussian (Fin n)).prod (paperCompletionNoiseLaw n K)) :=
      prod_quad_shuffle _ _ _ _
    have hg : Measurable (fun x : (EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n)) ×
        PaperAugmentedNoise n K => (x.1,F x.1 x.2)) := measurable_fst.prodMk hF
    change (((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).prod
      (paperAugmentedNoiseLaw n K)).map
      (((Prod.map A id) ∘ shuffle ∘ (Prod.map C id)) ∘ (fun x => (x.1,F x.1 x.2))) = _
    rw [← Measure.map_map ((hA.prodMap measurable_id).comp
      (hshuffle.comp (hC.prodMap measurable_id))) hg,hjoint]
    change (((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).prod
      ((gaussianUpperLaw σ (Fin (r+K))).prod (paperCompletionNoiseLaw n K))).map
      (((Prod.map A id) ∘ shuffle) ∘ (Prod.map C id)) = _
    rw [← Measure.map_map ((hA.prodMap measurable_id).comp hshuffle)
      (hC.prodMap measurable_id),hproject]
    let : IsProbabilityMeasure ((primitiveGaussian (Fin n)).prod (paperCompletionNoiseLaw n K)) :=
      paperCompletionNoiseLaw_probability n (K+1)
    rw [← Measure.map_map (hA.prodMap measurable_id) hshuffle,hshuffleLaw,
      ← Measure.map_prod_map _ _ hA measurable_id,Measure.map_id,hAlaw]
    rfl

@[expose] def actualPaperAugmentedOutput (r K : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : PaperAugmentedNoise (r+K) K) :
    Matrix (Fin (r+K)) (Fin (r+K)) ℝ × PaperCompletionNoise (r+K) K :=
  (actualPaperProposal r K σ target update a (paperAugmentedOriginal (r+K) K z),
    paperIndependentCompletions r (r+K) target update K (a,1) z)

lemma actualPaperAugmentedOutput_measurable (r K : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (Function.uncurry (actualPaperAugmentedOutput r K σ target update)) := by
  apply Measurable.prodMk
  · exact (actualPaperProposal_measurable r K σ target update htarget hupdate).comp
      (measurable_fst.prodMk ((paperAugmentedOriginal_measurable (r+K) K).comp measurable_snd))
  · exact (paperIndependentCompletions_measurable r (r+K) target update htarget hupdate K).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem actualPaperAugmentedOutput_law (r K : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) (a : Past) :
    (paperAugmentedNoiseLaw (r+K) K).map (actualPaperAugmentedOutput r K σ target update a) =
      ((primitiveGaussian (Fin (r+K) × Fin (r+K))).map (goeMatrix σ)).prod
        (paperCompletionNoiseLaw (r+K) K) := by
  have hI : ∀ i j : Fin (r+K), dot ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) i)
      ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) j)=if i=j then 1 else 0 := by
    intro i j
    have he : (1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)=canonicalBasis := by
      ext i j
      exact Matrix.one_apply
    rw [he]
    exact canonicalBasis_orthogonal i j
  have hu := paperAugmentedCausalOutput_joint_law r (r+K) σ target update htarget hupdate K (a,1) hI
  have hm : Measurable (paperAugmentedCausalOutput r (r+K) σ target update K (a,1)) :=
    (paperAugmentedCausalOutput_measurable r (r+K) σ target update htarget hupdate K).comp
      ((show Measurable (fun _ : PaperAugmentedNoise (r+K) K => (a,(1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ))) from measurable_const).prodMk measurable_id)
  have hB := basisAssembly_measurable (1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)
  have hh := congrArg (fun μ => μ.map (Prod.map
    (basisAssembly (1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)) id)) hu
  rw [Measure.map_map (hB.prodMap measurable_id) hm,
    ← Measure.map_prod_map _ _ hB measurable_id,Measure.map_id,basisAssembly_law σ _ hI] at hh
  convert hh using 1
  congr 1
  funext z
  apply Prod.ext
  · exact (paperTensorOutput_eq_tensor r (r+K) σ target update K (a,1)
      (paperAugmentedOriginal (r+K) K z)).symm
  · rfl

theorem actualPaperAugmentedOutput_joint_law (μ : Measure Past) [SFinite μ]
    (r K : ℕ) (σ : ℝ)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    (μ.prod (paperAugmentedNoiseLaw (r+K) K)).map
      (fun x => (x.1,actualPaperAugmentedOutput r K σ target update x.1 x.2)) =
      μ.prod (((primitiveGaussian (Fin (r+K) × Fin (r+K))).map (goeMatrix σ)).prod
        (paperCompletionNoiseLaw (r+K) K)) :=
  adaptiveStep_joint_law
    (actualPaperAugmentedOutput_measurable r K σ target update htarget hupdate)
    (actualPaperAugmentedOutput_law r K σ target update htarget hupdate)

@[expose] def paperCompletionReplayNoise (n : ℕ) :
    (K : ℕ) → PaperCompletionNoise n K → StoppedNoise (Fin n) K
  | 0,_ => (0 : EuclideanSpace ℝ (Fin n × Fin n))
  | K+1,z => (WithLp.toLp 2 (Sum.elim z.1.ofLp (fun _ => 0)),paperCompletionReplayNoise n K z.2)

lemma paperCompletionReplayNoise_measurable (n K : ℕ) :
    Measurable (paperCompletionReplayNoise n K) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    apply Measurable.prodMk
    · apply (WithLp.measurable_toLp 2 _).comp
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (EuclideanSpace.proj i).continuous.measurable.comp measurable_fst
      | inr i => exact measurable_const
    · exact ih.comp measurable_snd

theorem paperIndependentCompletions_matrix_query_coupling (r n : ℕ) (N : ℝ) (hN : 0<N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hunit : ∀ k a z w,(∀ i : Fin n,z (.inl i)=w (.inl i)) → update k a z=update k a w)
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j,dot (s.2 i) (s.2 j)=if i=j then 1 else 0)
    (z : PaperAugmentedNoise n K) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcomp : frameProjection s.2 * W * frameProjection s.2 =
      paperTensorProposal r n (skSigma N) target update K s (paperAugmentedOriginal n K z)) :
    paperMatrixQueryRun r n N target update K s
      (paperCompletionReplayNoise n K (paperIndependentCompletions r n target update K s z)) W =
      proposalTerminalPast update K s.1 (paperAugmentedOriginal n K z) := by
  induction K generalizing W with
  | zero => rfl
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    have hF := paperFrame_orthogonal s.2 (target K s.1) horth
    have he := matrix_query_completed_endpoint_of_compression r n K N hN target update
      s horth (paperAugmentedOriginal n (K+1) z) W hcomp
    have hz : ∀ i : Fin n,
        paperQueriedNoise N F W
          (WithLp.toLp 2 (Sum.elim (paperIndependentCompletion F z.1).ofLp (fun _ => 0))) (.inl i) =
            z.1.1 (.inl i) := by
      intro i
      change (remainingProjection F *ᵥ (W *ᵥ normalizedQuery N (F 0))+
        paperUsedProjection F *ᵥ (paperIndependentCompletion F z.1).ofLp) i = _
      rw [paperIndependentCompletion_used F hF]
      exact congrFun he i
    have hu := hunit K s.1 _ z.1.1 hz
    change paperMatrixQueryRun r n N target update K
      (update K s.1 (paperQueriedNoise N F W
        (WithLp.toLp 2 (Sum.elim (paperIndependentCompletion F z.1).ofLp (fun _ => 0)))),tailRows F)
      (paperCompletionReplayNoise n K
        (paperIndependentCompletions r n target update K (update K s.1 z.1.1,tailRows F) z.2)) W =
      proposalTerminalPast update K (update K s.1 z.1.1) (paperAugmentedOriginal n K z.2)
    rw [hu]
    apply ih (update K s.1 z.1.1,tailRows F) (tailRows_orthogonal F hF) z.2 W
    exact matrix_remaining_compression_of_compression r n K (skSigma N) target update
      s horth (paperAugmentedOriginal n (K+1) z) W hcomp

end SKConstants.GaussianProposal
