module

public import SKConstants.GaussianProposalPaperQuery
import Mathlib.Tactic

set_option maxHeartbeats 100000

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal

variable {Past : Type*} [MeasurableSpace Past]

abbrev PaperState (r n K : ℕ) (Past : Type*) :=
  Past × Matrix (Fin (r + K)) (Fin n) ℝ

@[expose] def paperCausalUpper (r n : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K →
      UpperPair (Fin (r + K)) → ℝ
  | 0, s, z => fun p => compressedEntry sigma (fun i j => s.2 i j) p z
  | K + 1, s, z =>
      let B := completionFrame 0 (paperDirection s.2 (target K s.1))
      let F := paperFrame s.2 (target K s.1)
      matrixUpper (basisAssembly B (joinUpper (r + K)
        (ambientColumn sigma (r + K) (fun i j => F i j) z.1,
          paperCausalUpper r n sigma target update K
            (update K s.1 z.1, tailRows F) z.2)))

theorem ambientColumn_step_measurable (r n K : ℕ) (sigma : ℝ)
    (F : PaperState r n (K + 1) Past → Matrix (Fin (r + K + 1)) (Fin n) ℝ)
    (hF : ∀ i j, Measurable (fun s => F s i j)) :
    Measurable (fun x : PaperState r n (K + 1) Past × StoppedNoise (Fin n) (K + 1) =>
      ambientColumn sigma (r + K) (fun i j => F x.1 i j) x.2.1) := by
  have hc := ambientColumn_joint_measurable (Ambient := Fin n)
    (Past := PaperState r n (K + 1) Past) sigma (r + K) (fun s i j => F s i j) hF
  exact hc.comp (measurable_fst.prodMk measurable_snd.fst)

theorem assembledStep_measurable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (m : ℕ) (B : A → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (C : A × X → Fin (m + 1) → ℝ) (Q : A × X → UpperPair (Fin m) → ℝ)
    (hB : ∀ i j, Measurable (fun a => B a i j)) (hC : Measurable C) (hQ : Measurable Q) :
    Measurable (fun x => matrixUpper (basisAssembly (B x.1) (joinUpper m (C x,Q x)))) := by
  have hj := (joinUpper_measurable m).comp (hC.prodMk hQ)
  have hasm := (adaptiveAssembly_measurable B hB).comp (measurable_fst.prodMk hj)
  exact (matrixUpper_measurable (m + 1)).comp hasm

theorem paperCausalUpper_measurable (r n : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) : Measurable (Function.uncurry (paperCausalUpper r n sigma target update K)) := by
  induction K with
  | zero =>
    exact compressedEntries_joint_measurable sigma (fun s : PaperState r n 0 Past =>
      fun i j => s.2 i j) (fun i j => by fun_prop)
  | succ K ih =>
    let B (s : PaperState r n (K + 1) Past) : Matrix (Fin (r + K + 1)) (Fin (r + K + 1)) ℝ :=
      completionFrame (0 : Fin (r + K + 1)) (paperDirection s.2 (target K s.1))
    let F (s : PaperState r n (K + 1) Past) : Matrix (Fin (r + K + 1)) (Fin n) ℝ := paperFrame s.2 (target K s.1)
    have hd (i : Fin (r + K + 1)) : Measurable (fun s : PaperState r n (K + 1) Past =>
        paperDirection s.2 (target K s.1) i) :=
      (measurable_pi_apply i).comp (paperDirection_measurable
        (m := r + K) (n := n) (A := PaperState r n (K + 1) Past)
        (fun s => s.2) (fun s => target K s.1) (fun i j => by fun_prop)
        (fun j => (htarget K j).comp measurable_fst))
    have hB (i j) : Measurable (fun s => B s i j) :=
      completionFrame_measurable 0 _ hd i j
    have hF (i : Fin (r + K + 1)) (j : Fin n) : Measurable (fun s => F s i j) :=
      paperFrame_measurable (m := r + K) (n := n)
      (A := PaperState r n (K + 1) Past) (fun s => s.2) (fun s => target K s.1) (fun i j => by fun_prop)
      (fun j => (htarget K j).comp measurable_fst) i j
    have hs : Measurable (fun x : PaperState r n (K + 1) Past × StoppedNoise (Fin n) (K + 1) =>
        (update K x.1.1 x.2.1, tailRows (F x.1))) := by
      apply Measurable.prodMk
      · exact (hupdate K).comp (measurable_fst.fst.prodMk measurable_snd.fst)
      · apply Measurable.of_eval
        intro i
        apply Measurable.of_eval
        intro j
        exact (hF i.succ j).comp measurable_fst
    have hq : Measurable (fun x : PaperState r n (K + 1) Past × StoppedNoise (Fin n) (K + 1) =>
        paperCausalUpper r n sigma target update K
          (update K x.1.1 x.2.1, tailRows (F x.1)) x.2.2) :=
      ih.comp (hs.prodMk measurable_snd.snd)
    have hc : Measurable (fun x : PaperState r n (K + 1) Past × StoppedNoise (Fin n) (K + 1) =>
        ambientColumn sigma (r + K) (fun i j => F x.1 i j) x.2.1) :=
      ambientColumn_step_measurable r n K sigma F hF
    have hstep := assembledStep_measurable (r + K) B
      (fun x : PaperState r n (K + 1) Past × StoppedNoise (Fin n) (K + 1) =>
        ambientColumn sigma (r + K) (fun i j => F x.1 i j) x.2.1)
      (fun x => paperCausalUpper r n sigma target update K
        (update K x.1.1 x.2.1, tailRows (F x.1)) x.2.2) hB hc hq
    change Measurable (fun x : PaperState r n (K + 1) Past × StoppedNoise (Fin n) (K + 1) =>
      matrixUpper (basisAssembly (B x.1) (joinUpper (r + K)
        (ambientColumn sigma (r + K) (fun i j => F x.1 i j) x.2.1,
          paperCausalUpper r n sigma target update K
            (update K x.1.1 x.2.1, tailRows (F x.1)) x.2.2))))
    exact hstep

theorem paperCausalUpper_law (r n : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0) :
    (stoppedNoiseLaw (Fin n) K).map (paperCausalUpper r n sigma target update K s) =
      gaussianUpperLaw sigma (Fin (r + K)) := by
  induction K with
  | zero => exact compressedEntries_joint_law sigma (fun i j => s.2 i j) horth
  | succ K ih =>
    let B := completionFrame (0 : Fin (r + K + 1)) (paperDirection s.2 (target K s.1))
    let frame := paperFrame s.2 (target K s.1)
    let C := ambientColumn sigma (r + K) (fun i j => frame i j)
    let F : EuclideanSpace ℝ (Fin n ⊕ Unit) → StoppedNoise (Fin n) K →
        UpperPair (Fin (r + K)) → ℝ := fun z noise =>
      paperCausalUpper r n sigma target update K (update K s.1 z, tailRows frame) noise
    have hframe : ∀ i j, dot (frame i) (frame j) = if i = j then 1 else 0 :=
      paperFrame_orthogonal s.2 (target K s.1) horth
    have htail : ∀ i j, dot (tailRows frame i) (tailRows frame j) =
        if i = j then 1 else 0 := by
      intro i j
      change dot (frame i.succ) (frame j.succ) = _
      simpa only [Fin.succ_inj] using hframe i.succ j.succ
    have hpast : Measurable (fun z => update K s.1 z) :=
      (hupdate K).comp (measurable_const.prodMk measurable_id)
    have hF : Measurable (Function.uncurry F) :=
      (paperCausalUpper_measurable r n sigma target update htarget hupdate K).comp
        (((hpast.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd)
    have hjoint := adaptiveStep_joint_law
      (μ := primitiveGaussian (Fin n ⊕ Unit)) (ν := stoppedNoiseLaw (Fin n) K)
      hF (fun z => ih (update K s.1 z, tailRows frame) htail)
    have hC : Measurable C := ambientColumn_measurable sigma (r + K) (fun i j => frame i j)
    have hproject :
        ((primitiveGaussian (Fin n ⊕ Unit)).prod (gaussianUpperLaw sigma (Fin (r + K)))).map
          (Prod.map C id) =
          (gaussianColumnLaw sigma (r + K)).prod (gaussianUpperLaw sigma (Fin (r + K))) := by
      rw [← Measure.map_prod_map _ _ hC measurable_id, Measure.map_id]
      rw [ambientColumn_law sigma (r + K) (fun i j => frame i j) hframe]
    let H : (Fin (r + K + 1) → ℝ) × (UpperPair (Fin (r + K)) → ℝ) →
        UpperPair (Fin (r + K + 1)) → ℝ :=
      fun x => matrixUpper (basisAssembly B (joinUpper (r + K) x))
    have hH : Measurable H := (matrixUpper_measurable (r + K + 1)).comp
      ((basisAssembly_measurable B).comp (joinUpper_measurable (r + K)))
    have hg : Measurable (fun x : EuclideanSpace ℝ (Fin n ⊕ Unit) ×
        StoppedNoise (Fin n) K => (x.1, F x.1 x.2)) := measurable_fst.prodMk hF
    change ((primitiveGaussian (Fin n ⊕ Unit)).prod (stoppedNoiseLaw (Fin n) K)).map
      (fun x => H (C x.1, F x.1 x.2)) = _
    calc
      _ = (((primitiveGaussian (Fin n ⊕ Unit)).prod (stoppedNoiseLaw (Fin n) K)).map
          (fun x => (x.1, F x.1 x.2))).map (H ∘ Prod.map C id) := by
        rw [Measure.map_map (hH.comp (hC.prodMap measurable_id)) hg]
        rfl
      _ = ((primitiveGaussian (Fin n ⊕ Unit)).prod
          (gaussianUpperLaw sigma (Fin (r + K)))).map (H ∘ Prod.map C id) := by rw [hjoint]
      _ = (((primitiveGaussian (Fin n ⊕ Unit)).prod
          (gaussianUpperLaw sigma (Fin (r + K)))).map (Prod.map C id)).map H :=
        (Measure.map_map hH (hC.prodMap measurable_id)).symm
      _ = ((gaussianColumnLaw sigma (r + K)).prod (gaussianUpperLaw sigma (Fin (r + K)))).map H := by
        rw [hproject]
      _ = (gaussianUpperLaw sigma (Fin (r + K + 1))).map
          (fun q => matrixUpper (basisAssembly B q)) := by
        rw [← joinUpper_law sigma (r + K)]
        exact (Measure.map_map
          ((matrixUpper_measurable (r + K + 1)).comp (basisAssembly_measurable B))
          (joinUpper_measurable (r + K))).symm
      _ = _ := assemblyUpper_law sigma (r + K + 1) B
        (completionFrame_orthogonal 0 (paperDirection s.2 (target K s.1)))

@[expose] def paperTensorProposal (r n : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K → Matrix (Fin n) (Fin n) ℝ
  | 0, s, z => (s.2ᵀ * s.2) * goeMatrix sigma z * (s.2ᵀ * s.2)
  | K + 1, s, z =>
      let F := paperFrame s.2 (target K s.1)
      physicalColumnTerm sigma (r + K) F z.1 +
        paperTensorProposal r n sigma target update K (update K s.1 z.1, tailRows F) z.2

@[expose] def paperTensorOutput (r n : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    Matrix (Fin n) (Fin n) ℝ :=
  s.2ᵀ * fillSymmetricMatrix (paperCausalUpper r n sigma target update K s z) * s.2

 theorem paperTensorOutput_step (r n K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past) (z : StoppedNoise (Fin n) (K + 1)) :
    paperTensorOutput r n sigma target update (K + 1) s z =
      physicalColumnTerm sigma (r + K) (paperFrame s.2 (target K s.1)) z.1 +
        paperTensorOutput r n sigma target update K
          (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2 := by
  let E : Matrix (Fin (r + K + 1)) (Fin n) ℝ := s.2
  let B := completionFrame (0 : Fin (r + K + 1)) (paperDirection E (target K s.1))
  let F := paperFrame E (target K s.1)
  let c := ambientColumn sigma (r + K) (fun i j => F i j) z.1
  let q := paperCausalUpper r n sigma target update K (update K s.1 z.1, tailRows F) z.2
  change Eᵀ * fillSymmetricMatrix (matrixUpper (basisAssembly B (joinUpper (r + K) (c,q)))) * E = _
  rw [fill_matrixUpper_of_isSymm _ (basisAssembly_isSymm B _)]
  have hconj : Eᵀ * basisAssembly B (joinUpper (r + K) (c,q)) * E =
      Fᵀ * borderMatrix (r + K) c (fillSymmetricMatrix q) * F := by
    change Eᵀ * basisAssembly B (joinUpper (r + K) (c,q)) * E =
      (B * E)ᵀ * borderMatrix (r + K) c (fillSymmetricMatrix q) * (B * E)
    rw [Matrix.transpose_mul]
    unfold basisAssembly
    rw [fillJoin_border]
    simp only [Matrix.mul_assoc]
  rw [hconj, border_conjugation_decomposition]
  have hdiag : c 0 = 2 * sigma * z.1 (.inr ()) := ambientColumn_zero sigma (r + K) _ _
  have hoff : columnOffVector F c = (Real.sqrt 2 * sigma) •
      (((tailRows F)ᵀ * tailRows F) *ᵥ (fun i => z.1 (.inl i))) :=
    ambientColumn_offVector sigma (r + K) F z.1
  rw [hdiag, hoff]
  rfl

theorem paperTensorOutput_eq_tensor (r n : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperTensorOutput r n sigma target update K s z =
      paperTensorProposal r n sigma target update K s z := by
  induction K with
  | zero =>
    let E : Matrix (Fin r) (Fin n) ℝ := s.2
    change Eᵀ * fillSymmetricMatrix (fun p => compressedEntry sigma (fun i j => E i j) p z) * E =
      (Eᵀ * E) * goeMatrix sigma z * (Eᵀ * E)
    have hc := compressedMatrix_eq_conjugation sigma E z
    change fillSymmetricMatrix (fun p => compressedEntry sigma (fun i j => E i j) p z) =
      E * goeMatrix sigma z * Eᵀ at hc
    rw [hc]
    simp only [Matrix.mul_assoc]
  | succ K ih =>
    rw [paperTensorOutput_step]
    rw [ih]
    rfl

theorem paperTensorProposal_law (r K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin (r + K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (s : PaperState r (r + K) K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0) :
    (stoppedNoiseLaw (Fin (r + K)) K).map (paperTensorProposal r (r + K) sigma target update K s) =
      (primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma) := by
  have heq : paperTensorProposal r (r + K) sigma target update K s =
      fun z => basisAssembly s.2 (paperCausalUpper r (r + K) sigma target update K s z) := by
    funext z
    exact (paperTensorOutput_eq_tensor r (r + K) sigma target update K s z).symm
  have hsource : Measurable (paperCausalUpper r (r + K) sigma target update K s) :=
    (paperCausalUpper_measurable r (r + K) sigma target update htarget hupdate K).comp
      (measurable_const.prodMk measurable_id)
  rw [heq]
  calc
    _ = ((stoppedNoiseLaw (Fin (r + K)) K).map
        (paperCausalUpper r (r + K) sigma target update K s)).map (basisAssembly s.2) :=
      (Measure.map_map (basisAssembly_measurable s.2) hsource).symm
    _ = (gaussianUpperLaw sigma (Fin (r + K))).map (basisAssembly s.2) := by
      rw [paperCausalUpper_law r (r + K) sigma target update htarget hupdate K s horth]
    _ = _ := basisAssembly_law sigma s.2 horth

@[expose] def actualPaperProposal (r K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin (r + K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r + K)) K) :
    Matrix (Fin (r + K)) (Fin (r + K)) ℝ :=
  paperTensorProposal r (r + K) sigma target update K (a, 1) z

theorem actualPaperProposal_law (r K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin (r + K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) (a : Past) :
    (stoppedNoiseLaw (Fin (r + K)) K).map (actualPaperProposal r K sigma target update a) =
      (primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma) := by
  apply paperTensorProposal_law r K sigma target update htarget hupdate (a, 1)
  intro i j
  change dot ((1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) i)
    ((1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) j) = _
  have hId : (1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) = canonicalBasis := by
    ext i j
    exact Matrix.one_apply
  rw [hId]
  exact canonicalBasis_orthogonal i j

theorem actualPaperProposal_measurable (r K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin (r + K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (Function.uncurry (actualPaperProposal r K sigma target update)) := by
  have hs : Measurable (fun x : Past × StoppedNoise (Fin (r + K)) K => ((x.1, (1 :
      Matrix (Fin (r + K)) (Fin (r + K)) ℝ)), x.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hupper := (paperCausalUpper_measurable r (r + K) sigma target update htarget hupdate K).comp hs
  have hphysical := (basisAssembly_measurable (1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ)).comp hupper
  convert hphysical using 1
  funext x
  exact (paperTensorOutput_eq_tensor r (r + K) sigma target update K (x.1, 1) x.2).symm

theorem actualPaperProposal_joint_law
    (μ : Measure Past) [SFinite μ] (r K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin (r + K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (htarget : ∀ k j, Measurable (fun a => target k a j))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    (μ.prod (stoppedNoiseLaw (Fin (r + K)) K)).map
      (fun x => (x.1, actualPaperProposal r K sigma target update x.1 x.2)) =
      μ.prod ((primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma)) :=
  adaptiveStep_joint_law
    (actualPaperProposal_measurable r K sigma target update htarget hupdate)
    (actualPaperProposal_law r K sigma target update htarget hupdate)

end SKConstants.GaussianProposal
