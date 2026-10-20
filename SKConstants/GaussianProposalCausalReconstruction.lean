module

public import SKConstants.GaussianProposalMeasurableFrame
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

@[expose] def upperPairSplit (n : ℕ) :
    UpperPair (Fin (n + 1)) ≃ Fin (n + 1) ⊕ UpperPair (Fin n) where
  toFun p := if hi : p.1.1 = 0 then .inl p.1.2 else
    .inr ⟨(p.1.1.pred hi, p.1.2.pred (by
      intro hj
      have := p.property
      simp only [hj, Fin.le_zero_iff] at this
      exact hi this)), by
        have hp := p.property
        simp only [Fin.le_def] at hp ⊢
        simp only [Fin.val_pred]
        omega⟩
  invFun s := match s with
    | .inl j => ⟨(0, j), Fin.zero_le j⟩
    | .inr p => ⟨(p.1.1.succ, p.1.2.succ), by
        simpa only [Fin.succ_le_succ_iff] using p.property⟩
  left_inv p := by
    by_cases hi : p.1.1 = 0
    · simp only [dite_eq_left hi]
      apply Subtype.ext
      exact Prod.ext hi.symm rfl
    · simp only [dite_eq_right hi]
      apply Subtype.ext
      apply Prod.ext <;> simp
  right_inv s := by
    cases s with
    | inl j => simp
    | inr p => simp

@[expose] def gaussianColumnLaw (sigma : ℝ) (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  Measure.pi (fun j => gaussianReal 0
    (if j = 0 then (4 * sigma ^ 2).toNNReal else (2 * sigma ^ 2).toNNReal))

instance gaussianColumnLaw_probability (sigma : ℝ) (n : ℕ) :
    IsProbabilityMeasure (gaussianColumnLaw sigma n) := by
  unfold gaussianColumnLaw
  infer_instance

@[expose] def joinUpper (n : ℕ)
    (x : (Fin (n + 1) → ℝ) × (UpperPair (Fin n) → ℝ)) :
    UpperPair (Fin (n + 1)) → ℝ :=
  fun p => Sum.elim x.1 x.2 (upperPairSplit n p)

theorem joinUpper_measurable (n : ℕ) : Measurable (joinUpper n) := by
  apply Measurable.of_eval
  intro p
  unfold joinUpper
  cases upperPairSplit n p with
  | inl j => exact (measurable_pi_apply j).comp measurable_fst
  | inr q => exact (measurable_pi_apply q).comp measurable_snd

theorem joinUpper_law (sigma : ℝ) (n : ℕ) :
    ((gaussianColumnLaw sigma n).prod (gaussianUpperLaw sigma (Fin n))).map
      (joinUpper n) = gaussianUpperLaw sigma (Fin (n + 1)) := by
  let μ : UpperPair (Fin (n + 1)) → Measure ℝ := fun p => gaussianReal 0
    (if p.1.1 = p.1.2 then (4 * sigma ^ 2).toNNReal else (2 * sigma ^ 2).toNNReal)
  let ν := fun s => μ ((upperPairSplit n).symm s)
  have hL : (Measure.pi fun j => ν (.inl j)) = gaussianColumnLaw sigma n := by
    unfold gaussianColumnLaw ν μ
    congr 1
    funext j
    simp [upperPairSplit, eq_comm]
  have hR : (Measure.pi fun p => ν (.inr p)) = gaussianUpperLaw sigma (Fin n) := by
    unfold gaussianUpperLaw ν μ
    congr 1
    funext p
    simp [upperPairSplit]
  have hS := measurePreserving_sumPiEquivProdPi_symm ν
  have hI := measurePreserving_piCongrLeft μ (upperPairSplit n).symm
  have h := hI.comp hS
  rw [hL, hR] at h
  convert h.map_eq using 1
  · congr 1
    funext x p
    simp [joinUpper, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi]
    cases upperPairSplit n p <;> rfl
  · rfl

@[expose] def matrixUpper {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    UpperPair (Fin n) → ℝ := fun p => M p.1.1 p.1.2

theorem matrixUpper_measurable (n : ℕ) :
    Measurable (matrixUpper (n := n)) := by
  apply Measurable.of_eval
  intro p
  exact (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)

theorem matrixUpper_fill {n : ℕ} (q : UpperPair (Fin n) → ℝ) :
    matrixUpper (fillSymmetricMatrix q) = q := by
  funext p
  unfold matrixUpper fillSymmetricMatrix sortedPair
  congr 1
  apply Subtype.ext
  simp [min_eq_left p.property, max_eq_right p.property]

theorem assemblyUpper_law (sigma : ℝ) (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, dot (B i) (B j) = if i = j then 1 else 0) :
    (gaussianUpperLaw sigma (Fin n)).map (fun q => matrixUpper (basisAssembly B q)) =
      gaussianUpperLaw sigma (Fin n) := by
  calc
    _ = ((gaussianUpperLaw sigma (Fin n)).map (basisAssembly B)).map matrixUpper := by
      rw [Measure.map_map (matrixUpper_measurable n) (basisAssembly_measurable B)]
      rfl
    _ = ((gaussianUpperLaw sigma (Fin n)).map fillSymmetricMatrix).map matrixUpper := by
      rw [basisAssembly_law sigma B hB, filledGaussian_law]
    _ = gaussianUpperLaw sigma (Fin n) := by
      rw [Measure.map_map (matrixUpper_measurable n) fillSymmetricMatrix_measurable]
      have hmap : (fun q : UpperPair (Fin n) → ℝ => matrixUpper (fillSymmetricMatrix q)) = id := by
        funext q
        exact matrixUpper_fill q
      rw [show matrixUpper ∘ fillSymmetricMatrix = id from hmap, Measure.map_id]

@[expose] def CausalNoise : ℕ → Type
  | 0 => UpperPair (Fin 0) → ℝ
  | n + 1 => (Fin (n + 1) → ℝ) × CausalNoise n

instance causalNoiseMeasurableSpace : (n : ℕ) → MeasurableSpace (CausalNoise n)
  | 0 => inferInstanceAs (MeasurableSpace (UpperPair (Fin 0) → ℝ))
  | n + 1 => by
    letI := causalNoiseMeasurableSpace n
    exact inferInstanceAs (MeasurableSpace ((Fin (n + 1) → ℝ) × CausalNoise n))

@[expose] def causalNoiseLaw (sigma : ℝ) : (n : ℕ) → Measure (CausalNoise n)
  | 0 => gaussianUpperLaw sigma (Fin 0)
  | n + 1 => (gaussianColumnLaw sigma n).prod (causalNoiseLaw sigma n)

instance causalNoiseLaw_probability (sigma : ℝ) :
    (n : ℕ) → IsProbabilityMeasure (causalNoiseLaw sigma n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (gaussianUpperLaw sigma (Fin 0)))
  | n + 1 => by
    let := causalNoiseLaw_probability sigma n
    exact inferInstanceAs
      (IsProbabilityMeasure ((gaussianColumnLaw sigma n).prod (causalNoiseLaw sigma n)))

variable {Past : Type*} [MeasurableSpace Past]

@[expose] def causalUpper
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past) :
    (n : ℕ) → Past → CausalNoise n → (UpperPair (Fin n) → ℝ)
  | 0, _, z => z
  | n + 1, a, z => matrixUpper (basisAssembly (completionFrame 0 (direction n a))
      (joinUpper n (z.1, causalUpper direction update n (update n a z.1) z.2)))

theorem causalUpper_measurable
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) : Measurable (Function.uncurry (causalUpper direction update n)) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    let B : Past → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun a => completionFrame 0 (direction n a)
    have hB := completionFrame_measurable (0 : Fin (n + 1))
      (direction n) (hdirection n)
    have hc : Measurable (fun x : Past × CausalNoise (n + 1) => x.2.1) :=
      measurable_fst.comp measurable_snd
    have hz : Measurable (fun x : Past × CausalNoise (n + 1) => x.2.2) :=
      measurable_snd.comp measurable_snd
    have hpast : Measurable (fun x : Past × CausalNoise (n + 1) =>
        update n x.1 x.2.1) := (hupdate n).comp (measurable_fst.prodMk hc)
    have hsub : Measurable (fun x : Past × CausalNoise (n + 1) =>
        causalUpper direction update n (update n x.1 x.2.1) x.2.2) :=
      ih.comp (hpast.prodMk hz)
    have hjoin := (joinUpper_measurable n).comp (hc.prodMk hsub)
    have hasm := (adaptiveAssembly_measurable B hB).comp
      (measurable_fst.prodMk hjoin)
    exact (matrixUpper_measurable (n + 1)).comp hasm

theorem causalUpper_law
    (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) (a : Past) :
    (causalNoiseLaw sigma n).map (causalUpper direction update n a) =
      gaussianUpperLaw sigma (Fin n) := by
  induction n generalizing a with
  | zero => exact Measure.map_id
  | succ n ih =>
    let B := completionFrame (0 : Fin (n + 1)) (direction n a)
    let F : (Fin (n + 1) → ℝ) → CausalNoise n → UpperPair (Fin n) → ℝ :=
      fun c z => causalUpper direction update n (update n a c) z
    have hpast : Measurable (fun c => update n a c) :=
      (hupdate n).comp (measurable_const.prodMk measurable_id)
    have hF : Measurable (Function.uncurry F) :=
      (causalUpper_measurable direction update hdirection hupdate n).comp
        ((hpast.comp measurable_fst).prodMk measurable_snd)
    have hjoint := adaptiveStep_joint_law
      (μ := gaussianColumnLaw sigma n) (ν := causalNoiseLaw sigma n)
      hF (fun c => ih (update n a c))
    have hpost : Measurable (fun x : (Fin (n + 1) → ℝ) ×
        (UpperPair (Fin n) → ℝ) => matrixUpper (basisAssembly B (joinUpper n x))) :=
      (matrixUpper_measurable (n + 1)).comp
        ((basisAssembly_measurable B).comp (joinUpper_measurable n))
    have hg : Measurable (fun x : (Fin (n + 1) → ℝ) × CausalNoise n =>
        (x.1, F x.1 x.2)) := measurable_fst.prodMk hF
    change ((gaussianColumnLaw sigma n).prod (causalNoiseLaw sigma n)).map
      (fun x => matrixUpper (basisAssembly B (joinUpper n (x.1, F x.1 x.2)))) = _
    calc
      _ = (((gaussianColumnLaw sigma n).prod (causalNoiseLaw sigma n)).map
          (fun x => (x.1, F x.1 x.2))).map
          (fun x => matrixUpper (basisAssembly B (joinUpper n x))) := by
        rw [Measure.map_map hpost hg]
        rfl
      _ = ((gaussianColumnLaw sigma n).prod (gaussianUpperLaw sigma (Fin n))).map
          (fun x => matrixUpper (basisAssembly B (joinUpper n x))) := by rw [hjoint]
      _ = (gaussianUpperLaw sigma (Fin (n + 1))).map
          (fun q => matrixUpper (basisAssembly B q)) := by
        rw [← joinUpper_law sigma n]
        exact (Measure.map_map
          ((matrixUpper_measurable (n + 1)).comp (basisAssembly_measurable B))
          (joinUpper_measurable n)).symm
      _ = _ := assemblyUpper_law sigma (n + 1) B
        (completionFrame_orthogonal 0 (direction n a))

@[expose] def causalGOE
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (n : ℕ) (a : Past) (z : CausalNoise n) : Matrix (Fin n) (Fin n) ℝ :=
  fillSymmetricMatrix (causalUpper direction update n a z)

theorem causalGOE_measurable
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) : Measurable (Function.uncurry (causalGOE direction update n)) :=
  fillSymmetricMatrix_measurable.comp
    (causalUpper_measurable direction update hdirection hupdate n)

theorem causalGOE_law
    (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) (a : Past) :
    (causalNoiseLaw sigma n).map (causalGOE direction update n a) =
      (primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma) := by
  have hf : Measurable (causalUpper direction update n a) :=
    (causalUpper_measurable direction update hdirection hupdate n).comp
    (measurable_const.prodMk measurable_id)
  calc
    _ = ((causalNoiseLaw sigma n).map (causalUpper direction update n a)).map
        fillSymmetricMatrix := by
      rw [Measure.map_map fillSymmetricMatrix_measurable hf]
      rfl
    _ = (gaussianUpperLaw sigma (Fin n)).map fillSymmetricMatrix := by
      rw [causalUpper_law sigma direction update hdirection hupdate n a]
    _ = _ := filledGaussian_law sigma

theorem causalGOE_joint_law
    (μ : Measure Past) [SFinite μ] (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) :
    (μ.prod (causalNoiseLaw sigma n)).map
      (fun x => (x.1, causalGOE direction update n x.1 x.2)) =
      μ.prod ((primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)) :=
  adaptiveStep_joint_law (causalGOE_measurable direction update hdirection hupdate n)
    (causalGOE_law sigma direction update hdirection hupdate n)

theorem causalGOE_independent
    (μ : Measure Past) [IsProbabilityMeasure μ] (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (update : (n : ℕ) → Past → (Fin (n + 1) → ℝ) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) :
    IndepFun Prod.fst (fun x => causalGOE direction update n x.1 x.2)
      (μ.prod (causalNoiseLaw sigma n)) :=
  adaptiveStep_independent_ae (causalGOE_measurable direction update hdirection hupdate n)
    (Filter.Eventually.of_forall
      (causalGOE_law sigma direction update hdirection hupdate n))

end SKConstants.GaussianProposal
