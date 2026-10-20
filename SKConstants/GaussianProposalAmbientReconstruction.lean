module

public import SKConstants.GaussianProposalCausalReconstruction
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem linearForms_family_gaussian (a : κ → ι → ℝ) :
    HasGaussianLaw (fun z : EuclideanSpace ℝ ι => fun k => linearForm (a k) z)
      (primitiveGaussian ι) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := primitiveGaussian ι)).map_fun
    (ContinuousLinearMap.pi (fun k => linearFormCLM (a k)))
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  funext k
  simp only [id_eq, ContinuousLinearMap.pi_apply, linearFormCLM_apply]

theorem orthogonalLinearForms_joint_law (a : κ → ι → ℝ)
    (horth : ∀ k l, k ≠ l → dot (a k) (a l) = 0) :
    (primitiveGaussian ι).map (fun z k => linearForm (a k) z) =
      Measure.pi (fun k => gaussianReal 0 (dot (a k) (a k)).toNNReal) := by
  have hgauss := linearForms_family_gaussian a
  have hind : iIndepFun (fun k => linearForm (a k)) (primitiveGaussian ι) := by
    apply hgauss.iIndepFun_of_covariance_eq_zero
    intro k l hkl
    rw [linearForm_covariance]
    exact horth k l hkl
  have hmeas k := (linearForm_gaussian (a k)).aemeasurable
  rw [iIndepFun.map_fun_eq_pi_map hmeas hind]
  congr 1
  funext k
  rw [(linearForm_gaussian (a k)).map_eq_gaussianReal, linearForm_mean]
  have hv : Var[linearForm (a k); primitiveGaussian ι] = dot (a k) (a k) := by
    rw [← covariance_self (hmeas k), linearForm_covariance]
    rfl
  rw [hv]

variable {Ambient : Type} [Fintype Ambient] [DecidableEq Ambient]

@[expose] def ambientColumnCoefficients (sigma : ℝ) (n : ℕ)
    (frame : Fin (n + 1) → Ambient → ℝ) (j : Fin (n + 1)) : Ambient ⊕ Unit → ℝ :=
  fun r => if j = 0 then Sum.elim (fun _ => 0) (fun _ => 2 * sigma) r
    else Sum.elim (fun i => Real.sqrt 2 * sigma * frame j i) (fun _ => 0) r

theorem ambientColumnCoefficients_dot (sigma : ℝ) (n : ℕ)
    (frame : Fin (n + 1) → Ambient → ℝ)
    (hframe : ∀ i j, dot (frame i) (frame j) = if i = j then 1 else 0)
    (j k : Fin (n + 1)) :
    dot (ambientColumnCoefficients sigma n frame j)
      (ambientColumnCoefficients sigma n frame k) =
      if j = k then (if j = 0 then 4 * sigma ^ 2 else 2 * sigma ^ 2) else 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases hj : j = 0 <;> by_cases hk : k = 0
  · subst j
    subst k
    simp [ambientColumnCoefficients, dot]
    ring
  · simp [ambientColumnCoefficients, dot, hj, hk, Ne.symm hk]
  · simp [ambientColumnCoefficients, dot, hj, hk]
  · have hs : ∑ i, (Real.sqrt 2 * sigma * frame j i) *
        (Real.sqrt 2 * sigma * frame k i) =
        2 * sigma ^ 2 * dot (frame j) (frame k) := by
      calc
        _ = (Real.sqrt 2 ^ 2 * sigma ^ 2) * ∑ i, frame j i * frame k i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hsqrt]; rfl
    simp only [dot, ambientColumnCoefficients, ite_eq_right hj, ite_eq_right hk,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [hs, hframe]
    by_cases hjk : j = k <;> simp [hjk]

@[expose] def ambientColumn (sigma : ℝ) (n : ℕ) (frame : Fin (n + 1) → Ambient → ℝ)
    (z : EuclideanSpace ℝ (Ambient ⊕ Unit)) : Fin (n + 1) → ℝ :=
  fun j => linearForm (ambientColumnCoefficients sigma n frame j) z

theorem ambientColumn_law (sigma : ℝ) (n : ℕ)
    (frame : Fin (n + 1) → Ambient → ℝ)
    (hframe : ∀ i j, dot (frame i) (frame j) = if i = j then 1 else 0) :
    (primitiveGaussian (Ambient ⊕ Unit)).map (ambientColumn sigma n frame) =
      gaussianColumnLaw sigma n := by
  have h := orthogonalLinearForms_joint_law (ambientColumnCoefficients sigma n frame)
    (fun j k hjk => by rw [ambientColumnCoefficients_dot sigma n frame hframe, ite_eq_right hjk])
  change (primitiveGaussian (Ambient ⊕ Unit)).map
    (fun z j => linearForm (ambientColumnCoefficients sigma n frame j) z) = _
  rw [h]
  unfold gaussianColumnLaw
  congr 1
  funext j
  rw [ambientColumnCoefficients_dot sigma n frame hframe]
  simp only [ite_eq_left rfl]
  split_ifs <;> rfl

variable {Past : Type*} [MeasurableSpace Past]

theorem ambientColumn_joint_measurable (sigma : ℝ) (n : ℕ)
    (frame : Past → Fin (n + 1) → Ambient → ℝ)
    (hframe : ∀ j i, Measurable (fun a => frame a j i)) :
    Measurable (Function.uncurry (fun a => ambientColumn sigma n (frame a))) := by
  have hcoeff (j : Fin (n + 1)) (r : Ambient ⊕ Unit) :
      Measurable (fun a => ambientColumnCoefficients sigma n (frame a) j r) := by
    cases r with
    | inl i =>
      by_cases hj : j = 0 <;> simp only [ambientColumnCoefficients, hj, ite_true,
        ite_false, Sum.elim_inl]
      · exact measurable_const
      · exact (measurable_const.mul measurable_const).mul (hframe j i)
    | inr q =>
      by_cases hj : j = 0 <;> simp only [ambientColumnCoefficients, hj, ite_true,
        ite_false, Sum.elim_inr] <;> exact measurable_const
  rw [Function.uncurry_def]
  apply Measurable.of_eval
  intro j
  unfold ambientColumn linearForm
  have hc (r : Ambient ⊕ Unit) : Measurable (fun x :
      Past × EuclideanSpace ℝ (Ambient ⊕ Unit) =>
      ambientColumnCoefficients sigma n (frame x.1) j r) :=
    (hcoeff j r).comp measurable_fst
  have hz (r : Ambient ⊕ Unit) : Measurable (fun x :
      Past × EuclideanSpace ℝ (Ambient ⊕ Unit) => x.2 r) :=
    (EuclideanSpace.proj r).continuous.measurable.comp measurable_snd
  fun_prop

theorem ambientColumn_measurable (sigma : ℝ) (n : ℕ)
    (frame : Fin (n + 1) → Ambient → ℝ) :
    Measurable (ambientColumn sigma n frame) := by
  have h := ambientColumn_joint_measurable (Past := Unit) sigma n
    (fun _ => frame) (fun _ _ => measurable_const)
  exact h.comp ((show Measurable (fun _ : EuclideanSpace ℝ (Ambient ⊕ Unit) =>
    ()) from measurable_const).prodMk measurable_id)

@[expose] def AmbientNoise (Ambient : Type) : ℕ → Type
  | 0 => UpperPair (Fin 0) → ℝ
  | n + 1 => EuclideanSpace ℝ (Ambient ⊕ Unit) × AmbientNoise Ambient n

instance ambientNoiseMeasurableSpace : (n : ℕ) → MeasurableSpace (AmbientNoise Ambient n)
  | 0 => inferInstanceAs (MeasurableSpace (UpperPair (Fin 0) → ℝ))
  | n + 1 => by
    letI := ambientNoiseMeasurableSpace n
    exact inferInstanceAs
      (MeasurableSpace (EuclideanSpace ℝ (Ambient ⊕ Unit) × AmbientNoise Ambient n))

@[expose] def ambientNoiseLaw (Ambient : Type) [Fintype Ambient] (sigma : ℝ) :
    (n : ℕ) → Measure (AmbientNoise Ambient n)
  | 0 => gaussianUpperLaw sigma (Fin 0)
  | n + 1 => (primitiveGaussian (Ambient ⊕ Unit)).prod (ambientNoiseLaw Ambient sigma n)

instance ambientNoiseLaw_probability (sigma : ℝ) :
    (n : ℕ) → IsProbabilityMeasure (ambientNoiseLaw Ambient sigma n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (gaussianUpperLaw sigma (Fin 0)))
  | n + 1 => by
    let := ambientNoiseLaw_probability sigma n
    exact inferInstanceAs (IsProbabilityMeasure
      ((primitiveGaussian (Ambient ⊕ Unit)).prod (ambientNoiseLaw Ambient sigma n)))

@[expose] def ambientCausalUpper (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (n : ℕ) → Past → AmbientNoise Ambient n → (UpperPair (Fin n) → ℝ)
  | 0, _, z => z
  | n + 1, a, z => matrixUpper (basisAssembly (completionFrame 0 (direction n a))
      (joinUpper n (ambientColumn sigma n (frame n a) z.1,
        ambientCausalUpper sigma direction frame update n (update n a z.1) z.2)))

theorem ambientCausalUpper_measurable (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hframe : ∀ n j i, Measurable (fun a => frame n a j i))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) : Measurable (Function.uncurry
      (ambientCausalUpper sigma direction frame update n)) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    let B : Past → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun a => completionFrame 0 (direction n a)
    have hB := completionFrame_measurable (0 : Fin (n + 1))
      (direction n) (hdirection n)
    have hfresh : Measurable (fun x : Past × AmbientNoise Ambient (n + 1) => x.2.1) :=
      measurable_fst.comp measurable_snd
    have hz : Measurable (fun x : Past × AmbientNoise Ambient (n + 1) => x.2.2) :=
      measurable_snd.comp measurable_snd
    have hpast : Measurable (fun x : Past × AmbientNoise Ambient (n + 1) =>
        update n x.1 x.2.1) := (hupdate n).comp (measurable_fst.prodMk hfresh)
    have hsub : Measurable (fun x : Past × AmbientNoise Ambient (n + 1) =>
        ambientCausalUpper sigma direction frame update n (update n x.1 x.2.1) x.2.2) :=
      ih.comp (hpast.prodMk hz)
    have hc := (ambientColumn_joint_measurable sigma n (frame n) (hframe n)).comp
      (measurable_fst.prodMk hfresh)
    have hjoin := (joinUpper_measurable n).comp (hc.prodMk hsub)
    have hasm := (adaptiveAssembly_measurable B hB).comp
      (measurable_fst.prodMk hjoin)
    exact (matrixUpper_measurable (n + 1)).comp hasm

theorem ambientCausalUpper_law (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hframe : ∀ n j i, Measurable (fun a => frame n a j i))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ)
    (horth : ∀ m, m < n → ∀ a i j,
      dot (frame m a i) (frame m a j) = if i = j then 1 else 0)
    (a : Past) :
    (ambientNoiseLaw Ambient sigma n).map
      (ambientCausalUpper sigma direction frame update n a) =
      gaussianUpperLaw sigma (Fin n) := by
  induction n generalizing a with
  | zero => exact Measure.map_id
  | succ n ih =>
    have hprefix : ∀ m, m < n → ∀ a i j,
        dot (frame m a i) (frame m a j) = if i = j then 1 else 0 :=
      fun m hm => horth m (lt_trans hm (Nat.lt_succ_self n))
    let B := completionFrame (0 : Fin (n + 1)) (direction n a)
    let C := ambientColumn sigma n (frame n a)
    let F : EuclideanSpace ℝ (Ambient ⊕ Unit) → AmbientNoise Ambient n →
        UpperPair (Fin n) → ℝ := fun z r =>
      ambientCausalUpper sigma direction frame update n (update n a z) r
    have hpast : Measurable (fun z => update n a z) :=
      (hupdate n).comp (measurable_const.prodMk measurable_id)
    have hF : Measurable (Function.uncurry F) :=
      (ambientCausalUpper_measurable sigma direction frame update
        hdirection hframe hupdate n).comp
        ((hpast.comp measurable_fst).prodMk measurable_snd)
    have hjoint := adaptiveStep_joint_law
      (μ := primitiveGaussian (Ambient ⊕ Unit)) (ν := ambientNoiseLaw Ambient sigma n)
      hF (fun z => ih hprefix (update n a z))
    have hC : Measurable C := ambientColumn_measurable sigma n (frame n a)
    have hproject :
        ((primitiveGaussian (Ambient ⊕ Unit)).prod (gaussianUpperLaw sigma (Fin n))).map
          (Prod.map C id) =
          (gaussianColumnLaw sigma n).prod (gaussianUpperLaw sigma (Fin n)) := by
      rw [← Measure.map_prod_map _ _ hC measurable_id, Measure.map_id]
      rw [ambientColumn_law sigma n (frame n a) (horth n (Nat.lt_succ_self n) a)]
    let H : (Fin (n + 1) → ℝ) × (UpperPair (Fin n) → ℝ) →
        UpperPair (Fin (n + 1)) → ℝ :=
      fun x => matrixUpper (basisAssembly B (joinUpper n x))
    have hH : Measurable H := (matrixUpper_measurable (n + 1)).comp
      ((basisAssembly_measurable B).comp (joinUpper_measurable n))
    have hg : Measurable (fun x : EuclideanSpace ℝ (Ambient ⊕ Unit) ×
        AmbientNoise Ambient n => (x.1, F x.1 x.2)) := measurable_fst.prodMk hF
    change ((primitiveGaussian (Ambient ⊕ Unit)).prod (ambientNoiseLaw Ambient sigma n)).map
      (fun x => H (C x.1, F x.1 x.2)) = _
    calc
      _ = (((primitiveGaussian (Ambient ⊕ Unit)).prod (ambientNoiseLaw Ambient sigma n)).map
          (fun x => (x.1, F x.1 x.2))).map (H ∘ Prod.map C id) := by
        rw [Measure.map_map (hH.comp (hC.prodMap measurable_id)) hg]
        rfl
      _ = ((primitiveGaussian (Ambient ⊕ Unit)).prod
          (gaussianUpperLaw sigma (Fin n))).map (H ∘ Prod.map C id) := by rw [hjoint]
      _ = (((primitiveGaussian (Ambient ⊕ Unit)).prod
          (gaussianUpperLaw sigma (Fin n))).map (Prod.map C id)).map H :=
        (Measure.map_map hH (hC.prodMap measurable_id)).symm
      _ = ((gaussianColumnLaw sigma n).prod (gaussianUpperLaw sigma (Fin n))).map H := by
        rw [hproject]
      _ = (gaussianUpperLaw sigma (Fin (n + 1))).map
          (fun q => matrixUpper (basisAssembly B q)) := by
        rw [← joinUpper_law sigma n]
        exact (Measure.map_map
          ((matrixUpper_measurable (n + 1)).comp (basisAssembly_measurable B))
          (joinUpper_measurable n)).symm
      _ = _ := assemblyUpper_law sigma (n + 1) B
        (completionFrame_orthogonal 0 (direction n a))

@[expose] def ambientCausalGOE (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (n : ℕ) (a : Past) (z : AmbientNoise Ambient n) : Matrix (Fin n) (Fin n) ℝ :=
  fillSymmetricMatrix (ambientCausalUpper sigma direction frame update n a z)

theorem ambientCausalGOE_measurable (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hframe : ∀ n j i, Measurable (fun a => frame n a j i))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ) : Measurable (Function.uncurry
      (ambientCausalGOE sigma direction frame update n)) :=
  fillSymmetricMatrix_measurable.comp
    (ambientCausalUpper_measurable sigma direction frame update hdirection hframe hupdate n)

theorem ambientCausalGOE_law (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hframe : ∀ n j i, Measurable (fun a => frame n a j i))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ)
    (horth : ∀ m, m < n → ∀ a i j,
      dot (frame m a i) (frame m a j) = if i = j then 1 else 0)
    (a : Past) :
    (ambientNoiseLaw Ambient sigma n).map
      (ambientCausalGOE sigma direction frame update n a) =
      (primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma) := by
  have hf : Measurable (ambientCausalUpper sigma direction frame update n a) :=
    (ambientCausalUpper_measurable sigma direction frame update
      hdirection hframe hupdate n).comp (measurable_const.prodMk measurable_id)
  calc
    _ = ((ambientNoiseLaw Ambient sigma n).map
        (ambientCausalUpper sigma direction frame update n a)).map fillSymmetricMatrix := by
      rw [Measure.map_map fillSymmetricMatrix_measurable hf]
      rfl
    _ = (gaussianUpperLaw sigma (Fin n)).map fillSymmetricMatrix := by
      rw [ambientCausalUpper_law sigma direction frame update hdirection hframe hupdate n horth a]
    _ = _ := filledGaussian_law sigma

theorem ambientCausalGOE_joint_law
    (μ : Measure Past) [SFinite μ] (sigma : ℝ)
    (direction : (n : ℕ) → Past → Fin (n + 1) → ℝ)
    (frame : (n : ℕ) → Past → Fin (n + 1) → Ambient → ℝ)
    (update : (n : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hdirection : ∀ n j, Measurable (fun a => direction n a j))
    (hframe : ∀ n j i, Measurable (fun a => frame n a j i))
    (hupdate : ∀ n, Measurable (Function.uncurry (update n)))
    (n : ℕ)
    (horth : ∀ m, m < n → ∀ a i j,
      dot (frame m a i) (frame m a j) = if i = j then 1 else 0) :
    (μ.prod (ambientNoiseLaw Ambient sigma n)).map
      (fun x => (x.1, ambientCausalGOE sigma direction frame update n x.1 x.2)) =
      μ.prod ((primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)) :=
  adaptiveStep_joint_law
    (ambientCausalGOE_measurable sigma direction frame update hdirection hframe hupdate n)
    (ambientCausalGOE_law sigma direction frame update hdirection hframe hupdate n horth)

variable {Index : Type*} [Fintype Index] [LinearOrder Index]

@[expose] def compressedEntry (sigma : ℝ) (basis : Index → Ambient → ℝ) (p : UpperPair Index)
    (z : EuclideanSpace ℝ (Ambient × Ambient)) : ℝ :=
  goeBilinear sigma (basis p.1.1) (basis p.1.2) z

theorem compressedEntry_covariance (sigma : ℝ) (basis : Index → Ambient → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0)
    (p q : UpperPair Index) :
    cov[compressedEntry sigma basis p, compressedEntry sigma basis q;
      primitiveGaussian (Ambient × Ambient)] =
      if p = q then (if p.1.1 = p.1.2 then 4 * sigma ^ 2 else 2 * sigma ^ 2)
      else 0 := by
  unfold compressedEntry
  rw [goeBilinear_covariance]
  simp_rw [horth]
  by_cases hpq : p = q
  · subst q
    by_cases hdiag : p.1.1 = p.1.2 <;> simp [hdiag] <;> ring
  · have hdirect : ¬(p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := by
      rintro ⟨h1,h2⟩
      apply hpq
      exact Subtype.ext (Prod.ext h1 h2)
    have hreverse : ¬(p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := by
      rintro ⟨h1,h2⟩
      have hdiag : p.1.1 = p.1.2 := le_antisymm p.property
        (by simpa only [h1,h2] using q.property)
      apply hpq
      apply Subtype.ext
      apply Prod.ext
      · exact hdiag.trans h2
      · exact hdiag.symm.trans h1
    by_cases h11 : p.1.1 = q.1.1 <;> by_cases h22 : p.1.2 = q.1.2 <;>
      by_cases h12 : p.1.1 = q.1.2 <;> by_cases h21 : p.1.2 = q.1.1 <;>
      simp_all

theorem compressedEntries_independent (sigma : ℝ) (basis : Index → Ambient → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    iIndepFun (compressedEntry sigma basis) (primitiveGaussian (Ambient × Ambient)) := by
  have hjoint := goeBilinear_family_gaussian sigma
    (fun p : UpperPair Index => basis p.1.1) (fun p => basis p.1.2)
  apply hjoint.iIndepFun_of_covariance_eq_zero
  intro p q hpq
  change cov[compressedEntry sigma basis p, compressedEntry sigma basis q;
    primitiveGaussian (Ambient × Ambient)] = 0
  rw [compressedEntry_covariance sigma basis horth p q, if_neg hpq]

theorem compressedEntry_law (sigma : ℝ) (basis : Index → Ambient → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0)
    (p : UpperPair Index) :
    (primitiveGaussian (Ambient × Ambient)).map (compressedEntry sigma basis p) =
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * sigma ^ 2).toNNReal
        else (2 * sigma ^ 2).toNNReal) := by
  have hgauss := goeBilinear_gaussian sigma (basis p.1.1) (basis p.1.2)
  change HasGaussianLaw (compressedEntry sigma basis p) (primitiveGaussian (Ambient × Ambient)) at hgauss
  rw [hgauss.map_eq_gaussianReal]
  have hmean : (∫ z, compressedEntry sigma basis p z ∂primitiveGaussian (Ambient × Ambient)) = 0 :=
    goeBilinear_mean sigma _ _
  have hvar : Var[compressedEntry sigma basis p; primitiveGaussian (Ambient × Ambient)] =
      if p.1.1 = p.1.2 then 4 * sigma ^ 2 else 2 * sigma ^ 2 := by
    rw [← covariance_self hgauss.aemeasurable,
      compressedEntry_covariance sigma basis horth p p]
    simp
  change gaussianReal (∫ z, compressedEntry sigma basis p z ∂primitiveGaussian (Ambient × Ambient))
    Var[compressedEntry sigma basis p; primitiveGaussian (Ambient × Ambient)].toNNReal = _
  rw [hmean,hvar]
  split_ifs <;> rfl

set_option maxHeartbeats 800000 in
theorem compressedEntries_joint_law (sigma : ℝ) (basis : Index → Ambient → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    (primitiveGaussian (Ambient × Ambient)).map (fun z p => compressedEntry sigma basis p z) =
      Measure.pi (fun p : UpperPair Index => gaussianReal 0
        (if p.1.1 = p.1.2 then (4 * sigma ^ 2).toNNReal
          else (2 * sigma ^ 2).toNNReal)) := by
  have hmeas (p : UpperPair Index) : AEMeasurable (compressedEntry sigma basis p)
      (primitiveGaussian (Ambient × Ambient)) := by
    exact (goeBilinear_gaussian sigma (basis p.1.1) (basis p.1.2)).aemeasurable
  have hmap := iIndepFun.map_fun_eq_pi_map
    (μ := primitiveGaussian (Ambient × Ambient)) (f := compressedEntry sigma basis)
      hmeas (compressedEntries_independent sigma basis horth)
  calc
    _ = Measure.pi (fun p => (primitiveGaussian (Ambient × Ambient)).map
          (compressedEntry sigma basis p)) := hmap
    _ = _ := ?_
  congr 1
  funext p
  exact compressedEntry_law sigma basis horth p

theorem compressedEntries_joint_measurable (sigma : ℝ)
    (basis : Past → Index → Ambient → ℝ)
    (hbasis : ∀ j i, Measurable (fun a => basis a j i)) :
    Measurable (fun x : Past × EuclideanSpace ℝ (Ambient × Ambient) =>
      fun p : UpperPair Index => compressedEntry sigma (basis x.1) p x.2) := by
  apply Measurable.of_eval
  intro p
  unfold compressedEntry goeBilinear linearForm
  have hb (j : Index) (i : Ambient) : Measurable (fun x :
      Past × EuclideanSpace ℝ (Ambient × Ambient) => basis x.1 j i) :=
    (hbasis j i).comp measurable_fst
  have hz (r : Ambient × Ambient) : Measurable (fun x :
      Past × EuclideanSpace ℝ (Ambient × Ambient) => x.2 r) :=
    (EuclideanSpace.proj r).continuous.measurable.comp measurable_snd
  fun_prop

@[expose] def StoppedNoise (Ambient : Type) : ℕ → Type
  | 0 => EuclideanSpace ℝ (Ambient × Ambient)
  | k + 1 => EuclideanSpace ℝ (Ambient ⊕ Unit) × StoppedNoise Ambient k

instance stoppedNoiseMeasurableSpace : (k : ℕ) → MeasurableSpace (StoppedNoise Ambient k)
  | 0 => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Ambient × Ambient)))
  | k + 1 => by
    letI := stoppedNoiseMeasurableSpace k
    exact inferInstanceAs
      (MeasurableSpace (EuclideanSpace ℝ (Ambient ⊕ Unit) × StoppedNoise Ambient k))

@[expose] def stoppedNoiseLaw (Ambient : Type) [Fintype Ambient] :
    (k : ℕ) → Measure (StoppedNoise Ambient k)
  | 0 => primitiveGaussian (Ambient × Ambient)
  | k + 1 => (primitiveGaussian (Ambient ⊕ Unit)).prod (stoppedNoiseLaw Ambient k)

instance stoppedNoiseLaw_probability :
    (k : ℕ) → IsProbabilityMeasure (stoppedNoiseLaw Ambient k)
  | 0 => inferInstanceAs (IsProbabilityMeasure (primitiveGaussian (Ambient × Ambient)))
  | k + 1 => by
    let := stoppedNoiseLaw_probability k
    exact inferInstanceAs (IsProbabilityMeasure
      ((primitiveGaussian (Ambient ⊕ Unit)).prod (stoppedNoiseLaw Ambient k)))

@[expose] def stoppedCausalUpper (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → (UpperPair (Fin (r + K)) → ℝ)
  | 0, a, z => fun p => compressedEntry sigma (residualFrame a) p z
  | K + 1, a, z => matrixUpper (basisAssembly (completionFrame 0 (direction K a))
      (joinUpper (r + K) (ambientColumn sigma (r + K) (frame K a) z.1,
        stoppedCausalUpper r sigma residualFrame direction frame update K (update K a z.1) z.2)))

theorem stoppedCausalUpper_measurable (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hresidual : ∀ j i, Measurable (fun a => residualFrame a j i))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) : Measurable (Function.uncurry
      (stoppedCausalUpper r sigma residualFrame direction frame update K)) := by
  induction K with
  | zero => exact compressedEntries_joint_measurable sigma residualFrame hresidual
  | succ K ih =>
    let B : Past → Matrix (Fin (r + K + 1)) (Fin (r + K + 1)) ℝ :=
      fun a => completionFrame 0 (direction K a)
    have hB := completionFrame_measurable (0 : Fin (r + K + 1))
      (direction K) (hdirection K)
    have hfresh : Measurable (fun x : Past × StoppedNoise Ambient (K + 1) => x.2.1) :=
      measurable_fst.comp measurable_snd
    have hz : Measurable (fun x : Past × StoppedNoise Ambient (K + 1) => x.2.2) :=
      measurable_snd.comp measurable_snd
    have hpast : Measurable (fun x : Past × StoppedNoise Ambient (K + 1) =>
        update K x.1 x.2.1) := (hupdate K).comp (measurable_fst.prodMk hfresh)
    have hsub : Measurable (fun x : Past × StoppedNoise Ambient (K + 1) =>
        stoppedCausalUpper r sigma residualFrame direction frame update K
          (update K x.1 x.2.1) x.2.2) := ih.comp (hpast.prodMk hz)
    have hc := (ambientColumn_joint_measurable sigma (r + K) (frame K) (hframe K)).comp
      (measurable_fst.prodMk hfresh)
    have hjoin := (joinUpper_measurable (r + K)).comp (hc.prodMk hsub)
    have hasm := (adaptiveAssembly_measurable B hB).comp
      (measurable_fst.prodMk hjoin)
    exact (matrixUpper_measurable (r + K + 1)).comp hasm

theorem stoppedCausalUpper_law (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hresidual : ∀ j i, Measurable (fun a => residualFrame a j i))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hresorth : ∀ a i j,
      dot (residualFrame a i) (residualFrame a j) = if i = j then 1 else 0)
    (K : ℕ)
    (horth : ∀ k, k < K → ∀ a i j,
      dot (frame k a i) (frame k a j) = if i = j then 1 else 0)
    (a : Past) :
    (stoppedNoiseLaw Ambient K).map
      (stoppedCausalUpper r sigma residualFrame direction frame update K a) =
      gaussianUpperLaw sigma (Fin (r + K)) := by
  induction K generalizing a with
  | zero => exact compressedEntries_joint_law sigma (residualFrame a) (hresorth a)
  | succ K ih =>
    have hprefix : ∀ m, m < K → ∀ a i j,
        dot (frame m a i) (frame m a j) = if i = j then 1 else 0 :=
      fun m hm => horth m (lt_trans hm (Nat.lt_succ_self K))
    let B := completionFrame (0 : Fin (r + K + 1)) (direction K a)
    let C := ambientColumn sigma (r + K) (frame K a)
    let F : EuclideanSpace ℝ (Ambient ⊕ Unit) → StoppedNoise Ambient K →
        UpperPair (Fin (r + K)) → ℝ := fun z noise =>
      stoppedCausalUpper r sigma residualFrame direction frame update K (update K a z) noise
    have hpast : Measurable (fun z => update K a z) :=
      (hupdate K).comp (measurable_const.prodMk measurable_id)
    have hF : Measurable (Function.uncurry F) :=
      (stoppedCausalUpper_measurable r sigma residualFrame direction frame update
        hresidual hdirection hframe hupdate K).comp
        ((hpast.comp measurable_fst).prodMk measurable_snd)
    have hjoint := adaptiveStep_joint_law
      (μ := primitiveGaussian (Ambient ⊕ Unit)) (ν := stoppedNoiseLaw Ambient K)
      hF (fun z => ih hprefix (update K a z))
    have hC : Measurable C := ambientColumn_measurable sigma (r + K) (frame K a)
    have hproject :
        ((primitiveGaussian (Ambient ⊕ Unit)).prod (gaussianUpperLaw sigma (Fin (r + K)))).map
          (Prod.map C id) =
          (gaussianColumnLaw sigma (r + K)).prod (gaussianUpperLaw sigma (Fin (r + K))) := by
      rw [← Measure.map_prod_map _ _ hC measurable_id, Measure.map_id]
      rw [ambientColumn_law sigma (r + K) (frame K a) (horth K (Nat.lt_succ_self K) a)]
    let H : (Fin (r + K + 1) → ℝ) × (UpperPair (Fin (r + K)) → ℝ) →
        UpperPair (Fin (r + K + 1)) → ℝ :=
      fun x => matrixUpper (basisAssembly B (joinUpper (r + K) x))
    have hH : Measurable H := (matrixUpper_measurable (r + K + 1)).comp
      ((basisAssembly_measurable B).comp (joinUpper_measurable (r + K)))
    have hg : Measurable (fun x : EuclideanSpace ℝ (Ambient ⊕ Unit) ×
        StoppedNoise Ambient K => (x.1, F x.1 x.2)) := measurable_fst.prodMk hF
    change ((primitiveGaussian (Ambient ⊕ Unit)).prod (stoppedNoiseLaw Ambient K)).map
      (fun x => H (C x.1, F x.1 x.2)) = _
    calc
      _ = (((primitiveGaussian (Ambient ⊕ Unit)).prod (stoppedNoiseLaw Ambient K)).map
          (fun x => (x.1, F x.1 x.2))).map (H ∘ Prod.map C id) := by
        rw [Measure.map_map (hH.comp (hC.prodMap measurable_id)) hg]
        rfl
      _ = ((primitiveGaussian (Ambient ⊕ Unit)).prod
          (gaussianUpperLaw sigma (Fin (r + K)))).map (H ∘ Prod.map C id) := by rw [hjoint]
      _ = (((primitiveGaussian (Ambient ⊕ Unit)).prod
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
        (completionFrame_orthogonal 0 (direction K a))

@[expose] def stoppedCausalGOE (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) :
    Matrix (Fin (r + K)) (Fin (r + K)) ℝ :=
  fillSymmetricMatrix (stoppedCausalUpper r sigma residualFrame direction frame update K a z)

theorem stoppedCausalGOE_measurable (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hresidual : ∀ j i, Measurable (fun a => residualFrame a j i))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) : Measurable (Function.uncurry
      (stoppedCausalGOE r sigma residualFrame direction frame update K)) :=
  fillSymmetricMatrix_measurable.comp
    (stoppedCausalUpper_measurable r sigma residualFrame direction frame update
      hresidual hdirection hframe hupdate K)

theorem stoppedCausalGOE_law (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hresidual : ∀ j i, Measurable (fun a => residualFrame a j i))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hresorth : ∀ a i j,
      dot (residualFrame a i) (residualFrame a j) = if i = j then 1 else 0)
    (K : ℕ)
    (horth : ∀ k, k < K → ∀ a i j,
      dot (frame k a i) (frame k a j) = if i = j then 1 else 0)
    (a : Past) :
    (stoppedNoiseLaw Ambient K).map
      (stoppedCausalGOE r sigma residualFrame direction frame update K a) =
      (primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma) := by
  have hf : Measurable (stoppedCausalUpper r sigma residualFrame direction frame update K a) :=
    (stoppedCausalUpper_measurable r sigma residualFrame direction frame update
      hresidual hdirection hframe hupdate K).comp (measurable_const.prodMk measurable_id)
  calc
    _ = ((stoppedNoiseLaw Ambient K).map
        (stoppedCausalUpper r sigma residualFrame direction frame update K a)).map
          fillSymmetricMatrix := by
      rw [Measure.map_map fillSymmetricMatrix_measurable hf]
      rfl
    _ = (gaussianUpperLaw sigma (Fin (r + K))).map fillSymmetricMatrix := by
      rw [stoppedCausalUpper_law r sigma residualFrame direction frame update
        hresidual hdirection hframe hupdate hresorth K horth a]
    _ = _ := filledGaussian_law sigma

theorem stoppedCausalGOE_joint_law
    (μ : Measure Past) [SFinite μ] (r : ℕ) (sigma : ℝ)
    (residualFrame : Past → Fin r → Ambient → ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Fin (r + k + 1) → Ambient → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hresidual : ∀ j i, Measurable (fun a => residualFrame a j i))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hresorth : ∀ a i j,
      dot (residualFrame a i) (residualFrame a j) = if i = j then 1 else 0)
    (K : ℕ)
    (horth : ∀ k, k < K → ∀ a i j,
      dot (frame k a i) (frame k a j) = if i = j then 1 else 0) :
    (μ.prod (stoppedNoiseLaw Ambient K)).map
      (fun x => (x.1, stoppedCausalGOE r sigma residualFrame direction frame update K x.1 x.2)) =
      μ.prod ((primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma)) :=
  adaptiveStep_joint_law
    (stoppedCausalGOE_measurable r sigma residualFrame direction frame update
      hresidual hdirection hframe hupdate K)
    (stoppedCausalGOE_law r sigma residualFrame direction frame update
      hresidual hdirection hframe hupdate hresorth K horth)

end SKConstants.GaussianProposal
