module

public import SKConstants.GaussianProposalScalarCallbacks
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal
set_option backward.isDefEq.respectTransparency false

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
lemma primitiveGaussian_ofLp_map :
    (primitiveGaussian I).map (WithLp.ofLp : EuclideanSpace ℝ I → I → ℝ) =
      Measure.pi (fun _ : I => gaussianReal 0 1) := by
  rw [primitiveGaussian,← map_pi_eq_stdGaussian,
    Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)]
  exact Measure.map_id

@[expose] def primitiveGaussianPairJoin (p : EuclideanSpace ℝ I × EuclideanSpace ℝ J) :
    EuclideanSpace ℝ (I ⊕ J) := WithLp.toLp 2 (Sum.elim p.1.ofLp p.2.ofLp)

omit [DecidableEq I] [DecidableEq J] in
lemma primitiveGaussianPairJoin_hasLaw :
    HasLaw (primitiveGaussianPairJoin (I := I) (J := J)) (primitiveGaussian (I ⊕ J))
      ((primitiveGaussian I).prod (primitiveGaussian J)) := by
  have hp : HasLaw (Prod.map
      (WithLp.ofLp : EuclideanSpace ℝ I → I → ℝ)
      (WithLp.ofLp : EuclideanSpace ℝ J → J → ℝ))
      ((Measure.pi (fun _ : I => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : J => gaussianReal 0 1)))
      ((primitiveGaussian I).prod (primitiveGaussian J)) := by
    refine ⟨((WithLp.measurable_ofLp 2 _).prodMap (WithLp.measurable_ofLp 2 _)).aemeasurable,?_⟩
    rw [← Measure.map_prod_map _ _ (WithLp.measurable_ofLp 2 _) (WithLp.measurable_ofLp 2 _),
      primitiveGaussian_ofLp_map,primitiveGaussian_ofLp_map]
  have hs := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : I ⊕ J => gaussianReal 0 1)).hasLaw
  have ht : HasLaw (WithLp.toLp 2 : ((I ⊕ J) → ℝ) → EuclideanSpace ℝ (I ⊕ J))
      (primitiveGaussian (I ⊕ J)) (Measure.pi (fun _ : I ⊕ J => gaussianReal 0 1)) :=
    ⟨(WithLp.measurable_toLp 2 _).aemeasurable,map_pi_eq_stdGaussian⟩
  exact ht.comp (hs.comp hp)

variable {m n : ℕ}

@[expose] def paperUsedProjection (F : Matrix (Fin (m+1)) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1-remainingProjection F

lemma remainingProjection_transpose (F : Matrix (Fin (m+1)) (Fin n) ℝ) :
    (remainingProjection F)ᵀ=remainingProjection F := by
  simp only [remainingProjection,Matrix.transpose_mul,Matrix.transpose_transpose]

lemma paperUsedProjection_transpose (F : Matrix (Fin (m+1)) (Fin n) ℝ) :
    (paperUsedProjection F)ᵀ=paperUsedProjection F := by
  rw [paperUsedProjection,Matrix.transpose_sub,Matrix.transpose_one,remainingProjection_transpose]

lemma paperUsedProjection_symm (F : Matrix (Fin (m+1)) (Fin n) ℝ) (i j : Fin n) :
    paperUsedProjection F i j=paperUsedProjection F j i :=
  congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j i) (paperUsedProjection_transpose F)

lemma paperUsedProjection_idempotent (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) :
    paperUsedProjection F*paperUsedProjection F=paperUsedProjection F := by
  have hP := remainingProjection_idempotent F hF
  unfold paperUsedProjection
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,Matrix.one_mul,Matrix.one_mul,
    Matrix.mul_one,hP]
  abel

lemma paperCompletion_row_covariance (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) (i k : Fin n) :
    dot (paperUsedProjection F i) (paperUsedProjection F k)+
      dot (remainingProjection F i) (remainingProjection F k)=if i=k then 1 else 0 := by
  have hM : paperUsedProjection F*(paperUsedProjection F)ᵀ+
      remainingProjection F*(remainingProjection F)ᵀ=1 := by
    rw [paperUsedProjection_transpose,remainingProjection_transpose,
      paperUsedProjection_idempotent F hF,remainingProjection_idempotent F hF]
    unfold paperUsedProjection
    abel
  simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,dot]
    using congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i k) hM

lemma tailRows_mul_paperUsedProjection (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) :
    tailRows F*paperUsedProjection F=0 := by
  unfold paperUsedProjection remainingProjection
  rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,
    frame_mul_transpose (tailRows F) (tailRows_orthogonal F hF),Matrix.one_mul,sub_self]

lemma paperCompletion_offColumn_covariance (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) (j : Fin m) (i : Fin n) :
    dot (F j.succ) (paperUsedProjection F i)=0 := by
  have h := congrArg (fun A : Matrix (Fin m) (Fin n) ℝ => A j i)
    (tailRows_mul_paperUsedProjection F hF)
  simp only [Matrix.mul_apply,Matrix.zero_apply,tailRows] at h
  unfold dot
  simp_rw [paperUsedProjection_symm F i]
  exact h

@[expose] def paperIndependentCompletion (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (paperUsedProjection F *ᵥ (fun i => p.1 (.inl i))+
    remainingProjection F *ᵥ p.2.ofLp)

@[expose] def paperColumnCompletionCoefficients (σ : ℝ) (F : Matrix (Fin (m+1)) (Fin n) ℝ) :
    (Fin (m+1) ⊕ Fin n) → ((Fin n ⊕ Unit) ⊕ Fin n) → ℝ
  | .inl j => Sum.elim (ambientColumnCoefficients σ m F j) (fun _ => 0)
  | .inr i => Sum.elim (Sum.elim (paperUsedProjection F i) (fun _ => 0))
      (remainingProjection F i)

lemma paperColumnCompletionCoefficients_cross (σ : ℝ) (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) (j : Fin (m+1)) (i : Fin n) :
    dot (paperColumnCompletionCoefficients σ F (.inl j))
      (paperColumnCompletionCoefficients σ F (.inr i))=0 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [paperColumnCompletionCoefficients,ambientColumnCoefficients,dot,Fintype.sum_sum_type]
  · simp only [paperColumnCompletionCoefficients,ambientColumnCoefficients,Fin.succ_ne_zero,
      ite_false,Sum.elim_inl,Sum.elim_inr,dot,Fintype.sum_sum_type,mul_zero,
      zero_mul,Finset.sum_const_zero,add_zero,mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have he := paperCompletion_offColumn_covariance F hF j i
    unfold dot at he
    rw [he,mul_zero,mul_zero]

lemma paperColumnCompletionCoefficients_dot (σ : ℝ) (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0)
    (u v : Fin (m+1) ⊕ Fin n) :
    dot (paperColumnCompletionCoefficients σ F u) (paperColumnCompletionCoefficients σ F v)=
      if u=v then Sum.elim (fun j => if j=0 then 4*σ^2 else 2*σ^2) (fun _ => 1) u else 0 := by
  cases u with
  | inl j =>
    cases v with
    | inl k =>
      simpa only [paperColumnCompletionCoefficients,dot,Fintype.sum_sum_type,Sum.elim_inl,
        Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero,Sum.inl.injEq] using
        ambientColumnCoefficients_dot σ m F hF j k
    | inr i =>
      simpa using paperColumnCompletionCoefficients_cross σ F hF j i
  | inr i =>
    cases v with
    | inl j =>
      have hc := paperColumnCompletionCoefficients_cross σ F hF j i
      have he : dot (paperColumnCompletionCoefficients σ F (.inr i))
          (paperColumnCompletionCoefficients σ F (.inl j)) =
          dot (paperColumnCompletionCoefficients σ F (.inl j))
            (paperColumnCompletionCoefficients σ F (.inr i)) := by
        unfold dot
        simp_rw [mul_comm]
      rw [he]
      simpa using hc
    | inr k =>
      simpa only [paperColumnCompletionCoefficients,dot,Fintype.sum_sum_type,Sum.elim_inl,
        Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero,Sum.inr.injEq] using
        paperCompletion_row_covariance F hF i k

lemma paperColumnCompletion_linearForms (σ : ℝ) (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n)) :
    (fun u => linearForm (paperColumnCompletionCoefficients σ F u)
      (primitiveGaussianPairJoin p)) =
    Sum.elim (ambientColumn σ m F p.1) (paperIndependentCompletion F p).ofLp := by
  funext u
  cases u with
  | inl j =>
    simp [linearForm,paperColumnCompletionCoefficients,primitiveGaussianPairJoin,
      Fintype.sum_sum_type,ambientColumn]
  | inr i =>
    simp [linearForm,paperColumnCompletionCoefficients,primitiveGaussianPairJoin,
      Fintype.sum_sum_type,paperIndependentCompletion,Matrix.mulVec, dotProduct]

lemma paperIndependentCompletion_measurable (F : Matrix (Fin (m+1)) (Fin n) ℝ) :
    Measurable (paperIndependentCompletion F) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  change Measurable (fun p : EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n) =>
    (paperUsedProjection F *ᵥ (fun i => p.1 (.inl i)) + remainingProjection F *ᵥ p.2.ofLp) i)
  simp only [Pi.add_apply,Matrix.mulVec,dotProduct]
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun j _ => measurable_const.mul
      ((EuclideanSpace.proj (Sum.inl j : Fin n ⊕ Unit)).continuous.measurable.comp measurable_fst))
  · exact Finset.measurable_sum _ (fun j _ => measurable_const.mul
      ((EuclideanSpace.proj j).continuous.measurable.comp measurable_snd))

theorem paperColumnIndependentCompletion_joint_law (σ : ℝ)
    (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) :
    ((primitiveGaussian (Fin n ⊕ Unit)).prod (primitiveGaussian (Fin n))).map
      (fun p => (ambientColumn σ m F p.1,paperIndependentCompletion F p)) =
      (gaussianColumnLaw σ m).prod (primitiveGaussian (Fin n)) := by
  let ν : (Fin (m+1) ⊕ Fin n) → Measure ℝ := Sum.elim
    (fun j => gaussianReal 0 (if j=0 then 4*σ^2 else 2*σ^2).toNNReal)
    (fun _ => gaussianReal 0 1)
  let : ∀ u, IsProbabilityMeasure (ν u) := fun u => by
    cases u <;> dsimp [ν] <;> infer_instance
  have hlin : HasLaw (fun z u => linearForm (paperColumnCompletionCoefficients σ F u) z)
      (Measure.pi ν) (primitiveGaussian ((Fin n ⊕ Unit) ⊕ Fin n)) := by
    have hm : Measurable (fun z u => linearForm (paperColumnCompletionCoefficients σ F u) z) := by
      apply Measurable.of_eval
      intro u
      convert (linearFormCLM (paperColumnCompletionCoefficients σ F u)).continuous.measurable using 1
      funext z
      exact (linearFormCLM_apply _ _).symm
    refine ⟨hm.aemeasurable,?_⟩
    rw [orthogonalLinearForms_joint_law _ (fun u v huv => by
      rw [paperColumnCompletionCoefficients_dot σ F hF,ite_eq_right huv])]
    congr 1
    funext u
    rw [paperColumnCompletionCoefficients_dot σ F hF,ite_eq_left rfl]
    cases u <;> simp [ν]
  have hjoin := hlin.comp (primitiveGaussianPairJoin_hasLaw
    (I := Fin n ⊕ Unit) (J := Fin n))
  have hsplit := (measurePreserving_sumPiEquivProdPi ν).hasLaw.comp hjoin
  have ht : HasLaw (Prod.map id (WithLp.toLp 2))
      ((gaussianColumnLaw σ m).prod (primitiveGaussian (Fin n)))
      ((Measure.pi (fun j : Fin (m+1) => ν (.inl j))).prod
        (Measure.pi (fun i : Fin n => ν (.inr i)))) := by
    refine ⟨(measurable_id.prodMap (WithLp.measurable_toLp 2 _)).aemeasurable,?_⟩
    rw [← Measure.map_prod_map _ _ measurable_id (WithLp.measurable_toLp 2 _),Measure.map_id]
    have hl : Measure.pi (fun j : Fin (m+1) => ν (.inl j)) = gaussianColumnLaw σ m := by
      congr 1
      funext j
      simp only [ν,Sum.elim_inl]
      split_ifs <;> rfl
    rw [hl]
    change (gaussianColumnLaw σ m).prod
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)) = _
    rw [map_pi_eq_stdGaussian]
    rfl
  have hout := ht.comp hsplit
  have he : (Prod.map id (WithLp.toLp 2)) ∘
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (m+1) ⊕ Fin n => ℝ)) ∘
      ((fun z u => linearForm (paperColumnCompletionCoefficients σ F u) z) ∘
        primitiveGaussianPairJoin) =
      fun p => (ambientColumn σ m F p.1,paperIndependentCompletion F p) := by
    funext p
    rw [Function.comp_apply,Function.comp_apply,Function.comp_apply,
      paperColumnCompletion_linearForms]
    rfl
  rw [he] at hout
  exact hout.map_eq

lemma paperUsedProjection_mul_remainingProjection (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0) :
    paperUsedProjection F * remainingProjection F = 0 := by
  unfold paperUsedProjection
  rw [Matrix.sub_mul,Matrix.one_mul,remainingProjection_idempotent F hF,sub_self]

lemma paperIndependentCompletion_used (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j,dot (F i) (F j)=if i=j then 1 else 0)
    (p : EuclideanSpace ℝ (Fin n ⊕ Unit) × EuclideanSpace ℝ (Fin n)) :
    paperUsedProjection F *ᵥ (paperIndependentCompletion F p).ofLp =
      paperUsedProjection F *ᵥ (fun i => p.1 (.inl i)) := by
  change paperUsedProjection F *ᵥ
    (paperUsedProjection F *ᵥ (fun i => p.1 (.inl i))+
      remainingProjection F *ᵥ p.2.ofLp) = _
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    paperUsedProjection_idempotent F hF,paperUsedProjection_mul_remainingProjection F hF,
    Matrix.zero_mulVec,add_zero]

variable {A : Type*} [MeasurableSpace A]
lemma paperIndependentCompletion_joint_measurable
    (F : A → Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j, Measurable (fun a => F a i j)) :
    Measurable (Function.uncurry (fun a => paperIndependentCompletion (F a))) := by
  have hp (i j : Fin n) : Measurable (fun a => remainingProjection (F a) i j) := by
    simp only [remainingProjection,Matrix.mul_apply,Matrix.transpose_apply,tailRows]
    exact Finset.measurable_sum _ (fun k _ => (hF k.succ i).mul (hF k.succ j))
  have hq (i j : Fin n) : Measurable (fun a => paperUsedProjection (F a) i j) :=
    measurable_const.sub (hp i j)
  have hm : Measurable (fun x : A × (EuclideanSpace ℝ (Fin n ⊕ Unit) ×
      EuclideanSpace ℝ (Fin n)) =>
      paperUsedProjection (F x.1) *ᵥ (fun i => x.2.1 (.inl i))+
        remainingProjection (F x.1) *ᵥ x.2.2.ofLp) := by
    apply Measurable.of_eval
    intro i
    simp only [Pi.add_apply,Matrix.mulVec,dotProduct]
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun j _ => ((hq i j).comp measurable_fst).mul
        ((EuclideanSpace.proj (Sum.inl j : Fin n ⊕ Unit)).continuous.measurable.comp measurable_snd.fst))
    · exact Finset.measurable_sum _ (fun j _ => ((hp i j).comp measurable_fst).mul
        ((EuclideanSpace.proj j).continuous.measurable.comp measurable_snd.snd))
  exact (WithLp.measurable_toLp 2 _).comp hm

end SKConstants.GaussianProposal
