module
public import SKConstants.GaussianProposalIndependentCompletions

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def piHead {n : ℕ} (α : Fin (n+1) → Type*) [∀ i, MeasurableSpace (α i)] :
    ((i : Fin (n+1)) → α i) ≃ᵐ α 0 × ((i : Fin n) → α i.succ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := (measurable_pi_apply _).prodMk
    (Measurable.of_eval (fun i => measurable_pi_apply i.succ))
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (measurable_fst : Measurable (Prod.fst :
        α 0 × ((i : Fin n) → α i.succ) → α 0))
    · simpa only [Fin.cons_succ, Function.comp_def] using
        ((measurable_pi_apply j).comp measurable_snd :
          Measurable (fun p : α 0 × ((i : Fin n) → α i.succ) => p.2 j))

theorem piHead_law {n : ℕ} {α : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : Fin (n+1)) → Measure (α i))
    [∀ i, SigmaFinite (μ i)] :
    (Measure.pi μ).map (piHead α) =
      (μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ)) := by
  have h : MeasurePreserving (piHead α).symm
      ((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) (Measure.pi μ) := by
    refine ⟨(piHead α).symm.measurable, (Measure.pi_eq (fun s hs => ?_)).symm⟩
    rw [(piHead α).symm.map_apply]
    have he : (piHead α).symm ⁻¹' Set.univ.pi s =
        s 0 ×ˢ Set.univ.pi (fun i : Fin n => s i.succ) := by
      ext p
      simp only [piHead, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_symm_mk, Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
      rw [Fin.forall_fin_succ]
      simp
    rw [he, Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_succ]
  exact h.symm.map_eq

def ResidualNoise (n : ℕ) : ℕ → Type
  | 0 => EuclideanSpace ℝ (Fin n × Fin n)
  | q+1 => (EuclideanSpace ℝ Unit × EuclideanSpace ℝ (Fin n)) × ResidualNoise n q

instance residualNoiseMeasurableSpace (n : ℕ) : (q : ℕ) → MeasurableSpace (ResidualNoise n q)
  | 0 => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin n × Fin n)))
  | q+1 => by
    letI := residualNoiseMeasurableSpace n q
    exact inferInstanceAs (MeasurableSpace
      ((EuclideanSpace ℝ Unit × EuclideanSpace ℝ (Fin n)) × ResidualNoise n q))

def residualNoiseLaw (n : ℕ) : (q : ℕ) → Measure (ResidualNoise n q)
  | 0 => primitiveGaussian (Fin n × Fin n)
  | q+1 => ((primitiveGaussian Unit).prod (primitiveGaussian (Fin n))).prod
      (residualNoiseLaw n q)

instance residualNoiseLaw_probability (n : ℕ) :
    (q : ℕ) → IsProbabilityMeasure (residualNoiseLaw n q)
  | 0 => inferInstanceAs (IsProbabilityMeasure (primitiveGaussian (Fin n × Fin n)))
  | q+1 => by
    let := residualNoiseLaw_probability n q
    exact inferInstanceAs (IsProbabilityMeasure
      (((primitiveGaussian Unit).prod (primitiveGaussian (Fin n))).prod (residualNoiseLaw n q)))

def NoiseEndpoints (n : ℕ) : (q : ℕ) → PaperAugmentedNoise n q →
    Fin q → EuclideanSpace ℝ (Fin n)
  | 0, _ => Fin.elim0
  | q+1, z => Fin.cons (WithLp.toLp 2 (fun i => z.1.1 (.inl i)))
      (NoiseEndpoints n q z.2)

def NoiseResidual (n : ℕ) : (q : ℕ) → PaperAugmentedNoise n q → ResidualNoise n q
  | 0, z => z
  | q+1, z => ((WithLp.toLp 2 (fun i => z.1.1 (.inr i)), z.1.2),
      NoiseResidual n q z.2)

def PackNoise (n : ℕ) : (q : ℕ) →
    (Fin q → EuclideanSpace ℝ (Fin n)) × ResidualNoise n q → PaperAugmentedNoise n q
  | 0, p => p.2
  | q+1, p => ((primitiveGaussianPairJoin (p.1 0,p.2.1.1), p.2.1.2),
      PackNoise n q (Fin.tail p.1,p.2.2))

theorem measurable_NoiseEndpoints (n q : ℕ) : Measurable (NoiseEndpoints n q) := by
  induction q with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ q ih =>
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (WithLp.measurable_toLp 2 _).comp
        (Measurable.of_eval (fun j =>
          (EuclideanSpace.proj (Sum.inl j)).continuous.measurable.comp measurable_fst.fst))
    · exact ((measurable_pi_apply j).comp ih).comp measurable_snd

theorem measurable_NoiseResidual (n q : ℕ) : Measurable (NoiseResidual n q) := by
  induction q with
  | zero => exact measurable_id
  | succ q ih =>
    exact (((WithLp.measurable_toLp 2 _).comp
      (Measurable.of_eval (fun j =>
        (EuclideanSpace.proj (Sum.inr j)).continuous.measurable.comp measurable_fst.fst))).prodMk
          measurable_fst.snd).prodMk (ih.comp measurable_snd)

theorem measurable_PackNoise (n q : ℕ) : Measurable (PackNoise n q) := by
  induction q with
  | zero => exact measurable_snd
  | succ q ih =>
    have hj : Measurable (primitiveGaussianPairJoin (I := Fin n) (J := Unit)) := by
      exact (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval (fun i => by
        cases i with
        | inl j => exact (EuclideanSpace.proj j).continuous.measurable.comp measurable_fst
        | inr j => exact (EuclideanSpace.proj j).continuous.measurable.comp measurable_snd))
    exact ((hj.comp (((measurable_pi_apply 0).comp measurable_fst).prodMk
      measurable_snd.fst.fst)).prodMk measurable_snd.fst.snd).prodMk
        (ih.comp ((Measurable.of_eval (fun j =>
          (measurable_pi_apply j.succ).comp measurable_fst)).prodMk measurable_snd.snd))

theorem PackNoise_extract (n q : ℕ) (z : PaperAugmentedNoise n q) :
    PackNoise n q (NoiseEndpoints n q z,NoiseResidual n q z) = z := by
  induction q with
  | zero => rfl
  | succ q ih =>
    apply Prod.ext
    · apply Prod.ext
      · ext i
        cases i <;> rfl
      · rfl
    · exact ih z.2

theorem NoiseEndpoints_pack (n q : ℕ)
    (p : (Fin q → EuclideanSpace ℝ (Fin n)) × ResidualNoise n q) :
    NoiseEndpoints n q (PackNoise n q p) = p.1 := by
  induction q with
  | zero => funext i; exact Fin.elim0 i
  | succ q ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (Fin.tail p.1,p.2.2)) j

theorem NoiseResidual_pack (n q : ℕ)
    (p : (Fin q → EuclideanSpace ℝ (Fin n)) × ResidualNoise n q) :
    NoiseResidual n q (PackNoise n q p) = p.2 := by
  induction q with
  | zero => rfl
  | succ q ih =>
    apply Prod.ext
    · rfl
    · exact ih (Fin.tail p.1,p.2.2)

theorem measurable_primitiveGaussianPairJoin (n : ℕ) :
    Measurable (primitiveGaussianPairJoin (I := Fin n) (J := Unit)) := by
  exact (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval (fun i => by
    cases i with
    | inl j => exact (EuclideanSpace.proj j).continuous.measurable.comp measurable_fst
    | inr j => exact (EuclideanSpace.proj j).continuous.measurable.comp measurable_snd))

theorem PackNoise_law (n q : ℕ) :
    ((Measure.pi (fun _ : Fin q => primitiveGaussian (Fin n))).prod
      (residualNoiseLaw n q)).map (PackNoise n q) = paperAugmentedNoiseLaw n q := by
  induction q with
  | zero =>
    change ((Measure.pi (fun _ : Fin 0 => primitiveGaussian (Fin n))).prod
      (primitiveGaussian (Fin n × Fin n))).map Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    rfl
  | succ q ih =>
    let μ := primitiveGaussian (Fin n)
    let ν := primitiveGaussian Unit
    let E := Measure.pi (fun _ : Fin q => μ)
    let R := residualNoiseLaw n q
    have hsplit : MeasurePreserving
        (Prod.map (piHead (fun _ : Fin (q+1) => EuclideanSpace ℝ (Fin n))) id)
        ((Measure.pi (fun _ : Fin (q+1) => μ)).prod ((ν.prod μ).prod R))
        ((μ.prod E).prod ((ν.prod μ).prod R)) := by
      refine ⟨(piHead _).measurable.prodMap measurable_id, ?_⟩
      rw [← Measure.map_prod_map _ _ (piHead _).measurable measurable_id,
        piHead_law, Measure.map_id]
    have hshuffle : MeasurePreserving
        (fun x : (EuclideanSpace ℝ (Fin n) × (Fin q → EuclideanSpace ℝ (Fin n))) ×
            ((EuclideanSpace ℝ Unit × EuclideanSpace ℝ (Fin n)) × ResidualNoise n q) =>
          ((x.1.1,x.2.1),(x.1.2,x.2.2)))
        ((μ.prod E).prod ((ν.prod μ).prod R)) ((μ.prod (ν.prod μ)).prod (E.prod R)) :=
      ⟨by fun_prop, prod_quad_shuffle μ E (ν.prod μ) R⟩
    have hjoin : MeasurePreserving (primitiveGaussianPairJoin (I := Fin n) (J := Unit))
        (μ.prod ν) (primitiveGaussian (Fin n ⊕ Unit)) :=
      ⟨measurable_primitiveGaussianPairJoin n, primitiveGaussianPairJoin_hasLaw.map_eq⟩
    have hhead := (hjoin.prod (MeasurePreserving.id μ)).comp
      (measurePreserving_prodAssoc μ ν μ).symm
    have htail : MeasurePreserving (PackNoise n q) (E.prod R) (paperAugmentedNoiseLaw n q) :=
      ⟨measurable_PackNoise n q, ih⟩
    exact ((hhead.prod htail).comp (hshuffle.comp hsplit)).map_eq

theorem NoiseEndpoints_residual_joint_law (n q : ℕ) :
    (paperAugmentedNoiseLaw n q).map
      (fun z => (NoiseEndpoints n q z,NoiseResidual n q z)) =
      (Measure.pi (fun _ : Fin q => primitiveGaussian (Fin n))).prod
        (residualNoiseLaw n q) := by
  rw [← PackNoise_law n q, Measure.map_map
    ((measurable_NoiseEndpoints n q).prodMk (measurable_NoiseResidual n q))
    (measurable_PackNoise n q)]
  have he : (fun z => (NoiseEndpoints n q z,NoiseResidual n q z)) ∘ PackNoise n q = id := by
    funext p
    exact Prod.ext (NoiseEndpoints_pack n q p) (NoiseResidual_pack n q p)
  rw [he, Measure.map_id]

theorem NoiseEndpoints_law (n q : ℕ) :
    (paperAugmentedNoiseLaw n q).map (NoiseEndpoints n q) =
      Measure.pi (fun _ : Fin q => primitiveGaussian (Fin n)) := by
  have h := congrArg (fun μ => μ.map Prod.fst) (NoiseEndpoints_residual_joint_law n q)
  rw [Measure.map_map measurable_fst
    ((measurable_NoiseEndpoints n q).prodMk (measurable_NoiseResidual n q)),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

end SKConstants.M1
