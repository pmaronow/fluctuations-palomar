module

public import SKConstants.Completion.LC0.PathConcatenation
public import SKConstants.ScalarOrthogonalPathLaw

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N9Q2
open SKConstantsOAI.ZeroTemperatureSK M1
variable {Ω : Type*} [MeasurableSpace Ω]

def shiftedCoefficient (f : StieltjesFunction ℝ) (hf : Continuous f) (a : ℝ≥0) :
    StieltjesFunction ℝ where
  toFun t := f ((a : ℝ)+t)
  mono' := fun _ _ h => f.mono (add_le_add le_rfl h)
  right_continuous' t := (hf.comp (continuous_const.add continuous_id)).continuousWithinAt

theorem continuous_shiftedCoefficient (f : StieltjesFunction ℝ) (hf : Continuous f)
    (a : ℝ≥0) : Continuous (shiftedCoefficient f hf a) :=
  hf.comp (continuous_const.add continuous_id)

theorem concat_eval_after (a v : ℝ≥0) (B : ScalarContinuousPath a)
    (p : ScalarContinuousPath v) (t : Icc (0 : ℝ) (v : ℝ)) :
    scalarConcatPath a v (B,p)
      ⟨(a : ℝ)+t,add_nonneg a.coe_nonneg t.property.1,
        by simpa only [NNReal.coe_add] using (add_le_add le_rfl t.property.2 :
          (a : ℝ)+(t : ℝ) ≤ (a : ℝ)+(v : ℝ))⟩ =
      B ⟨a,a.coe_nonneg,le_rfl⟩+p t-p ⟨0,le_rfl,v.coe_nonneg⟩ := by
  simp only [scalarConcatPath,ContinuousMap.coe_mk,
    projIcc_of_right_le a.coe_nonneg (le_add_of_nonneg_right t.property.1),
    add_sub_cancel_left,projIcc_of_mem _ t.property]

theorem weighted_concat_increment (f : StieltjesFunction ℝ) (hf : Continuous f)
    (a v u : ℝ≥0) (hu : u ≤ v) (B : ScalarContinuousPath a)
    (p : ScalarContinuousPath v) (hp : p ⟨0,le_rfl,v.coe_nonneg⟩ = 0) :
    scalarStieltjesWeightedPath f hf (a+v) (scalarConcatPath a v (B,p))
      ⟨a+u,(a+u).coe_nonneg,by exact_mod_cast (add_le_add le_rfl hu : a+u ≤ a+v)⟩ -
    scalarStieltjesWeightedPath f hf (a+v) (scalarConcatPath a v (B,p))
      ⟨a,a.coe_nonneg,by exact_mod_cast (le_self_add : a ≤ a+v)⟩ =
    scalarStieltjesWeightedPath (shiftedCoefficient f hf a)
      (continuous_shiftedCoefficient f hf a) v p ⟨u,u.coe_nonneg,hu⟩ := by
  have he (l : ℕ) : scalarStieltjesDyadicIntervalSum f (a+v)
      (scalarConcatPath a v (B,p)) a (a+u) l =
      scalarStieltjesDyadicSumAt (shiftedCoefficient f hf a) v p u l := by
    unfold scalarStieltjesDyadicIntervalSum scalarStieltjesDyadicSumAt scalarStieltjesMeshSum
    apply Finset.sum_congr rfl
    intro i hi
    have ht (j : ℕ) (hj : j ≤ 2^l) : scalarStieltjesDyadicTime u l j ∈
        Icc (0 : ℝ) (v : ℝ) :=
      ⟨(scalarStieltjesDyadicTime_mem u l j hj).1,
        (scalarStieltjesDyadicTime_mem u l j hj).2.trans hu⟩
    have hev (j : ℕ) (hj : j ≤ 2^l) :
        IccExtend (a+v).coe_nonneg (scalarConcatPath a v (B,p))
          (scalarStieltjesDyadicIntervalTime a (a+u) l j) =
        B ⟨a,a.coe_nonneg,le_rfl⟩+
          IccExtend v.coe_nonneg p (scalarStieltjesDyadicTime u l j)-
            p ⟨0,le_rfl,v.coe_nonneg⟩ := by
      simp only [scalarStieltjesDyadicIntervalTime,add_tsub_cancel_left]
      have hm : (a : ℝ)+scalarStieltjesDyadicTime u l j ∈ Icc (0 : ℝ) (a+v : ℝ≥0) :=
        ⟨add_nonneg a.coe_nonneg (ht j hj).1,
          by simpa only [NNReal.coe_add] using (add_le_add le_rfl (ht j hj).2 :
            (a : ℝ)+_ ≤ (a : ℝ)+(v : ℝ))⟩
      simp only [IccExtend,Function.comp_apply,projIcc_of_mem _ hm,
        projIcc_of_mem _ (ht j hj)]
      exact concat_eval_after a v B p ⟨_,ht j hj⟩
    rw [hev (i+1) (Finset.mem_range.mp hi),hev i (Finset.mem_range.mp hi).le]
    simp only [scalarStieltjesDyadicIntervalTime,add_tsub_cancel_left,shiftedCoefficient]
    ring
  have h₁ := scalarStieltjesDyadicIntervalSum_tendsto f hf (a+v) a (a+u)
    le_self_add (add_le_add le_rfl hu) (scalarConcatPath a v (B,p))
  have h₂ := scalarStieltjesDyadicSumAt_tendsto_of_zero (shiftedCoefficient f hf a)
    (continuous_shiftedCoefficient f hf a) v u hu p hp
  exact tendsto_nhds_unique (h₁.congr he) h₂

theorem twoDriver_concat_increment (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (a v u : ℝ≥0) (hu : u ≤ v)
    (B D : ScalarContinuousPath a) (p q : ScalarContinuousPath v)
    (hp : p ⟨0,le_rfl,v.coe_nonneg⟩ = 0) (hq : q ⟨0,le_rfl,v.coe_nonneg⟩ = 0) :
    scalarTwoDriverWeightedPath f g hf hg (a+v)
      (scalarConcatPath a v (B,p),scalarConcatPath a v (D,q))
      ⟨a+u,(a+u).coe_nonneg,by exact_mod_cast (add_le_add le_rfl hu : a+u ≤ a+v)⟩ -
    scalarTwoDriverWeightedPath f g hf hg (a+v)
      (scalarConcatPath a v (B,p),scalarConcatPath a v (D,q))
      ⟨a,a.coe_nonneg,by exact_mod_cast (le_self_add : a ≤ a+v)⟩ =
    scalarTwoDriverWeightedPath (shiftedCoefficient f hf a) (shiftedCoefficient g hg a)
      (continuous_shiftedCoefficient f hf a) (continuous_shiftedCoefficient g hg a) v (p,q)
      ⟨u,u.coe_nonneg,hu⟩ := by
  have h₁ := weighted_concat_increment f hf a v u hu B p hp
  have h₂ := weighted_concat_increment g hg a v u hu D q hq
  simp only [scalarTwoDriverWeightedPath,ContinuousMap.add_apply,ContinuousMap.neg_apply]
  linarith

theorem weighted_wiener_law (W : BrownianSystem Ω)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (v : ℝ≥0)
    (hunit : ∀ s ∈ Icc (0 : ℝ) (v : ℝ), (f s)^2+(g s)^2 = 1) :
    ((scalarPrimitiveBrownianPathLaw W v).prod (scalarPrimitiveBrownianPathLaw W v)).map
      (scalarTwoDriverWeightedPath f g hf hg v) = scalarPrimitiveBrownianPathLaw W v := by
  letI := W.isProbability
  let F := scalarPrimitiveBrownianPathVersion W v
  have hF : Measurable F := measurable_scalarPrimitiveBrownianPathVersion W v
  have hl := scalarOrthogonalWeightedPaths_joint_law W.law W.law W.B W.B
    W.brownian.toIsPreBrownianReal W.brownian.toIsPreBrownianReal f g hf hg v hunit
    F F hF hF (scalarPrimitiveBrownianPathVersion_ae W v)
      (scalarPrimitiveBrownianPathVersion_ae W v)
  have hpair : Measurable (fun u : Ω × Ω => (F u.1,F u.2)) := hF.prodMap hF
  have hL : Measurable (fun u : Ω × Ω =>
      (scalarTwoDriverWeightedPath f g hf hg v (F u.1,F u.2),
       scalarOrthogonalWeightedAuxPath f g hf hg v (F u.1,F u.2))) :=
    ((measurable_scalarTwoDriverWeightedPath f g hf hg v).comp hpair).prodMk
      ((measurable_scalarOrthogonalWeightedAuxPath f g hf hg v).comp hpair)
  have he := congrArg (fun μ => μ.map Prod.fst) hl
  rw [Measure.map_map measurable_fst hL,
    Measure.map_map measurable_fst hpair] at he
  change (W.law.prod W.law).map
    (scalarTwoDriverWeightedPath f g hf hg v ∘ (fun u : Ω × Ω => (F u.1,F u.2))) =
      (W.law.prod W.law).map (F ∘ Prod.fst) at he
  have hp : (W.law.prod W.law).map (fun u : Ω × Ω => (F u.1,F u.2)) =
      (W.law.map F).prod (W.law.map F) := (Measure.map_prod_map W.law W.law hF hF).symm
  rw [← Measure.map_map (measurable_scalarTwoDriverWeightedPath f g hf hg v) hpair,hp,
    ← Measure.map_map hF measurable_fst,Measure.map_fst_prod,measure_univ,one_smul] at he
  exact he

end SKConstants.Completion.N9Q2
