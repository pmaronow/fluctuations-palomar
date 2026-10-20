module
public import SKConstants.ScalarUniformPathLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def scalarPathHorizonCast {S T : ℝ≥0} (h : S=T) (p : ScalarContinuousPath T) :
    ScalarContinuousPath S := h.symm ▸ p

lemma measurable_scalarPathHorizonCast {S T : ℝ≥0} (h : S=T) :
    Measurable (scalarPathHorizonCast h) := by cases h; exact measurable_id

lemma scalarPathHorizonCast_eval {S T : ℝ≥0} (h : S=T) (p : ScalarContinuousPath T)
    (t : Icc (0:ℝ) (S:ℝ)) :
    scalarPathHorizonCast h p t=p ⟨t,t.property.1,by simpa only [h] using t.property.2⟩ := by
  cases h
  rfl

lemma scalarPathHorizonCast_twoDriver {S T : ℝ≥0} (h : S=T)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (p : ScalarContinuousPath T × ScalarContinuousPath T) :
    scalarTwoDriverWeightedPath f g hf hg S
      (scalarPathHorizonCast h p.1,scalarPathHorizonCast h p.2)=
      scalarPathHorizonCast h (scalarTwoDriverWeightedPath f g hf hg T p) := by
  cases h
  rfl

lemma scalarPathHorizonCast_auxDriver {S T : ℝ≥0} (h : S=T)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (p : ScalarContinuousPath T × ScalarContinuousPath T) :
    scalarOrthogonalWeightedAuxPath f g hf hg S
      (scalarPathHorizonCast h p.1,scalarPathHorizonCast h p.2)=
      scalarPathHorizonCast h (scalarOrthogonalWeightedAuxPath f g hf hg T p) := by
  cases h
  rfl

lemma scalarPathUniformStep_affine_horizon (T : ℝ≥0) (n : ℕ) :
    scalarBrownianAffineTime 0 (scalarPathUniformStep T n) (n+1)=T := by
  simpa only [scalarBrownianAffineTime,zero_add] using scalarPathUniformStep_horizon T n

lemma scalarUniformPathBlockIncrement_cast (T : ℝ≥0) (n : ℕ)
    (p : ScalarContinuousPath T) (j : Fin (n+1)) :
    scalarUniformPathBlockIncrement 0 (scalarPathUniformStep T n)
      (scalarPathHorizonCast (scalarPathUniformStep_affine_horizon T n) p) j =
    IccExtend T.coe_nonneg p (((j.val+1:ℕ):ℝ)*(scalarPathUniformStep T n:ℝ))-
      IccExtend T.coe_nonneg p ((j:ℝ)*(scalarPathUniformStep T n:ℝ)) := by
  unfold scalarUniformPathBlockIncrement
  rw [scalarPathHorizonCast_eval,scalarPathHorizonCast_eval]
  have hm (k : ℕ) (hk : k≤n+1) : ((k:ℝ)*(scalarPathUniformStep T n:ℝ))∈Icc 0 (T:ℝ) := by
    constructor
    · positivity
    · have H := congrArg (fun x : ℝ≥0 => (x:ℝ)) (scalarPathUniformStep_horizon T n)
      simp only [NNReal.coe_mul,NNReal.coe_natCast] at H
      rw [←H]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (scalarPathUniformStep T n).coe_nonneg
  simp only [IccExtend,Function.comp_def,projIcc_of_mem _ (hm (j.val+1) (by omega)),
    projIcc_of_mem _ (hm j.val j.isLt.le),scalarBrownianAffineTime,NNReal.coe_add,
    NNReal.coe_zero,zero_add,NNReal.coe_mul,NNReal.coe_natCast,Fin.val_natCast]

lemma scalarOrthogonalUniformBlockIncrements_cast (T : ℝ≥0) (n : ℕ)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (p : ScalarContinuousPath T × ScalarContinuousPath T) :
    scalarOrthogonalUniformBlockIncrements f g hf hg 0 (scalarPathUniformStep T n)
      (scalarPathHorizonCast (scalarPathUniformStep_affine_horizon T n) p.1,
        scalarPathHorizonCast (scalarPathUniformStep_affine_horizon T n) p.2)=
      scalarPathUniformIncrements T n
        (scalarTwoDriverWeightedPath f g hf hg T p,
          scalarOrthogonalWeightedAuxPath f g hf hg T p) := by
  funext j
  cases j with
  | inl j =>
    simp only [scalarOrthogonalUniformBlockIncrements,scalarPathUniformIncrements,Sum.elim_inl]
    rw [scalarPathHorizonCast_twoDriver,scalarUniformPathBlockIncrement_cast]
  | inr j =>
    simp only [scalarOrthogonalUniformBlockIncrements,scalarPathUniformIncrements,Sum.elim_inr]
    rw [scalarPathHorizonCast_auxDriver,scalarUniformPathBlockIncrement_cast]

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

lemma scalarOrthogonalFixedUniformIncrements_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (hunit : ∀ s∈Icc (0:ℝ) (T:ℝ),(f s)^2+(g s)^2=1)
    (F : Ω → ScalarContinuousPath T) (G : A → ScalarContinuousPath T)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ w ∂P,∀t:Icc (0:ℝ) (T:ℝ),F w t=B ⟨t,t.property.1⟩ w)
    (hG : ∀ᵐ w ∂Q,∀t:Icc (0:ℝ) (T:ℝ),G w t=C ⟨t,t.property.1⟩ w) (n : ℕ) :
    HasLaw (fun u : Ω × A => scalarPathUniformIncrements T n
      (scalarTwoDriverWeightedPath f g hf hg T (F u.1,G u.2),
        scalarOrthogonalWeightedAuxPath f g hf hg T (F u.1,G u.2)))
      (Measure.pi (fun _ : Fin (n+1) ⊕ Fin (n+1) => gaussianReal 0 (scalarPathUniformStep T n)))
      (P.prod Q) := by
  let H := scalarBrownianAffineTime 0 (scalarPathUniformStep T n) (n+1)
  have hH : H=T := scalarPathUniformStep_affine_horizon T n
  let F' : Ω → ScalarContinuousPath H := fun w => scalarPathHorizonCast hH (F w)
  let G' : A → ScalarContinuousPath H := fun w => scalarPathHorizonCast hH (G w)
  have hF' : ∀ᵐ w ∂P,∀t:Icc (0:ℝ) (H:ℝ),F' w t=B ⟨t,t.property.1⟩ w := by
    filter_upwards [hF] with w hw
    intro t
    rw [show F' w t=F w ⟨t,t.property.1,by simpa only [hH] using t.property.2⟩ from scalarPathHorizonCast_eval hH (F w) t]
    exact hw _
  have hG' : ∀ᵐ w ∂Q,∀t:Icc (0:ℝ) (H:ℝ),G' w t=C ⟨t,t.property.1⟩ w := by
    filter_upwards [hG] with w hw
    intro t
    rw [show G' w t=G w ⟨t,t.property.1,by simpa only [hH] using t.property.2⟩ from scalarPathHorizonCast_eval hH (G w) t]
    exact hw _
  have hl := scalarOrthogonalUniformBlockIncrements_hasLaw P Q B C hB hC f g hf hg
    0 (scalarPathUniformStep T n) (fun s hs => hunit s (by simpa only [scalarPathUniformStep_affine_horizon] using hs))
    F' G' ((measurable_scalarPathHorizonCast hH).comp hFm)
    ((measurable_scalarPathHorizonCast hH).comp hGm) hF' hG'
  convert hl using 1
  funext u
  exact (scalarOrthogonalUniformBlockIncrements_cast T n f g hf hg (F u.1,G u.2)).symm

lemma scalarRawFixedUniformIncrements_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q) (T : ℝ≥0)
    (F : Ω → ScalarContinuousPath T) (G : A → ScalarContinuousPath T)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ w ∂P,∀t:Icc (0:ℝ) (T:ℝ),F w t=B ⟨t,t.property.1⟩ w)
    (hG : ∀ᵐ w ∂Q,∀t:Icc (0:ℝ) (T:ℝ),G w t=C ⟨t,t.property.1⟩ w) (n : ℕ) :
    HasLaw (fun u : Ω × A => scalarPathUniformIncrements T n (F u.1,G u.2))
      (Measure.pi (fun _ : Fin (n+1) ⊕ Fin (n+1) => gaussianReal 0 (scalarPathUniformStep T n)))
      (P.prod Q) := by
  have hl := scalarTwoBrownianMeshFamily_hasLaw P Q B C hB hC
    (scalarBrownianAffineTime 0 (scalarPathUniformStep T n))
    (scalarBrownianAffineTime_mono 0 (scalarPathUniformStep T n)) (n+1)
  simp only [brownianMeshVariance_scalarBrownianAffineTime] at hl
  have hv (i : Fin (n+1) ⊕ Fin (n+1)) :
      Sum.elim (fun _ : Fin (n+1) => scalarPathUniformStep T n)
        (fun _ : Fin (n+1) => scalarPathUniformStep T n) i=scalarPathUniformStep T n := by
    cases i <;> rfl
  simp only [hv] at hl
  have he : (fun u : Ω × A => scalarPathUniformIncrements T n (F u.1,G u.2)) =ᵐ[P.prod Q]
      scalarTwoBrownianMeshFamily B C (scalarBrownianAffineTime 0 (scalarPathUniformStep T n)) (n+1) := by
    filter_upwards [(measurePreserving_fst (μ:=P) (ν:=Q)).quasiMeasurePreserving.ae hF,
      (measurePreserving_snd (μ:=P) (ν:=Q)).quasiMeasurePreserving.ae hG] with u huF huG
    have heval (p : ScalarContinuousPath T) (D : ℝ≥0 → ℝ) (hp : ∀ t:Icc (0:ℝ) (T:ℝ),p t=D ⟨t,t.property.1⟩)
        (k : ℕ) (hk : k≤n+1) :
        IccExtend T.coe_nonneg p ((k:ℝ)*(scalarPathUniformStep T n:ℝ))=
          D (scalarBrownianAffineTime 0 (scalarPathUniformStep T n) k) := by
      have hm : ((k:ℝ)*(scalarPathUniformStep T n:ℝ))∈Icc 0 (T:ℝ) := by
        constructor
        · positivity
        · have H := congrArg (fun x : ℝ≥0 => (x:ℝ)) (scalarPathUniformStep_horizon T n)
          simp only [NNReal.coe_mul,NNReal.coe_natCast] at H
          rw [←H]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (scalarPathUniformStep T n).coe_nonneg
      simp only [IccExtend,Function.comp_def,projIcc_of_mem _ hm]
      have hn : (⟨(k:ℝ)*(scalarPathUniformStep T n:ℝ),hm.1⟩:ℝ≥0)=
          scalarBrownianAffineTime 0 (scalarPathUniformStep T n) k := by
        apply NNReal.eq
        simp only [scalarBrownianAffineTime,NNReal.coe_add,NNReal.coe_zero,zero_add,NNReal.coe_mul,NNReal.coe_natCast]
        rfl
      simpa only [hn] using hp ⟨_,hm⟩
    funext j
    cases j with
    | inl j =>
      simp only [scalarPathUniformIncrements,scalarTwoBrownianMeshFamily,Sum.elim_inl,brownianMeshIncrement]
      rw [heval (F u.1) (fun t => B t u.1) huF _ (by omega),heval (F u.1) (fun t => B t u.1) huF _ j.isLt.le]
    | inr j =>
      simp only [scalarPathUniformIncrements,scalarTwoBrownianMeshFamily,Sum.elim_inr,brownianMeshIncrement]
      rw [heval (G u.2) (fun t => C t u.2) huG _ (by omega),heval (G u.2) (fun t => C t u.2) huG _ j.isLt.le]
  exact ⟨((measurable_scalarPathUniformIncrements T n).comp (hFm.prodMap hGm)).aemeasurable,
    (Measure.map_congr he).trans hl.map_eq⟩

theorem scalarOrthogonalWeightedPaths_joint_law
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (hunit : ∀ s∈Icc (0:ℝ) (T:ℝ),(f s)^2+(g s)^2=1)
    (F : Ω → ScalarContinuousPath T) (G : A → ScalarContinuousPath T)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ w ∂P,∀t:Icc (0:ℝ) (T:ℝ),F w t=B ⟨t,t.property.1⟩ w)
    (hG : ∀ᵐ w ∂Q,∀t:Icc (0:ℝ) (T:ℝ),G w t=C ⟨t,t.property.1⟩ w) :
    (P.prod Q).map (fun u : Ω × A =>
      (scalarTwoDriverWeightedPath f g hf hg T (F u.1,G u.2),
        scalarOrthogonalWeightedAuxPath f g hf hg T (F u.1,G u.2))) =
      (P.prod Q).map (fun u : Ω × A => (F u.1,G u.2)) := by
  let X : Ω × A → ScalarContinuousPath T × ScalarContinuousPath T := fun u =>
    (scalarTwoDriverWeightedPath f g hf hg T (F u.1,G u.2),
      scalarOrthogonalWeightedAuxPath f g hf hg T (F u.1,G u.2))
  let Y : Ω × A → ScalarContinuousPath T × ScalarContinuousPath T := fun u => (F u.1,G u.2)
  have hY : Measurable Y := hFm.prodMap hGm
  have hX : Measurable X :=
    ((measurable_scalarTwoDriverWeightedPath f g hf hg T).comp hY).prodMk
      ((measurable_scalarOrthogonalWeightedAuxPath f g hf hg T).comp hY)
  have hY0 : ∀ᵐ u ∂P.prod Q,(Y u).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (Y u).2 ⟨0,le_rfl,T.coe_nonneg⟩=0 := by
    filter_upwards [(measurePreserving_fst (μ:=P) (ν:=Q)).quasiMeasurePreserving.ae hF,
      (measurePreserving_snd (μ:=P) (ν:=Q)).quasiMeasurePreserving.ae hG,
      (measurePreserving_fst (μ:=P) (ν:=Q)).quasiMeasurePreserving.ae hB.eval_zero_ae_eq_zero,
      (measurePreserving_snd (μ:=P) (ν:=Q)).quasiMeasurePreserving.ae hC.eval_zero_ae_eq_zero] with u huF huG huB huC
    exact ⟨(huF _).trans huB,(huG _).trans huC⟩
  have hX0 : ∀ᵐ u ∂P.prod Q,(X u).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (X u).2 ⟨0,le_rfl,T.coe_nonneg⟩=0 := by
    filter_upwards [hY0] with u hu
    simp only [Y] at hu
    simp [X,scalarTwoDriverWeightedPath,scalarOrthogonalWeightedAuxPath,scalarStieltjesWeightedPath,
      hu.1,hu.2]
  by_cases hT : 0<T
  · apply scalarPairPath_law_of_uniform_increments (P.prod Q) (P.prod Q) T hT X Y hX hY hX0 hY0
    intro n
    exact (scalarOrthogonalFixedUniformIncrements_hasLaw P Q B C hB hC f g hf hg T hunit F G hFm hGm hF hG n).map_eq.trans
      (scalarRawFixedUniformIncrements_hasLaw P Q B C hB hC T F G hFm hGm hF hG n).map_eq.symm
  · have hT0 : T=0 := le_antisymm (le_of_not_gt hT) (show 0≤T from zero_le)
    apply Measure.map_congr
    filter_upwards [hX0,hY0] with u huX huY
    have ht (t : Icc (0:ℝ) (T:ℝ)) : t=⟨0,le_rfl,T.coe_nonneg⟩ := by
      apply Subtype.ext
      have h0 : (T:ℝ)=0 := congrArg (fun x:ℝ≥0 => (x:ℝ)) hT0
      linarith [t.property.1,t.property.2]
    apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      simpa only [ht t] using huX.1.trans huY.1.symm
    · apply ContinuousMap.ext
      intro t
      simpa only [ht t] using huX.2.trans huY.2.symm

end SKConstants
