module
public import SKConstants.ScalarContinuousLawLimit
public import SKConstants.ScalarContinuousOrthogonalSplit

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def scalarPathUniformStep (T : ℝ≥0) (n : ℕ) : ℝ≥0 := T/((n+1:ℕ):ℝ≥0)

lemma scalarPathUniformStep_horizon (T : ℝ≥0) (n : ℕ) :
    ((n+1:ℕ):ℝ≥0)*scalarPathUniformStep T n=T := by
  unfold scalarPathUniformStep
  rw [mul_div_cancel₀ _ (by positivity)]

lemma scalarPathUniformStep_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (scalarPathUniformStep T n:ℝ)) atTop (𝓝 0) := by
  simpa only [scalarPathUniformStep,NNReal.coe_div,NNReal.coe_add,NNReal.coe_one,NNReal.coe_natCast,Nat.cast_add,Nat.cast_one,
    mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0)).const_mul (T:ℝ)

def scalarPathUniformIncrements (T : ℝ≥0) (n : ℕ)
    (p : ScalarContinuousPath T × ScalarContinuousPath T) : (Fin (n+1) ⊕ Fin (n+1)) → ℝ :=
  Sum.elim
    (fun j => IccExtend T.coe_nonneg p.1 (((j.val+1:ℕ):ℝ)*(scalarPathUniformStep T n:ℝ))-
      IccExtend T.coe_nonneg p.1 ((j:ℝ)*(scalarPathUniformStep T n:ℝ)))
    (fun j => IccExtend T.coe_nonneg p.2 (((j.val+1:ℕ):ℝ)*(scalarPathUniformStep T n:ℝ))-
      IccExtend T.coe_nonneg p.2 ((j:ℝ)*(scalarPathUniformStep T n:ℝ)))

lemma measurable_scalarPathUniformIncrements (T : ℝ≥0) (n : ℕ) :
    Measurable (scalarPathUniformIncrements T n) := by
  apply Measurable.of_eval
  intro j
  cases j with
  | inl j =>
    exact ((ContinuousMap.measurable_eval _).comp measurable_fst).sub
      ((ContinuousMap.measurable_eval _).comp measurable_fst)
  | inr j =>
    exact ((ContinuousMap.measurable_eval _).comp measurable_snd).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd)

lemma scalarPathUniformPrefix_sum (T : ℝ≥0) (n k : ℕ) (hk : k ≤ n+1)
    (p : ScalarContinuousPath T) :
    (∑ j : Fin (n+1), if j.val<k then
      IccExtend T.coe_nonneg p (((j.val+1:ℕ):ℝ)*(scalarPathUniformStep T n:ℝ))-
        IccExtend T.coe_nonneg p ((j:ℝ)*(scalarPathUniformStep T n:ℝ)) else 0) =
      IccExtend T.coe_nonneg p ((k:ℝ)*(scalarPathUniformStep T n:ℝ))-p ⟨0,le_rfl,T.coe_nonneg⟩ := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j<k then
    IccExtend T.coe_nonneg p (((j+1:ℕ):ℝ)*(scalarPathUniformStep T n:ℝ))-
      IccExtend T.coe_nonneg p ((j:ℝ)*(scalarPathUniformStep T n:ℝ)) else 0)]
  have he : (Finset.range (n+1)).filter (fun j => j<k)=Finset.range k := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [←Finset.sum_filter,he,Finset.sum_range_sub (fun a : ℕ => IccExtend T.coe_nonneg p ((a:ℝ)*(scalarPathUniformStep T n:ℝ)))]
  simp [IccExtend,projIcc_of_mem _ (show (0:ℝ)∈Icc 0 (T:ℝ) from ⟨le_rfl,T.coe_nonneg⟩)]

lemma scalarPathUniformIndex_bound {T : ℝ≥0} (hT : 0<T) (n : ℕ)
    (t : Icc (0:ℝ) (T:ℝ)) : ⌊(t:ℝ)/(scalarPathUniformStep T n:ℝ)⌋₊ ≤ n+1 := by
  have hh : 0<(scalarPathUniformStep T n:ℝ) := by unfold scalarPathUniformStep; positivity
  have ht : (t:ℝ)/(scalarPathUniformStep T n:ℝ) ≤ ((n+1:ℕ):ℝ) := by
    apply (div_le_iff₀ hh).mpr
    have H := congrArg (fun x : ℝ≥0 => (x:ℝ)) (scalarPathUniformStep_horizon T n)
    simpa only [NNReal.coe_mul,NNReal.coe_natCast] using t.property.2.trans H.symm.le
  simpa only [Nat.floor_natCast] using Nat.floor_mono ht

lemma scalarPathUniformFloorTime_tendsto {T : ℝ≥0} (hT : 0<T)
    (t : Icc (0:ℝ) (T:ℝ)) :
    Tendsto (fun n => (⌊(t:ℝ)/(scalarPathUniformStep T n:ℝ)⌋₊:ℝ)*
      (scalarPathUniformStep T n:ℝ)) atTop (𝓝 (t:ℝ)) := by
  have hh (n : ℕ) : 0<(scalarPathUniformStep T n:ℝ) := by unfold scalarPathUniformStep; positivity
  have hlo (n : ℕ) : (t:ℝ)-(scalarPathUniformStep T n:ℝ) <
      (⌊(t:ℝ)/(scalarPathUniformStep T n:ℝ)⌋₊:ℝ)*(scalarPathUniformStep T n:ℝ) := by
    have H := (div_lt_iff₀ (hh n)).mp (Nat.lt_floor_add_one ((t:ℝ)/(scalarPathUniformStep T n:ℝ)))
    nlinarith
  have hhi (n : ℕ) : (⌊(t:ℝ)/(scalarPathUniformStep T n:ℝ)⌋₊:ℝ)*
      (scalarPathUniformStep T n:ℝ) ≤ (t:ℝ) :=
    (le_div_iff₀ (hh n)).mp (Nat.floor_le (div_nonneg t.property.1 (hh n).le))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n => (t:ℝ)-(scalarPathUniformStep T n:ℝ)) atTop (𝓝 (t:ℝ)) by
      simpa only [sub_zero] using tendsto_const_nhds.sub (scalarPathUniformStep_tendsto T))
    tendsto_const_nhds (fun n => (hlo n).le) hhi

theorem scalarPairPath_samples_law_of_uniform_increments
    {Ω A ι : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (T : ℝ≥0) (hT : 0<T)
    (X : Ω → ScalarContinuousPath T × ScalarContinuousPath T)
    (Y : A → ScalarContinuousPath T × ScalarContinuousPath T)
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ᵐ w ∂P,(X w).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (X w).2 ⟨0,le_rfl,T.coe_nonneg⟩=0)
    (hY0 : ∀ᵐ w ∂Q,(Y w).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (Y w).2 ⟨0,le_rfl,T.coe_nonneg⟩=0)
    (hgrid : ∀ n,P.map (scalarPathUniformIncrements T n ∘ X)=
      Q.map (scalarPathUniformIncrements T n ∘ Y))
    (t : ι → Icc (0:ℝ) (T:ℝ)) :
    P.map (fun w => Sum.elim (fun i => (X w).1 (t i)) (fun i => (X w).2 (t i))) =
      Q.map (fun w => Sum.elim (fun i => (Y w).1 (t i)) (fun i => (Y w).2 (t i))) := by
  let J (n : ℕ) (z : (Fin (n+1) ⊕ Fin (n+1)) → ℝ) : (ι ⊕ ι) → ℝ :=
    Sum.elim
      (fun i => ∑ j : Fin (n+1),if j.val<⌊(t i:ℝ)/(scalarPathUniformStep T n:ℝ)⌋₊ then z (.inl j) else 0)
      (fun i => ∑ j : Fin (n+1),if j.val<⌊(t i:ℝ)/(scalarPathUniformStep T n:ℝ)⌋₊ then z (.inr j) else 0)
  have hJ (n : ℕ) : Measurable (J n) := by
    apply Measurable.of_eval
    intro i
    cases i with
    | inl i => exact Finset.measurable_fun_sum _ (fun j _ => by split_ifs <;> fun_prop)
    | inr i => exact Finset.measurable_fun_sum _ (fun j _ => by split_ifs <;> fun_prop)
  have hlaw (n : ℕ) : P.map (J n ∘ scalarPathUniformIncrements T n ∘ X)=
      Q.map (J n ∘ scalarPathUniformIncrements T n ∘ Y) := by
    rw [←Measure.map_map (hJ n) ((measurable_scalarPathUniformIncrements T n).comp hX),
      hgrid n,Measure.map_map (hJ n) ((measurable_scalarPathUniformIncrements T n).comp hY)]
  have hm (Z : Ω → ScalarContinuousPath T × ScalarContinuousPath T) (hZ : Measurable Z) :
      Measurable (fun w => Sum.elim (fun i => (Z w).1 (t i)) (fun i => (Z w).2 (t i))) := by
    apply Measurable.of_eval
    intro i
    cases i with
    | inl i => exact (ContinuousMap.measurable_eval _).comp (measurable_fst.comp hZ)
    | inr i => exact (ContinuousMap.measurable_eval _).comp (measurable_snd.comp hZ)
  have hlim (Z : Ω → ScalarContinuousPath T × ScalarContinuousPath T)
      (hZ0 : ∀ᵐ w ∂P,(Z w).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (Z w).2 ⟨0,le_rfl,T.coe_nonneg⟩=0) :
      ∀ᵐ w ∂P,Tendsto (fun n => J n (scalarPathUniformIncrements T n (Z w))) atTop
        (𝓝 (Sum.elim (fun i => (Z w).1 (t i)) (fun i => (Z w).2 (t i)))) := by
    filter_upwards [hZ0] with w hw
    apply tendsto_pi_nhds.mpr
    intro i
    cases i with
    | inl i =>
      simp only [Function.comp_def,J,scalarPathUniformIncrements,Sum.elim_inl]
      simp_rw [scalarPathUniformPrefix_sum T _ _ (scalarPathUniformIndex_bound hT _ (t i)),hw.1,sub_zero]
      have H := ((Z w).1.continuous.Icc_extend' (h := T.coe_nonneg)).continuousAt.tendsto.comp
        (scalarPathUniformFloorTime_tendsto hT (t i))
      simpa only [Function.comp_def,IccExtend,projIcc_of_mem _ (t i).property] using H
    | inr i =>
      simp only [Function.comp_def,J,scalarPathUniformIncrements,Sum.elim_inr]
      simp_rw [scalarPathUniformPrefix_sum T _ _ (scalarPathUniformIndex_bound hT _ (t i)),hw.2,sub_zero]
      have H := ((Z w).2.continuous.Icc_extend' (h := T.coe_nonneg)).continuousAt.tendsto.comp
        (scalarPathUniformFloorTime_tendsto hT (t i))
      simpa only [Function.comp_def,IccExtend,projIcc_of_mem _ (t i).property] using H
  exact scalarLaw_eq_of_ae_tendsto_comparison P Q
    (fun n => J n ∘ scalarPathUniformIncrements T n ∘ X)
    (fun n => J n ∘ scalarPathUniformIncrements T n ∘ Y)
    _ _ (fun n => ((hJ n).comp ((measurable_scalarPathUniformIncrements T n).comp hX)).aemeasurable)
    (fun n => ((hJ n).comp ((measurable_scalarPathUniformIncrements T n).comp hY)).aemeasurable)
    hlaw (hm X hX).aemeasurable (by
      apply Measurable.aemeasurable
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (ContinuousMap.measurable_eval _).comp (measurable_fst.comp hY)
      | inr i => exact (ContinuousMap.measurable_eval _).comp (measurable_snd.comp hY))
    (hlim X hX0) (by
      filter_upwards [hY0] with w hw
      apply tendsto_pi_nhds.mpr
      intro i
      cases i with
      | inl i =>
        simp only [Function.comp_def,J,scalarPathUniformIncrements,Sum.elim_inl]
        simp_rw [scalarPathUniformPrefix_sum T _ _ (scalarPathUniformIndex_bound hT _ (t i)),hw.1,sub_zero]
        exact (by simpa only [Function.comp_def,IccExtend,projIcc_of_mem _ (t i).property] using
          ((Y w).1.continuous.Icc_extend' (h := T.coe_nonneg)).continuousAt.tendsto.comp (scalarPathUniformFloorTime_tendsto hT (t i)))
      | inr i =>
        simp only [Function.comp_def,J,scalarPathUniformIncrements,Sum.elim_inr]
        simp_rw [scalarPathUniformPrefix_sum T _ _ (scalarPathUniformIndex_bound hT _ (t i)),hw.2,sub_zero]
        exact (by simpa only [Function.comp_def,IccExtend,projIcc_of_mem _ (t i).property] using
          ((Y w).2.continuous.Icc_extend' (h := T.coe_nonneg)).continuousAt.tendsto.comp (scalarPathUniformFloorTime_tendsto hT (t i))))

theorem scalarPairPath_law_of_uniform_increments
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (T : ℝ≥0) (hT : 0<T)
    (X : Ω → ScalarContinuousPath T × ScalarContinuousPath T)
    (Y : A → ScalarContinuousPath T × ScalarContinuousPath T)
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ᵐ w ∂P,(X w).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (X w).2 ⟨0,le_rfl,T.coe_nonneg⟩=0)
    (hY0 : ∀ᵐ w ∂Q,(Y w).1 ⟨0,le_rfl,T.coe_nonneg⟩=0 ∧ (Y w).2 ⟨0,le_rfl,T.coe_nonneg⟩=0)
    (hgrid : ∀ n,P.map (scalarPathUniformIncrements T n ∘ X)=
      Q.map (scalarPathUniformIncrements T n ∘ Y)) : P.map X=Q.map Y := by
  let S : ScalarContinuousPath T × ScalarContinuousPath T → (ℕ ⊕ ℕ) → ℝ :=
    fun p => Sum.elim (scalarPathDenseSamples T p.1) (scalarPathDenseSamples T p.2)
  have hS : MeasurableEmbedding S :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ℕ ⊕ ℕ => ℝ)).symm.measurableEmbedding.comp
      ((scalarPathDenseSamples_measurableEmbedding T).prodMap
        (scalarPathDenseSamples_measurableEmbedding T))
  have he (I : Finset (ℕ ⊕ ℕ)) :
      P.map (fun w => I.restrict (S (X w)))=Q.map (fun w => I.restrict (S (Y w))) := by
    let t : I → Icc (0:ℝ) (T:ℝ) := fun i => scalarPathDenseTimes T (Sum.elim id id i.val)
    let J : (I ⊕ I → ℝ) → I → ℝ := fun z i => match i.val with
      | .inl _ => z (.inl i)
      | .inr _ => z (.inr i)
    have hJ : Measurable J := by
      apply Measurable.of_eval
      intro i
      cases hi : i.val with
      | inl k => simpa only [J,hi] using (measurable_pi_apply (Sum.inl i : I ⊕ I) : Measurable (fun z : I ⊕ I → ℝ => z (.inl i)))
      | inr k => simpa only [J,hi] using (measurable_pi_apply (Sum.inr i : I ⊕ I) : Measurable (fun z : I ⊕ I → ℝ => z (.inr i)))
    have hm (Z : Ω → ScalarContinuousPath T × ScalarContinuousPath T) (hZ : Measurable Z) :
        Measurable (fun w => Sum.elim (fun i => (Z w).1 (t i)) (fun i => (Z w).2 (t i))) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (ContinuousMap.measurable_eval _).comp (measurable_fst.comp hZ)
      | inr i => exact (ContinuousMap.measurable_eval _).comp (measurable_snd.comp hZ)
    have hmY : Measurable (fun w => Sum.elim (fun i => (Y w).1 (t i)) (fun i => (Y w).2 (t i))) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (ContinuousMap.measurable_eval _).comp (measurable_fst.comp hY)
      | inr i => exact (ContinuousMap.measurable_eval _).comp (measurable_snd.comp hY)
    have HH := congrArg (fun μ : Measure (I ⊕ I → ℝ) => μ.map J)
      (scalarPairPath_samples_law_of_uniform_increments P Q T hT X Y hX hY hX0 hY0 hgrid t)
    rw [Measure.map_map hJ (hm X hX),Measure.map_map hJ hmY] at HH
    convert HH using 1 <;> congr 1 <;> funext w i <;> cases hi : i.val <;>
      simp only [S,J,t,hi,Finset.restrict_def,scalarPathDenseSamples,Function.comp_def,
        Sum.elim_inl,Sum.elim_inr,id_eq]
  have hFP : IsProjectiveLimit (P.map (S ∘ X))
      (fun I : Finset (ℕ ⊕ ℕ) => P.map (fun w => I.restrict (S (X w)))) :=
    isProjectiveLimit_map (hS.measurable.comp hX).aemeasurable
  have hGQ : IsProjectiveLimit (Q.map (S ∘ Y))
      (fun I : Finset (ℕ ⊕ ℕ) => P.map (fun w => I.restrict (S (X w)))) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (hS.measurable.comp hY)]
    exact (he I).symm
  apply hS.map_injective
  rw [Measure.map_map hS.measurable hX,Measure.map_map hS.measurable hY]
  exact hFP.unique hGQ

end SKConstants
