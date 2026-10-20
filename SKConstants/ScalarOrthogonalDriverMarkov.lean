module
public import SKConstants.ScalarOrthogonalWeightedBrownian
public import SKConstants.GaussianTwoDriverBrownian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

lemma scalarIndepFun_pair_prod
    {Ω A E E' F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace E] [MeasurableSpace E'] [MeasurableSpace F] [MeasurableSpace F']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (X : Ω → E) (Y : Ω → E') (U : A → F) (V : A → F')
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable U) (hV : Measurable V)
    (hXY : IndepFun X Y P) (hUV : IndepFun U V Q) :
    IndepFun (fun p : Ω × A => (X p.1,U p.2)) (fun p : Ω × A => (Y p.1,V p.2)) (P.prod Q) := by
  let μX := P.map X
  let μY := P.map Y
  let μU := Q.map U
  let μV := Q.map V
  haveI : IsProbabilityMeasure μX := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure μY := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure μU := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure μV := (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hx : HasLaw X μX P := ⟨hX.aemeasurable,rfl⟩
  have hy : HasLaw Y μY P := ⟨hY.aemeasurable,rfl⟩
  have hu : HasLaw U μU Q := ⟨hU.aemeasurable,rfl⟩
  have hv : HasLaw V μV Q := ⟨hV.aemeasurable,rfl⟩
  have hxy := hXY.hasLaw_prod hx hy
  have huv := hUV.hasLaw_prod hu hv
  have hh := (indepFun_prod (hX.prodMk hY) (hU.prodMk hV)).hasLaw_prod
    (hxy.comp (measurePreserving_fst (μ:=P) (ν:=Q)).hasLaw)
    (huv.comp (measurePreserving_snd (μ:=P) (ν:=Q)).hasLaw)
  have hl := (measurePreserving_pairShuffle μX μY μU μV).hasLaw.comp hh
  have hxu := (indepFun_prod hX hU).hasLaw_prod
    (hx.comp (measurePreserving_fst (μ:=P) (ν:=Q)).hasLaw)
    (hu.comp (measurePreserving_snd (μ:=P) (ν:=Q)).hasLaw)
  have hyv := (indepFun_prod hY hV).hasLaw_prod
    (hy.comp (measurePreserving_fst (μ:=P) (ν:=Q)).hasLaw)
    (hv.comp (measurePreserving_snd (μ:=P) (ν:=Q)).hasLaw)
  apply (indepFun_iff_map_prod_eq_prod_map_map
    ((hX.comp measurable_fst).prodMk (hU.comp measurable_snd)).aemeasurable
    ((hY.comp measurable_fst).prodMk (hV.comp measurable_snd)).aemeasurable).mpr
  rw [hxu.map_eq,hyv.map_eq]
  exact hl.map_eq

def scalarShiftedStieltjesSum (f : StieltjesFunction ℝ) (a : ℝ≥0)
    (p : ℝ≥0 → ℝ) (t : ℝ≥0) (l : ℕ) : ℝ :=
  ∑i∈Finset.range (2^l), f (a+scalarBrownianDyadicTime t l i : ℝ≥0)*
    (p (scalarBrownianDyadicTime t l (i+1))-p (scalarBrownianDyadicTime t l i))

def scalarShiftedStieltjesLimit (f : StieltjesFunction ℝ) (a : ℝ≥0)
    (p : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  atTop.limUnder (scalarShiftedStieltjesSum f a p t)

lemma measurable_scalarShiftedStieltjesLimit (f : StieltjesFunction ℝ) (a : ℝ≥0) :
    Measurable (scalarShiftedStieltjesLimit f a) := by
  apply Measurable.of_eval
  intro t
  change Measurable (fun p : ℝ≥0 → ℝ => atTop.limUnder (scalarShiftedStieltjesSum f a p t))
  have hm (l : ℕ) : Measurable (fun p : ℝ≥0 → ℝ => scalarShiftedStieltjesSum f a p t l) := by
    unfold scalarShiftedStieltjesSum
    exact Finset.measurable_fun_sum _ (fun i _ => measurable_const.mul
      ((measurable_pi_apply _).sub (measurable_pi_apply _)))
  exact (StronglyMeasurable.limUnder (fun l => (hm l).stronglyMeasurable)).measurable

lemma scalarShiftedStieltjesLimit_eq_actual_increment
    {Ω : Type*} [MeasurableSpace Ω] (f : StieltjesFunction ℝ) (hf : Continuous f)
    (B : ℝ≥0 → Ω → ℝ) (a t : ℝ≥0) (w : Ω)
    (hB : Continuous (fun r => B r w)) :
    scalarShiftedStieltjesLimit f a (fun r => B (a+r) w-B a w) t=
      scalarGlobalStieltjesWeightedProcess f B (a+t) w-
        scalarGlobalStieltjesWeightedProcess f B a w := by
  let H := a+t
  let p : ScalarContinuousPath H :=
    ⟨fun r => B ⟨r,r.property.1⟩ w,hB.comp (continuous_subtype_val.subtype_mk (fun r => r.property.1))⟩
  have hp (r : Icc (0:ℝ) (H:ℝ)) : p r=B ⟨r,r.property.1⟩ w := rfl
  have hinc := scalarStieltjesDyadicIntervalSum_tendsto f hf H a H (le_add_of_nonneg_right bot_le) le_rfl p
  rw [←scalarGlobalStieltjesWeightedProcess_eq_finitePath f hf B H w p hp ⟨H,H.coe_nonneg,le_rfl⟩,
    ←scalarGlobalStieltjesWeightedProcess_eq_finitePath f hf B H w p hp ⟨a,a.coe_nonneg,le_add_of_nonneg_right t.coe_nonneg⟩] at hinc
  have he (l : ℕ) : scalarShiftedStieltjesSum f a (fun r => B (a+r) w-B a w) t l=
      scalarStieltjesDyadicIntervalSum f H p a H l := by
    unfold scalarShiftedStieltjesSum scalarStieltjesDyadicIntervalSum scalarStieltjesMeshSum
    apply Finset.sum_congr rfl
    intro i hi
    have ht (j : ℕ) (hj : j≤2^l) : a+scalarBrownianDyadicTime t l j≤H := by
      change a+scalarBrownianDyadicTime t l j≤a+t
      have hs := scalarBrownianDyadicTime_mono t l hj
      rw [scalarBrownianDyadicTime_end] at hs
      exact add_le_add le_rfl hs
    have htime (j : ℕ) : scalarStieltjesDyadicIntervalTime a H l j=
        (a+scalarBrownianDyadicTime t l j : ℝ≥0) := by
      simp only [H,scalarStieltjesDyadicIntervalTime,add_tsub_cancel_left,
        NNReal.coe_add,scalarBrownianDyadicTime_coe]
    have heval (j : ℕ) (hj : j≤2^l) :
        IccExtend H.coe_nonneg p (scalarStieltjesDyadicIntervalTime a H l j)=
          B (a+scalarBrownianDyadicTime t l j) w := by
      rw [htime]
      have hm : ((a+scalarBrownianDyadicTime t l j:ℝ≥0):ℝ)∈Icc 0 (H:ℝ) :=
        ⟨(a+scalarBrownianDyadicTime t l j).coe_nonneg,by exact_mod_cast ht j hj⟩
      simp only [IccExtend,Function.comp_def,projIcc_of_mem _ hm]
      change B ⟨((a+scalarBrownianDyadicTime t l j:ℝ≥0):ℝ),hm.1⟩ w=_
      congr 1
    rw [heval (i+1) (Finset.mem_range.mp hi),heval i (Finset.mem_range.mp hi).le,htime]
    ring
  unfold scalarShiftedStieltjesLimit
  have hlim : Tendsto (scalarShiftedStieltjesSum f a (fun r => B (a+r) w-B a w) t) atTop
      (𝓝 (scalarGlobalStieltjesWeightedProcess f B (a+t) w-scalarGlobalStieltjesWeightedProcess f B a w)) := by
    have hfun : scalarShiftedStieltjesSum f a (fun r => B (a+r) w-B a w) t=
        scalarStieltjesDyadicIntervalSum f H p a H := funext he
    have hH : (⟨(H:ℝ),H.coe_nonneg⟩:ℝ≥0)=H := by apply NNReal.eq; rfl
    have hA : (⟨(a:ℝ),a.coe_nonneg⟩:ℝ≥0)=a := by apply NNReal.eq; rfl
    rw [←hfun,hH,hA] at hinc
    exact hinc
  exact hlim.limUnder_eq

lemma scalarTwoDriver_future_indep_originalPast
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (a : ℝ≥0) :
    IndepFun (fun u : Ω × A => ((fun r => W.B (a+r) u.1-W.B a u.1),
      (fun r => Z.B (a+r) u.2-Z.B a u.2)))
      (fun u : Ω × A => ((fun r : Iic a => W.B r u.1),(fun r : Iic a => Z.B r u.2)))
      (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  apply scalarIndepFun_pair_prod W.law Z.law
    (fun w r => W.B (a+r) w-W.B a w) (fun w (r:Iic a) => W.B r w)
    (fun w r => Z.B (a+r) w-Z.B a w) (fun w (r:Iic a) => Z.B r w)
    (Measurable.of_eval (fun r => (W.measurable _).sub (W.measurable _)))
    (Measurable.of_eval (fun r => W.measurable _))
    (Measurable.of_eval (fun r => (Z.measurable _).sub (Z.measurable _)))
    (Measurable.of_eval (fun r => Z.measurable _))
    (W.brownian.toIsPreBrownianReal.indepFun_shift a)
    (Z.brownian.toIsPreBrownianReal.indepFun_shift a)

theorem scalarOrthogonalQuery_future_indep_originalPast
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (a : ℝ≥0) :
    IndepFun (fun u : Ω × A => fun t =>
      scalarOrthogonalQueryProcess W Z f g (a+t) u-scalarOrthogonalQueryProcess W Z f g a u)
      (fun u : Ω × A => ((fun r : Iic a => W.B r u.1),(fun r : Iic a => Z.B r u.2)))
      (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  let J : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0 → ℝ := fun p t =>
    -scalarShiftedStieltjesLimit f a p.1 t+scalarShiftedStieltjesLimit g a p.2 t
  have hJ : Measurable J := by
    apply Measurable.of_eval
    intro t
    exact (((measurable_pi_apply t).comp (measurable_scalarShiftedStieltjesLimit f a)).comp measurable_fst).neg.add
      (((measurable_pi_apply t).comp (measurable_scalarShiftedStieltjesLimit g a)).comp measurable_snd)
  have hi := (scalarTwoDriver_future_indep_originalPast W Z a).comp hJ measurable_id
  apply hi.congr _ (ae_of_all _ (fun u => rfl))
  filter_upwards [(measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae W.driver_continuous,
    (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae Z.driver_continuous,
    (measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae W.driver_indistinguishable,
    (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae Z.driver_indistinguishable] with u huW huZ hdW hdZ
  funext t
  change -scalarShiftedStieltjesLimit f a (fun r => W.B (a+r) u.1-W.B a u.1) t+
      scalarShiftedStieltjesLimit g a (fun r => Z.B (a+r) u.2-Z.B a u.2) t=_
  simp_rw [←hdW,←hdZ]
  rw [scalarShiftedStieltjesLimit_eq_actual_increment f hf W.driver a t u.1 huW,
    scalarShiftedStieltjesLimit_eq_actual_increment g hg Z.driver a t u.2 huZ]
  dsimp only [scalarOrthogonalQueryProcess]
  ring

theorem actualParisiQuery_future_indep_originalPast
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β) (a : ℝ≥0) :
    IndepFun (fun u : Ω × A => fun t =>
      (actualParisiQueryBrownianSystem W Z β hβ).B (a+t) u-
        (actualParisiQueryBrownianSystem W Z β hβ).B a u)
      (fun u : Ω × A => ((fun r : Iic a => W.B r u.1),(fun r : Iic a => Z.B r u.2)))
      (W.law.prod Z.law) :=
  scalarOrthogonalQuery_future_indep_originalPast W Z _ _
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) a

end SKConstants
