module
public import SKConstants.ScalarOrthogonalPathLaw
public import SKConstants.ParisiBrownianMarkov
public import SKConstants.ScalarProcessParisiRho

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def scalarGlobalStieltjesWeightedProcess (f : StieltjesFunction ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (w : Ω) : ℝ :=
  f t*B t w-∫s in (0:ℝ)..(t:ℝ),B (Real.toNNReal s) w ∂f.measure

attribute [local irreducible] BrownianSystem.driver BrownianSystem.progressiveVersion

set_option backward.isDefEq.respectTransparency true in
lemma measurable_scalarGlobalStieltjesWeightedProcess (W : BrownianSystem Ω)
    (f : StieltjesFunction ℝ) (t : ℝ≥0) :
    Measurable (scalarGlobalStieltjesWeightedProcess f W.driver t) := by
  have hW : Measurable (fun p : ℝ≥0 × Ω => W.driver p.1 p.2) :=
    progressive_joint_measurable
      (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (α:=W.driver) W.driver_progressive
  have hm : Measurable (fun p : Ω × ℝ => W.driver (Real.toNNReal p.2) p.1) :=
    hW.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν:=f.measure.restrict (Ioc (0:ℝ) (t:ℝ)))
  have he : scalarGlobalStieltjesWeightedProcess f W.driver t=
      fun w => f t*W.driver t w-∫s in Ioc (0:ℝ) (t:ℝ),W.driver (Real.toNNReal s) w ∂f.measure := by
    funext w
    unfold scalarGlobalStieltjesWeightedProcess
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
  rw [he]
  exact (((progressive_measurable_at _ W.driver_progressive t).mono
    ((Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)).le t) le_rfl).const_mul _).sub hi.measurable

lemma continuous_scalarGlobalStieltjesWeightedProcess
    (f : StieltjesFunction ℝ) (hf : Continuous f) (B : ℝ≥0 → Ω → ℝ)
    (w : Ω) (hB : Continuous (fun t => B t w)) :
    Continuous (fun t => scalarGlobalStieltjesWeightedProcess f B t w) := by
  let : NullSingletonClass f.measure := scalarStieltjes_noAtoms f hf
  have hX : Continuous (fun s : ℝ => B (Real.toNNReal s) w) :=
    hB.comp continuous_real_toNNReal
  have hi : ∀a b : ℝ,IntervalIntegrable (fun s => B (Real.toNNReal s) w) f.measure a b :=
    fun a b => (hX.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  exact ((hf.comp continuous_subtype_val).mul hB).sub
    ((intervalIntegral.continuous_primitive hi 0).comp continuous_subtype_val)

lemma scalarGlobalStieltjesWeightedProcess_eq_finitePath
    (f : StieltjesFunction ℝ) (hf : Continuous f) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (w : Ω) (p : ScalarContinuousPath T)
    (hp : ∀s:Icc (0:ℝ) (T:ℝ),p s=B ⟨s,s.property.1⟩ w)
    (t : Icc (0:ℝ) (T:ℝ)) :
    scalarGlobalStieltjesWeightedProcess f B ⟨t,t.property.1⟩ w=
      scalarStieltjesWeightedPath f hf T p t := by
  unfold scalarGlobalStieltjesWeightedProcess
  change f t*B ⟨t,t.property.1⟩ w-_ = f t*p t-_
  rw [hp t]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change s ∈ uIcc (0:ℝ) (t:ℝ) at hs
  have hs0 : 0 ≤ s := by simpa only [min_eq_left t.property.1] using hs.1
  have hst : s ≤ (t:ℝ) := by simpa only [max_eq_right t.property.1] using hs.2
  have hsT : s ≤ (T:ℝ) := hst.trans t.property.2
  simp only [IccExtend,Function.comp_def,projIcc_of_mem _ ⟨hs0,hsT⟩]
  rw [hp ⟨s,hs0,hsT⟩]
  congr 1
  exact NNReal.eq (Real.coe_toNNReal s hs0)

def scalarOrthogonalQueryProcess (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (t : ℝ≥0) (u : Ω × A) : ℝ :=
  -scalarGlobalStieltjesWeightedProcess f W.driver t u.1+
    scalarGlobalStieltjesWeightedProcess g Z.driver t u.2

def scalarOrthogonalAuxProcess (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (t : ℝ≥0) (u : Ω × A) : ℝ :=
  scalarGlobalStieltjesWeightedProcess g W.driver t u.1+
    scalarGlobalStieltjesWeightedProcess f Z.driver t u.2

lemma measurable_scalarOrthogonalQueryProcess (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (t : ℝ≥0) : Measurable (scalarOrthogonalQueryProcess W Z f g t) :=
  ((measurable_scalarGlobalStieltjesWeightedProcess W f t).comp measurable_fst).neg.add
    ((measurable_scalarGlobalStieltjesWeightedProcess Z g t).comp measurable_snd)

lemma measurable_scalarOrthogonalAuxProcess (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (t : ℝ≥0) : Measurable (scalarOrthogonalAuxProcess W Z f g t) :=
  ((measurable_scalarGlobalStieltjesWeightedProcess W g t).comp measurable_fst).add
    ((measurable_scalarGlobalStieltjesWeightedProcess Z f t).comp measurable_snd)

lemma scalarOrthogonalProcesses_finite_path_version (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0) :
    ∀ᵐ u ∂W.law.prod Z.law,∀t:Icc (0:ℝ) (T:ℝ),
      scalarOrthogonalQueryProcess W Z f g ⟨t,t.property.1⟩ u=
        scalarTwoDriverWeightedPath f g hf hg T (brownianFinitePath W T u.1,brownianFinitePath Z T u.2) t ∧
      scalarOrthogonalAuxProcess W Z f g ⟨t,t.property.1⟩ u=
        scalarOrthogonalWeightedAuxPath f g hf hg T (brownianFinitePath W T u.1,brownianFinitePath Z T u.2) t := by
  let := W.isProbability
  let := Z.isProbability
  filter_upwards [(measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae (brownianFinitePath_version W T),
    (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae (brownianFinitePath_version Z T),
    (measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae W.driver_indistinguishable,
    (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae Z.driver_indistinguishable] with u huW huZ hdW hdZ
  have hW : ∀t:Icc (0:ℝ) (T:ℝ),brownianFinitePath W T u.1 t=W.driver ⟨t,t.property.1⟩ u.1 :=
    fun t => (huW t).trans (hdW _).symm
  have hZ : ∀t:Icc (0:ℝ) (T:ℝ),brownianFinitePath Z T u.2 t=Z.driver ⟨t,t.property.1⟩ u.2 :=
    fun t => (huZ t).trans (hdZ _).symm
  intro t
  simp only [scalarOrthogonalQueryProcess,scalarOrthogonalAuxProcess,
    scalarTwoDriverWeightedPath,scalarOrthogonalWeightedAuxPath,ContinuousMap.add_apply,ContinuousMap.neg_apply]
  rw [scalarGlobalStieltjesWeightedProcess_eq_finitePath f hf W.driver T u.1 _ hW t,
    scalarGlobalStieltjesWeightedProcess_eq_finitePath g hg Z.driver T u.2 _ hZ t,
    scalarGlobalStieltjesWeightedProcess_eq_finitePath g hg W.driver T u.1 _ hW t,
    scalarGlobalStieltjesWeightedProcess_eq_finitePath f hf Z.driver T u.2 _ hZ t]
  exact ⟨rfl,rfl⟩

theorem scalarOrthogonalProcesses_samples_joint_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀s∈Ici (0:ℝ),(f s)^2+(g s)^2=1)
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) :
    (W.law.prod Z.law).map (fun u : Ω × A => Sum.elim
      (fun i => scalarOrthogonalQueryProcess W Z f g (t i) u)
      (fun i => scalarOrthogonalAuxProcess W Z f g (t i) u))=
      (W.law.prod Z.law).map (fun u : Ω × A => Sum.elim
        (fun i => W.B (t i) u.1) (fun i => Z.B (t i) u.2)) := by
  let := W.isProbability
  let := Z.isProbability
  let T : ℝ≥0 := Finset.univ.sup t
  have ht (i : ι) : t i≤T := Finset.le_sup (Finset.mem_univ i)
  let J : ScalarContinuousPath T × ScalarContinuousPath T → (ι ⊕ ι) → ℝ :=
    fun p => Sum.elim (fun i => p.1 ⟨t i,(t i).coe_nonneg,ht i⟩)
      (fun i => p.2 ⟨t i,(t i).coe_nonneg,ht i⟩)
  have hJ : Measurable J := by
    apply Measurable.of_eval
    intro i
    cases i with
    | inl i => exact (ContinuousMap.measurable_eval _).comp measurable_fst
    | inr i => exact (ContinuousMap.measurable_eval _).comp measurable_snd
  have hh := scalarOrthogonalWeightedPaths_joint_law W.law Z.law W.B Z.B
    W.brownian.toIsPreBrownianReal Z.brownian.toIsPreBrownianReal f g hf hg T
    (fun s hs => hunit s hs.1) (brownianFinitePath W T) (brownianFinitePath Z T)
    (measurable_brownianFinitePath W T) (measurable_brownianFinitePath Z T)
    (brownianFinitePath_version W T) (brownianFinitePath_version Z T)
  have hme := (measurable_brownianFinitePath W T).prodMap (measurable_brownianFinitePath Z T)
  have hms := ((measurable_scalarTwoDriverWeightedPath f g hf hg T).comp hme).prodMk
    ((measurable_scalarOrthogonalWeightedAuxPath f g hf hg T).comp hme)
  have hmap := congrArg (fun μ => μ.map J) hh
  have hms' : Measurable (fun u : Ω × A => (scalarTwoDriverWeightedPath f g hf hg T (brownianFinitePath W T u.1,brownianFinitePath Z T u.2),scalarOrthogonalWeightedAuxPath f g hf hg T (brownianFinitePath W T u.1,brownianFinitePath Z T u.2))) := hms
  have hme' : Measurable (fun u : Ω × A => (brownianFinitePath W T u.1,brownianFinitePath Z T u.2)) := hme
  rw [Measure.map_map hJ hms',Measure.map_map hJ hme'] at hmap
  have hleft : (fun u : Ω × A => Sum.elim
      (fun i => scalarOrthogonalQueryProcess W Z f g (t i) u)
      (fun i => scalarOrthogonalAuxProcess W Z f g (t i) u))=ᵐ[W.law.prod Z.law]
      (J ∘ fun u => (scalarTwoDriverWeightedPath f g hf hg T (brownianFinitePath W T u.1,brownianFinitePath Z T u.2),
        scalarOrthogonalWeightedAuxPath f g hf hg T (brownianFinitePath W T u.1,brownianFinitePath Z T u.2))) := by
    filter_upwards [scalarOrthogonalProcesses_finite_path_version W Z f g hf hg T] with u hu
    funext i
    cases i with
    | inl i => exact (hu ⟨t i,(t i).coe_nonneg,ht i⟩).1
    | inr i => exact (hu ⟨t i,(t i).coe_nonneg,ht i⟩).2
  have hright : (J ∘ fun u : Ω × A => (brownianFinitePath W T u.1,brownianFinitePath Z T u.2))=ᵐ[W.law.prod Z.law]
      (fun u : Ω × A => Sum.elim (fun i => W.B (t i) u.1) (fun i => Z.B (t i) u.2)) := by
    filter_upwards [(measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae (brownianFinitePath_version W T),
      (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae (brownianFinitePath_version Z T)] with u huW huZ
    funext i
    cases i with
    | inl i => exact huW ⟨t i,(t i).coe_nonneg,ht i⟩
    | inr i => exact huZ ⟨t i,(t i).coe_nonneg,ht i⟩
  exact (Measure.map_congr hleft).trans (hmap.trans (Measure.map_congr hright))

theorem scalarOrthogonalQueryProcess_isBrownian (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀s∈Ici (0:ℝ),(f s)^2+(g s)^2=1) :
    IsBrownianReal (scalarOrthogonalQueryProcess W Z f g) (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  refine ⟨⟨fun I => ?_⟩,?_⟩
  · let J : (I ⊕ I → ℝ) → I → ℝ := fun z i => z (.inl i)
    have hJ : Measurable J := Measurable.of_eval (fun i => measurable_pi_apply (Sum.inl i : I ⊕ I))
    have hh := scalarOrthogonalProcesses_samples_joint_law W Z f g hf hg hunit (fun i : I => i.val)
    have hms : Measurable (fun u : Ω × A => Sum.elim
        (fun i : I => scalarOrthogonalQueryProcess W Z f g i.val u)
        (fun i : I => scalarOrthogonalAuxProcess W Z f g i.val u)) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact measurable_scalarOrthogonalQueryProcess W Z f g i.val
      | inr i => exact measurable_scalarOrthogonalAuxProcess W Z f g i.val
    have hmr : Measurable (fun u : Ω × A => Sum.elim
        (fun i : I => W.B i.val u.1) (fun i : I => Z.B i.val u.2)) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (W.measurable i.val).comp measurable_fst
      | inr i => exact (Z.measurable i.val).comp measurable_snd
    have hmap := congrArg (fun μ => μ.map J) hh
    rw [Measure.map_map hJ hms,Measure.map_map hJ hmr] at hmap
    have he : (W.law.prod Z.law).map (fun u : Ω × A => I.restrict (scalarOrthogonalQueryProcess W Z f g · u))=
        (W.law.prod Z.law).map (fun u : Ω × A => I.restrict (W.B · u.1)) := by
      simpa only [J,Finset.restrict_def,Function.comp_def,Sum.elim_inl] using hmap
    refine ⟨(Measurable.of_eval (fun i : I => measurable_scalarOrthogonalQueryProcess W Z f g i.val)).aemeasurable,?_⟩
    exact he.trans ((W.brownian.hasLaw I).comp (measurePreserving_fst (μ:=W.law) (ν:=Z.law)).hasLaw).map_eq
  · filter_upwards [(measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae W.driver_continuous,
      (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae Z.driver_continuous] with u huW huZ
    exact (continuous_scalarGlobalStieltjesWeightedProcess f hf W.driver u.1 huW).neg.add
      (continuous_scalarGlobalStieltjesWeightedProcess g hg Z.driver u.2 huZ)

theorem scalarOrthogonalAuxProcess_isBrownian (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀s∈Ici (0:ℝ),(f s)^2+(g s)^2=1) :
    IsBrownianReal (scalarOrthogonalAuxProcess W Z f g) (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  refine ⟨⟨fun I => ?_⟩,?_⟩
  · let J : (I ⊕ I → ℝ) → I → ℝ := fun z i => z (.inr i)
    have hJ : Measurable J := Measurable.of_eval (fun i => measurable_pi_apply (Sum.inr i : I ⊕ I))
    have hh := scalarOrthogonalProcesses_samples_joint_law W Z f g hf hg hunit (fun i : I => i.val)
    have hms : Measurable (fun u : Ω × A => Sum.elim
        (fun i : I => scalarOrthogonalQueryProcess W Z f g i.val u)
        (fun i : I => scalarOrthogonalAuxProcess W Z f g i.val u)) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact measurable_scalarOrthogonalQueryProcess W Z f g i.val
      | inr i => exact measurable_scalarOrthogonalAuxProcess W Z f g i.val
    have hmr : Measurable (fun u : Ω × A => Sum.elim
        (fun i : I => W.B i.val u.1) (fun i : I => Z.B i.val u.2)) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (W.measurable i.val).comp measurable_fst
      | inr i => exact (Z.measurable i.val).comp measurable_snd
    have hmap := congrArg (fun μ => μ.map J) hh
    rw [Measure.map_map hJ hms,Measure.map_map hJ hmr] at hmap
    have he : (W.law.prod Z.law).map (fun u : Ω × A => I.restrict (scalarOrthogonalAuxProcess W Z f g · u))=
        (W.law.prod Z.law).map (fun u : Ω × A => I.restrict (Z.B · u.2)) := by
      simpa only [J,Finset.restrict_def,Function.comp_def,Sum.elim_inr] using hmap
    refine ⟨(Measurable.of_eval (fun i : I => measurable_scalarOrthogonalAuxProcess W Z f g i.val)).aemeasurable,?_⟩
    exact he.trans ((Z.brownian.hasLaw I).comp (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).hasLaw).map_eq
  · filter_upwards [(measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae W.driver_continuous,
      (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae Z.driver_continuous] with u huW huZ
    exact (continuous_scalarGlobalStieltjesWeightedProcess g hg W.driver u.1 huW).add
      (continuous_scalarGlobalStieltjesWeightedProcess f hf Z.driver u.2 huZ)

def actualParisiQueryBrownianSystem (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1<β) : BrownianSystem (Ω × A) where
  law := W.law.prod Z.law
  isProbability := by let := W.isProbability; let := Z.isProbability; infer_instance
  B := scalarOrthogonalQueryProcess W Z (actualParisiNegativeRhoStieltjes W β hβ)
    (actualParisiSigmaStieltjes W β hβ)
  measurable := measurable_scalarOrthogonalQueryProcess W Z _ _
  brownian := scalarOrthogonalQueryProcess_isBrownian W Z _ _
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (fun s _ => actualParisiStieltjesCoefficients_unit W β hβ s)

def actualParisiAuxBrownianSystem (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1<β) : BrownianSystem (Ω × A) where
  law := W.law.prod Z.law
  isProbability := by let := W.isProbability; let := Z.isProbability; infer_instance
  B := scalarOrthogonalAuxProcess W Z (actualParisiNegativeRhoStieltjes W β hβ)
    (actualParisiSigmaStieltjes W β hβ)
  measurable := measurable_scalarOrthogonalAuxProcess W Z _ _
  brownian := scalarOrthogonalAuxProcess_isBrownian W Z _ _
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (fun s _ => actualParisiStieltjesCoefficients_unit W β hβ s)

theorem scalarOrthogonalProcesses_full_joint_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀s∈Ici (0:ℝ),(f s)^2+(g s)^2=1) :
    (W.law.prod Z.law).map (fun u : Ω × A => Sum.elim
      (fun t => scalarOrthogonalQueryProcess W Z f g t u)
      (fun t => scalarOrthogonalAuxProcess W Z f g t u))=
      (W.law.prod Z.law).map (fun u : Ω × A => Sum.elim
        (fun t => W.B t u.1) (fun t => Z.B t u.2)) := by
  let := W.isProbability
  let := Z.isProbability
  let L : Ω × A → (ℝ≥0 ⊕ ℝ≥0) → ℝ := fun u => Sum.elim
    (fun t => scalarOrthogonalQueryProcess W Z f g t u)
    (fun t => scalarOrthogonalAuxProcess W Z f g t u)
  let R : Ω × A → (ℝ≥0 ⊕ ℝ≥0) → ℝ := fun u => Sum.elim
    (fun t => W.B t u.1) (fun t => Z.B t u.2)
  have hL : Measurable L := by
    apply Measurable.of_eval
    intro t
    cases t with
    | inl t => exact measurable_scalarOrthogonalQueryProcess W Z f g t
    | inr t => exact measurable_scalarOrthogonalAuxProcess W Z f g t
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro t
    cases t with
    | inl t => exact (W.measurable t).comp measurable_fst
    | inr t => exact (Z.measurable t).comp measurable_snd
  have he (I : Finset (ℝ≥0 ⊕ ℝ≥0)) :
      (W.law.prod Z.law).map (fun u => I.restrict (L u))=
        (W.law.prod Z.law).map (fun u => I.restrict (R u)) := by
    let t : I → ℝ≥0 := fun i => Sum.elim id id i.val
    let J : (I ⊕ I → ℝ) → I → ℝ := fun z i => match i.val with
      | .inl _ => z (.inl i)
      | .inr _ => z (.inr i)
    have hJ : Measurable J := by
      apply Measurable.of_eval
      intro i
      cases hi : i.val with
      | inl t => simpa only [J,hi] using (measurable_pi_apply (Sum.inl i : I ⊕ I) : Measurable (fun z : I ⊕ I → ℝ => z (.inl i)))
      | inr t => simpa only [J,hi] using (measurable_pi_apply (Sum.inr i : I ⊕ I) : Measurable (fun z : I ⊕ I → ℝ => z (.inr i)))
    have hh := scalarOrthogonalProcesses_samples_joint_law W Z f g hf hg hunit t
    have hms : Measurable (fun u : Ω × A => Sum.elim
        (fun i => scalarOrthogonalQueryProcess W Z f g (t i) u)
        (fun i => scalarOrthogonalAuxProcess W Z f g (t i) u)) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact measurable_scalarOrthogonalQueryProcess W Z f g (t i)
      | inr i => exact measurable_scalarOrthogonalAuxProcess W Z f g (t i)
    have hmr : Measurable (fun u : Ω × A => Sum.elim
        (fun i => W.B (t i) u.1) (fun i => Z.B (t i) u.2)) := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (W.measurable (t i)).comp measurable_fst
      | inr i => exact (Z.measurable (t i)).comp measurable_snd
    have hm := congrArg (fun μ => μ.map J) hh
    rw [Measure.map_map hJ hms,Measure.map_map hJ hmr] at hm
    convert hm using 1 <;> congr 1 <;> funext u i <;> cases hi : i.val <;>
      simp only [L,R,J,t,hi,Finset.restrict_def,Function.comp_def,Sum.elim_inl,Sum.elim_inr,id_eq]
  have hLP : IsProjectiveLimit ((W.law.prod Z.law).map L)
      (fun I => (W.law.prod Z.law).map (fun u => I.restrict (L u))) := isProjectiveLimit_map hL.aemeasurable
  have hRP : IsProjectiveLimit ((W.law.prod Z.law).map R)
      (fun I => (W.law.prod Z.law).map (fun u => I.restrict (L u))) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hR]
    exact (he I).symm
  exact hLP.unique hRP

theorem actualParisiQueryAux_full_joint_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1<β) :
    (W.law.prod Z.law).map (fun u : Ω × A => Sum.elim
      (fun t => (actualParisiQueryBrownianSystem W Z β hβ).B t u)
      (fun t => (actualParisiAuxBrownianSystem W Z β hβ).B t u))=
      (W.law.prod Z.law).map (fun u : Ω × A => Sum.elim
        (fun t => W.B t u.1) (fun t => Z.B t u.2)) :=
  scalarOrthogonalProcesses_full_joint_law W Z _ _
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (fun s _ => actualParisiStieltjesCoefficients_unit W β hβ s)

end SKConstants
