module

public import SKConstants.Completion.LM4b.ActualNoise
public import SKConstants.ScalarOrthogonalDriverMarkov

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology
namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto LM4 LC1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem brownianFinitePathFromPast_ae (W : BrownianSystem Ω) (T : ℝ≥0) :
    (fun w => scalarPathFromPast T (brownianFullPast W.B T w)) =ᵐ[W.law] brownianFinitePath W T := by
  filter_upwards [brownianFinitePath_version W T] with w hw
  unfold scalarPathFromPast brownianFullPast
  have he : (fun k => W.B ⟨scalarPathDenseTimes T k,(scalarPathDenseTimes T k).property.1⟩ w) =
      scalarPathDenseSamples T (brownianFinitePath W T w) := by
    funext k
    exact (hw (scalarPathDenseTimes T k)).symm
  rw [he]
  exact scalarPathFromDenseSamples_leftInverse T _

theorem indepFun_comp_measurePreserving {X Y E F : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {r : X → Y} (hr : MeasurePreserving r μ ν)
    {f : Y → E} {g : Y → F} (hf : Measurable f) (hg : Measurable g) (hi : IndepFun f g ν) :
    IndepFun (f ∘ r) (g ∘ r) μ := by
  have hfL : HasLaw f (ν.map f) ν := ⟨hf.aemeasurable,rfl⟩
  have hgL : HasLaw g (ν.map g) ν := ⟨hg.aemeasurable,rfl⟩
  exact (indepFun_iff_hasLaw_prodMk_prod (hfL.comp hr.hasLaw) (hgL.comp hr.hasLaw)).2
    ((hi.hasLaw_prod hfL hgL).comp hr.hasLaw)

theorem actualQueryIncrement_indep_rowPast (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    IndepFun (fun u : (Bool × Ω) × A => (u.1.1,
      (brownianFinitePath W (t n) u.1.2,brownianFinitePath Z (t n) u.2)))
      (actualNoiseIncrement W Z β hβ t n) (actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  let T := t n
  let Δ := t (n+1)-t n
  have he : T+Δ=t (n+1) := add_tsub_cancel_of_le (ht (Nat.le_succ n))
  have hi := (actualParisiQuery_future_indep_originalPast W Z β hβ T).symm.comp
    ((measurable_scalarPathFromPast T).prodMap (measurable_scalarPathFromPast T))
    (measurable_pi_apply Δ)
  have hp : IndepFun (fun u : Ω × A =>
      (brownianFinitePath W T u.1,brownianFinitePath Z T u.2))
      (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t n)
      (W.law.prod Z.law) := by
    apply hi.congr
    · filter_upwards [(measurePreserving_fst (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae
        (brownianFinitePathFromPast_ae W T),
      (measurePreserving_snd (μ:=W.law) (ν:=Z.law)).quasiMeasurePreserving.ae
        (brownianFinitePathFromPast_ae Z T)] with u huW huZ
      exact Prod.ext huW huZ
    · exact ae_of_all _ (fun u => by dsimp only [Function.comp_def]; rw [he]; rfl)
  have hmP : Measurable (fun u : Ω × A => (brownianFinitePath W T u.1,brownianFinitePath Z T u.2)) :=
    (measurable_brownianFinitePath W T).prodMap (measurable_brownianFinitePath Z T)
  have hmX : Measurable (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t n) :=
    ((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
      ((actualParisiQueryBrownianSystem W Z β hβ).measurable _)
  have hs := indepFun_static_prod_left (scalarHiddenPriorBool 0) (W.law.prod Z.law)
    hmP.aemeasurable hmX.aemeasurable hp
  exact indepFun_comp_measurePreserving (measurePreserving_prodAssoc (scalarHiddenPriorBool 0) W.law Z.law)
    (measurable_fst.prodMk (hmP.comp measurable_snd)) (hmX.comp measurable_snd) hs

def pastMagnetization (β : ℝ) (T s : ℝ≥0) (p : ScalarContinuousPath T) : ℝ :=
  actualParisiFullMagnetization β s
    (IccExtend T.coe_nonneg (scalarForwardPicardPath (actualParisiFullScalarDrift β) T (0,p)) s)

def pastQuery (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T s : ℝ≥0)
    (p : ScalarContinuousPath T × ScalarContinuousPath T) : ℝ :=
  IccExtend T.coe_nonneg (scalarTwoDriverWeightedPath
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) T p) s

theorem measurable_pastMagnetization (β : ℝ) (T s : ℝ≥0) : Measurable (pastMagnetization β T s) := by
  have hY : Measurable (fun p : ScalarContinuousPath T =>
      scalarForwardPicardPath (actualParisiFullScalarDrift β) T (0,p)) :=
    (measurable_scalarForwardPicardPath (actualParisiFullScalarDrift β) T).comp
      ((measurable_const (a:=(0:ℝ))).prodMk measurable_id)
  have hEval : Measurable (fun p : ScalarContinuousPath T =>
      (scalarForwardPicardPath (actualParisiFullScalarDrift β) T (0,p))
        (projIcc 0 (T:ℝ) T.coe_nonneg (s:ℝ))) := (ContinuousMap.measurable_eval _).comp hY
  exact ((continuous_actualParisiFullMagnetization β).comp
    ((continuous_const : Continuous (fun _ : ℝ => (s:ℝ))).prodMk continuous_id)).measurable.comp hEval

theorem measurable_pastQuery (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T s : ℝ≥0) :
    Measurable (pastQuery W β hβ T s) :=
  (ContinuousMap.measurable_eval (projIcc 0 (T:ℝ) T.coe_nonneg (s:ℝ))).comp
    (measurable_scalarTwoDriverWeightedPath _ _ _ _ T)

def noisePastCoefficient (β : ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n j : ℕ)
    (p : Bool × (ScalarContinuousPath (t n) × ScalarContinuousPath (t n))) : ℝ :=
  c j * (scalarHiddenSign p.1 - pastMagnetization β (t n) (t j) p.2.1)

def noisePastState (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (p : Bool × (ScalarContinuousPath (t n) × ScalarContinuousPath (t n))) : ℝ × ℝ × ℝ :=
  ((∑ j ∈ Finset.range n, noisePastCoefficient β t c n j p *
      (pastQuery W β hβ (t n) (t (j+1)) p.2-pastQuery W β hβ (t n) (t j) p.2)),
    noisePastCoefficient β t c n n p,
    ∑ j ∈ Finset.range n, (noisePastCoefficient β t c n j p)^2 * (brownianMeshVariance t j : ℝ))

theorem measurable_noisePastState (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) : Measurable (noisePastState W β hβ t c n) := by
  have hC (j : ℕ) : Measurable (noisePastCoefficient β t c n j) :=
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub
      ((measurable_pastMagnetization β (t n) (t j)).comp (measurable_fst.comp measurable_snd))).const_mul _
  have hB (j : ℕ) : Measurable (fun p : Bool × (ScalarContinuousPath (t n) × ScalarContinuousPath (t n)) =>
      pastQuery W β hβ (t n) (t j) p.2) :=
    (measurable_pastQuery W β hβ (t n) (t j)).comp measurable_snd
  exact (Finset.measurable_fun_sum _ (fun j _ => (hC j).mul ((hB (j+1)).sub (hB j)))).prodMk
    ((hC n).prodMk (Finset.measurable_fun_sum _ (fun j _ => ((hC j).pow_const 2).mul_const _)))

theorem actualQueryPredictableState (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) :
    ActualQueryPredictableStateStatement W Z β hβ t c := by
  let := W.isProbability
  let := Z.isProbability
  intro n
  have hi := (actualQueryIncrement_indep_rowPast W Z β hβ t ht n).comp
    (measurable_noisePastState W β hβ t c n) measurable_id
  apply hi.congr _ (ae_of_all _ (fun _ => rfl))
  have hW := (measurePreserving_snd (μ:=scalarHiddenPriorBool 0) (ν:=W.law)).comp
    (measurePreserving_fst (μ:=(scalarHiddenPriorBool 0).prod W.law) (ν:=Z.law))
  have hpair := (measurePreserving_snd (μ:=scalarHiddenPriorBool 0) (ν:=W.law)).prod
    (MeasurePreserving.id Z.law)
  filter_upwards [hW.quasiMeasurePreserving.ae
      (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) (t n)),
    hpair.quasiMeasurePreserving.ae (scalarOrthogonalProcesses_finite_path_version W Z
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (t n))] with u huY huB
  have hC (j : ℕ) (hj : j ≤ n) :
      noisePastCoefficient β t c n j (u.1.1,(brownianFinitePath W (t n) u.1.2,brownianFinitePath Z (t n) u.2)) =
        actualNoiseCoefficient W β t c j u := by
    have hs : (t j:ℝ) ∈ Icc 0 (t n:ℝ) := ⟨(t j).coe_nonneg, NNReal.coe_le_coe.mpr (ht hj)⟩
    simp only [noisePastCoefficient, actualNoiseCoefficient, pastMagnetization,
      IccExtend, Function.comp_def, projIcc_of_mem _ hs]
    have hy := huY ⟨t j,hs⟩
    change (scalarForwardPicardPath (actualParisiFullScalarDrift β) (t n)
      (0,brownianFinitePath W (t n) u.1.2)) ⟨t j,hs⟩ = actualParisiFullScalarProcess W β (t j) u.1.2 at hy
    rw [hy]
    rfl
  have hB (j : ℕ) (hj : j ≤ n) :
      pastQuery W β hβ (t n) (t j) (brownianFinitePath W (t n) u.1.2,brownianFinitePath Z (t n) u.2) =
        (actualParisiQueryBrownianSystem W Z β hβ).B (t j) (u.1.2,u.2) := by
    have hs : (t j:ℝ) ∈ Icc 0 (t n:ℝ) := ⟨(t j).coe_nonneg, NNReal.coe_le_coe.mpr (ht hj)⟩
    simp only [pastQuery,IccExtend,Function.comp_def,projIcc_of_mem _ hs]
    exact (huB ⟨t j,hs⟩).1.symm
  change noisePastState W β hβ t c n _ = _
  unfold noisePastState actualNoise
  rw [predictableGaussianSum_eq_range_sum, predictableGaussianVariation_eq_range_sum]
  dsimp only [Function.comp_def]
  apply Prod.ext
  · dsimp only
    apply Finset.sum_congr rfl
    intro j hj
    rw [hC j (Finset.mem_range.mp hj).le, hB j (Finset.mem_range.mp hj).le,
      hB (j+1) (Finset.mem_range.mp hj)]
    rfl
  · apply Prod.ext
    · exact hC n le_rfl
    · dsimp only
      apply Finset.sum_congr rfl
      intro j hj
      rw [hC j (Finset.mem_range.mp hj).le]

end SKConstants.Completion.LM4b
