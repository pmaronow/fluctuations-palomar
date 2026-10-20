module
public import SKConstants.ParisiCDFSymmetry
public import SKConstants.ParisiPicardReflection
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Projective

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK

abbrev RealContinuousPath := C(ℝ≥0, ℝ)

theorem exists_measurable_continuousPath_version {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ᵐ w ∂P, Continuous (fun t => B t w)) :
    ∃ F : Ω → RealContinuousPath, Measurable F ∧
      ∀ᵐ w ∂P, ∀ t, F w t = B t w := by
  classical
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let F : Ω → RealContinuousPath := fun w =>
    if hw : w ∈ N then 0 else ⟨fun t => B t w, by
      by_contra h
      exact hw (hN h)⟩
  refine ⟨F, ContinuousMap.measurable_iff_eval.mpr ?_, ?_⟩
  · intro t
    have he : (fun w => F w t) = fun w => if w ∈ N then 0 else B t w := by
      funext w
      dsimp [F]
      split_ifs <;> rfl
    rw [he]
    exact measurable_const.piecewise hNm (hm t)
  · have H : ∀ᵐ w ∂P, w ∉ N := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hN0
    filter_upwards [H] with w hw t
    simp only [F, dite_eq_right hw, ContinuousMap.coe_mk]

theorem continuousPath_measure_ext {μ ν : Measure RealContinuousPath}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset ℝ≥0,
      μ.map (fun p : RealContinuousPath => I.restrict (fun t => p t)) =
        ν.map (fun p : RealContinuousPath => I.restrict (fun t => p t))) : μ = ν := by
  let coePath : RealContinuousPath → (ℝ≥0 → ℝ) := fun p t => p t
  have hm : Measurable coePath := .of_eval fun t => ContinuousMap.measurable_eval t
  have hmap : μ.map coePath = ν.map coePath := by
    have hμ : IsProjectiveLimit (μ.map coePath)
        (fun I : Finset ℝ≥0 => μ.map (fun p : RealContinuousPath => I.restrict (fun t => p t))) := by
      intro I
      rw [Measure.map_map (by fun_prop) hm]
      rfl
    have hν : IsProjectiveLimit (ν.map coePath)
        (fun I : Finset ℝ≥0 => μ.map (fun p : RealContinuousPath => I.restrict (fun t => p t))) := by
      intro I
      rw [Measure.map_map (by fun_prop) hm]
      exact (h I).symm
    exact hμ.unique hν
  have hsigma : (inferInstance : MeasurableSpace RealContinuousPath) =
      MeasurableSpace.comap coePath (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) := by
    change borel RealContinuousPath = _
    rw [ContinuousMap.borel_eq_iSup_comap_eval, MeasurableSpace.pi,
      MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    rfl
  apply Measure.ext
  intro s hs
  change MeasurableSet[(inferInstance : MeasurableSpace RealContinuousPath)] s at hs
  rw [hsigma] at hs
  obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  rw [← Measure.map_apply hm hu, ← Measure.map_apply hm hu, hmap]

theorem brownian_continuousPath_law_neg {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (F : Ω → RealContinuousPath) (hF : Measurable F)
    (he : ∀ᵐ w ∂W.law, ∀ t, F w t = W.B t w) :
    (W.law.map F).map (fun p : RealContinuousPath => -p) = W.law.map F := by
  let := W.isProbability
  apply continuousPath_measure_ext
  intro I
  have hm : Measurable (fun p : RealContinuousPath => I.restrict (fun t => p t)) :=
    .of_eval fun t => ContinuousMap.measurable_eval t.1
  rw [Measure.map_map hm (by fun_prop), Measure.map_map (hm.comp (by fun_prop)) hF,
    Measure.map_map hm hF]
  have hpos := (W.brownian.hasLaw I).map_eq
  have hneg := (W.brownian.neg.hasLaw I).map_eq
  change W.law.map (fun w => I.restrict (fun t => -W.B t w)) =
    BrownianReal.projectiveFamily I at hneg
  have hp : (fun w => I.restrict (fun t => F w t)) =ᵐ[W.law]
      (fun w => I.restrict (fun t => W.B t w)) := by
    filter_upwards [he] with w hw
    funext t
    exact hw t
  have hn : (fun w => I.restrict (fun t => (-F w) t)) =ᵐ[W.law]
      (fun w => I.restrict (fun t => -W.B t w)) := by
    filter_upwards [he] with w hw
    funext t
    simp only [ContinuousMap.neg_apply, hw]
  change W.law.map (fun w => I.restrict (fun t => (-F w) t)) =
    W.law.map (fun w => I.restrict (fun t => F w t))
  rw [Measure.map_congr hn, Measure.map_congr hp, hneg, hpos]

def continuousPathEvaluation (v : ℝ≥0) (p : RealContinuousPath) : ℝ := p v

def continuousPathFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace RealContinuousPath) :=
  Filtration.natural continuousPathEvaluation
    (fun v => (ContinuousMap.measurable_eval v).stronglyMeasurable)

theorem continuousPathEvaluation_progressive :
    IsProgressive continuousPathFiltration continuousPathEvaluation := by
  exact (Filtration.stronglyAdapted_natural
    (fun v => (ContinuousMap.measurable_eval v).stronglyMeasurable)).isStronglyProgressive_of_continuous
      (fun p => p.continuous) |>.isProgressive

def picardPathEndpoint (b : BoundedLipschitzDrift) (v : ℝ≥0) (p : RealContinuousPath) : ℝ :=
  b.solution continuousPathEvaluation v p

theorem picardPathEndpoint_measurable (b : BoundedLipschitzDrift) (v : ℝ≥0) :
    Measurable (picardPathEndpoint b v) :=
  ((b.solution_progressive continuousPathFiltration continuousPathEvaluation_progressive).adapted v).mono
    (continuousPathFiltration.le v) le_rfl

theorem picardPathEndpoint_odd (b : BoundedLipschitzDrift)
    (ho : ∀ v, Function.Odd (b.f v)) (v : ℝ≥0) :
    Function.Odd (picardPathEndpoint b v) := by
  intro p
  change b.solution continuousPathEvaluation v (-p) = -b.solution continuousPathEvaluation v p
  calc
    b.solution continuousPathEvaluation v (-p) =
        b.solution (fun t q => -continuousPathEvaluation t q) v p :=
      solution_congr_path b _ _ (-p) p (fun t => rfl) v
    _ = _ := solution_neg_of_odd b ho continuousPathFiltration _
      continuousPathEvaluation_progressive v p

theorem boundedOddDrift_seedLaw_neg {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (ho : ∀ v, Function.Odd (b.f v)) (v : ℝ≥0) :
    (W.law.map (b.solution W.driver v)).map (fun x : ℝ => -x) =
      W.law.map (b.solution W.driver v) := by
  let := W.isProbability
  obtain ⟨F, hF, he⟩ := exists_measurable_continuousPath_version W.law W.B W.measurable W.brownian.cont
  have heDriver : ∀ᵐ w ∂W.law, ∀ t, F w t = W.driver t w := by
    filter_upwards [he, W.driver_indistinguishable] with w hw hd t
    rw [hw, hd]
  have hendpoint : (b.solution W.driver v) =ᵐ[W.law] (fun w => picardPathEndpoint b v (F w)) := by
    filter_upwards [heDriver] with w hw
    exact solution_congr_path b W.driver continuousPathEvaluation w (F w) (fun t => (hw t).symm) v
  have hΦ := picardPathEndpoint_measurable b v
  have hν : W.law.map (b.solution W.driver v) = (W.law.map F).map (picardPathEndpoint b v) := by
    rw [Measure.map_map hΦ hF]
    exact Measure.map_congr hendpoint
  rw [hν, Measure.map_map (by fun_prop) hΦ]
  have hcomp : (fun p : RealContinuousPath => -(picardPathEndpoint b v p)) =
      (fun p => picardPathEndpoint b v (-p)) :=
    funext (fun p => (picardPathEndpoint_odd b ho v p).symm)
  change (W.law.map F).map (fun p : RealContinuousPath => -(picardPathEndpoint b v p)) = _
  rw [hcomp]
  change (W.law.map F).map ((picardPathEndpoint b v) ∘ (fun p : RealContinuousPath => -p)) = _
  rw [← Measure.map_map hΦ (show Measurable (fun p : RealContinuousPath => -p) by fun_prop),
    brownian_continuousPath_law_neg W F hF he]

theorem boundedOddDrift_seed_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (ho : ∀ v, Function.Odd (b.f v)) (v : ℝ≥0) :
    ∫ w, b.solution W.driver v w ∂W.law = 0 := by
  have hs := boundedOddDrift_seedLaw_neg W b ho v
  have hm := b.solution_measurable W v
  have H := congrArg (fun ν : Measure ℝ => ∫ x, x ∂ν) hs
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map hm.aemeasurable (by fun_prop),
    integral_map hm.aemeasurable (by fun_prop), integral_neg] at H
  linarith

theorem finiteTemperatureCDFProcess_seedLaw_neg {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (v : ℝ≥0) :
    (W.law.map (ParisiFullSupport.finiteTemperatureCDFProcess W β α ha h1 v)).map
        (fun x : ℝ => -x) =
      W.law.map (ParisiFullSupport.finiteTemperatureCDFProcess W β α ha h1 v) :=
  boundedOddDrift_seedLaw_neg W (ParisiFullSupport.finiteTemperatureCDFDrift β α ha h1)
    (finiteTemperatureCDFDrift_odd β α ha h1) v

theorem finiteTemperatureCDFProcess_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (v : ℝ≥0) :
    ∫ w, ParisiFullSupport.finiteTemperatureCDFProcess W β α ha h1 v w ∂W.law = 0 :=
  boundedOddDrift_seed_integral_zero W (ParisiFullSupport.finiteTemperatureCDFDrift β α ha h1)
    (finiteTemperatureCDFDrift_odd β α ha h1) v

theorem integral_odd_eq_zero_of_map_neg (μ : Measure ℝ)
    (hs : μ.map (fun x : ℝ => -x) = μ) (f : ℝ → ℝ)
    (hf : Continuous f) (ho : Function.Odd f) : ∫ x, f x ∂μ = 0 := by
  have H := congrArg (fun ν : Measure ℝ => ∫ x, f x ∂ν) hs
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable] at H
  have he : (fun x : ℝ => f (-x)) = fun x => -f x := funext ho
  change (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ at H
  rw [he, integral_neg] at H
  linarith

theorem finiteTemperatureCDFProcess_tanh_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (v : ℝ≥0) :
    ∫ w, Real.tanh (ParisiFullSupport.finiteTemperatureCDFProcess W β α ha h1 v w)
      ∂W.law = 0 := by
  have htanh : Continuous Real.tanh := by
    have he : Real.tanh = Real.sinh / Real.cosh :=
      funext Real.tanh_eq_sinh_div_cosh
    rw [he]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have H := integral_odd_eq_zero_of_map_neg
    (W.law.map (ParisiFullSupport.finiteTemperatureCDFProcess W β α ha h1 v))
    (finiteTemperatureCDFProcess_seedLaw_neg W β α ha h1 v) Real.tanh
    htanh Real.tanh_neg
  rw [integral_map
    (ParisiFullSupport.finiteTemperatureCDFProcess_measurable W β α ha h1 v).aemeasurable
    htanh.aestronglyMeasurable] at H
  exact H

end SKConstants
