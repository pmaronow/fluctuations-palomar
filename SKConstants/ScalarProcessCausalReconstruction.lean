module
public import SKConstants.ScalarProcessContinuous
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Bases
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SKConstants

theorem hasDerivAt_scalarTanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - (Real.tanh x)^2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have he : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      Real.cosh x ^ 2 = 1 - Real.tanh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [he] at h
  convert h using 1
  ext u
  exact Real.tanh_eq_sinh_div_cosh u

theorem lipschitzWith_scalarTanh : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_scalarTanh x).differentiableAt)
  intro x
  rw [(hasDerivAt_scalarTanh x).deriv]
  change ‖1 - Real.tanh x ^ 2‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.tanh_sq_lt_one x])]
  linarith [sq_nonneg (Real.tanh x)]

theorem scalarVolterra_unique {f g : ℝ → ℝ} {z T : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ t ∈ Icc 0 T,
      f t - z - (∫ s in (0 : ℝ)..t, Real.tanh (f s)) =
      g t - z - (∫ s in (0 : ℝ)..t, Real.tanh (g s))) :
    ∀ t ∈ Icc 0 T, f t = g t := by
  let d : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, Real.tanh (f s)) -
    (∫ s in (0 : ℝ)..t, Real.tanh (g s))
  have htf : Continuous (fun s => Real.tanh (f s)) := lipschitzWith_scalarTanh.continuous.comp hf
  have htg : Continuous (fun s => Real.tanh (g s)) := lipschitzWith_scalarTanh.continuous.comp hg
  have hd : ∀ t ∈ Icc 0 T, d t = f t - g t := by
    intro t ht
    dsimp [d]
    linarith [heq t ht]
  have hd' : ∀ t, HasDerivAt d (Real.tanh (f t) - Real.tanh (g t)) t := by
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right (htf.intervalIntegrable _ _)
      htf.aestronglyMeasurable.stronglyMeasurableAtFilter htf.continuousAt).sub
      (intervalIntegral.integral_hasDerivAt_right (htg.intervalIntegrable _ _)
        htg.aestronglyMeasurable.stronglyMeasurableAtFilter htg.continuousAt)
  have hzero : ∀ t ∈ Icc 0 T, d t = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (K := 1)
      (show ContinuousOn d (Icc 0 T) from
        (continuous_iff_continuousAt.2 (fun t => (hd' t).continuousAt)).continuousOn)
      (fun t _ => (hd' t).hasDerivWithinAt)
      (by simp [d]) (by
        intro t ht
        have h := lipschitzWith_scalarTanh.norm_sub_le (f t) (g t)
        simpa [hd t ⟨ht.1, ht.2.le⟩] using h)
  intro t ht
  have := hzero t ht
  rw [hd t ht] at this
  exact sub_eq_zero.mp this

abbrev ScalarContinuousPath (T : ℝ≥0) := C(Icc (0 : ℝ) (T : ℝ), ℝ)

def scalarInnovationPath (T : ℝ≥0) (z : ℝ) (f : ScalarContinuousPath T) :
    ScalarContinuousPath T where
  toFun t := f t - z - ∫ s in (0 : ℝ)..(t : ℝ),
    Real.tanh (IccExtend T.coe_nonneg f s)
  continuous_toFun := (f.continuous.sub continuous_const).sub
    ((intervalIntegral.differentiable_integral_of_continuous
      (lipschitzWith_scalarTanh.continuous.comp f.continuous.Icc_extend')).continuous.comp
        continuous_subtype_val)

theorem scalarInnovationPath_injective (T : ℝ≥0) (z : ℝ) :
    Function.Injective (scalarInnovationPath T z) := by
  intro f g he
  have heq : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      IccExtend T.coe_nonneg f t - z -
        (∫ s in (0 : ℝ)..t, Real.tanh (IccExtend T.coe_nonneg f s)) =
      IccExtend T.coe_nonneg g t - z -
        (∫ s in (0 : ℝ)..t, Real.tanh (IccExtend T.coe_nonneg g s)) := by
    intro t ht
    have hh := congrArg (fun p : ScalarContinuousPath T => p ⟨t, ht⟩) he
    change f ⟨t, ht⟩ - z - (∫ s in (0 : ℝ)..t,
      Real.tanh (IccExtend T.coe_nonneg f s)) =
      g ⟨t, ht⟩ - z - (∫ s in (0 : ℝ)..t,
      Real.tanh (IccExtend T.coe_nonneg g s)) at hh
    simpa only [IccExtend, Function.comp_apply,
      projIcc_of_mem _ ht] using hh
  ext t
  have hh := scalarVolterra_unique f.continuous.Icc_extend' g.continuous.Icc_extend' heq t t.2
  simpa only [IccExtend, Function.comp_apply, projIcc_val] using hh

theorem measurable_scalarInnovationPath (T : ℝ≥0) (z : ℝ) :
    Measurable (scalarInnovationPath T z) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  have hc : Continuous (fun p : ScalarContinuousPath T × ℝ =>
      IccExtend T.coe_nonneg p.1 p.2) := by
    exact continuous_eval.comp (continuous_fst.prodMk
      ((continuous_projIcc (h := T.coe_nonneg)).comp continuous_snd))
  have hm := (lipschitzWith_scalarTanh.continuous.comp hc).measurable.stronglyMeasurable
  have hi := hm.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
  have he : (fun f : ScalarContinuousPath T => scalarInnovationPath T z f t) =
      fun (f : ScalarContinuousPath T) => f t - z - ∫ s in Ioc (0 : ℝ) (t : ℝ),
        Real.tanh (IccExtend T.coe_nonneg f s) := by
    funext f
    exact congrArg (fun q => f t - z - q)
      (intervalIntegral.integral_of_le t.property.1)
  rw [he]
  exact ((ContinuousMap.measurable_eval t).sub measurable_const).sub hi.measurable

theorem scalarInnovationPath_measurableEmbedding (T : ℝ≥0) (z : ℝ) :
    MeasurableEmbedding (scalarInnovationPath T z) :=
  (measurable_scalarInnovationPath T z).measurableEmbedding
    (scalarInnovationPath_injective T z)

theorem scalarInnovationPath_comap_eq {Ω : Type*} (T : ℝ≥0) (z : ℝ)
    (Y : Ω → ScalarContinuousPath T) :
    MeasurableSpace.comap (fun ω => scalarInnovationPath T z (Y ω)) inferInstance =
      MeasurableSpace.comap Y inferInstance := by
  change MeasurableSpace.comap ((scalarInnovationPath T z) ∘ Y) _ = _
  rw [← MeasurableSpace.comap_comp,
    (scalarInnovationPath_measurableEmbedding T z).comap_eq]

def scalarObservationPathFromInnovation (T : ℝ≥0) (z : ℝ) :
    ScalarContinuousPath T → ScalarContinuousPath T :=
  (scalarInnovationPath_measurableEmbedding T z).invFun

theorem measurable_scalarObservationPathFromInnovation (T : ℝ≥0) (z : ℝ) :
    Measurable (scalarObservationPathFromInnovation T z) :=
  (scalarInnovationPath_measurableEmbedding T z).measurable_invFun

theorem scalarObservationPathFromInnovation_leftInverse (T : ℝ≥0) (z : ℝ) :
    Function.LeftInverse (scalarObservationPathFromInnovation T z) (scalarInnovationPath T z) :=
  (scalarInnovationPath_measurableEmbedding T z).leftInverse_invFun

def scalarContinuousPathRestriction (T : ℝ≥0) (Y : ℝ → ℝ) (hY : Continuous Y) :
    ScalarContinuousPath T := ⟨fun t => Y t, hY.comp continuous_subtype_val⟩

theorem scalarInnovationPath_restriction (T : ℝ≥0) (z : ℝ) (Y : ℝ → ℝ)
    (hY : Continuous Y) (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarInnovationPath T z (scalarContinuousPathRestriction T Y hY) t =
      Y t - z - ∫ s in (0 : ℝ)..(t : ℝ), Real.tanh (Y s) := by
  change Y t - z - (∫ s in (0 : ℝ)..(t : ℝ),
    Real.tanh (IccExtend T.coe_nonneg (scalarContinuousPathRestriction T Y hY) s)) = _
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  have hsT : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs.1, hs.2.trans t.property.2⟩
  simp only [IccExtend, Function.comp_apply, projIcc_of_mem _ hsT]
  rfl

theorem scalarObservationPath_reconstruction (T : ℝ≥0) (z : ℝ) (Y : ℝ → ℝ)
    (hY : Continuous Y) (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarObservationPathFromInnovation T z
      (scalarInnovationPath T z (scalarContinuousPathRestriction T Y hY)) t = Y t := by
  rw [scalarObservationPathFromInnovation_leftInverse]
  rfl

theorem scalarInnovationPath_hiddenField_eq {Ω : Type*} (T : ℝ≥0) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (u : Bool × Ω) (hB : Continuous (fun t => B t u.2))
    (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarInnovationPath T z
      (scalarContinuousPathRestriction T (fun s => scalarHiddenFieldReal z B s u)
        (continuous_scalarHiddenFieldReal z B u hB)) t =
      scalarContinuousInnovation z B ⟨t, t.property.1⟩ u := by
  rw [scalarInnovationPath_restriction]
  unfold scalarContinuousInnovation scalarContinuousDrift
  change scalarHiddenFieldReal z B (t : ℝ) u - z -
      (∫ s in (0 : ℝ)..(t : ℝ), Real.tanh (scalarHiddenFieldReal z B s u)) =
    scalarHiddenContinuousField z B ⟨t, t.property.1⟩ u - z -
      ∫ s in Icc (0 : ℝ) (t : ℝ), Real.tanh (scalarHiddenFieldReal z B s u)
  rw [intervalIntegral.integral_of_le t.property.1, integral_Icc_eq_integral_Ioc]
  congr 2
  unfold scalarHiddenFieldReal scalarHiddenContinuousField
  simp only [Real.toNNReal_of_nonneg t.property.1]
  rfl

theorem scalarInnovationPath_past_comap_eq {Ω : Type*} (T : ℝ≥0) (z : ℝ)
    (Y : Ω → ScalarContinuousPath T) :
    (⨆ t : Icc (0 : ℝ) (T : ℝ),
      MeasurableSpace.comap (fun ω => scalarInnovationPath T z (Y ω) t) (borel ℝ)) =
    ⨆ t : Icc (0 : ℝ) (T : ℝ),
      MeasurableSpace.comap (fun ω => Y ω t) (borel ℝ) := by
  have he := scalarInnovationPath_comap_eq T z Y
  simp_rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval,
    MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def] at he
  exact he

theorem exists_measurable_scalarPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (Y : ℝ → Ω → ℝ)
    (hY : ∀ s, Measurable (Y s))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun s => Y s ω)) :
    ∃ paths : Ω → ScalarContinuousPath T, Measurable paths ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ), paths ω t = Y t ω := by
  obtain ⟨good, hgood, hgoodm, hgoodc⟩ := hcont.exists_measurable_mem
  classical
  let paths : Ω → ScalarContinuousPath T := fun ω =>
    if hw : ω ∈ good then scalarContinuousPathRestriction T (fun s => Y s ω) (hgoodc ω hw)
    else ContinuousMap.const _ 0
  refine ⟨paths, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.2
    intro t
    have he : (fun ω => paths ω t) = good.indicator (Y t) := by
      funext ω
      by_cases hw : ω ∈ good <;> simp [paths, hw, scalarContinuousPathRestriction]
    rw [he]
    exact (hY t).indicator hgoodm
  · filter_upwards [hgood] with ω hw
    intro t
    simp [paths, hw, scalarContinuousPathRestriction]

theorem scalarHiddenBrownian_measurable_pathVersions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBmeas : Measurable (Function.uncurry B)) :
    ∃ Ypaths Mpaths : Bool × Ω → ScalarContinuousPath T,
      Measurable Ypaths ∧ Measurable Mpaths ∧
      (∀ u, Mpaths u = scalarInnovationPath T z (Ypaths u)) ∧
      (∀ᵐ u ∂scalarHiddenBrownianLaw z P,
        ∀ t : Icc (0 : ℝ) (T : ℝ),
          Ypaths u t = scalarHiddenContinuousField z B ⟨t, t.property.1⟩ u ∧
          Mpaths u t = scalarContinuousInnovation z B ⟨t, t.property.1⟩ u) ∧
      MeasurableSpace.comap Ypaths inferInstance =
        MeasurableSpace.comap Mpaths inferInstance := by
  have hcontB : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hcontY : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun s => scalarHiddenFieldReal z B s u) :=
    hcontB.mono (fun u hu => continuous_scalarHiddenFieldReal z B u hu)
  have hmY : ∀ s, Measurable (scalarHiddenFieldReal z B s) := by
    intro s
    exact (measurable_scalarHiddenFieldReal z B hBmeas).comp
      (measurable_const.prodMk measurable_id)
  obtain ⟨Ypaths, hYm, hYe⟩ := exists_measurable_scalarPathVersion
    (scalarHiddenBrownianLaw z P) T (scalarHiddenFieldReal z B) hmY hcontY
  let Mpaths := fun u => scalarInnovationPath T z (Ypaths u)
  refine ⟨Ypaths, Mpaths, hYm, (measurable_scalarInnovationPath T z).comp hYm,
    fun _ => rfl, ?_, ?_⟩
  · filter_upwards [hYe, hcontB] with u hu hc
    have hpath : Ypaths u = scalarContinuousPathRestriction T
        (fun s => scalarHiddenFieldReal z B s u)
        (continuous_scalarHiddenFieldReal z B u hc) := by
      ext t
      exact hu t
    intro t
    constructor
    · rw [hu t]
      unfold scalarHiddenFieldReal scalarHiddenContinuousField
      simp only [Real.toNNReal_of_nonneg t.property.1]
      rfl
    · change scalarInnovationPath T z (Ypaths u) t = _
      rw [hpath]
      exact scalarInnovationPath_hiddenField_eq T z B u hc t
  · exact (scalarInnovationPath_comap_eq T z Ypaths).symm

theorem indepFun_scalarObservationPath_of_innovation {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) (T : ℝ≥0) (z : ℝ)
    (Ypaths : Ω → ScalarContinuousPath T) (X : Ω → E)
    (h : IndepFun X (fun ω => scalarInnovationPath T z (Ypaths ω)) P) :
    IndepFun X Ypaths P := by
  have he : scalarObservationPathFromInnovation T z ∘
      (fun ω => scalarInnovationPath T z (Ypaths ω)) = Ypaths := by
    funext ω
    exact scalarObservationPathFromInnovation_leftInverse T z (Ypaths ω)
  have hi := h.comp (φ := id) (ψ := scalarObservationPathFromInnovation T z)
    measurable_id (measurable_scalarObservationPathFromInnovation T z)
  simpa only [Function.id_comp, he] using hi

theorem indepFun_scalarObservationStatistic_of_innovation {Ω E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Ω) (T : ℝ≥0) (z : ℝ) (Ypaths : Ω → ScalarContinuousPath T)
    (X : Ω → E) (Φ : ScalarContinuousPath T → F) (hΦ : Measurable Φ)
    (h : IndepFun X (fun ω => scalarInnovationPath T z (Ypaths ω)) P) :
    IndepFun X (fun ω => Φ (Ypaths ω)) P := by
  exact (indepFun_scalarObservationPath_of_innovation P T z Ypaths X h).comp
    measurable_id hΦ

def scalarPathDenseTimes (T : ℝ≥0) : ℕ → Icc (0 : ℝ) (T : ℝ) := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  exact TopologicalSpace.denseSeq (Icc (0 : ℝ) (T : ℝ))

theorem denseRange_scalarPathDenseTimes (T : ℝ≥0) : DenseRange (scalarPathDenseTimes T) := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  exact TopologicalSpace.denseRange_denseSeq _

def scalarPathDenseSamples (T : ℝ≥0) (f : ScalarContinuousPath T) : ℕ → ℝ :=
  fun k => f (scalarPathDenseTimes T k)

theorem scalarPathDenseSamples_measurableEmbedding (T : ℝ≥0) :
    MeasurableEmbedding (scalarPathDenseSamples T) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun k => ContinuousMap.measurable_eval _)
  · intro f g he
    have he' : (f : Icc (0 : ℝ) (T : ℝ) → ℝ) ∘ scalarPathDenseTimes T =
        (g : Icc (0 : ℝ) (T : ℝ) → ℝ) ∘ scalarPathDenseTimes T := he
    have heq := (denseRange_scalarPathDenseTimes T).equalizer f.continuous g.continuous he'
    exact ContinuousMap.coe_injective heq

def scalarPathFromDenseSamples (T : ℝ≥0) : (ℕ → ℝ) → ScalarContinuousPath T :=
  (scalarPathDenseSamples_measurableEmbedding T).invFun

theorem measurable_scalarPathFromDenseSamples (T : ℝ≥0) :
    Measurable (scalarPathFromDenseSamples T) :=
  (scalarPathDenseSamples_measurableEmbedding T).measurable_invFun

theorem scalarPathFromDenseSamples_leftInverse (T : ℝ≥0) :
    Function.LeftInverse (scalarPathFromDenseSamples T) (scalarPathDenseSamples T) :=
  (scalarPathDenseSamples_measurableEmbedding T).leftInverse_invFun

def scalarPathFromPast (T : ℝ≥0) (w : Iic T → ℝ) : ScalarContinuousPath T :=
  scalarPathFromDenseSamples T (fun k => w
    ⟨⟨scalarPathDenseTimes T k, (scalarPathDenseTimes T k).property.1⟩,
      (scalarPathDenseTimes T k).property.2⟩)

theorem measurable_scalarPathFromPast (T : ℝ≥0) : Measurable (scalarPathFromPast T) := by
  exact (measurable_scalarPathFromDenseSamples T).comp
    (Measurable.of_eval (fun k => measurable_pi_apply _))

theorem indepFun_scalarPathVersion_of_past {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) (T : ℝ≥0)
    (M : ℝ≥0 → Ω → ℝ) (Mpaths : Ω → ScalarContinuousPath T) (X : Ω → E)
    (hversion : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      Mpaths ω t = M ⟨t, t.property.1⟩ ω)
    (h : IndepFun X (fun ω (t : Iic T) => M t ω) P) :
    IndepFun X Mpaths P := by
  have he : scalarPathFromPast T ∘ (fun ω (t : Iic T) => M t ω) =ᵐ[P] Mpaths := by
    filter_upwards [hversion] with ω hw
    have hs : (fun k => M
        ⟨scalarPathDenseTimes T k, (scalarPathDenseTimes T k).property.1⟩ ω) =
        scalarPathDenseSamples T (Mpaths ω) := by
      funext k
      exact (hw (scalarPathDenseTimes T k)).symm
    change scalarPathFromDenseSamples T
      (fun k => M ⟨scalarPathDenseTimes T k, (scalarPathDenseTimes T k).property.1⟩ ω) = _
    rw [hs]
    exact scalarPathFromDenseSamples_leftInverse T (Mpaths ω)
  have hi := h.comp (φ := id) (ψ := scalarPathFromPast T)
    measurable_id (measurable_scalarPathFromPast T)
  exact hi.congr (Filter.Eventually.of_forall (fun _ => rfl)) he

theorem brownian_indepFun_shift_scalarPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (M : ℝ≥0 → Ω → ℝ) (hM : IsPreBrownianReal M P)
    (Mpaths : Ω → ScalarContinuousPath T)
    (hversion : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      Mpaths ω t = M ⟨t, t.property.1⟩ ω) :
    IndepFun (fun ω t => M (T + t) ω - M T ω) Mpaths P :=
  indepFun_scalarPathVersion_of_past P T M Mpaths _ hversion (hM.indepFun_shift T)

end SKConstants
