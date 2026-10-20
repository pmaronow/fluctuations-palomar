module
public import SKConstants.ParisiPicardRestart
public import SKConstants.ParisiBrownianSeedSymmetry

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]

def shiftedBrownianSystem (W : BrownianSystem Ω) (a : ℝ≥0) : BrownianSystem Ω where
  law := W.law
  isProbability := W.isProbability
  B s w := W.B (a+s) w-W.B a w
  measurable s := (W.measurable _).sub (W.measurable _)
  brownian := W.brownian.shift a

theorem exists_brownianFinitePath (W : BrownianSystem Ω) (T : ℝ≥0) :
    ∃ F : Ω → ScalarContinuousPath T, Measurable F ∧
      ∀ᵐ w ∂W.law, ∀ t : Icc (0:ℝ) (T:ℝ), F w t = W.B ⟨t,t.property.1⟩ w := by
  obtain ⟨F,hF,he⟩ := exists_measurable_scalarPathVersion W.law T
    (fun r w => W.B (Real.toNNReal r) w)
    (fun r => W.measurable _)
    (W.brownian.cont.mono (fun w hw => hw.comp continuous_real_toNNReal))
  refine ⟨F,hF,?_⟩
  filter_upwards [he] with w hw t
  rw [hw t]
  congr 1
  exact NNReal.coe_injective (Real.coe_toNNReal _ t.property.1)

def brownianFinitePath (W : BrownianSystem Ω) (T : ℝ≥0) : Ω → ScalarContinuousPath T :=
  Classical.choose (exists_brownianFinitePath W T)

theorem measurable_brownianFinitePath (W : BrownianSystem Ω) (T : ℝ≥0) :
    Measurable (brownianFinitePath W T) :=
  (Classical.choose_spec (exists_brownianFinitePath W T)).1

theorem brownianFinitePath_version (W : BrownianSystem Ω) (T : ℝ≥0) :
    ∀ᵐ w ∂W.law, ∀ t : Icc (0:ℝ) (T:ℝ),
      brownianFinitePath W T w t = W.B ⟨t,t.property.1⟩ w :=
  (Classical.choose_spec (exists_brownianFinitePath W T)).2

def boundedDriftPastPath (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (a : ℝ≥0) : Ω → ScalarContinuousPath a :=
  fun w => scalarForwardPicardPath b a (0,brownianFinitePath W a w)

theorem measurable_boundedDriftPastPath (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a : ℝ≥0) : Measurable (boundedDriftPastPath W b a) :=
  (measurable_scalarForwardPicardPath b a).comp
    (measurable_const.prodMk (measurable_brownianFinitePath W a))

theorem boundedDriftPastPath_version (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a : ℝ≥0) :
    ∀ᵐ w ∂W.law, ∀ t : Icc (0:ℝ) (a:ℝ),
      boundedDriftPastPath W b a w t = b.solution W.driver ⟨t,t.property.1⟩ w := by
  filter_upwards [brownianFinitePath_version W a,W.driver_indistinguishable] with w hw hd
  intro t
  apply solution_congr_prefix b (scalarContinuousSeedDriver a) W.driver
    (0,brownianFinitePath W a w) w a _ ⟨t,t.property.1⟩ t.property.2
  intro s hs
  change 0+brownianFinitePath W a w (projIcc 0 (a:ℝ) a.coe_nonneg s) = W.driver s w
  rw [projIcc_of_mem a.coe_nonneg ⟨s.coe_nonneg,hs⟩,zero_add,hw]
  simpa only [hd] using congrArg (fun u => W.B u w) (Subtype.ext (by rfl) :
    (⟨(s:ℝ),s.coe_nonneg⟩:ℝ≥0) = s)

theorem brownian_future_indep_boundedDriftPastPath (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a : ℝ≥0) :
    IndepFun (fun w s => W.B (a+s) w-W.B a w) (boundedDriftPastPath W b a) W.law := by
  have H := brownian_indepFun_shift_scalarPathVersion W.law a W.B
    W.brownian.toIsPreBrownianReal (brownianFinitePath W a) (brownianFinitePath_version W a)
  exact H.comp measurable_id
    ((measurable_scalarForwardPicardPath b a).comp (measurable_const.prodMk measurable_id))

theorem brownian_futurePath_indep_boundedDriftPastPath (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a T : ℝ≥0) :
    IndepFun (brownianFinitePath (shiftedBrownianSystem W a) T)
      (boundedDriftPastPath W b a) W.law := by
  have H := (brownian_future_indep_boundedDriftPastPath W b a).symm
  have hm : Measurable (fun f : ℝ≥0 → ℝ => fun t : Iic T => f t.1) :=
    Measurable.of_eval (fun t => measurable_pi_apply t.1)
  have HP := H.comp measurable_id hm
  exact (indepFun_scalarPathVersion_of_past W.law T
    (fun s w => W.B (a+s) w-W.B a w)
    (brownianFinitePath (shiftedBrownianSystem W a) T) _
    (brownianFinitePath_version (shiftedBrownianSystem W a) T) HP).symm

theorem brownian_futurePath_law (W : BrownianSystem Ω) (a T : ℝ≥0) :
    W.law.map (brownianFinitePath (shiftedBrownianSystem W a) T) =
      W.law.map (brownianFinitePath W T) := by
  let := W.isProbability
  exact scalarBrownian_continuousPath_law_unique W.law W.law
    (shiftedBrownianSystem W a).B W.B
    (shiftedBrownianSystem W a).brownian.toIsPreBrownianReal W.brownian.toIsPreBrownianReal T
    (brownianFinitePath (shiftedBrownianSystem W a) T) (brownianFinitePath W T)
    (measurable_brownianFinitePath _ _) (measurable_brownianFinitePath _ _)
    (brownianFinitePath_version _ _) (brownianFinitePath_version _ _)

theorem boundedDriftPast_future_jointLaw (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a T : ℝ≥0) :
    W.law.map (fun w => (boundedDriftPastPath W b a w,
      brownianFinitePath (shiftedBrownianSystem W a) T w)) =
      (W.law.map (boundedDriftPastPath W b a)).prod
        (W.law.map (brownianFinitePath W T)) := by
  let := W.isProbability
  rw [(brownian_futurePath_indep_boundedDriftPastPath W b a T).symm.map_prod_eq_prod_map_map
    (measurable_boundedDriftPastPath W b a).aemeasurable (measurable_brownianFinitePath _ _).aemeasurable,
    brownian_futurePath_law]

def boundedDriftRestartCallback (b : BoundedLipschitzDrift) (a T : ℝ≥0)
    (p : ScalarContinuousPath a × ScalarContinuousPath T) : ScalarContinuousPath T :=
  scalarForwardPicardPath (SKConstants.BoundedLipschitzDrift.translated b a 0) T
    (p.1 ⟨a,a.coe_nonneg,le_rfl⟩,p.2)

theorem measurable_boundedDriftRestartCallback (b : BoundedLipschitzDrift) (a T : ℝ≥0) :
    Measurable (boundedDriftRestartCallback b a T) :=
  (measurable_scalarForwardPicardPath _ T).comp
    (((ContinuousMap.measurable_eval _).comp measurable_fst).prodMk measurable_snd)

theorem boundedDriftRestartCallback_fresh_version (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a T : ℝ≥0) (past : ScalarContinuousPath a) :
    ∀ᵐ w ∂W.law, ∀ t : Icc (0:ℝ) (T:ℝ),
      boundedDriftRestartCallback b a T (past,brownianFinitePath W T w) t =
        past ⟨a,a.coe_nonneg,le_rfl⟩+
          (SKConstants.BoundedLipschitzDrift.translated b a
            (past ⟨a,a.coe_nonneg,le_rfl⟩)).solution W.driver ⟨t,t.property.1⟩ w := by
  filter_upwards [brownianFinitePath_version W T,W.driver_indistinguishable] with w hf hd
  intro t
  let z := past ⟨a,a.coe_nonneg,le_rfl⟩
  let v : ℝ≥0 := ⟨t,t.property.1⟩
  have HE : boundedDriftRestartCallback b a T (past,brownianFinitePath W T w) t =
      (SKConstants.BoundedLipschitzDrift.translated b a 0).solution
        (fun s u => z+W.driver s u) v w := by
    apply solution_congr_prefix (SKConstants.BoundedLipschitzDrift.translated b a 0)
      (scalarContinuousSeedDriver T) _ (z,brownianFinitePath W T w) w T _ v t.property.2
    intro s hs
    change z+brownianFinitePath W T w (projIcc 0 (T:ℝ) T.coe_nonneg s) = z+W.driver s w
    rw [projIcc_of_mem T.coe_nonneg ⟨s.coe_nonneg,hs⟩,hf,hd]
    rfl
  rw [HE]
  exact (SKConstants.BoundedLipschitzDrift.solution_translated_add_seed b a z W.driver v w).symm

def boundedDriftRestartPath (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (a T : ℝ≥0) (w : Ω) : ScalarContinuousPath T :=
  boundedDriftRestartCallback b a T
    (boundedDriftPastPath W b a w,brownianFinitePath (shiftedBrownianSystem W a) T w)

theorem measurable_boundedDriftRestartPath (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a T : ℝ≥0) : Measurable (boundedDriftRestartPath W b a T) :=
  (measurable_boundedDriftRestartCallback b a T).comp
    ((measurable_boundedDriftPastPath W b a).prodMk (measurable_brownianFinitePath _ _))

theorem boundedDriftRestartPath_version (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a T : ℝ≥0) :
    ∀ᵐ w ∂W.law, ∀ t : Icc (0:ℝ) (T:ℝ),
      boundedDriftRestartPath W b a T w t = b.solution W.driver (a+⟨t,t.property.1⟩) w := by
  filter_upwards [boundedDriftPastPath_version W b a,
    brownianFinitePath_version (shiftedBrownianSystem W a) T,
    W.driver_continuous,W.driver_indistinguishable] with w hp hf hc hd
  intro t
  let v : ℝ≥0 := ⟨t,t.property.1⟩
  let z := b.solution W.driver a w
  let C : ℝ≥0 → Unit → ℝ := fun s _ => W.driver (a+s) w-W.driver a w
  have HR := SKConstants.BoundedLipschitzDrift.solution_restart b _ W.driver
    W.driver_progressive w hc a v
  have HS := SKConstants.BoundedLipschitzDrift.solution_translated_add_seed b a z C v ()
  have HE : boundedDriftRestartPath W b a T w t =
      (SKConstants.BoundedLipschitzDrift.translated b a 0).solution
        (fun s (_ : Unit) => z+C s ()) v () := by
    change (SKConstants.BoundedLipschitzDrift.translated b a 0).solution
      (scalarContinuousSeedDriver T) v
      (boundedDriftPastPath W b a w ⟨a,a.coe_nonneg,le_rfl⟩,
        brownianFinitePath (shiftedBrownianSystem W a) T w) = _
    rw [hp]
    apply solution_congr_prefix (SKConstants.BoundedLipschitzDrift.translated b a 0)
      (scalarContinuousSeedDriver T) _ _ () T _ v t.property.2
    intro s hs
    change z+brownianFinitePath (shiftedBrownianSystem W a) T w
      (projIcc 0 (T:ℝ) T.coe_nonneg s) = z+C s ()
    rw [projIcc_of_mem T.coe_nonneg ⟨s.coe_nonneg,hs⟩,hf]
    simp only [shiftedBrownianSystem,C,hd]
    rfl
  rw [HE,←HS]
  exact HR.symm

theorem boundedDriftPast_restart_jointLaw (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (a T : ℝ≥0) :
    W.law.map (fun w => (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a T w)) =
      ((W.law.map (boundedDriftPastPath W b a)).prod
        (W.law.map (brownianFinitePath W T))).map
          (fun p => (p.1,boundedDriftRestartCallback b a T p)) := by
  have hm : Measurable (fun p : ScalarContinuousPath a × ScalarContinuousPath T =>
      (p.1,boundedDriftRestartCallback b a T p)) :=
    measurable_fst.prodMk (measurable_boundedDriftRestartCallback b a T)
  rw [←boundedDriftPast_future_jointLaw W b a T,
    Measure.map_map hm ((measurable_boundedDriftPastPath W b a).prodMk
      (measurable_brownianFinitePath _ _))]
  rfl

end SKConstants
