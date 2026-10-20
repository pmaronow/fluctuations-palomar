module

public import SKConstants.GaussianProposalScalarMeshCallbacks
public import SKConstants.ParisiBrownianSeedSymmetry
public import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators Matrix
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

lemma exists_scalarPrimitiveBrownianPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    ∃ F : Ω → ScalarContinuousPath H,Measurable F ∧
      ∀ᵐ ω ∂W.law,∀ t : Icc (0 : ℝ) (H : ℝ),F ω t=W.B ⟨t,t.property.1⟩ ω := by
  obtain ⟨F,hFm,hFe⟩ := exists_measurable_scalarPathVersion W.law H
    (fun t ω => W.B t.toNNReal ω) (fun t => W.measurable _)
    (W.brownian.cont.mono (fun ω h => h.comp continuous_real_toNNReal))
  refine ⟨F,hFm,?_⟩
  filter_upwards [hFe] with ω hω t
  have he : (t : ℝ).toNNReal = ⟨t,t.property.1⟩ :=
    by
      apply NNReal.eq
      exact Real.coe_toNNReal _ t.property.1
  have Ht := hω t
  rw [he] at Ht
  exact Ht

def scalarPrimitiveBrownianPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) : Ω → ScalarContinuousPath H :=
  Classical.choose (exists_scalarPrimitiveBrownianPathVersion W H)

lemma measurable_scalarPrimitiveBrownianPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    Measurable (scalarPrimitiveBrownianPathVersion W H) :=
  (Classical.choose_spec (exists_scalarPrimitiveBrownianPathVersion W H)).1

lemma scalarPrimitiveBrownianPathVersion_ae {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    ∀ᵐ ω ∂W.law,∀ t : Icc (0 : ℝ) (H : ℝ),
      scalarPrimitiveBrownianPathVersion W H ω t=W.B ⟨t,t.property.1⟩ ω :=
  (Classical.choose_spec (exists_scalarPrimitiveBrownianPathVersion W H)).2

def scalarPrimitiveBrownianPathLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) : Measure (ScalarContinuousPath H) :=
  W.law.map (scalarPrimitiveBrownianPathVersion W H)

instance scalarPrimitiveBrownianPathLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    IsProbabilityMeasure (scalarPrimitiveBrownianPathLaw W H) := by
  let := W.isProbability
  unfold scalarPrimitiveBrownianPathLaw
  infer_instance

def scalarPrimitiveBridgePathLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (h : ℝ≥0) : Measure (ScalarContinuousPath h) :=
  (scalarPrimitiveBrownianPathLaw W h).map (scalarBrownianBridgePath h)

instance scalarPrimitiveBridgePathLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (h : ℝ≥0) :
    IsProbabilityMeasure (scalarPrimitiveBridgePathLaw W h) := by
  unfold scalarPrimitiveBridgePathLaw
  infer_instance

def scalarInitialAuxiliaryB (H h : ℝ≥0) (F : ScalarContinuousPath h) : ScalarContinuousPath H :=
  ⟨fun t => IccExtend h.coe_nonneg F t,
    F.continuous.Icc_extend'.comp continuous_subtype_val⟩

lemma measurable_scalarInitialAuxiliaryB (H h : ℝ≥0) : Measurable (scalarInitialAuxiliaryB H h) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ContinuousMap.measurable_eval _

lemma scalarInitialAuxiliaryB_on_interval (H h : ℝ≥0) (hh : h ≤ H)
    (F : ScalarContinuousPath h) (t : Icc (0 : ℝ) (h : ℝ)) :
    scalarInitialAuxiliaryB H h F ⟨t,t.property.1,t.property.2.trans hh⟩ = F t := by
  simp only [scalarInitialAuxiliaryB,ContinuousMap.coe_mk,IccExtend,Function.comp_apply,
    projIcc_of_mem _ t.property]

abbrev ScalarGrowingPaperInitialData (H δ : ℝ≥0) (n : ℕ) :=
  (Fin n → ScalarContinuousPath H) ×
    ((Fin n → ScalarContinuousPath (growingQueryDuration δ 0)) ×
      ((j : ℕ) → Fin n → ScalarContinuousPath (growingQueryDuration δ j)))

def scalarGrowingPaperInitialState (H δ : ℝ≥0) (n : ℕ)
    (p : ScalarGrowingPaperInitialData H δ n) : ScalarGrowingPaperPast H δ n :=
  ((fun _ => 0,(p.1,p.2.2)),fun i => scalarInitialAuxiliaryB H (growingQueryDuration δ 0) (p.2.1 i))

lemma measurable_scalarGrowingPaperInitialState (H δ : ℝ≥0) (n : ℕ) :
    Measurable (scalarGrowingPaperInitialState H δ n) := by
  apply Measurable.prodMk
  · exact measurable_const.prodMk (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  · apply Measurable.of_eval
    intro i
    exact (measurable_scalarInitialAuxiliaryB H _).comp
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))

def scalarGrowingPaperInitialDataLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H δ : ℝ≥0) (n : ℕ) :
    Measure (ScalarGrowingPaperInitialData H δ n) :=
  (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W H)).prod
    ((Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
      (Measure.infinitePi (fun j : ℕ => Measure.pi
        (fun _ : Fin n => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))))

instance scalarGrowingPaperInitialDataLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H δ : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (scalarGrowingPaperInitialDataLaw W H δ n) := by
  unfold scalarGrowingPaperInitialDataLaw
  infer_instance

def scalarGrowingPaperInitialStateLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H δ : ℝ≥0) (n : ℕ) :
    Measure (ScalarGrowingPaperPast H δ n) :=
  (scalarGrowingPaperInitialDataLaw W H δ n).map (scalarGrowingPaperInitialState H δ n)

instance scalarGrowingPaperInitialStateLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H δ : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (scalarGrowingPaperInitialStateLaw W H δ n) := by
  unfold scalarGrowingPaperInitialStateLaw
  infer_instance

def scalarInitialAuxiliaryRestriction (H h : ℝ≥0) (hh : h ≤ H)
    (F : ScalarContinuousPath H) : ScalarContinuousPath h :=
  ⟨fun t => F ⟨t,t.property.1,t.property.2.trans hh⟩,
    F.continuous.comp (by fun_prop)⟩

lemma measurable_scalarInitialAuxiliaryRestriction (H h : ℝ≥0) (hh : h ≤ H) :
    Measurable (scalarInitialAuxiliaryRestriction H h hh) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ContinuousMap.measurable_eval _

theorem scalarInitialAuxiliaryB_initial_interval_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H h : ℝ≥0) (hh : h ≤ H) :
    ((scalarPrimitiveBrownianPathLaw W h).map (scalarInitialAuxiliaryB H h)).map
      (scalarInitialAuxiliaryRestriction H h hh) = scalarPrimitiveBrownianPathLaw W h := by
  rw [Measure.map_map (measurable_scalarInitialAuxiliaryRestriction H h hh)
    (measurable_scalarInitialAuxiliaryB H h)]
  have he : (scalarInitialAuxiliaryRestriction H h hh) ∘ (scalarInitialAuxiliaryB H h) = id := by
    funext F
    apply ContinuousMap.ext
    intro t
    exact scalarInitialAuxiliaryB_on_interval H h hh F t
  rw [he,Measure.map_id]

lemma scalarGrowingPaperInitialState_B_on_first_interval (H δ : ℝ≥0) (n : ℕ)
    (p : ScalarGrowingPaperInitialData H δ n) (i : Fin n)
    (hh : growingQueryDuration δ 0 ≤ H)
    (t : Icc (0 : ℝ) (growingQueryDuration δ 0 : ℝ)) :
    (scalarGrowingPaperInitialState H δ n p).2 i ⟨t,t.property.1,t.property.2.trans hh⟩ =
      p.2.1 i t := scalarInitialAuxiliaryB_on_interval H _ hh _ t

def scalarGrowingSourceHorizon (δ : ℝ≥0) (q : ℕ) : ℝ≥0 := growingQueryTime δ (q+1)

open GaussianProposal in
def scalarGrowingSourceProposal (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (z : StoppedNoise (Fin (ranks+q)) q) : Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ :=
  actualPaperProposal ranks q (skSigma (ranks+q))
    (scalarGrowingPaperTarget b f g hf hg m r (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
    (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
    (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p) z

open GaussianProposal in
lemma measurable_scalarGrowingSourceProposal (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) :
    Measurable (Function.uncurry (scalarGrowingSourceProposal b f g hf hg m r δ ranks q)) := by
  exact (actualPaperProposal_measurable ranks q (skSigma (ranks+q)) _ _
    (fun k i => measurable_scalarMeshPaperTarget b f g hf hg m hm _ _ _ _ (ranks+q) q k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ (ranks+q) q k)).comp
    (((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_fst).prodMk measurable_snd)

open GaussianProposal in
theorem scalarGrowingSourceProposal_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) :
    ((scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
      (stoppedNoiseLaw (Fin (ranks+q)) q)).map (fun p =>
        (p.1,scalarGrowingSourceProposal b f g hf hg m r δ ranks q p.1 p.2)) =
      (scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
        (skDisorderLaw (ranks+q)) := by
  exact adaptiveStep_joint_law
    (measurable_scalarGrowingSourceProposal b f g hf hg m hm r δ ranks q)
    (fun p => scalarGrowingPaperProposal_law b f g hf hg m hm r _ δ ranks q _)

open GaussianProposal in
theorem scalarGrowingSourceProposal_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) :
    ((scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
      (stoppedNoiseLaw (Fin (ranks+q)) q)).map
        (Function.uncurry (scalarGrowingSourceProposal b f g hf hg m r δ ranks q)) =
      skDisorderLaw (ranks+q) := by
  exact adaptiveStep_output_law_ae
    (measurable_scalarGrowingSourceProposal b f g hf hg m hm r δ ranks q)
    (Filter.Eventually.of_forall (fun p => scalarGrowingPaperProposal_law b f g hf hg m hm r _ δ ranks q _))

theorem scalarGrowingSource_last_B_endpoint (δ : ℝ≥0) (hδ : 0 < δ) (n q : ℕ)
    (s : ScalarGrowingPaperPast (scalarGrowingSourceHorizon δ q) δ n) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ n q 0 s z).2 i
        ⟨scalarGrowingSourceHorizon δ q,(scalarGrowingSourceHorizon δ q).coe_nonneg,le_rfl⟩ -
      s.2 i ⟨growingQueryTime δ q,(growingQueryTime δ q).coe_nonneg,
        (growingQueryTime_strictMono δ hδ).monotone (by omega)⟩ =
        Real.sqrt (growingQueryDuration δ q)*z (.inl i) := by
  simpa only [Nat.sub_zero,scalarGrowingSourceHorizon] using
    scalarGrowingPaperUpdate_B_endpoint (scalarGrowingSourceHorizon δ q) δ hδ n q 0 s i z (by
      simp only [Nat.sub_zero,scalarGrowingSourceHorizon]
      exact le_rfl)

end SKConstants
