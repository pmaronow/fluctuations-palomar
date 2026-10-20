module

public import SKConstants.ScalarDeterministicWeightedPaths
public import SKConstants.ScalarBrownianBridge
public import SKConstants.GaussianProposalMatrixReplay
public import SKConstants.SKModel
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators Matrix
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

def scalarPinnedBridge (h : ℝ≥0) (f : ScalarContinuousPath h) : ScalarContinuousPath h :=
  ⟨fun t => f t - (1-(t : ℝ)/(h : ℝ))*f ⟨0,le_rfl,h.coe_nonneg⟩ -
    ((t : ℝ)/(h : ℝ))*f ⟨h,h.coe_nonneg,le_rfl⟩,
    (f.continuous.sub
      ((continuous_const.sub (continuous_subtype_val.div_const _)).mul continuous_const)).sub
      ((continuous_subtype_val.div_const _).mul continuous_const)⟩

theorem measurable_scalarPinnedBridge (h : ℝ≥0) : Measurable (scalarPinnedBridge h) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval t).sub
    ((ContinuousMap.measurable_eval _).const_mul _)).sub
    ((ContinuousMap.measurable_eval _).const_mul _)

theorem scalarPinnedBridge_zero (h : ℝ≥0) (f : ScalarContinuousPath h) :
    scalarPinnedBridge h f ⟨0,le_rfl,h.coe_nonneg⟩ = 0 := by
  simp [scalarPinnedBridge]

theorem scalarPinnedBridge_endpoint (h : ℝ≥0) (hh : 0 < h) (f : ScalarContinuousPath h) :
    scalarPinnedBridge h f ⟨h,h.coe_nonneg,le_rfl⟩ = 0 := by
  simp [scalarPinnedBridge, (NNReal.coe_pos.mpr hh).ne']

def scalarQueryBridgeComplete (h : ℝ≥0) (p : ℝ × ScalarContinuousPath h) :
    ScalarContinuousPath h :=
  scalarBrownianBridgeComplete h (Real.sqrt h*p.1,scalarPinnedBridge h p.2)

theorem measurable_scalarQueryBridgeComplete (h : ℝ≥0) :
    Measurable (scalarQueryBridgeComplete h) :=
  (measurable_scalarBrownianBridgeComplete h).comp
    ((measurable_fst.const_mul _).prodMk
      ((measurable_scalarPinnedBridge h).comp measurable_snd))

theorem scalarQueryBridgeComplete_zero (h : ℝ≥0) (p : ℝ × ScalarContinuousPath h) :
    scalarQueryBridgeComplete h p ⟨0,le_rfl,h.coe_nonneg⟩ = 0 := by
  simp [scalarQueryBridgeComplete,scalarBrownianBridgeComplete,scalarPinnedBridge]

theorem scalarQueryBridgeComplete_endpoint (h : ℝ≥0) (hh : 0 < h)
    (p : ℝ × ScalarContinuousPath h) :
    scalarQueryBridgeComplete h p ⟨h,h.coe_nonneg,le_rfl⟩ = Real.sqrt h*p.1 := by
  simp [scalarQueryBridgeComplete,scalarBrownianBridgeComplete,scalarPinnedBridge,
    (NNReal.coe_pos.mpr hh).ne']

def scalarAppendQueryInterval (H h : ℝ≥0) (a : ℝ)
    (p : ScalarContinuousPath H × (ℝ × ScalarContinuousPath h)) : ScalarContinuousPath H :=
  ⟨fun t => p.1 (projIcc 0 (H : ℝ) H.coe_nonneg (min (t : ℝ) a)) +
    scalarQueryBridgeComplete h p.2
      (projIcc 0 (h : ℝ) h.coe_nonneg ((t : ℝ)-a)),
    (p.1.continuous.comp ((continuous_projIcc (h := H.coe_nonneg)).comp
      (continuous_subtype_val.min continuous_const))).add
      ((scalarQueryBridgeComplete h p.2).continuous.comp
        ((continuous_projIcc (h := h.coe_nonneg)).comp
          (continuous_subtype_val.sub continuous_const)))⟩

theorem measurable_scalarAppendQueryInterval (H h : ℝ≥0) (a : ℝ) :
    Measurable (scalarAppendQueryInterval H h a) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval _).comp measurable_fst).add
    ((ContinuousMap.measurable_eval _).comp
      ((measurable_scalarQueryBridgeComplete h).comp measurable_snd))

theorem scalarAppendQueryInterval_prefix (H h : ℝ≥0) (a : ℝ)
    (p : ScalarContinuousPath H × (ℝ × ScalarContinuousPath h))
    (t : Icc (0 : ℝ) (H : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarAppendQueryInterval H h a p t = p.1 t := by
  change p.1 (projIcc 0 (H : ℝ) H.coe_nonneg (min (t : ℝ) a)) + _ = p.1 t
  rw [min_eq_left ht,projIcc_of_mem _ t.property,
    projIcc_of_le_left h.coe_nonneg (by linarith : (t : ℝ)-a ≤ 0)]
  rw [scalarQueryBridgeComplete_zero,add_zero]

abbrev ScalarPaperStatic (H h : ℝ≥0) (n : ℕ) :=
  (Fin n → ℝ) × ((Fin n → ScalarContinuousPath H) ×
    (ℕ → Fin n → ScalarContinuousPath h))

abbrev ScalarPaperPast (H h : ℝ≥0) (n : ℕ) :=
  ScalarPaperStatic H h n × (Fin n → ScalarContinuousPath H)

def scalarPaperObservation (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H h : ℝ≥0) (n : ℕ) (s : ScalarPaperPast H h n) (i : Fin n) : ScalarContinuousPath H :=
  scalarTwoDriverPicardPath b f g hf hg H (s.1.1 i,(s.2 i,s.1.2.1 i))

theorem measurable_scalarPaperObservation (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H h : ℝ≥0) (n : ℕ) (i : Fin n) :
    Measurable (fun s => scalarPaperObservation b f g hf hg H h n s i) := by
  apply (measurable_scalarTwoDriverPicardPath b f g hf hg H).comp
  exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).prodMk
    (((measurable_pi_apply i).comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))))

def scalarPaperQueryTime (h : ℝ≥0) (K k : ℕ) : ℝ := (K-k : ℕ)* (h : ℝ)

def scalarPaperTarget (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H h : ℝ≥0) (n K k : ℕ)
    (s : ScalarPaperPast H h n) (i : Fin n) : ℝ :=
  let t := scalarPaperQueryTime h K k
  let a := scalarPaperQueryTime h K (k+1)
  (m t (scalarPaperObservation b f g hf hg H h n s i (projIcc 0 (H : ℝ) H.coe_nonneg t)) -
    m a (scalarPaperObservation b f g hf hg H h n s i (projIcc 0 (H : ℝ) H.coe_nonneg a))) /
      scale (K-k)

theorem measurable_scalarPaperTarget (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H h : ℝ≥0) (n K k : ℕ) (i : Fin n) :
    Measurable (fun s => scalarPaperTarget b f g hf hg m scale H h n K k s i) := by
  have hY := measurable_scalarPaperObservation b f g hf hg H h n i
  exact ((hm.comp (measurable_const.prodMk
      ((ContinuousMap.measurable_eval _).comp hY))).sub
    (hm.comp (measurable_const.prodMk
      ((ContinuousMap.measurable_eval _).comp hY)))).div_const _

def scalarPaperUpdate (H h : ℝ≥0) (n K k : ℕ) (s : ScalarPaperPast H h n)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) : ScalarPaperPast H h n :=
  (s.1,fun i => scalarAppendQueryInterval H h (scalarPaperQueryTime h K k)
    (s.2 i,(z (.inl i),s.1.2.2 (K-k) i)))

theorem measurable_scalarPaperUpdate (H h : ℝ≥0) (n K k : ℕ) :
    Measurable (Function.uncurry (scalarPaperUpdate H h n K k)) := by
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply Measurable.of_eval
  intro i
  apply (measurable_scalarAppendQueryInterval H h (scalarPaperQueryTime h K k)).comp
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).prodMk
    (((show Measurable (fun z : EuclideanSpace ℝ (Fin n ⊕ Unit) => z (.inl i)) from by fun_prop).comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp ((measurable_pi_apply (K-k)).comp
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))))

def scalarPathPrefixTruncate (H : ℝ≥0) (a : ℝ) (D : ScalarContinuousPath H) :
    ScalarContinuousPath H :=
  ⟨fun t => D (projIcc 0 (H : ℝ) H.coe_nonneg (min (t : ℝ) a)),
    D.continuous.comp ((continuous_projIcc (h := H.coe_nonneg)).comp
      (continuous_subtype_val.min continuous_const))⟩

theorem measurable_scalarPathPrefixTruncate (H : ℝ≥0) (a : ℝ) :
    Measurable (scalarPathPrefixTruncate H a) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ContinuousMap.measurable_eval _

theorem scalarPathPrefixTruncate_prefix (H : ℝ≥0) (a : ℝ) (D : ScalarContinuousPath H)
    (t : Icc (0 : ℝ) (H : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarPathPrefixTruncate H a D t = D t := by
  change D (projIcc 0 (H : ℝ) H.coe_nonneg (min (t : ℝ) a)) = D t
  rw [min_eq_left ht,projIcc_of_mem _ t.property]

def scalarPaperTruncateD (H h : ℝ≥0) (n : ℕ) (a : ℝ) (s : ScalarPaperPast H h n) :
    ScalarPaperPast H h n :=
  ((s.1.1,(fun i => scalarPathPrefixTruncate H a (s.1.2.1 i),s.1.2.2)),s.2)

theorem measurable_scalarPaperTruncateD (H h : ℝ≥0) (n : ℕ) (a : ℝ) :
    Measurable (scalarPaperTruncateD H h n a) := by
  apply Measurable.prodMk _ measurable_snd
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply Measurable.prodMk _ (measurable_snd.comp (measurable_snd.comp measurable_fst))
  apply Measurable.of_eval
  intro i
  exact (measurable_scalarPathPrefixTruncate H a).comp
    ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))

theorem scalarPaperObservation_truncateD (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H h : ℝ≥0) (n : ℕ) (s : ScalarPaperPast H h n) (i : Fin n)
    (a : ℝ≥0) (ha : a ≤ H) (t : Icc (0 : ℝ) (H : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarPaperObservation b f g hf hg H h n (scalarPaperTruncateD H h n a s) i t =
      scalarPaperObservation b f g hf hg H h n s i t := by
  apply scalarTwoDriverPicardPath_congr_prefix b f g hf hg H
    (s.1.1 i) (s.2 i) (s.2 i) _ _ a ha _ _ t ht
  · exact fun _ _ => rfl
  · intro u hu
    exact scalarPathPrefixTruncate_prefix H a (s.1.2.1 i) u hu

theorem scalarPaperTarget_truncateD (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H h : ℝ≥0) (n K k : ℕ)
    (s : ScalarPaperPast H h n) (i : Fin n)
    (a : ℝ≥0) (ha : a ≤ H)
    (ht : scalarPaperQueryTime h K k ∈ Icc (0 : ℝ) (a : ℝ))
    (hv : scalarPaperQueryTime h K (k+1) ∈ Icc (0 : ℝ) (a : ℝ)) :
    scalarPaperTarget b f g hf hg m scale H h n K k
      (scalarPaperTruncateD H h n a s) i =
        scalarPaperTarget b f g hf hg m scale H h n K k s i := by
  have htH : scalarPaperQueryTime h K k ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨ht.1,ht.2.trans ha⟩
  have hvH : scalarPaperQueryTime h K (k+1) ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨hv.1,hv.2.trans ha⟩
  dsimp only [scalarPaperTarget]
  rw [projIcc_of_mem _ htH,projIcc_of_mem _ hvH,
    scalarPaperObservation_truncateD b f g hf hg H h n s i a ha _ ht.2,
    scalarPaperObservation_truncateD b f g hf hg H h n s i a ha _ hv.2]

open GaussianProposal in
theorem scalarPaperProposal_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H h : ℝ≥0) (r K : ℕ) (s : ScalarPaperPast H h (r+K)) :
    (stoppedNoiseLaw (Fin (r+K)) K).map
      (actualPaperProposal r K (skSigma (r+K))
        (scalarPaperTarget b f g hf hg m scale H h (r+K) K)
        (scalarPaperUpdate H h (r+K) K) s) =
      skDisorderLaw (r+K) := by
  simpa only [skDisorderLaw,skSigma,Nat.cast_add,Nat.cast_ofNat] using
    actualPaperProposal_law r K (skSigma (r+K)) _ _
    (fun k i => measurable_scalarPaperTarget b f g hf hg m hm scale H h (r+K) K k i)
    (fun k => measurable_scalarPaperUpdate H h (r+K) K k) s

open GaussianProposal in
theorem scalarPaperProposal_joint_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H h : ℝ≥0) (r K : ℕ)
    (μ : Measure (ScalarPaperPast H h (r+K))) [SFinite μ] :
    (μ.prod (stoppedNoiseLaw (Fin (r+K)) K)).map (fun p =>
      (p.1,actualPaperProposal r K (skSigma (r+K))
        (scalarPaperTarget b f g hf hg m scale H h (r+K) K)
        (scalarPaperUpdate H h (r+K) K) p.1 p.2)) =
      μ.prod (skDisorderLaw (r+K)) := by
  simpa only [skDisorderLaw,skSigma,Nat.cast_add,Nat.cast_ofNat] using
    actualPaperProposal_joint_law μ r K (skSigma (r+K)) _ _
    (fun k i => measurable_scalarPaperTarget b f g hf hg m hm scale H h (r+K) K k i)
    (fun k => measurable_scalarPaperUpdate H h (r+K) K k)

open GaussianProposal in
theorem scalarPaperProposal_matrix_query_coupling
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H h : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (s : ScalarPaperPast H h (r+K)) (z : StoppedNoise (Fin (r+K)) K) :
    paperMatrixQueryRun r (r+K) (r+K)
      (scalarPaperTarget b f g hf hg m scale H h (r+K) K)
      (scalarPaperUpdate H h (r+K) K) K (s,1) z
      (actualPaperProposal r K (skSigma (r+K))
        (scalarPaperTarget b f g hf hg m scale H h (r+K) K)
        (scalarPaperUpdate H h (r+K) K) s z) =
      proposalTerminalPast (scalarPaperUpdate H h (r+K) K) K s z :=
  actualPaperProposal_matrix_query_coupling r K (r+K) (by exact_mod_cast hN) _ _ s z

def scalarPaperIncrementScale (r : ℝ → ℝ) (h : ℝ≥0) (j : ℕ) : ℝ :=
  Real.sqrt (∫ v in ((j-1 : ℕ) : ℝ)*(h : ℝ)..(j : ℝ)*(h : ℝ),r v)

theorem scalarAppendQueryInterval_on_interval (H h : ℝ≥0) (a : ℝ)
    (ha : 0 ≤ a) (haH : a+(h : ℝ) ≤ H)
    (p : ScalarContinuousPath H × (ℝ × ScalarContinuousPath h))
    (s : Icc (0 : ℝ) (h : ℝ)) :
    scalarAppendQueryInterval H h a p
        ⟨a+(s : ℝ),by constructor <;> linarith [s.property.1,s.property.2]⟩ =
      p.1 ⟨a,⟨ha,by linarith [h.coe_nonneg]⟩⟩ + scalarQueryBridgeComplete h p.2 s := by
  change p.1 (projIcc 0 (H : ℝ) H.coe_nonneg (min (a+(s : ℝ)) a)) +
    scalarQueryBridgeComplete h p.2
      (projIcc 0 (h : ℝ) h.coe_nonneg (a+(s : ℝ)-a)) = _
  rw [min_eq_right (by linarith [s.property.1]),
    projIcc_of_mem _ ⟨ha,by linarith [h.coe_nonneg]⟩,
    show a+(s : ℝ)-a = (s : ℝ) by ring,projIcc_of_mem _ s.property]

theorem scalarPaperUpdate_B_endpoint (H h : ℝ≥0) (hh : 0 < h) (n K k : ℕ)
    (s : ScalarPaperPast H h n) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (ha : 0 ≤ scalarPaperQueryTime h K k)
    (haH : scalarPaperQueryTime h K k+(h : ℝ) ≤ H) :
    (scalarPaperUpdate H h n K k s z).2 i
        ⟨scalarPaperQueryTime h K k+(h : ℝ),by constructor <;> linarith [h.coe_nonneg]⟩ -
      s.2 i ⟨scalarPaperQueryTime h K k,⟨ha,by linarith [h.coe_nonneg]⟩⟩ =
        Real.sqrt h*z (.inl i) := by
  change scalarAppendQueryInterval H h (scalarPaperQueryTime h K k)
      (s.2 i,(z (.inl i),s.1.2.2 (K-k) i)) _ - _ = _
  rw [scalarAppendQueryInterval_on_interval H h _ ha haH _ ⟨h,h.coe_nonneg,le_rfl⟩,
    scalarQueryBridgeComplete_endpoint h hh]
  ring

theorem scalarPaperUpdate_B_congr (H h : ℝ≥0) (n K k : ℕ)
    (s t : ScalarPaperPast H h n) (z : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hB : s.2 = t.2) (hbridge : s.1.2.2 (K-k) = t.1.2.2 (K-k)) :
    (scalarPaperUpdate H h n K k s z).2 = (scalarPaperUpdate H h n K k t z).2 := by
  funext i
  dsimp only [scalarPaperUpdate]
  rw [hB,hbridge]

theorem scalarPathPrefixTruncate_measurable_of_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (H : ℝ≥0) (a : ℝ≥0) (_ha : a ≤ H)
    (D : Ω → ScalarContinuousPath H)
    (hD : ∀ t : Icc (0 : ℝ) (H : ℝ), (t : ℝ) ≤ a → Measurable[𝔪] (fun ω => D ω t)) :
    Measurable[𝔪] (fun ω => scalarPathPrefixTruncate H a (D ω)) := by
  let : MeasurableSpace Ω := 𝔪
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have ht : min (t : ℝ) (a : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨le_min t.property.1 a.coe_nonneg,(min_le_left _ _).trans t.property.2⟩
  have hh := hD ⟨min (t : ℝ) (a : ℝ),ht⟩ (min_le_right _ _)
  simpa only [scalarPathPrefixTruncate,ContinuousMap.coe_mk,projIcc_of_mem _ ht] using hh

theorem scalarPaperTarget_measurable_of_D_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H h : ℝ≥0) (n K k : ℕ)
    (S : Ω → ScalarPaperPast H h n) (i : Fin n)
    (a : ℝ≥0) (ha : a ≤ H)
    (ht : scalarPaperQueryTime h K k ∈ Icc (0 : ℝ) (a : ℝ))
    (hv : scalarPaperQueryTime h K (k+1) ∈ Icc (0 : ℝ) (a : ℝ))
    (hz : Measurable[𝔪] (fun ω => (S ω).1.1 i))
    (hB : Measurable[𝔪] (fun ω => (S ω).2 i))
    (hD : ∀ t : Icc (0 : ℝ) (H : ℝ), (t : ℝ) ≤ a →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t)) :
    Measurable[𝔪] (fun ω => scalarPaperTarget b f g hf hg m scale H h n K k (S ω) i) := by
  let : MeasurableSpace Ω := 𝔪
  have hDp := scalarPathPrefixTruncate_measurable_of_past 𝔪 H a ha
    (fun ω => (S ω).1.2.1 i) hD
  let Y : Ω → ScalarContinuousPath H := fun ω => scalarTwoDriverPicardPath b f g hf hg H
    ((S ω).1.1 i,((S ω).2 i,scalarPathPrefixTruncate H a ((S ω).1.2.1 i)))
  have hY : Measurable Y := (measurable_scalarTwoDriverPicardPath b f g hf hg H).comp
    (hz.prodMk (hB.prodMk hDp))
  have hTarget : Measurable (fun ω => scalarPaperTarget b f g hf hg m scale H h n K k
      (scalarPaperTruncateD H h n a (S ω)) i) := by
    exact ((hm.comp (measurable_const.prodMk
        ((ContinuousMap.measurable_eval _).comp hY))).sub
      (hm.comp (measurable_const.prodMk
        ((ContinuousMap.measurable_eval _).comp hY)))).div_const _
  convert hTarget using 1
  funext ω
  exact (scalarPaperTarget_truncateD b f g hf hg m scale H h n K k (S ω) i a ha ht hv).symm

open GaussianProposal in
theorem continuous_paperQueriedNoise (m n : ℕ) (N : ℝ) :
    Continuous (fun p : (Matrix (Fin (m+1)) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ) × EuclideanSpace ℝ (Fin n ⊕ Unit) =>
      paperQueriedNoise N p.1.1 p.1.2 p.2) := by
  unfold paperQueriedNoise
  apply (show Continuous (fun v : Fin n ⊕ Unit → ℝ => WithLp.toLp 2 v) from by fun_prop).comp
  apply continuous_pi
  intro j
  cases j with
  | inl j =>
    dsimp only [Sum.elim_inl]
    unfold remainingProjection normalizedQuery tailRows
    fun_prop
  | inr j =>
    dsimp only [Sum.elim_inr]
    fun_prop

open GaussianProposal in
theorem measurable_paperQueriedNoise (m n : ℕ) (N : ℝ) :
    Measurable (fun p : (Matrix (Fin (m+1)) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ) × EuclideanSpace ℝ (Fin n ⊕ Unit) =>
      paperQueriedNoise N p.1.1 p.1.2 p.2) := by
  let : SecondCountableTopology (Matrix (Fin (m+1)) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin (m+1) → Fin n → ℝ))
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact (continuous_paperQueriedNoise m n N).measurable

open GaussianProposal in
theorem scalarPaperCurrentB_measurable_of_D_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (mfield : ℝ → ℝ → ℝ) (hmfield : Measurable (Function.uncurry mfield))
    (scale : ℕ → ℝ) (H h : ℝ≥0) (n K k rem : ℕ) (N : ℝ)
    (S : Ω → ScalarPaperPast H h n)
    (E : Ω → Matrix (Fin (rem+1)) (Fin n) ℝ)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n ⊕ Unit))
    (a : ℝ≥0) (ha : a ≤ H)
    (ht : scalarPaperQueryTime h K k ∈ Icc (0 : ℝ) (a : ℝ))
    (hv : scalarPaperQueryTime h K (k+1) ∈ Icc (0 : ℝ) (a : ℝ))
    (hz : ∀ i,Measurable[𝔪] (fun ω => (S ω).1.1 i))
    (hB : ∀ i,Measurable[𝔪] (fun ω => (S ω).2 i))
    (hD : ∀ i (t : Icc (0 : ℝ) (H : ℝ)), (t : ℝ) ≤ a →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t))
    (hbridge : ∀ i,Measurable[𝔪] (fun ω => (S ω).1.2.2 (K-k) i))
    (hE : ∀ i j,Measurable[𝔪] (fun ω => E ω i j))
    (hW : Measurable[𝔪] W) (hZ : Measurable[𝔪] Z) :
    ∀ i,Measurable[𝔪] (fun ω => (scalarPaperUpdate H h n K k (S ω)
      (paperQueriedNoise N
        (paperFrame (E ω) (scalarPaperTarget b f g hf hg mfield scale H h n K k (S ω)))
        (W ω) (Z ω))).2 i) := by
  let : MeasurableSpace Ω := 𝔪
  have hTarget (i : Fin n) := scalarPaperTarget_measurable_of_D_past 𝔪 b f g hf hg
    mfield hmfield scale H h n K k S i a ha ht hv (hz i) (hB i) (hD i)
  have hF := paperFrame_measurable E
    (fun ω => scalarPaperTarget b f g hf hg mfield scale H h n K k (S ω)) hE hTarget
  have hFm : Measurable (fun ω => paperFrame (E ω)
      (scalarPaperTarget b f g hf hg mfield scale H h n K k (S ω))) :=
    Measurable.of_eval (fun i => Measurable.of_eval (hF i))
  have hNoise := (measurable_paperQueriedNoise rem n N).comp
    ((hFm.prodMk hW).prodMk hZ)
  intro i
  apply (measurable_scalarAppendQueryInterval H h (scalarPaperQueryTime h K k)).comp
  exact (hB i).prodMk
    (((show Measurable (fun z : EuclideanSpace ℝ (Fin n ⊕ Unit) => z (.inl i)) from by
      fun_prop).comp hNoise).prodMk (hbridge i))

end SKConstants
