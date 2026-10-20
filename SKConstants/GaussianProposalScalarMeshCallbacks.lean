module

public import SKConstants.GaussianProposalScalarCallbacks
public import SKConstants.GaussianProposalQueryTrace
public import SKConstants.GrowingQueryMesh
public import SKConstants.ScalarProcessContinuationProfiles
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators Matrix
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
abbrev ScalarMeshPaperStatic (H : ℝ≥0) (δ _τ : ℕ → ℝ≥0) (n : ℕ) :=
  (Fin n → ℝ) × ((Fin n → ScalarContinuousPath H) ×
    ((j : ℕ) → Fin n → ScalarContinuousPath (δ j)))

abbrev ScalarMeshPaperPast (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) :=
  ScalarMeshPaperStatic H δ τ n × (Fin n → ScalarContinuousPath H)

def scalarMeshPaperObservation (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (s : ScalarMeshPaperPast H δ τ n) (i : Fin n) : ScalarContinuousPath H :=
  scalarTwoDriverPicardPath b f g hf hg H (s.1.1 i,(s.2 i,s.1.2.1 i))

theorem measurable_scalarMeshPaperObservation (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (i : Fin n) :
    Measurable (fun s => scalarMeshPaperObservation b f g hf hg H δ τ n s i) := by
  apply (measurable_scalarTwoDriverPicardPath b f g hf hg H).comp
  exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).prodMk
    (((measurable_pi_apply i).comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))))

def scalarMeshPaperQueryTime (τ : ℕ → ℝ≥0) (K k : ℕ) : ℝ := τ (K-k)

def scalarMeshPaperTarget (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (i : Fin n) : ℝ :=
  let t := scalarMeshPaperQueryTime τ K k
  let a := scalarMeshPaperQueryTime τ K (k+1)
  (m t (scalarMeshPaperObservation b f g hf hg H δ τ n s i (projIcc 0 (H : ℝ) H.coe_nonneg t)) -
    m a (scalarMeshPaperObservation b f g hf hg H δ τ n s i (projIcc 0 (H : ℝ) H.coe_nonneg a))) /
      scale (K-k)

theorem measurable_scalarMeshPaperTarget (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ) (i : Fin n) :
    Measurable (fun s => scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s i) := by
  have hY := measurable_scalarMeshPaperObservation b f g hf hg H δ τ n i
  exact ((hm.comp (measurable_const.prodMk
      ((ContinuousMap.measurable_eval _).comp hY))).sub
    (hm.comp (measurable_const.prodMk
      ((ContinuousMap.measurable_eval _).comp hY)))).div_const _

def scalarMeshPaperUpdate (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ) (s : ScalarMeshPaperPast H δ τ n)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) : ScalarMeshPaperPast H δ τ n :=
  (s.1,fun i => scalarAppendQueryInterval H (δ (K-k)) (scalarMeshPaperQueryTime τ K k)
    (s.2 i,(z (.inl i),s.1.2.2 (K-k) i)))

theorem measurable_scalarMeshPaperUpdate (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ) :
    Measurable (Function.uncurry (scalarMeshPaperUpdate H δ τ n K k)) := by
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply Measurable.of_eval
  intro i
  apply (measurable_scalarAppendQueryInterval H (δ (K-k)) (scalarMeshPaperQueryTime τ K k)).comp
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).prodMk
    (((show Measurable (fun z : EuclideanSpace ℝ (Fin n ⊕ Unit) => z (.inl i)) from by fun_prop).comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp ((measurable_pi_apply (K-k)).comp
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))))

def scalarMeshPaperTruncateD (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (a : ℝ) (s : ScalarMeshPaperPast H δ τ n) :
    ScalarMeshPaperPast H δ τ n :=
  ((s.1.1,(fun i => scalarPathPrefixTruncate H a (s.1.2.1 i),s.1.2.2)),s.2)

theorem measurable_scalarMeshPaperTruncateD (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (a : ℝ) :
    Measurable (scalarMeshPaperTruncateD H δ τ n a) := by
  apply Measurable.prodMk _ measurable_snd
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply Measurable.prodMk _ (measurable_snd.comp (measurable_snd.comp measurable_fst))
  apply Measurable.of_eval
  intro i
  exact (measurable_scalarPathPrefixTruncate H a).comp
    ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))

theorem scalarMeshPaperObservation_truncateD (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (s : ScalarMeshPaperPast H δ τ n) (i : Fin n)
    (a : ℝ≥0) (ha : a ≤ H) (t : Icc (0 : ℝ) (H : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarMeshPaperObservation b f g hf hg H δ τ n (scalarMeshPaperTruncateD H δ τ n a s) i t =
      scalarMeshPaperObservation b f g hf hg H δ τ n s i t := by
  apply scalarTwoDriverPicardPath_congr_prefix b f g hf hg H
    (s.1.1 i) (s.2 i) (s.2 i) _ _ a ha _ _ t ht
  · exact fun _ _ => rfl
  · intro u hu
    exact scalarPathPrefixTruncate_prefix H a (s.1.2.1 i) u hu

theorem scalarMeshPaperTarget_truncateD (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (i : Fin n)
    (a : ℝ≥0) (ha : a ≤ H)
    (ht : scalarMeshPaperQueryTime τ K k ∈ Icc (0 : ℝ) (a : ℝ))
    (hv : scalarMeshPaperQueryTime τ K (k+1) ∈ Icc (0 : ℝ) (a : ℝ)) :
    scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k
      (scalarMeshPaperTruncateD H δ τ n a s) i =
        scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s i := by
  have htH : scalarMeshPaperQueryTime τ K k ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨ht.1,ht.2.trans ha⟩
  have hvH : scalarMeshPaperQueryTime τ K (k+1) ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨hv.1,hv.2.trans ha⟩
  dsimp only [scalarMeshPaperTarget]
  rw [projIcc_of_mem _ htH,projIcc_of_mem _ hvH,
    scalarMeshPaperObservation_truncateD b f g hf hg H δ τ n s i a ha _ ht.2,
    scalarMeshPaperObservation_truncateD b f g hf hg H δ τ n s i a ha _ hv.2]

open GaussianProposal in
theorem scalarMeshPaperProposal_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r K : ℕ) (s : ScalarMeshPaperPast H δ τ (r+K)) :
    (stoppedNoiseLaw (Fin (r+K)) K).map
      (actualPaperProposal r K (skSigma (r+K))
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) s) =
      skDisorderLaw (r+K) := by
  simpa only [skDisorderLaw,skSigma,Nat.cast_add,Nat.cast_ofNat] using
    actualPaperProposal_law r K (skSigma (r+K)) _ _
    (fun k i => measurable_scalarMeshPaperTarget b f g hf hg m hm scale H δ τ (r+K) K k i)
    (fun k => measurable_scalarMeshPaperUpdate H δ τ (r+K) K k) s

open GaussianProposal in
theorem scalarMeshPaperProposal_joint_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r K : ℕ)
    (μ : Measure (ScalarMeshPaperPast H δ τ (r+K))) [SFinite μ] :
    (μ.prod (stoppedNoiseLaw (Fin (r+K)) K)).map (fun p =>
      (p.1,actualPaperProposal r K (skSigma (r+K))
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) p.1 p.2)) =
      μ.prod (skDisorderLaw (r+K)) := by
  simpa only [skDisorderLaw,skSigma,Nat.cast_add,Nat.cast_ofNat] using
    actualPaperProposal_joint_law μ r K (skSigma (r+K)) _ _
    (fun k i => measurable_scalarMeshPaperTarget b f g hf hg m hm scale H δ τ (r+K) K k i)
    (fun k => measurable_scalarMeshPaperUpdate H δ τ (r+K) K k)

open GaussianProposal in
theorem scalarMeshPaperProposal_matrix_query_coupling
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (s : ScalarMeshPaperPast H δ τ (r+K)) (z : StoppedNoise (Fin (r+K)) K) :
    paperMatrixQueryRun r (r+K) (r+K)
      (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
      (scalarMeshPaperUpdate H δ τ (r+K) K) K (s,1) z
      (actualPaperProposal r K (skSigma (r+K))
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K)
        (scalarMeshPaperUpdate H δ τ (r+K) K) s z) =
      proposalTerminalPast (scalarMeshPaperUpdate H δ τ (r+K) K) K s z :=
  actualPaperProposal_matrix_query_coupling r K (r+K) (by exact_mod_cast hN) _ _ s z

def scalarMeshPaperIncrementScale (r : ℝ → ℝ) (τ : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  Real.sqrt (∫ v in (τ (j-1) : ℝ)..(τ j : ℝ),r v)

theorem scalarMeshPaperUpdate_B_endpoint (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ) (hh : 0 < δ (K-k))
    (s : ScalarMeshPaperPast H δ τ n) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (ha : 0 ≤ scalarMeshPaperQueryTime τ K k)
    (haH : scalarMeshPaperQueryTime τ K k+(δ (K-k) : ℝ) ≤ H) :
    (scalarMeshPaperUpdate H δ τ n K k s z).2 i
        ⟨scalarMeshPaperQueryTime τ K k+(δ (K-k) : ℝ),by constructor <;> linarith [(δ (K-k)).coe_nonneg]⟩ -
      s.2 i ⟨scalarMeshPaperQueryTime τ K k,⟨ha,by linarith [(δ (K-k)).coe_nonneg]⟩⟩ =
        Real.sqrt (δ (K-k))*z (.inl i) := by
  change scalarAppendQueryInterval H (δ (K-k)) (scalarMeshPaperQueryTime τ K k)
      (s.2 i,(z (.inl i),s.1.2.2 (K-k) i)) _ - _ = _
  rw [scalarAppendQueryInterval_on_interval H (δ (K-k)) _ ha haH _ ⟨δ (K-k),(δ (K-k)).coe_nonneg,le_rfl⟩,
    scalarQueryBridgeComplete_endpoint (δ (K-k)) hh]
  ring

theorem scalarMeshPaperUpdate_B_congr (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (s t : ScalarMeshPaperPast H δ τ n) (z : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hB : s.2 = t.2) (hbridge : s.1.2.2 (K-k) = t.1.2.2 (K-k)) :
    (scalarMeshPaperUpdate H δ τ n K k s z).2 = (scalarMeshPaperUpdate H δ τ n K k t z).2 := by
  funext i
  dsimp only [scalarMeshPaperUpdate]
  rw [hB,hbridge]

theorem scalarMeshPaperTarget_measurable_of_D_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (S : Ω → ScalarMeshPaperPast H δ τ n) (i : Fin n)
    (a : ℝ≥0) (ha : a ≤ H)
    (ht : scalarMeshPaperQueryTime τ K k ∈ Icc (0 : ℝ) (a : ℝ))
    (hv : scalarMeshPaperQueryTime τ K (k+1) ∈ Icc (0 : ℝ) (a : ℝ))
    (hz : Measurable[𝔪] (fun ω => (S ω).1.1 i))
    (hB : Measurable[𝔪] (fun ω => (S ω).2 i))
    (hD : ∀ t : Icc (0 : ℝ) (H : ℝ), (t : ℝ) ≤ a →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t)) :
    Measurable[𝔪] (fun ω => scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k (S ω) i) := by
  let : MeasurableSpace Ω := 𝔪
  have hDp := scalarPathPrefixTruncate_measurable_of_past 𝔪 H a ha
    (fun ω => (S ω).1.2.1 i) hD
  let Y : Ω → ScalarContinuousPath H := fun ω => scalarTwoDriverPicardPath b f g hf hg H
    ((S ω).1.1 i,((S ω).2 i,scalarPathPrefixTruncate H a ((S ω).1.2.1 i)))
  have hY : Measurable Y := (measurable_scalarTwoDriverPicardPath b f g hf hg H).comp
    (hz.prodMk (hB.prodMk hDp))
  have hTarget : Measurable (fun ω => scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k
      (scalarMeshPaperTruncateD H δ τ n a (S ω)) i) := by
    exact ((hm.comp (measurable_const.prodMk
        ((ContinuousMap.measurable_eval _).comp hY))).sub
      (hm.comp (measurable_const.prodMk
        ((ContinuousMap.measurable_eval _).comp hY)))).div_const _
  convert hTarget using 1
  funext ω
  exact (scalarMeshPaperTarget_truncateD b f g hf hg m scale H δ τ n K k (S ω) i a ha ht hv).symm

open GaussianProposal in
theorem scalarMeshPaperCurrentB_measurable_of_D_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (mfield : ℝ → ℝ → ℝ) (hmfield : Measurable (Function.uncurry mfield))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k rem : ℕ) (N : ℝ)
    (S : Ω → ScalarMeshPaperPast H δ τ n)
    (E : Ω → Matrix (Fin (rem+1)) (Fin n) ℝ)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n ⊕ Unit))
    (a : ℝ≥0) (ha : a ≤ H)
    (ht : scalarMeshPaperQueryTime τ K k ∈ Icc (0 : ℝ) (a : ℝ))
    (hv : scalarMeshPaperQueryTime τ K (k+1) ∈ Icc (0 : ℝ) (a : ℝ))
    (hz : ∀ i,Measurable[𝔪] (fun ω => (S ω).1.1 i))
    (hB : ∀ i,Measurable[𝔪] (fun ω => (S ω).2 i))
    (hD : ∀ i (t : Icc (0 : ℝ) (H : ℝ)), (t : ℝ) ≤ a →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t))
    (hbridge : ∀ i,Measurable[𝔪] (fun ω => (S ω).1.2.2 (K-k) i))
    (hE : ∀ i j,Measurable[𝔪] (fun ω => E ω i j))
    (hW : Measurable[𝔪] W) (hZ : Measurable[𝔪] Z) :
    ∀ i,Measurable[𝔪] (fun ω => (scalarMeshPaperUpdate H δ τ n K k (S ω)
      (paperQueriedNoise N
        (paperFrame (E ω) (scalarMeshPaperTarget b f g hf hg mfield scale H δ τ n K k (S ω)))
        (W ω) (Z ω))).2 i) := by
  let : MeasurableSpace Ω := 𝔪
  have hTarget (i : Fin n) := scalarMeshPaperTarget_measurable_of_D_past 𝔪 b f g hf hg
    mfield hmfield scale H δ τ n K k S i a ha ht hv (hz i) (hB i) (hD i)
  have hF := paperFrame_measurable E
    (fun ω => scalarMeshPaperTarget b f g hf hg mfield scale H δ τ n K k (S ω)) hE hTarget
  have hFm : Measurable (fun ω => paperFrame (E ω)
      (scalarMeshPaperTarget b f g hf hg mfield scale H δ τ n K k (S ω))) :=
    Measurable.of_eval (fun i => Measurable.of_eval (hF i))
  have hNoise := (measurable_paperQueriedNoise rem n N).comp
    ((hFm.prodMk hW).prodMk hZ)
  intro i
  apply (measurable_scalarAppendQueryInterval H (δ (K-k)) (scalarMeshPaperQueryTime τ K k)).comp
  exact (hB i).prodMk
    (((show Measurable (fun z : EuclideanSpace ℝ (Fin n ⊕ Unit) => z (.inl i)) from by
      fun_prop).comp hNoise).prodMk (hbridge i))

theorem scalarMeshPaperIncrementScale_pos (r : ℝ → ℝ) (hr : Continuous r)
    (hpos : ∀ v,0 < r v) (τ : ℕ → ℝ≥0) (hτ : StrictMono τ)
    (j : ℕ) (hj : 0 < j) : 0 < scalarMeshPaperIncrementScale r τ j := by
  apply Real.sqrt_pos.2
  exact intervalIntegral.integral_pos
    (by exact_mod_cast hτ (show j-1 < j by omega)) hr.continuousOn
    (fun x _ => (hpos x).le) ⟨τ (j-1),⟨le_rfl,(by exact_mod_cast (hτ.monotone (show j-1≤j by omega)))⟩,hpos _⟩

theorem scalarMeshPaperTarget_measurable_at_queryTime {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n K k : ℕ)
    (S : Ω → ScalarMeshPaperPast H δ τ n) (i : Fin n)
    (hH : τ (K-k) ≤ H)
    (hz : Measurable[𝔪] (fun ω => (S ω).1.1 i))
    (hB : Measurable[𝔪] (fun ω => (S ω).2 i))
    (hD : ∀ t : Icc (0 : ℝ) (H : ℝ), (t : ℝ) ≤ τ (K-k) →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t)) :
    Measurable[𝔪] (fun ω => scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k (S ω) i) := by
  exact scalarMeshPaperTarget_measurable_of_D_past 𝔪 b f g hf hg m hm scale H δ τ
    n K k S i (τ (K-k)) hH ⟨(τ (K-k)).coe_nonneg,le_rfl⟩
    ⟨(τ (K-(k+1))).coe_nonneg,hτ (by omega)⟩ hz hB hD

abbrev ScalarGrowingPaperPast (H δ : ℝ≥0) (n : ℕ) :=
  ScalarMeshPaperPast H (growingQueryDuration δ) (growingQueryTime δ) n

def scalarGrowingPaperTarget (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (H δ : ℝ≥0) (n K k : ℕ)
    (s : ScalarGrowingPaperPast H δ n) (i : Fin n) : ℝ :=
  scalarMeshPaperTarget b f g hf hg m
    (scalarMeshPaperIncrementScale r (growingQueryTime δ)) H
    (growingQueryDuration δ) (growingQueryTime δ) n K k s i

def scalarGrowingPaperUpdate (H δ : ℝ≥0) (n K k : ℕ)
    (s : ScalarGrowingPaperPast H δ n) (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    ScalarGrowingPaperPast H δ n :=
  scalarMeshPaperUpdate H (growingQueryDuration δ) (growingQueryTime δ) n K k s z

open GaussianProposal in
theorem scalarGrowingPaperProposal_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (H δ : ℝ≥0) (ranks K : ℕ)
    (s : ScalarGrowingPaperPast H δ (ranks+K)) :
    (stoppedNoiseLaw (Fin (ranks+K)) K).map
      (actualPaperProposal ranks K (skSigma (ranks+K))
        (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
        (scalarGrowingPaperUpdate H δ (ranks+K) K) s) = skDisorderLaw (ranks+K) :=
  scalarMeshPaperProposal_law b f g hf hg m hm _ H _ _ ranks K s

open GaussianProposal in
theorem scalarGrowingPaperProposal_joint_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (H δ : ℝ≥0) (ranks K : ℕ)
    (μ : Measure (ScalarGrowingPaperPast H δ (ranks+K))) [SFinite μ] :
    (μ.prod (stoppedNoiseLaw (Fin (ranks+K)) K)).map (fun p =>
      (p.1,actualPaperProposal ranks K (skSigma (ranks+K))
        (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
        (scalarGrowingPaperUpdate H δ (ranks+K) K) p.1 p.2)) =
      μ.prod (skDisorderLaw (ranks+K)) :=
  scalarMeshPaperProposal_joint_law b f g hf hg m hm _ H _ _ ranks K μ

open GaussianProposal in
theorem scalarGrowingPaperProposal_matrix_query_coupling
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (H δ : ℝ≥0) (ranks K : ℕ) (hN : 0 < ranks+K)
    (s : ScalarGrowingPaperPast H δ (ranks+K)) (z : StoppedNoise (Fin (ranks+K)) K) :
    paperMatrixQueryRun ranks (ranks+K) (ranks+K)
      (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
      (scalarGrowingPaperUpdate H δ (ranks+K) K) K (s,1) z
      (actualPaperProposal ranks K (skSigma (ranks+K))
        (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
        (scalarGrowingPaperUpdate H δ (ranks+K) K) s z) =
      proposalTerminalPast (scalarGrowingPaperUpdate H δ (ranks+K) K) K s z :=
  scalarMeshPaperProposal_matrix_query_coupling b f g hf hg m _ H _ _ ranks K hN s z

theorem scalarGrowingPaperUpdate_B_endpoint (H δ : ℝ≥0) (hδ : 0 < δ) (n K k : ℕ)
    (s : ScalarGrowingPaperPast H δ n) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hH : growingQueryTime δ (K-k+1) ≤ H) :
    (scalarGrowingPaperUpdate H δ n K k s z).2 i
        ⟨growingQueryTime δ (K-k+1),(growingQueryTime δ (K-k+1)).coe_nonneg,hH⟩ -
      s.2 i ⟨growingQueryTime δ (K-k),(growingQueryTime δ (K-k)).coe_nonneg,
        (growingQueryTime_strictMono δ hδ).monotone (by omega) |>.trans hH⟩ =
        Real.sqrt (growingQueryDuration δ (K-k))*z (.inl i) := by
  have H := scalarMeshPaperUpdate_B_endpoint H (growingQueryDuration δ) (growingQueryTime δ)
    n K k (growingQueryDuration_pos δ hδ _) s i z (growingQueryTime δ (K-k)).coe_nonneg
    (by
      have hHr : (growingQueryTime δ (K-k+1) : ℝ) ≤ H := by exact_mod_cast hH
      simpa only [scalarMeshPaperQueryTime,← NNReal.coe_add,← growingQueryTime_succ] using hHr)
  simpa only [scalarGrowingPaperUpdate,scalarMeshPaperQueryTime,
    ← NNReal.coe_add,← growingQueryTime_succ] using H

theorem scalarGrowing_actualParisiIncrementScale_pos {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (hδ : 0 < δ)
    (j : ℕ) (hj : 0 < j) :
    0 < scalarMeshPaperIncrementScale (actualParisiContinuationR W β) (growingQueryTime δ) j :=
  scalarMeshPaperIncrementScale_pos _ (continuous_actualParisiContinuationR W β)
    (actualParisiContinuationR_pos W β) _ (growingQueryTime_strictMono δ hδ) j hj

open GaussianProposal in
theorem scalarGrowingPaperCurrentB_measurable_of_D_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (mfield : ℝ → ℝ → ℝ) (hmfield : Measurable (Function.uncurry mfield))
    (r : ℝ → ℝ) (H δ : ℝ≥0) (hδ : 0 < δ) (n K k rem : ℕ) (N : ℝ)
    (S : Ω → ScalarGrowingPaperPast H δ n)
    (E : Ω → Matrix (Fin (rem+1)) (Fin n) ℝ)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hH : growingQueryTime δ (K-k) ≤ H)
    (hz : ∀ i,Measurable[𝔪] (fun ω => (S ω).1.1 i))
    (hB : ∀ i,Measurable[𝔪] (fun ω => (S ω).2 i))
    (hD : ∀ i (t : Icc (0 : ℝ) (H : ℝ)), (t : ℝ) ≤ growingQueryTime δ (K-k) →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t))
    (hbridge : ∀ i,Measurable[𝔪] (fun ω => (S ω).1.2.2 (K-k) i))
    (hE : ∀ i j,Measurable[𝔪] (fun ω => E ω i j))
    (hW : Measurable[𝔪] W) (hZ : Measurable[𝔪] Z) :
    ∀ i,Measurable[𝔪] (fun ω => (scalarGrowingPaperUpdate H δ n K k (S ω)
      (paperQueriedNoise N
        (paperFrame (E ω) (scalarGrowingPaperTarget b f g hf hg mfield r H δ n K k (S ω)))
        (W ω) (Z ω))).2 i) := by
  exact scalarMeshPaperCurrentB_measurable_of_D_past 𝔪 b f g hf hg mfield hmfield
    (scalarMeshPaperIncrementScale r (growingQueryTime δ)) H
    (growingQueryDuration δ) (growingQueryTime δ) n K k rem N S E W Z
    (growingQueryTime δ (K-k)) hH
    ⟨(growingQueryTime δ (K-k)).coe_nonneg,le_rfl⟩
    ⟨(growingQueryTime δ (K-(k+1))).coe_nonneg,
      (growingQueryTime_strictMono δ hδ).monotone (by omega)⟩
    hz hB hD hbridge hE hW hZ

theorem scalarGrowingPaper_target_scale_pos (r : ℝ → ℝ) (hr : Continuous r)
    (hpos : ∀ v,0 < r v) (δ : ℝ≥0) (hδ : 0 < δ) (K k : ℕ) (hk : k < K) :
    0 < scalarMeshPaperIncrementScale r (growingQueryTime δ) (K-k) :=
  scalarMeshPaperIncrementScale_pos r hr hpos _
    (growingQueryTime_strictMono δ hδ) _ (by omega)

open GaussianProposal in
theorem scalarGrowingPaper_remainingProjection_eq_past_queries
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (H δ : ℝ≥0) (ranks K : ℕ)
    (N : ℝ) (hN : 0 < N) (s : ScalarGrowingPaperPast H δ (ranks+K))
    (z : StoppedNoise (Fin (ranks+K)) K) (j : Fin (K+1)) :
    paperRemainingProjectionTrace ranks (ranks+K)
      (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
      (scalarGrowingPaperUpdate H δ (ranks+K) K) K (s,1) z j =
      1-∑ i : Fin K,if i.val<j.val then (1/N) •
        Matrix.vecMulVec (paperQueryDirectionTrace ranks (ranks+K) N
          (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
          (scalarGrowingPaperUpdate H δ (ranks+K) K) K (s,1) z i)
          (paperQueryDirectionTrace ranks (ranks+K) N
          (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
          (scalarGrowingPaperUpdate H δ (ranks+K) K) K (s,1) z i) else 0 :=
  by simpa only [one_div] using
    actualPaper_remainingProjection_eq_past_queries ranks K N hN
      (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+K) K)
      (scalarGrowingPaperUpdate H δ (ranks+K) K) s z j

end SKConstants
