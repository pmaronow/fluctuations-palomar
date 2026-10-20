module

public import SKConstants.GaussianProposalScalarAugmentation
public import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix
namespace SKConstants
open GaussianProposal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def ScalarMeshPastPrefixEq (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (a : ℝ≥0)
    (s t : ScalarMeshPaperPast H δ τ n) : Prop :=
  s.1.1=t.1.1 ∧ s.1.2.2=t.1.2.2 ∧
    (∀ i (u : Icc (0 : ℝ) (H : ℝ)),(u : ℝ)≤a → s.2 i u=t.2 i u) ∧
    (∀ i (u : Icc (0 : ℝ) (H : ℝ)),(u : ℝ)≤a → s.1.2.1 i u=t.1.2.1 i u)

lemma scalarMeshPaperObservation_eq_of_prefix
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ) (a : ℝ≥0) (ha : a≤H)
    (s t : ScalarMeshPaperPast H δ τ n) (h : ScalarMeshPastPrefixEq H δ τ n a s t)
    (i : Fin n) (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ)≤a) :
    scalarMeshPaperObservation b f g hf hg H δ τ n s i u =
      scalarMeshPaperObservation b f g hf hg H δ τ n t i u := by
  change scalarTwoDriverPicardPath b f g hf hg H (s.1.1 i,(s.2 i,s.1.2.1 i)) u = _
  rw [h.1]
  exact scalarTwoDriverPicardPath_congr_prefix b f g hf hg H (t.1.1 i)
    (s.2 i) (t.2 i) (s.1.2.1 i) (t.1.2.1 i) a ha (h.2.2.1 i) (h.2.2.2 i) u hu

lemma scalarMeshPaperTarget_eq_of_prefix
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n q k : ℕ) (a : ℝ≥0) (ha : a≤H)
    (s t : ScalarMeshPaperPast H δ τ n) (h : ScalarMeshPastPrefixEq H δ τ n a s t)
    (ht : τ (q-k)≤a) (hv : τ (q-(k+1))≤a) :
    scalarMeshPaperTarget b f g hf hg m scale H δ τ n q k s =
      scalarMeshPaperTarget b f g hf hg m scale H δ τ n q k t := by
  funext i
  dsimp only [scalarMeshPaperTarget,scalarMeshPaperQueryTime]
  have htH : (τ (q-k) : ℝ)∈Icc (0 : ℝ) (H : ℝ) := ⟨(τ _).coe_nonneg,ht.trans ha⟩
  have hvH : (τ (q-(k+1)) : ℝ)∈Icc (0 : ℝ) (H : ℝ) := ⟨(τ _).coe_nonneg,hv.trans ha⟩
  rw [projIcc_of_mem _ htH,projIcc_of_mem _ hvH]
  rw [scalarMeshPaperObservation_eq_of_prefix b f g hf hg H δ τ n a ha s t h i _ ht,
    scalarMeshPaperObservation_eq_of_prefix b f g hf hg H δ τ n a ha s t h i _ hv]

lemma scalarMeshPaperUpdate_prefix_of_endpoint_eq
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n q k : ℕ) (a : ℝ≥0)
    (s t : ScalarMeshPaperPast H δ τ n) (h : ScalarMeshPastPrefixEq H δ τ n a s t)
    (z w : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hz : ∀ i : Fin n,z (.inl i)=w (.inl i)) :
    ScalarMeshPastPrefixEq H δ τ n a
      (scalarMeshPaperUpdate H δ τ n q k s z) (scalarMeshPaperUpdate H δ τ n q k t w) := by
  refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
  intro i u hu
  change scalarAppendQueryInterval H (δ (q-k)) (τ (q-k))
    (s.2 i,(z (.inl i),s.1.2.2 (q-k) i)) u =
    scalarAppendQueryInterval H (δ (q-k)) (τ (q-k))
    (t.2 i,(w (.inl i),t.1.2.2 (q-k) i)) u
  have hm : min (u : ℝ) (τ (q-k) : ℝ)∈Icc (0 : ℝ) (H : ℝ) :=
    ⟨le_min u.property.1 (τ _).coe_nonneg,(min_le_left _ _).trans u.property.2⟩
  simp only [scalarAppendQueryInterval,ContinuousMap.coe_mk,projIcc_of_mem _ hm]
  rw [h.2.2.1 i _ ((min_le_left _ _).trans hu),hz i,h.2.1]

lemma scalarMeshMatrixQueryRun_static
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r n q K : ℕ) (N : ℝ)
    (s : PaperState r n K (ScalarMeshPaperPast H δ τ n))
    (z : StoppedNoise (Fin n) K) (W : Matrix (Fin n) (Fin n) ℝ) :
    (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
      (scalarMeshPaperUpdate H δ τ n q) K s z W).1=s.1.1 := by
  induction K with
  | zero => rfl
  | succ K ih => exact ih _ _

lemma scalarMeshMatrixQueryRun_B_prefix_of_before
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r n q K : ℕ) (N : ℝ)
    (s : PaperState r n K (ScalarMeshPaperPast H δ τ n))
    (z : StoppedNoise (Fin n) K) (W : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ≥0) (hbefore : ∀ k<K,a≤τ (q-k))
    (i : Fin n) (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ)≤a) :
    (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
      (scalarMeshPaperUpdate H δ τ n q) K s z W).2 i u=s.1.2 i u := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [paperMatrixQueryRun]
    rw [ih _ _ (fun k hk => hbefore k (hk.trans (Nat.lt_succ_self K)))]
    exact scalarAppendQueryInterval_prefix H (δ (q-K)) (τ (q-K)) _ u
      (hu.trans (hbefore K (Nat.lt_succ_self K)))

theorem scalarMeshMatrixQueryRun_prefix_congr
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (hτ : Monotone τ) (r n q K : ℕ) (N : ℝ)
    (a : ℝ≥0) (ha : a≤H)
    (s t : ScalarMeshPaperPast H δ τ n) (h : ScalarMeshPastPrefixEq H δ τ n a s t)
    (E : Matrix (Fin (r+K)) (Fin n) ℝ)
    (z : StoppedNoise (Fin n) K) (W : Matrix (Fin n) (Fin n) ℝ) :
    ScalarMeshPastPrefixEq H δ τ n a
      (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
        (scalarMeshPaperUpdate H δ τ n q) K (s,E) z W)
      (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
        (scalarMeshPaperUpdate H δ τ n q) K (t,E) z W) := by
  induction K generalizing s t with
  | zero => exact h
  | succ K ih =>
    by_cases hb : a≤τ (q-K)
    · have hbefore : ∀ k<K+1,a≤τ (q-k) := fun k hk =>
        hb.trans (hτ (by omega))
      have hs := scalarMeshMatrixQueryRun_static b f g hf hg m scale H δ τ r n q (K+1) N (s,E) z W
      have ht := scalarMeshMatrixQueryRun_static b f g hf hg m scale H δ τ r n q (K+1) N (t,E) z W
      refine ⟨?_,?_,?_,?_⟩
      · exact (congrArg (fun v => v.1) hs).trans (h.1.trans (congrArg (fun v => v.1) ht).symm)
      · exact (congrArg (fun v => v.2.2) hs).trans (h.2.1.trans (congrArg (fun v => v.2.2) ht).symm)
      · intro i u hu
        rw [scalarMeshMatrixQueryRun_B_prefix_of_before b f g hf hg m scale H δ τ r n q (K+1) N
          (s,E) z W a hbefore i u hu,
          scalarMeshMatrixQueryRun_B_prefix_of_before b f g hf hg m scale H δ τ r n q (K+1) N
          (t,E) z W a hbefore i u hu]
        exact h.2.2.1 i u hu
      · intro i u hu
        rw [hs,ht]
        exact h.2.2.2 i u hu
    · have hc : τ (q-K)≤a := (not_le.mp hb).le
      have hv : τ (q-(K+1))≤a := (hτ (by omega)).trans hc
      have he := scalarMeshPaperTarget_eq_of_prefix b f g hf hg m scale H δ τ n q K a ha s t h hc hv
      rw [paperMatrixQueryRun,paperMatrixQueryRun,he]
      apply ih
      exact scalarMeshPaperUpdate_prefix_of_endpoint_eq H δ τ n q K a s t h _ _ (fun _ => rfl)

lemma scalarMeshPaperTruncateD_prefix (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ)
    (a : ℝ≥0) (s : ScalarMeshPaperPast H δ τ n) :
    ScalarMeshPastPrefixEq H δ τ n a s (scalarMeshPaperTruncateD H δ τ n a s) := by
  refine ⟨rfl,rfl,fun _ _ _ => rfl,?_⟩
  intro i u hu
  exact (scalarPathPrefixTruncate_prefix H a (s.1.2.1 i) u hu).symm

theorem scalarMeshMatrixQueryRun_observation_truncateD
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (hτ : Monotone τ) (r n q K : ℕ) (N : ℝ)
    (a : ℝ≥0) (ha : a≤H)
    (s : ScalarMeshPaperPast H δ τ n) (E : Matrix (Fin (r+K)) (Fin n) ℝ)
    (z : StoppedNoise (Fin n) K) (W : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ)≤a) :
    scalarMeshPaperObservation b f g hf hg H δ τ n
      (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
        (scalarMeshPaperUpdate H δ τ n q) K (s,E) z W) i u =
    scalarMeshPaperObservation b f g hf hg H δ τ n
      (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
        (scalarMeshPaperUpdate H δ τ n q) K (scalarMeshPaperTruncateD H δ τ n a s,E) z W) i u :=
  scalarMeshPaperObservation_eq_of_prefix b f g hf hg H δ τ n a ha _ _
    (scalarMeshMatrixQueryRun_prefix_congr b f g hf hg m scale H δ τ hτ r n q K N a ha s _
      (scalarMeshPaperTruncateD_prefix H δ τ n a s) E z W) i u hu

lemma paperMatrixQueryRun_measurable_of_inputs {Past Ω : Type*}
    [MeasurableSpace Past] [MeasurableSpace Ω]
    (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k i,Measurable (fun a => target k a i))
    (hupdate : ∀ k,Measurable (Function.uncurry (update k))) (K : ℕ)
    (S : Ω → Past) (E : Ω → Matrix (Fin (r+K)) (Fin n) ℝ)
    (Z : Ω → StoppedNoise (Fin n) K) (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hS : Measurable S) (hE : Measurable E) (hZ : Measurable Z) (hW : Measurable W) :
    Measurable (fun ω => paperMatrixQueryRun r n N target update K (S ω,E ω) (Z ω) (W ω)) := by
  induction K generalizing S with
  | zero => exact hS
  | succ K ih =>
    let F (ω : Ω) := paperFrame (E ω) (target K (S ω))
    have hF (i : Fin (r+K+1)) (j : Fin n) : Measurable (fun ω => F ω i j) :=
      paperFrame_measurable E (fun ω => target K (S ω))
        (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hE))
        (fun j => (htarget K j).comp hS) i j
    have hFm : Measurable F := Measurable.of_eval (fun i => Measurable.of_eval (hF i))
    have hNoise := (measurable_paperQueriedNoise (r+K) n N).comp
      ((hFm.prodMk hW).prodMk hZ.fst)
    have hU := (hupdate K).comp (hS.prodMk hNoise)
    have hTail : Measurable (fun ω => tailRows (F ω)) :=
      Measurable.of_eval (fun i => Measurable.of_eval (fun j => hF i.succ j))
    change Measurable (fun ω => paperMatrixQueryRun r n N target update K
      (update K (S ω) (paperQueriedNoise N (F ω) (W ω) (Z ω).1),tailRows (F ω)) (Z ω).2 (W ω))
    exact ih _ _ _ hU hTail hZ.snd

lemma paperMatrixQueryRun_joint_measurable {Past : Type*} [MeasurableSpace Past]
    (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k i,Measurable (fun a => target k a i))
    (hupdate : ∀ k,Measurable (Function.uncurry (update k))) (K : ℕ) :
    Measurable (fun x : (PaperState r n K Past × StoppedNoise (Fin n) K) ×
        Matrix (Fin n) (Fin n) ℝ => paperMatrixQueryRun r n N target update K x.1.1 x.1.2 x.2) :=
  paperMatrixQueryRun_measurable_of_inputs r n N target update htarget hupdate K
    (fun x : (PaperState r n K Past × StoppedNoise (Fin n) K) × Matrix (Fin n) (Fin n) ℝ => x.1.1.1)
    (fun x => x.1.1.2) (fun x => x.1.2) (fun x => x.2)
    measurable_fst.fst.fst measurable_fst.fst.snd measurable_fst.snd measurable_snd

theorem scalarMeshMatrixQueryRun_observation_measurable_of_D_past {Ω : Type*}
    (𝔪 : MeasurableSpace Ω) (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m)) (scale : ℕ → ℝ)
    (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (hτ : Monotone τ) (r n q K : ℕ) (N : ℝ)
    (a : ℝ≥0) (ha : a≤H)
    (S : Ω → ScalarMeshPaperPast H δ τ n)
    (E : Ω → Matrix (Fin (r+K)) (Fin n) ℝ)
    (Z : Ω → StoppedNoise (Fin n) K) (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hz : Measurable[𝔪] (fun ω => (S ω).1.1))
    (hbridge : Measurable[𝔪] (fun ω => (S ω).1.2.2))
    (hB : Measurable[𝔪] (fun ω => (S ω).2))
    (hD : ∀ i (t : Icc (0 : ℝ) (H : ℝ)),(t : ℝ)≤a →
      Measurable[𝔪] (fun ω => (S ω).1.2.1 i t))
    (hE : Measurable[𝔪] E) (hZ : Measurable[𝔪] Z) (hW : Measurable[𝔪] W)
    (i : Fin n) (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ)≤a) :
    Measurable[𝔪] (fun ω => scalarMeshPaperObservation b f g hf hg H δ τ n
      (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
        (scalarMeshPaperUpdate H δ τ n q) K (S ω,E ω) (Z ω) (W ω)) i u) := by
  let : MeasurableSpace Ω := 𝔪
  have hDp : Measurable (fun ω i => scalarPathPrefixTruncate H a ((S ω).1.2.1 i)) := by
    apply Measurable.of_eval
    intro i
    exact scalarPathPrefixTruncate_measurable_of_past 𝔪 H a ha _ (hD i)
  have hS : Measurable (fun ω => scalarMeshPaperTruncateD H δ τ n a (S ω)) :=
    (hz.prodMk (hDp.prodMk hbridge)).prodMk hB
  have hRun := (paperMatrixQueryRun_joint_measurable r n N _ _
    (fun k j => measurable_scalarMeshPaperTarget b f g hf hg m hm scale H δ τ n q k j)
    (fun k => measurable_scalarMeshPaperUpdate H δ τ n q k) K).comp
    (((hS.prodMk hE).prodMk hZ).prodMk hW)
  have hY := ((ContinuousMap.measurable_eval u).comp
    (measurable_scalarMeshPaperObservation b f g hf hg H δ τ n i)).comp hRun
  convert hY using 1
  funext ω
  exact scalarMeshMatrixQueryRun_observation_truncateD b f g hf hg m scale H δ τ hτ
    r n q K N a ha (S ω) (E ω) (Z ω) (W ω) i u hu

abbrev ScalarGrowingReplayAuxData (δ : ℝ≥0) (n : ℕ) :=
  (Fin n → ScalarContinuousPath (growingQueryDuration δ 0)) ×
    ((j : ℕ) → Fin n → ScalarContinuousPath (growingQueryDuration δ j))

abbrev ScalarGrowingReplayStaticData (δ : ℝ≥0) (n q : ℕ) :=
  ScalarGrowingReplayAuxData δ n ×
    (Matrix (Fin n) (Fin n) ℝ × PaperCompletionNoise n q)

def scalarGrowingReplayStaticLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    Measure (ScalarGrowingReplayStaticData δ n q) :=
  ((Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
    (Measure.infinitePi (fun j : ℕ => Measure.pi
      (fun _ : Fin n => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))).prod
      ((skDisorderLaw n).prod (paperCompletionNoiseLaw n q))

instance scalarGrowingReplayStaticLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    IsProbabilityMeasure (scalarGrowingReplayStaticLaw W δ n q) := by
  unfold scalarGrowingReplayStaticLaw
  infer_instance

theorem scalarGrowingSourceReplayInput_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) :
    ((scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
      (paperAugmentedNoiseLaw (ranks+q) q)).map (fun p =>
        ((p.1.2,scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p.1 p.2),p.1.1)) =
      (scalarGrowingReplayStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) =>
          scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))) := by
  have hj := scalarGrowingSourceAugmentedOutput_joint_law W b f g hf hg m hm r δ ranks q
  have hPair := measurable_fst.prodMk
    (measurable_scalarGrowingSourceAugmentedOutput b f g hf hg m hm r δ ranks q)
  simp only [Function.uncurry_def] at hPair
  let shuffle : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q) ×
      (Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ × PaperCompletionNoise (ranks+q) q) →
      ScalarGrowingReplayStaticData δ (ranks+q) q ×
        (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q)) :=
    fun x => ((x.1.2,x.2),x.1.1)
  have hShuffle : Measurable shuffle :=
    (measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst
  have he := congrArg (fun μ => μ.map shuffle) hj
  rw [Measure.map_map hShuffle hPair] at he
  convert he using 1
  · rfl
  · let μD := Measure.pi (fun _ : Fin (ranks+q) =>
      scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))
    let μA := (Measure.pi (fun _ : Fin (ranks+q) =>
      scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
        (Measure.infinitePi (fun j : ℕ => Measure.pi (fun _ : Fin (ranks+q) =>
          scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))
    let μO := (skDisorderLaw (ranks+q)).prod (paperCompletionNoiseLaw (ranks+q) q)
    change (μA.prod μO).prod μD = ((μD.prod μA).prod μO).map
      (Prod.swap ∘ MeasurableEquiv.prodAssoc)
    rw [← Measure.map_map measurable_swap MeasurableEquiv.prodAssoc.measurable,
      Measure.prodAssoc_prod,Measure.prod_swap]

def scalarGrowingReplayField (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ)
    (t : ℝ≥0)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) : Fin (ranks+q) → ℝ :=
  let H := scalarGrowingSourceHorizon δ q
  let s := scalarGrowingPaperInitialState H δ (ranks+q) (x.2,x.1.1)
  let v := paperMatrixQueryRun ranks (ranks+q) (ranks+q)
    (scalarGrowingPaperTarget b f g hf hg m r H δ (ranks+q) q)
    (scalarGrowingPaperUpdate H δ (ranks+q) q) q (s,1)
    (paperCompletionReplayNoise (ranks+q) q x.1.2.2) x.1.2.1
  fun i => scalarMeshPaperObservation b f g hf hg H (growingQueryDuration δ)
    (growingQueryTime δ) (ranks+q) v i (projIcc 0 (H : ℝ) H.coe_nonneg t)

def scalarGrowingReplayPastMap (δ : ℝ≥0) (ranks q : ℕ) (t : ℝ≥0)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) :
    ScalarGrowingReplayStaticData δ (ranks+q) q × (Iic t → Fin (ranks+q) → ℝ) :=
  (x.1,fun u i => x.2 i (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ)
    (scalarGrowingSourceHorizon δ q).coe_nonneg u))

lemma continuous_scalarGrowingReplayField_time
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) :
    Continuous (fun t : ℝ≥0 => scalarGrowingReplayField b f g hf hg m r δ ranks q t x) := by
  apply continuous_pi
  intro i
  exact (scalarMeshPaperObservation b f g hf hg _ _ _ _ _ i).continuous.comp
    ((continuous_projIcc (h := (scalarGrowingSourceHorizon δ q).coe_nonneg)).comp
      NNReal.continuous_coe)

theorem scalarGrowingReplayField_measurable_of_past
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ)
    (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ q) :
    Measurable[(inferInstance : MeasurableSpace
      (ScalarGrowingReplayStaticData δ (ranks+q) q × (Iic t → Fin (ranks+q) → ℝ))).comap
        (scalarGrowingReplayPastMap δ ranks q t)]
      (scalarGrowingReplayField b f g hf hg m r δ ranks q t) := by
  let H := scalarGrowingSourceHorizon δ q
  let X := ScalarGrowingReplayStaticData δ (ranks+q) q ×
    (Fin (ranks+q) → ScalarContinuousPath H)
  let 𝔪 : MeasurableSpace X := (inferInstance : MeasurableSpace
    (ScalarGrowingReplayStaticData δ (ranks+q) q × (Iic t → Fin (ranks+q) → ℝ))).comap
      (scalarGrowingReplayPastMap δ ranks q t)
  let : MeasurableSpace X := 𝔪
  have hPast : Measurable (scalarGrowingReplayPastMap δ ranks q t) := comap_measurable _
  have hStatic : Measurable (fun x : X => x.1) := hPast.fst
  let S (x : X) := scalarGrowingPaperInitialState H δ (ranks+q) (x.2,x.1.1)
  have hz : Measurable (fun x : X => (S x).1.1) := measurable_const
  have hbridge : Measurable (fun x : X => (S x).1.2.2) := hStatic.fst.snd
  have hB : Measurable (fun x : X => (S x).2) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_scalarInitialAuxiliaryB H _).comp
      ((measurable_pi_apply i).comp hStatic.fst.fst)
  have hD (i : Fin (ranks+q)) (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ)≤t) :
      Measurable (fun x : X => (S x).1.2.1 i u) := by
    let v : Iic t := ⟨⟨u,u.property.1⟩,by exact_mod_cast hu⟩
    have hh := (measurable_pi_apply i).comp ((measurable_pi_apply v).comp hPast.snd)
    convert hh using 1
    funext x
    change x.2 i u = x.2 i (projIcc 0 (H : ℝ) H.coe_nonneg (v : ℝ≥0))
    change x.2 i u = x.2 i (projIcc 0 (H : ℝ) H.coe_nonneg (u : ℝ))
    rw [projIcc_of_mem _ u.property]
  have htH : (t : ℝ)∈Icc (0 : ℝ) (H : ℝ) := ⟨t.coe_nonneg,ht⟩
  apply Measurable.of_eval
  intro i
  have hY := scalarMeshMatrixQueryRun_observation_measurable_of_D_past 𝔪 b f g hf hg m hm
    (scalarMeshPaperIncrementScale r (growingQueryTime δ)) H (growingQueryDuration δ)
    (growingQueryTime δ) (growingQueryTime_strictMono δ hδ).monotone ranks (ranks+q) q q (ranks+q)
    t ht S (fun _ : X => (1 : Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ))
    (fun x => paperCompletionReplayNoise (ranks+q) q x.1.2.2) (fun x => x.1.2.1)
    hz hbridge hB hD measurable_const
    ((paperCompletionReplayNoise_measurable (ranks+q) q).comp hStatic.snd.snd) hStatic.snd.fst
    i ⟨t,htH⟩ le_rfl
  convert hY using 1
  funext x
  unfold scalarGrowingReplayField
  rw [projIcc_of_mem _ htH]
  rfl

theorem scalarGrowingReplayField_exists_past_callback
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ)
    (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ q) :
    ∃ F : ScalarGrowingReplayStaticData δ (ranks+q) q × (Iic t → Fin (ranks+q) → ℝ) →
      Fin (ranks+q) → ℝ,Measurable F ∧
      ∀ x,F (scalarGrowingReplayPastMap δ ranks q t x)=
        scalarGrowingReplayField b f g hf hg m r δ ranks q t x := by
  obtain ⟨F,hFm,hF⟩ := (scalarGrowingReplayField_measurable_of_past b f g hf hg m hm r δ hδ ranks q t ht).exists_eq_measurable_comp
  refine ⟨F,hFm,fun x => ?_⟩
  exact (congrFun hF x).symm

def scalarGrowingReplayPrefixCallback
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ)
    (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ q) :
    ScalarGrowingReplayStaticData δ (ranks+q) q × (Iic t → Fin (ranks+q) → ℝ) →
      Fin (ranks+q) → ℝ :=
  Classical.choose (scalarGrowingReplayField_exists_past_callback b f g hf hg m hm r δ hδ ranks q t ht)

lemma measurable_scalarGrowingReplayPrefixCallback
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ)
    (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ q) :
    Measurable (scalarGrowingReplayPrefixCallback b f g hf hg m hm r δ hδ ranks q t ht) :=
  (Classical.choose_spec (scalarGrowingReplayField_exists_past_callback b f g hf hg m hm r δ hδ ranks q t ht)).1

lemma scalarGrowingReplayPrefixCallback_identity
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ)
    (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ q)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) :
    scalarGrowingReplayPrefixCallback b f g hf hg m hm r δ hδ ranks q t ht
      (scalarGrowingReplayPastMap δ ranks q t x) =
      scalarGrowingReplayField b f g hf hg m r δ ranks q t x :=
  (Classical.choose_spec (scalarGrowingReplayField_exists_past_callback b f g hf hg m hm r δ hδ ranks q t ht)).2 x

lemma scalarGrowingReplayField_clip_time
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) (t : ℝ≥0)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) :
    scalarGrowingReplayField b f g hf hg m r δ ranks q
      (min t (scalarGrowingSourceHorizon δ q)) x =
      scalarGrowingReplayField b f g hf hg m r δ ranks q t x := by
  unfold scalarGrowingReplayField
  by_cases ht : t ≤ scalarGrowingSourceHorizon δ q
  · rw [min_eq_left ht]
  · have hh : scalarGrowingSourceHorizon δ q≤t := (not_le.mp ht).le
    rw [min_eq_right hh]
    dsimp only
    funext i
    congr 1
    exact (projIcc_of_right_le (scalarGrowingSourceHorizon δ q).coe_nonneg le_rfl).trans
      (projIcc_of_right_le (scalarGrowingSourceHorizon δ q).coe_nonneg hh).symm

def scalarGrowingReplayPastCallback
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ)
    (t : ℝ≥0)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q × (Iic t → Fin (ranks+q) → ℝ)) :
    Fin (ranks+q) → ℝ :=
  scalarGrowingReplayPrefixCallback b f g hf hg m hm r δ hδ ranks q
    (min t (scalarGrowingSourceHorizon δ q)) (min_le_right _ _)
    (x.1,fun u => x.2 ⟨(u : ℝ≥0),show (u : ℝ≥0) ≤ t from u.property.trans (min_le_left t _)⟩)

lemma measurable_scalarGrowingReplayPastCallback
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ) (t : ℝ≥0) :
    Measurable (scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t) := by
  unfold scalarGrowingReplayPastCallback
  apply (measurable_scalarGrowingReplayPrefixCallback b f g hf hg m hm r δ hδ ranks q
    (min t (scalarGrowingSourceHorizon δ q)) (min_le_right _ _)).comp
  apply Measurable.prodMk measurable_fst
  apply Measurable.of_eval
  intro u
  exact (measurable_pi_apply (⟨(u : ℝ≥0),show (u : ℝ≥0) ≤ t from u.property.trans (min_le_left t _)⟩ : Iic t)).comp measurable_snd

theorem scalarGrowingReplayPastCallback_identity
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0<δ) (ranks q : ℕ) (t : ℝ≥0)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) :
    scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t
      (scalarGrowingReplayPastMap δ ranks q t x) =
      scalarGrowingReplayField b f g hf hg m r δ ranks q t x := by
  unfold scalarGrowingReplayPastCallback
  change scalarGrowingReplayPrefixCallback b f g hf hg m hm r δ hδ ranks q
    (min t (scalarGrowingSourceHorizon δ q)) (min_le_right _ _)
    (scalarGrowingReplayPastMap δ ranks q (min t (scalarGrowingSourceHorizon δ q)) x) = _
  rw [scalarGrowingReplayPrefixCallback_identity]
  exact scalarGrowingReplayField_clip_time b f g hf hg m r δ ranks q t x

theorem scalarGrowingReplayPastCallback_identity_of_path_version
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ)
    (a : ScalarGrowingReplayStaticData δ (ranks+q) q)
    (D : ℝ≥0 → Fin (ranks+q) → ℝ)
    (F : Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))
    (hF : ∀ i (u : Icc (0 : ℝ) (scalarGrowingSourceHorizon δ q : ℝ)),
      F i u = D ⟨u,u.property.1⟩ i) (t : ℝ≥0) :
    scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t
      (a,fun u => D u) = scalarGrowingReplayField b f g hf hg m r δ ranks q t (a,F) := by
  let c := min t (scalarGrowingSourceHorizon δ q)
  have hpast : (a,fun u : Iic c => D u) =
      scalarGrowingReplayPastMap δ ranks q c (a,F) := by
    congr 1
    funext u i
    have hu : (u : ℝ≥0) ≤ scalarGrowingSourceHorizon δ q := u.property.trans (min_le_right _ _)
    let v : Icc (0 : ℝ) (scalarGrowingSourceHorizon δ q : ℝ) :=
      ⟨u, (u : ℝ≥0).coe_nonneg,hu⟩
    change D (u : ℝ≥0) i = F i (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ)
      (scalarGrowingSourceHorizon δ q).coe_nonneg u)
    rw [projIcc_of_mem _ v.property]
    exact (hF i v).symm
  change scalarGrowingReplayPrefixCallback b f g hf hg m hm r δ hδ ranks q c
    (min_le_right _ _) (a,fun u : Iic c => D u) = _
  rw [hpast,scalarGrowingReplayPrefixCallback_identity]
  exact scalarGrowingReplayField_clip_time b f g hf hg m r δ ranks q t (a,F)

lemma scalarPrimitiveBrownianVectorPathVersion_ae {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => W.law),∀ i (u : Icc (0 : ℝ) (H : ℝ)),
      scalarPrimitiveBrownianPathVersion W H (ω i) u = W.B ⟨u,u.property.1⟩ (ω i) := by
  let := W.isProbability
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => W.law) i).ae
    (scalarPrimitiveBrownianPathVersion_ae W H)

theorem scalarGrowingReplayPastCallback_brownian_ae {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin (ranks+q) => W.law),
      ∀ (a : ScalarGrowingReplayStaticData δ (ranks+q) q) (t : ℝ≥0),
        scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t
          (a,fun u i => W.B u (ω i)) =
        scalarGrowingReplayField b f g hf hg m r δ ranks q t
          (a,fun i => scalarPrimitiveBrownianPathVersion W (scalarGrowingSourceHorizon δ q) (ω i)) := by
  filter_upwards [scalarPrimitiveBrownianVectorPathVersion_ae W (scalarGrowingSourceHorizon δ q) (ranks+q)] with ω hω
  intro a t
  exact scalarGrowingReplayPastCallback_identity_of_path_version b f g hf hg m hm r δ hδ ranks q
    a (fun u i => W.B u (ω i)) _ hω t

lemma measurable_scalarGrowingReplayPastMap (δ : ℝ≥0) (ranks q : ℕ) (t : ℝ≥0) :
    Measurable (scalarGrowingReplayPastMap δ ranks q t) := by
  apply Measurable.prodMk measurable_fst
  apply Measurable.of_eval
  intro u
  apply Measurable.of_eval
  intro i
  exact (ContinuousMap.measurable_eval _).comp
    ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_scalarGrowingReplayField
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (t : ℝ≥0) :
    Measurable (scalarGrowingReplayField b f g hf hg m r δ ranks q t) := by
  have h := (measurable_scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t).comp
    (measurable_scalarGrowingReplayPastMap δ ranks q t)
  convert h using 1
  funext x
  exact (scalarGrowingReplayPastCallback_identity b f g hf hg m hm r δ hδ ranks q t x).symm

theorem scalarGrowingReplayPastCallback_continuous_brownian_ae {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ)
    (P : Measure (ScalarGrowingReplayStaticData δ (ranks+q) q)) [SFinite P] :
    ∀ᵐ x ∂P.prod (Measure.pi (fun _ : Fin (ranks+q) => W.law)),
      Continuous (fun t : ℝ≥0 => scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t
        (x.1,fun u i => W.B u (x.2 i))) := by
  let := W.isProbability
  have h := (Measure.quasiMeasurePreserving_snd (μ := P)
    (ν := Measure.pi (fun _ : Fin (ranks+q) => W.law))).ae
    (scalarGrowingReplayPastCallback_brownian_ae W b f g hf hg m hm r δ hδ ranks q)
  filter_upwards [h] with x hx
  have he : (fun t : ℝ≥0 => scalarGrowingReplayPastCallback b f g hf hg m hm r δ hδ ranks q t
      (x.1,fun u i => W.B u (x.2 i))) =
    (fun t : ℝ≥0 => scalarGrowingReplayField b f g hf hg m r δ ranks q t
      (x.1,fun i => scalarPrimitiveBrownianPathVersion W (scalarGrowingSourceHorizon δ q) (x.2 i))) := by
    funext t
    exact hx x.1 t
  rw [he]
  exact continuous_scalarGrowingReplayField_time b f g hf hg m r δ ranks q _

lemma measurable_scalarPrimitiveBrownianVectorPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) (n : ℕ) :
    Measurable (fun ω : Fin n → Ω => fun i => scalarPrimitiveBrownianPathVersion W H (ω i)) := by
  exact Measurable.of_eval fun i => (measurable_scalarPrimitiveBrownianPathVersion W H).comp
    (measurable_pi_apply i)

lemma scalarPrimitiveBrownianVectorPathVersion_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => W.law)).map
      (fun ω i => scalarPrimitiveBrownianPathVersion W H (ω i)) =
    Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W H) := by
  let := W.isProbability
  exact Measure.pi_map_pi (fun _ => (measurable_scalarPrimitiveBrownianPathVersion W H).aemeasurable)

theorem scalarGrowingReplayField_eq_source
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) (hn : 0 < ranks+q)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (z : PaperAugmentedNoise (ranks+q) q) (t : ℝ≥0) :
    scalarGrowingReplayField b f g hf hg m r δ ranks q t
      ((p.2,scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p z),p.1) =
    fun i => scalarMeshPaperObservation b f g hf hg (scalarGrowingSourceHorizon δ q)
      (growingQueryDuration δ) (growingQueryTime δ) (ranks+q)
      (proposalTerminalPast (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q) q
        (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p)
        (paperAugmentedOriginal (ranks+q) q z)) i
      (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg t) := by
  unfold scalarGrowingReplayField
  dsimp only
  rw [scalarGrowingSourceAugmentedOutput_matrix_query_coupling b f g hf hg m r δ ranks q hn p z]

end SKConstants
