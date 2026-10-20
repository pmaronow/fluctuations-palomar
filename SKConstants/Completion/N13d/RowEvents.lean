module

public import SKConstants.Completion.N13d.SourceEnergy
public import SKConstants.Completion.LM1b.ReplayTrace
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace SKConstants.Completion.N13d
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5 LM5 LGram

theorem paperEndpointTrace_eq_noiseTrace (n K : ℕ) (z : StoppedNoise (Fin n) K) :
    paperEndpointTrace n K z = paperNoiseTrace n K z := by
  induction K with
  | zero => rfl
  | succ K ih =>
    funext j
    exact Fin.cases rfl (fun j => congrFun (ih z.2) j) j

theorem paperEndpointTrace_ambient_eq_of_visible_eq (n K : ℕ)
    (z w : StoppedNoise (Fin n) K)
    (hvisible : (sourceSplit n K z).1 = (sourceSplit n K w).1)
    (j : Fin K) (i : Fin n) :
    paperEndpointTrace n K z j (.inl i) = paperEndpointTrace n K w j (.inl i) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    have hhead : ∀ i, z.1 (.inl i) = w.1 (.inl i) := by
      have h := congrArg Prod.fst hvisible
      intro i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    have htail : (sourceSplit n K z.2).1 = (sourceSplit n K w.2).1 :=
      congrArg Prod.snd hvisible
    exact Fin.cases (hhead i) (fun j => ih z.2 w.2 htail j) j

theorem paperRows_factors_visible {Past : Type*} (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) :
    paperRows r K target update a z x =
      paperRows r K target update a (visibleSource (r+K) K (sourceSplit (r+K) K z).1) x := by
  let w := visibleSource (r+K) K (sourceSplit (r+K) K z).1
  have hv : (sourceSplit (r+K) K z).1 = (sourceSplit (r+K) K w).1 := by
    rw [sourceSplit_visibleSource]
  have he := paperEndpointTrace_ambient_eq_of_visible_eq (r+K) K z w hv
  have hnoise := he
  simp_rw [paperEndpointTrace_eq_noiseTrace] at hnoise
  have ht := (paperTraces_congr_endpoints r (r+K) 1 target update hblind K (a,1) z w hnoise).1
  funext l
  unfold paperRows
  rw [ht]
  have hel : (fun j => paperEndpointTrace (r+K) K z j (.inl l)) =
      (fun j => paperEndpointTrace (r+K) K w j (.inl l)) := funext fun j => he j l
  rw [hel]

variable {Ω : Type*} [MeasurableSpace Ω]

def growingTranscriptRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (t : GrowingTranscript δ r K) :=
  paperRows r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K t.2.1) (visibleSource (r+K) K t.2.2) (signSpin t.1)

theorem literalSourceRows_factors_transcript (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    literalSourceRows W β hβ δ r K u =
      growingTranscriptRows W β hβ δ r K (growingSourceCompact δ r K u).1 :=
  paperRows_factors_visible r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingUpdate_blind δ r K) _ _ _

theorem measurable_growingTranscriptRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (growingTranscriptRows W β hβ δ r K) := by
  let U := GrowingTranscript δ r K
  let target := M1.Target W β hβ δ r K
  let update := M1.Update δ r K
  have hi : Measurable (fun t : U => growingInitial δ r K t.2.1) :=
    (measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_snd.fst
  have hz : Measurable (fun t : U => visibleSource (r+K) K t.2.2) :=
    (measurable_visibleSource (r+K) K).comp measurable_snd.snd
  have hin : Measurable (fun t : U =>
      (((growingInitial δ r K t.2.1,1) : PaperState r (r+K) K
        (ScalarGrowingPaperPast (M1.Horizon δ K) δ (r+K))), visibleSource (r+K) K t.2.2)) :=
    (hi.prodMk measurable_const).prodMk hz
  have ht (j : Fin K) (l : Fin (r+K)) : Measurable (fun t : U =>
      paperTargetTrace r (r+K) target update K (growingInitial δ r K t.2.1,1)
        (visibleSource (r+K) K t.2.2) j l) :=
    (measurable_paperTargetTrace r (r+K) target update
      (measurable_growingTarget W β hβ δ r K) (measurable_growingUpdate δ r K) K j l).comp hin
  have hg (j : Fin K) (l : Fin (r+K)) : Measurable (fun t : U =>
      paperEndpointTrace (r+K) K (visibleSource (r+K) K t.2.2) j (.inl l)) :=
    (measurable_paperEndpointTrace (r+K) K j (.inl l)).comp hz
  unfold growingTranscriptRows paperRows
  apply Measurable.of_eval
  intro l
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro a
  refine Fin.addCases (fun j => ?_) (fun a => ?_) a
  · simpa only [Fin.append_left] using ht j l
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) a
    · simpa only [Fin.append_right, Fin.append_left, Function.comp_def] using hg j l
    · have hs : Measurable (fun t : U => scalarHiddenSign (t.1 l)) :=
        (measurable_of_finite scalarHiddenSign).comp ((measurable_pi_apply l).comp measurable_fst)
      simpa only [Fin.append_right, signSpin] using hs

theorem growingSourceDiscardedEnergy_mgf_on_rows
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K)
    (S : Set (Fin (r+K) → EuclideanSpace ℝ (Fin (K+(K+1)))))
    (hS : MeasurableSet S) (θ : ℝ) :
    (∫⁻ u in (literalSourceRows W β hβ δ r K) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ*growingSourceDiscardedEnergy W β hβ δ r K u))
      ∂M1.SourceLinkedLaw W β hβ δ r K) =
    ∫⁻ u in (literalSourceRows W β hβ δ r K) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ^2*completionVariance (r+K:ℕ)
        (fun j => growingCoefficients W β hβ δ r K (growingSourceCompact δ r K u).1 j)
        (growingResidual W β hβ δ r K (growingSourceCompact δ r K u).1)/2))
      ∂M1.SourceLinkedLaw W β hβ δ r K := by
  have h := growingSourceDiscardedEnergy_mgf_on W β hβ δ r K hN
    ((growingTranscriptRows W β hβ δ r K) ⁻¹' S)
    (hS.preimage (measurable_growingTranscriptRows W β hβ δ r K)) θ
  have he : {u | (growingSourceCompact δ r K u).1 ∈
      (growingTranscriptRows W β hβ δ r K) ⁻¹' S} = (literalSourceRows W β hβ δ r K) ⁻¹' S := by
    ext u
    change growingTranscriptRows W β hβ δ r K (growingSourceCompact δ r K u).1 ∈ S ↔ _
    rw [← literalSourceRows_factors_transcript]
    rfl
  rw [he] at h
  exact h

end SKConstants.Completion.N13d
