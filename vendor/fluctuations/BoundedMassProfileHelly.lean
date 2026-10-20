module

public import SKFluctuationsOAI.Probability.SKFluctuations.UniformGridConvergence
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Algebra.Order.Archimedean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open Filter Set Function
open scoped Topology

theorem monotone_sequence_tendsto_at_continuity {f : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hf : ∀ n, Monotone (f n))
    (hq : ∀ q : ℚ, Tendsto (fun n => f n (q : ℝ)) atTop (𝓝 (a q)))
    {x : ℝ} (ha : ContinuousAt a x) :
    Tendsto (fun n => f n x) atTop (𝓝 (a x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨q, _, hqx, hqt⟩ :=
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).exists_seq_strictMono_tendsto
        Rat.cast_mono x
    have hqa : Tendsto (fun k => a (q k : ℝ)) atTop (𝓝 (a x)) := ha.tendsto.comp hqt
    obtain ⟨k, hk⟩ := (hqa.eventually (lt_mem_nhds hb)).exists
    filter_upwards [(hq (q k)).eventually (lt_mem_nhds hk)] with n hn
    exact hn.trans_le (hf n (hqx k).le)
  · intro b hb
    obtain ⟨q, _, hxq, hqt⟩ :=
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).exists_seq_strictAnti_tendsto
        Rat.cast_mono x
    have hqa : Tendsto (fun k => a (q k : ℝ)) atTop (𝓝 (a x)) := ha.tendsto.comp hqt
    obtain ⟨k, hk⟩ := (hqa.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hq (q k)).eventually (gt_mem_nhds hk)] with n hn
    exact (hf n (hxq k).le).trans_lt hn

theorem boundedMassProfiles_tendsto_subseq (u : ℕ → boundedMassProfiles) :
    ∃ (a : boundedMassProfiles) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 a) := by
  classical
  let : CompactSpace boundedMassProfiles :=
    isCompact_iff_compactSpace.mp boundedMassProfiles_compact
  obtain ⟨a, ha⟩ := exists_clusterPt_of_compactSpace (Filter.map u atTop)
  have ha' : MapClusterPt a atTop u := ha
  let S : Set ℝ := range (fun q : ℚ => (q : ℝ)) ∪ {x | ¬ContinuousAt a.val x}
  have hS : S.Countable :=
    (countable_range (fun q : ℚ => (q : ℝ))).union a.property.2.countable_not_continuousAt
  let : Countable S := hS.to_subtype
  let restriction : boundedMassProfiles → S → ℝ := fun b x => b.val x.val
  have hrestriction : Continuous restriction :=
    continuous_pi fun x => (continuous_apply x.val).comp continuous_subtype_val
  obtain ⟨φ, hφ, ht⟩ :=
    (ha'.continuousAt_comp hrestriction.continuousAt).tendsto_subseq
  have hSconv (x : S) :
      Tendsto (fun n => (u (φ n)).val x.val) atTop (𝓝 (a.val x.val)) :=
    tendsto_pi_nhds.mp ht x
  have hq (q : ℚ) : Tendsto (fun n => (u (φ n)).val (q : ℝ)) atTop (𝓝 (a.val q)) :=
    hSconv ⟨q, Or.inl ⟨q, rfl⟩⟩
  refine ⟨a, φ, hφ, tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr fun x => ?_)⟩
  by_cases hx : ContinuousAt a.val x
  · exact monotone_sequence_tendsto_at_continuity (fun n => (u (φ n)).property.2) hq hx
  · exact hSconv ⟨x, Or.inr hx⟩

end OAI.SKFluctuations.Hierarchy
