module

public import SKConstants.Completion.LM5.NoiseRegrouping
public import SKConstants.Completion.LC0.TerminalLinkLaw
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5 M1

variable {S : Type*} [MeasurableSpace S]

def sourceVisible (n K : ℕ) (z : S × StoppedNoise (Fin n) K) :
    S × PaperCompletionNoise n K := (z.1, (sourceSplit n K z.2).1)

def sourceCompact (n K : ℕ) (z : S × StoppedNoise (Fin n) K) :
    (S × PaperCompletionNoise n K) ×
      (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin n × Fin n)) :=
  (sourceVisible n K z, compactUnused n K (sourceSplit n K z.2).2)

theorem measurable_sourceVisible (n K : ℕ) : Measurable (sourceVisible (S := S) n K) :=
  measurable_fst.prodMk ((sourceSplit_measurable n K).fst.comp measurable_snd)

theorem measurable_sourceCompact (n K : ℕ) : Measurable (sourceCompact (S := S) n K) :=
  (measurable_sourceVisible n K).prodMk
    ((measurable_compactUnused n K).comp ((sourceSplit_measurable n K).snd.comp measurable_snd))

theorem sourceCompact_law (μ : Measure S) [SFinite μ] (n K : ℕ) :
    (μ.prod (stoppedNoiseLaw (Fin n) K)).map (sourceCompact n K) =
      (μ.prod (paperCompletionNoiseLaw n K)).prod (completionNoiseLaw n K) := by
  change (μ.prod (stoppedNoiseLaw (Fin n) K)).map
    (fun z => ((z.1,(sourceSplit n K z.2).1),compactUnused n K (sourceSplit n K z.2).2)) = _
  have h := linked_compact_source_law μ n K (fun _ => 1) measurable_const
  simpa only [withDensity_const, one_smul, sourceSplitWithStatic] using h

def terminalSourceCompact (n K : ℕ) (z : (Fin n → Bool) × (S × StoppedNoise (Fin n) K)) :
    ((Fin n → Bool) × (S × PaperCompletionNoise n K)) ×
      (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin n × Fin n)) :=
  ((z.1,sourceVisible n K z.2), compactUnused n K (sourceSplit n K z.2.2).2)

theorem measurable_terminalSourceCompact (n K : ℕ) :
    Measurable (terminalSourceCompact (S := S) n K) :=
  (measurable_fst.prodMk ((measurable_sourceVisible n K).comp measurable_snd)).prodMk
    ((measurable_compactUnused n K).comp
      ((sourceSplit_measurable n K).snd.comp measurable_snd.snd))

def terminalSourceLaw (μ : Measure S) (n K : ℕ) (β : ℝ) (H : ℝ≥0)
    (Y : S × PaperCompletionNoise n K → Fin n → ℝ) :
    Measure ((Fin n → Bool) × (S × StoppedNoise (Fin n) K)) :=
  TerminalLinkedLaw β H (μ.prod (stoppedNoiseLaw (Fin n) K)) (Y ∘ sourceVisible n K)

theorem terminalSourceLaw_probability (μ : Measure S) [IsProbabilityMeasure μ]
    (n K : ℕ) (β : ℝ) (H : ℝ≥0)
    (Y : S × PaperCompletionNoise n K → Fin n → ℝ) (hY : Measurable Y) :
    IsProbabilityMeasure (terminalSourceLaw μ n K β H Y) :=
  terminalLinkedLaw_probability _ _ _ _ (hY.comp (measurable_sourceVisible n K))

theorem terminalSourceCompact_law (μ : Measure S) [SFinite μ]
    (n K : ℕ) (β : ℝ) (H : ℝ≥0)
    (Y : S × PaperCompletionNoise n K → Fin n → ℝ) (hY : Measurable Y) :
    (terminalSourceLaw μ n K β H Y).map (terminalSourceCompact n K) =
      (TerminalLinkedLaw β H (μ.prod (paperCompletionNoiseLaw n K)) Y).prod
        (completionNoiseLaw n K) := by
  let F := terminalSourceCompact (S := S) n K
  have hF := measurable_terminalSourceCompact (S := S) n K
  have hbase : ((spinPrior n).prod (μ.prod (stoppedNoiseLaw (Fin n) K))).map F =
      ((spinPrior n).prod (μ.prod (paperCompletionNoiseLaw n K))).prod
        (completionNoiseLaw n K) := by
    have hp : MeasurePreserving (sourceCompact n K) (μ.prod (stoppedNoiseLaw (Fin n) K))
        ((μ.prod (paperCompletionNoiseLaw n K)).prod (completionNoiseLaw n K)) :=
      ⟨measurable_sourceCompact n K, sourceCompact_law μ n K⟩
    exact ((measurePreserving_prodAssoc (spinPrior n) (μ.prod (paperCompletionNoiseLaw n K))
      (completionNoiseLaw n K)).symm.comp ((MeasurePreserving.id (spinPrior n)).prod hp)).map_eq
  let L : (Fin n → Bool) × (S × PaperCompletionNoise n K) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (TerminalDensity β H Y z)
  have hL : Measurable L := (measurable_terminalDensity β H Y hY).ennreal_ofReal
  have ht := map_withDensity_composition
    ((spinPrior n).prod (μ.prod (stoppedNoiseLaw (Fin n) K))) F hF
    (fun p => L p.1) (hL.comp measurable_fst)
  rw [hbase, ← prod_withDensity_left hL] at ht
  exact ht

end SKConstants.Completion.LM5
