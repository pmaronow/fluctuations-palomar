module
public import SKConstants.Completion.LC4a.TerminalLinkLocal
public import SKConstants.Completion.LC0.TerminalLinkLaw
public import SKConstants.ProposalGibbsChangeOfMeasure

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

def terminalSpinFirst (A X D : Type*) [MeasurableSpace A] [MeasurableSpace X]
    [MeasurableSpace D] : ((A × X) × D) ≃ᵐ (X × (A × D)) where
  toFun u := (u.1.2, (u.1.1, u.2))
  invFun u := ((u.2.1, u.1), u.2.2)
  left_inv := by rintro ⟨⟨a, x⟩, d⟩; rfl
  right_inv := by rintro ⟨x, a, d⟩; rfl
  measurable_toFun := measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd)
  measurable_invFun := (measurable_snd.fst.prodMk measurable_fst).prodMk measurable_snd.snd

def spinFreeReplayField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (u : ScalarGrowingReplayStaticData δ (ranks + q) q × (Fin (ranks + q) → Ω)) :
    Fin (ranks + q) → ℝ :=
  actualParisiGrowingReplayField W β hβ δ ranks q V
    (u.1, fun i => scalarPrimitiveBrownianPathVersion W
      (scalarGrowingSourceHorizon δ q) (u.2 i))

theorem growingReplayLinkDensity_eq_terminalDensity
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0) (u : GrowingReplaySpace Ω δ ranks q) :
    growingReplayLinkDensity W β hβ δ ranks q V u =
      M1.TerminalDensity β V (spinFreeReplayField W β hβ δ ranks q V)
        (terminalSpinFirst _ _ _ u) := rfl

theorem terminalSpinFirst_map_prod {A X D : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace D]
    (P : Measure A) (S : Measure X) (Q : Measure D)
    [SFinite P] [SFinite S] [SFinite Q] :
    ((P.prod S).prod Q).map (terminalSpinFirst A X D) = S.prod (P.prod Q) := by
  exact ((measurePreserving_prodAssoc S P Q).comp
    ((Measure.measurePreserving_swap (μ := P) (ν := S)).prod (MeasurePreserving.id Q))).map_eq

theorem growingReplayUnlinkedLaw_spinFirst
    (W : BrownianSystem Ω) (δ : ℝ≥0) (ranks q : ℕ) :
    (growingReplayUnlinkedLaw W δ ranks q).map (terminalSpinFirst _ _ _) =
      (M1.spinPrior (ranks + q)).prod
        ((scalarGrowingReplayStaticLaw W δ (ranks + q) q).prod
          (Measure.pi (fun _ : Fin (ranks + q) => W.law))) := by
  let := W.isProbability
  exact terminalSpinFirst_map_prod _ _ _

theorem growingReplayLinkedLaw_spinFirst
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    (growingReplayLinkedLaw W β hβ δ ranks q V).map (terminalSpinFirst _ _ _) =
      M1.TerminalLinkedLaw β V
        ((scalarGrowingReplayStaticLaw W δ (ranks + q) q).prod
          (Measure.pi (fun _ : Fin (ranks + q) => W.law)))
        (spinFreeReplayField W β hβ δ ranks q V) := by
  let e := terminalSpinFirst (ScalarGrowingReplayStaticData δ (ranks + q) q)
    (Fin (ranks + q) → Bool) (Fin (ranks + q) → Ω)
  have hY : Measurable (spinFreeReplayField W β hβ δ ranks q V) := by
    have hm := (measurable_growingReplayFieldAt W β hβ δ hδ ranks q V).comp
      ((measurable_fst.prodMk (measurable_const : Measurable
        (fun _ : ScalarGrowingReplayStaticData δ (ranks + q) q × (Fin (ranks + q) → Ω) =>
          (fun _ : Fin (ranks + q) => false)))).prodMk measurable_snd)
    exact hm
  have hg := (M1.measurable_terminalDensity β V _ hY).ennreal_ofReal
  change ((growingReplayUnlinkedLaw W δ ranks q).withDensity
    ((fun u => ENNReal.ofReal (M1.TerminalDensity β V
      (spinFreeReplayField W β hβ δ ranks q V) u)) ∘ e)).map e = _
  rw [map_withDensity_comp _ e e.measurable _ hg, growingReplayUnlinkedLaw_spinFirst]
  rfl

end SKConstants.Completion.LM3
