module

public import SKConstants.Completion.Blueprint.Nodes
public import SKConstants.Completion.LM1a.GrowingCells

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def coarsePrefix_completion (n : ℕ) : (qf qb : ℕ) → qb ≤ qf →
    PaperCompletionNoise n qf → PaperCompletionNoise n qb
  | _, 0, _, _ => ()
  | 0, qb + 1, h, _ => False.elim (by omega)
  | qf + 1, qb + 1, h, z =>
      (z.1, coarsePrefix_completion n qf qb (by omega) z.2)

abbrev PrefixInput (δ : ℝ≥0) (n q : ℕ) :=
  ScalarGrowingReplayStaticData δ n q ×
    (Fin n → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))

def coarsePrefix_law {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (δ : ℝ≥0) (n q : ℕ) : Measure (PrefixInput δ n q) :=
  (scalarGrowingReplayStaticLaw W δ n q).prod
    (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
      (scalarGrowingSourceHorizon δ q)))

def coarsePrefix_input (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf) :
    PrefixInput δ n qf → PrefixInput δ n qb :=
  fun x => ((x.1.1, (x.1.2.1, coarsePrefix_completion n qf qb hq x.1.2.2)),
    fun i => scalarInitialAuxiliaryRestriction (scalarGrowingSourceHorizon δ qf)
      (scalarGrowingSourceHorizon δ qb)
      (M1.growingQueryTime_monotone δ (Nat.add_le_add_right hq 1)) (x.2 i))

def coarsePrefix_castInput (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m) :
    PrefixInput δ n q → PrefixInput δ m q := by
  subst m
  exact id

def coarsePrefix_replayInput (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) :
    M1.ReplayInput δ rf qf → M1.ReplayInput δ rb qb :=
  coarsePrefix_castInput δ qb hdim ∘ coarsePrefix_input δ (rf + qf) qb qf hq

def CoarsePrefixStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf),
    Measurable (coarsePrefix_replayInput δ rf qf rb qb hdim hq) ∧
    (M1.ReplayLaw W δ rf qf).map (coarsePrefix_replayInput δ rf qf rb qb hdim hq) =
      M1.ReplayLaw W δ rb qb ∧
    ∀ (v : M1.ReplayInput δ rf qf) (t : ℝ≥0),
      t ≤ scalarGrowingSourceHorizon δ qb →
      actualParisiGrowingReplayField W β hβ δ rb qb t
        (coarsePrefix_replayInput δ rf qf rb qb hdim hq v) =
      fun i => actualParisiGrowingReplayField W β hβ δ rf qf t v
        (Fin.cast hdim.symm i)

end SKConstants.N13a
