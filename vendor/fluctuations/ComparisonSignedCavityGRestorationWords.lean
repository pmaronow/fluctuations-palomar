module

public import ComparisonSignedCavityCanonicalMarkedTransport
public import ComparisonSignedCavityActualTerminalGWords
public import ComparisonSignedCavityActualGLawRestoration

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def NativeOriginalGMarkedWord.originalRestorationTest {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    (U : ℕ) (K b S : ℕ→ℝ) (P : T.Assignment→ℝ) (a : T.Slot) : g.tree.Assignment→ℝ :=
  fun σ=>P (g.p.restrict (g.r.restrict (g.z.restrict σ)))*
    nativeOriginalHighGAtom g.tree U K b S
      (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
      (g.z.embed g.r.mark) g.z.mark σ

theorem native_original_longitudinal_restoration_eq_words (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a : T.Slot) :
    nativeOriginalLongitudinalRestoration n q U b h K S T P a=
      ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*
        nativeActualLawRestorationRemainder n q U b h K g.tree
          (g.originalRestorationTest U K b S P a))).sum := by
  symm
  exact nativeOriginalGMarkedWords_weighted_kernel_sum T (fun p r z=>
    nativeActualLawRestorationRemainder n q U b h K z.tree (fun σ=>
      P (p.restrict (r.restrict (z.restrict σ)))*
        nativeOriginalHighGAtom z.tree U K b S (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ))

theorem NativeOriginalGMarkedWord.originalRestorationTest_canonical
    {n aDegree : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (G : ActualNaturalBoundaryShape n aDegree T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : LaplaceWindowFormalization.NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin aDegree→NativeSourceFactorForm) (U : ℕ) (K b S : ℕ→ℝ) (a : T.Slot) :
    g.originalRestorationTest U K b S (G.canonicalMinimumSource M forms).product a=
      fun σ=>((g.canonicalOldShape G).canonicalMinimumSource M forms).product σ*
        nativeOriginalHighGAtom g.tree U K b S
          (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
          (g.z.embed g.r.mark) g.z.mark σ := by
  funext σ
  rw [g.canonicalOldShape_product G M forms σ]
  rfl

end OAI.SKFluctuations.Cavity
