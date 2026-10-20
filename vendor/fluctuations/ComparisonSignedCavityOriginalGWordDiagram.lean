module

public import ComparisonSignedCavityHighFreshWordSums
public import ComparisonSignedCavityActualOriginalGHighRows

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeOriginalGDiagramValue {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ)
    (D : NativeObservedDiagram T) : ℝ :=
  match D.marks with
  | [f,e,c,t]=>D.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(A (D.tree.atSlot σ c) (D.tree.atSlot σ t)-
        A (T.atSlot (D.read σ) s) (D.tree.atSlot σ t))*
        (P (D.read σ)-P (nativeReplaceAtSlot T s (D.read σ) (D.tree.atSlot σ c)))*
        nativeOriginalHighGAtom D.tree U K b C (D.embed s) c e f σ) x
  | _=>0

theorem native_original_G_localized_resampling_eq_word
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeActualOriginalGProjectedLocalizedResampling T s star U K b C v q x A P=
      nativeObservedHighWordSum ((NativeObservedDiagram.identity T).fresh s star 0) s star 3
        (nativeOriginalGDiagramValue T s U K b C v q x A P) := by
  unfold nativeActualOriginalGProjectedLocalizedResampling nativeOriginalLocalizedHighPairing
  simp only [native_observed_high_word_sum_succ,native_observed_high_word_sum_zero,
    NativeObservedDiagram.identity,NativeObservedDiagram.fresh,NativeObservedDiagram.observe,
    List.map_nil,List.nil_append,List.map_cons,nativeOriginalGDiagramValue]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  congr 1
  apply congrArg (fun J=>z.tree.disorderExpect (fullWeight n) (fullFeature n) v q J x)
  funext σ
  simp only [id_eq,p.spin_at,p.restrict_at,r.restrict_at,z.restrict_at,
    (nativeFreshAtSlot T 0 s star).spin_at]

theorem native_original_G_resampling_eq_word_before_fresh
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeActualOriginalGProjectedResampling T s star U K b C v q x A P=
      nativeObservedHighWordSum (NativeObservedDiagram.identity T) s star 3
        (fun D=>nativeOriginalGDiagramValue T s U K b C v q x A P (D.fresh s star 0)) := by
  rw [native_original_G_projected_resampling_eq_three_high_rows T ho s star U hs hU,
    native_original_G_localized_resampling_eq_word,
    native_observed_high_word_sum_fresh 3 _ s star (hs.le.trans hU) 0]

end OAI.SKFluctuations.Cavity
