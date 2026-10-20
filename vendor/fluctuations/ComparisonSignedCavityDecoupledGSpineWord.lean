module

public import ComparisonSignedCavityGSpineRestLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_decoupled_G_spine_resampling_eq_rest_word
    {n : ℕ} {as : List PositiveMass} {B T : ClockTree (Spin n×Bool) as}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T} {star : ℕ}
    (spine : NativeProjectionSpine base star P) (ho : MassOrdered 0 as)
    (U : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (A R : Spin n→Spin n→ℝ) :
    nativeActualOriginalGProjectedResampling T P.target star U K b C 0
      (cutFullVariance n q U 0 0 b h K) 0 (fun u v=>A u.1 v.1)
      (P.value (fun u v=>R u.1 v.1) C)=
      nativeObservedHighWordSum (NativeObservedDiagram.identity B) base.target star 3
        (fun D=>nativeRestGSpineDiagramValue B base star U q b h K C A R
          ((spine.graftDiagram D).fresh base.target star 0)) := by
  rw [native_original_G_spine_resampling_eq_reset_word spine ho U hs hU]
  unfold nativeObservedHighWordSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  apply congrArg (fun v=>z.1*v)
  exact native_original_G_spine_diagram_decoupled_eq_rest B base ho star U hU q b h K C hKC A R
    ((spine.graftDiagram z.2).fresh base.target star 0)
    ((spine.validRead_graft (native_observed_high_words_validRead _
      (NativeObservedDiagram.validRead_identity B) base.target star 3 z hz)).fresh base.target star 0)

end OAI.SKFluctuations.Cavity
