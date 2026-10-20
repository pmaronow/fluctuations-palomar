module

public import ComparisonSignedCavityActualFullLeadingEndpoint
public import CavityScalarGammaTopology

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000
attribute [local instance] Classical.propDecidable

 theorem native_full_gamma_eq_split_or_diagonal {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (a c : T.Slot) :
    fullScalarCutGamma T U K a c=
      if a=c then 1 else scalarCutPairAtSplit as U K (T.splitIndex a c) := by
  change scalarCutGamma T.cavityRight U K (T.cavityRightSlot a) (T.cavityRightSlot c)=_
  rw [scalarCutGamma_eq_pair_or_diagonal T.cavityRight ho,T.splitIndex_cavityRight]
  simp only [T.cavityRightSlot.injective.eq_iff]

 theorem native_full_gamma_transport_split_and_diagonal
    {n n' : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (V : ClockTree (Spin n'×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (a c : T.Slot) (a' c' : V.Slot)
    (hsplit : T.splitIndex a c=V.splitIndex a' c') (hdiag : a=c ↔ a'=c') :
    fullScalarCutGamma T U K a c=fullScalarCutGamma V U K a' c' := by
  rw [native_full_gamma_eq_split_or_diagonal T ho,native_full_gamma_eq_split_or_diagonal V ho,
    hsplit,hdiag]

 theorem native_full_connected_four_marked_preserves {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (a c e f : T.Slot) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    fullScalarCutConnected4 p.tree U K (p.embed a) (p.embed c) (p.embed e) (p.embed f)=
      fullScalarCutConnected4 T U K a c e f := by
  have HM:=fullScalarCutMoment_marked_preserves T ho U K [a,c,e,f] p hp
  simp only [List.map_cons,List.map_nil] at HM
  unfold fullScalarCutConnected4
  rw [HM,fullScalarCutGamma_marked_preserves T ho U K a c p hp,
    fullScalarCutGamma_marked_preserves T ho U K e f p hp]

 theorem native_original_G_atom_marked_readout {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (K b C : ℕ→ℝ)
    (a c e f : T.Slot) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (σ : p.tree.Assignment) :
    nativeOriginalHighGAtom p.tree U K b C (p.embed a) (p.embed c) (p.embed e) (p.embed f) σ=
      nativeOriginalHighGAtom T U K b C a c e f (p.restrict σ) := by
  have HS:=T.markedAttach_embed_preserves 0 p hp
  have Hne : p.embed e≠p.embed f ↔ e≠f:=not_congr HS.1.eq_iff
  unfold nativeOriginalHighGAtom
  simp only [HS.2,Hne]
  rw [native_full_connected_four_marked_preserves T ho U K a c e f p hp]
  rw [←p.restrict_at σ e,←p.restrict_at σ f]

 theorem native_original_G_atom_marked_marginal {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (K b C : ℕ→ℝ)
    (a c e f : T.Slot) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (P : T.Assignment→ℝ) :
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict σ)*nativeOriginalHighGAtom p.tree U K b C
        (p.embed a) (p.embed c) (p.embed e) (p.embed f) σ) x=
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P σ*nativeOriginalHighGAtom T U K b C a c e f σ) x := by
  simp_rw [native_original_G_atom_marked_readout T ho U K b C a c e f p hp]
  exact T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho p hp v q
    (fun τ=>P τ*nativeOriginalHighGAtom T U K b C a c e f τ) x

 theorem native_original_G_atom_fresh_star_marginal {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U star : ℕ) (K b C : ℕ→ℝ)
    (a c e f s : T.Slot)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (P : T.Assignment→ℝ) :
    let p:=nativeFreshAtSlot T 0 s star
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict σ)*nativeOriginalHighGAtom p.tree U K b C
        (p.embed a) (p.embed c) (p.embed e) (p.embed f) σ) x=
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P σ*nativeOriginalHighGAtom T U K b C a c e f σ) x :=
  native_original_G_atom_marked_marginal T ho U K b C a c e f
    (nativeFreshAtSlot T 0 s star) (nativeFreshAtSlot_mem T 0 s star) v q x P

end OAI.SKFluctuations.Cavity
