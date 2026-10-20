module

public import ComparisonSignedCavityActualMarkedProjectionExchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem nativeReplaceAtSlot_self {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (σ : T.Assignment) (u : S) :
    T.atSlot (nativeReplaceAtSlot T s σ u) s=u := by
  classical
  rw [nativeReplaceAtSlot_at,ite_eq_left rfl]

theorem native_trunk_projected_neg {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (j : ℕ) {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ) :
    nativeTrunkProjectedMean w φ T s j q (fun σ d=>-Q σ d) x=
      -nativeTrunkProjectedMean w φ T s j q Q x := by
  rw [native_trunk_projected_eq_fresh_graft hw φ T ho,
    native_trunk_projected_eq_fresh_graft hw φ T ho]
  unfold expect
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem native_trunk_projected_sub {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (j : ℕ) {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (Q R : T.Assignment → S → ℝ) (x : ι → ℝ) :
    nativeTrunkProjectedMean w φ T s j q (fun σ d=>Q σ d-R σ d) x=
      nativeTrunkProjectedMean w φ T s j q Q x-nativeTrunkProjectedMean w φ T s j q R x := by
  rw [native_trunk_projected_eq_fresh_graft hw φ T ho,
    native_trunk_projected_eq_fresh_graft hw φ T ho,
    native_trunk_projected_eq_fresh_graft hw φ T ho]
  unfold expect
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

variable {B : Type} [Fintype B] [Nonempty B]

theorem native_actual_projected_placement_polarization
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    (h : NativeTargetStarSingleton T s star)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hh : star<p.tree.splitIndex (p.embed s) p.mark)
    (q : ℕ → ι → ℝ≥0) (R : S → S → ℝ)
    (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) :
    nativeTrunkProjectedMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star q (fun σ d=>
        (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
          P (p.restRestrict σ)) x=
    (1/2:ℝ)*nativeTrunkProjectedMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star q (fun σ d=>
        (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
          (P (p.restRestrict σ)-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
            (p.restRestrict σ) (p.restSpin σ)))) x := by
  let A:=fun (σ:p.tree.cavityLeft.Assignment) d=>
    (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
      P (p.restRestrict σ)
  let F:=fun (σ:p.tree.cavityLeft.Assignment) d=>
    (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
      P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ))
  have H:=native_target_singleton_full_rest_projected_exchange T s star h hw φ ho p hp hh q
    (fun σ u d=>(R u d-R (T.cavityLeft.atSlot σ (T.cavityLeftSlot s)) d)*P σ) x
  have Hfun : (fun σ d=>
      (R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d-
        R (T.cavityLeft.atSlot
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ))
          (T.cavityLeftSlot s)) d)*
        P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ)))=
      (fun σ d=>-F σ d) := by
    funext σ d
    rw [nativeReplaceAtSlot_self]
    dsimp only [F]
    ring
  rw [Hfun,native_trunk_projected_neg _ _ _ hw φ ho] at H
  have Hdiff : (fun σ d=>
      (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
        (P (p.restRestrict σ)-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
          (p.restRestrict σ) (p.restSpin σ))))=(fun σ d=>A σ d-F σ d) := by
    funext σ d
    dsimp only [A,F]
    ring
  rw [Hdiff,native_trunk_projected_sub _ _ _ hw φ ho]
  change nativeTrunkProjectedMean w φ p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed s)) star q A x=
      (1/2:ℝ)*(nativeTrunkProjectedMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed s)) star q A x-
        nativeTrunkProjectedMean w φ p.tree.cavityLeft
          (p.tree.cavityLeftSlot (p.embed s)) star q F x)
  change nativeTrunkProjectedMean w φ p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed s)) star q A x=
      -nativeTrunkProjectedMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed s)) star q F x at H
  linarith

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι : Type} [Fintype ι]

def nativeActualSignedProjectedDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (a : ℝ) (K : ℕ → ℝ)
    (w : Spin n → ℝ) (φ : Spin n → (ι → ℝ)→L[ℝ]ℝ) (q : ℕ → ι → ℝ≥0)
    (R : Spin n → Spin n → ℝ) (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (T.markedAttach a |>.map fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark*
    if U≤p.tree.splitIndex (p.embed s) p.mark then
      nativeTrunkProjectedMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed s)) star q (fun σ d=>
          (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
            P (p.restRestrict σ)) x else 0).sum

def nativeActualSignedProjectedResampling {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (a : ℝ) (K : ℕ → ℝ)
    (w : Spin n → ℝ) (φ : Spin n → (ι → ℝ)→L[ℝ]ℝ) (q : ℕ → ι → ℝ≥0)
    (R : Spin n → Spin n → ℝ) (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (T.markedAttach a |>.map fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark*
    if U≤p.tree.splitIndex (p.embed s) p.mark then
      nativeTrunkProjectedMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed s)) star q (fun σ d=>
          (R (p.restSpin σ) d-R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
            (P (p.restRestrict σ)-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
              (p.restRestrict σ) (p.restSpin σ)))) x else 0).sum

theorem native_actual_generated_signed_projected_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U k : ℕ}
    {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    {w : Spin n → ℝ} (hw : ∀σ,0<w σ) (φ : Spin n → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (K : ℕ → ℝ) (q : ℕ → ι → ℝ≥0)
    (R : Spin n → Spin n → ℝ) (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) :
    nativeActualSignedProjectedDisplacement T P₀.live.test.target star U a K w φ q R P x=
      (1/2:ℝ)*nativeActualSignedProjectedResampling T P₀.live.test.target star U a K w φ q R P x := by
  unfold nativeActualSignedProjectedDisplacement nativeActualSignedProjectedResampling
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hh : U≤p.tree.splitIndex (p.embed P₀.live.test.target) p.mark
  · rw [ite_eq_left hh,ite_eq_left hh,
      native_actual_projected_placement_polarization T P₀.live.test.target star
        (hP.targetStarSingleton hi) hw φ ho p hp (hs.trans_le hh)]
    ring
  · rw [ite_eq_right hh,ite_eq_right hh]
    ring

end OAI.SKFluctuations.Cavity
