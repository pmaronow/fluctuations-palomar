module

public import ComparisonSignedCavityActualProjectedRowPolarization
public import ComparisonSignedCavityLowAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]

omit [Fintype B] [Nonempty B] in
theorem native_original_full_fresh_expect_eq_trunk_projection
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (Q : T.cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    let g:=nativeFreshAtSlot T a s star
    g.tree.cavityLeft.expect w φ q (fun σ=>Q (g.restRestrict σ) (g.restSpin σ)) x=
      nativeTrunkProjectedMean w φ T.cavityLeft (T.cavityLeftSlot s) star q Q x := by
  dsimp only
  rw [nativeFreshAtSlot_full_rest_expect_transport T a s star hw φ ho q Q x]
  exact (native_trunk_projected_eq_fresh_graft (a:=a) hw φ T.cavityLeft ho
    (T.cavityLeftSlot s) star q Q x).symm

theorem native_actual_projected_placement_full_fresh_polarization
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    (h : NativeTargetStarSingleton T s star)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hh : star<p.tree.splitIndex (p.embed s) p.mark)
    (q : ℕ → ι → ℝ≥0) (R : S → S → ℝ)
    (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) :
    let g:=nativeFreshAtSlot p.tree a (p.embed s) star
    g.tree.cavityLeft.expect w φ q (fun σ=>
      (R (p.restSpin (g.restRestrict σ)) (g.restSpin σ)-
        R (T.cavityLeft.atSlot (p.restRestrict (g.restRestrict σ)) (T.cavityLeftSlot s)) (g.restSpin σ))*
        P (p.restRestrict (g.restRestrict σ))) x=
    (1/2:ℝ)*g.tree.cavityLeft.expect w φ q (fun σ=>
      (R (p.restSpin (g.restRestrict σ)) (g.restSpin σ)-
        R (T.cavityLeft.atSlot (p.restRestrict (g.restRestrict σ)) (T.cavityLeftSlot s)) (g.restSpin σ))*
        (P (p.restRestrict (g.restRestrict σ))-
          P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
            (p.restRestrict (g.restRestrict σ)) (p.restSpin (g.restRestrict σ))))) x := by
  dsimp only
  rw [native_original_full_fresh_expect_eq_trunk_projection p.tree (p.embed s) star hw φ ho q
    (fun σ d=>(R (p.restSpin σ) d-
      R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*P (p.restRestrict σ)) x,
    native_original_full_fresh_expect_eq_trunk_projection p.tree (p.embed s) star hw φ ho q
      (fun σ d=>(R (p.restSpin σ) d-
        R (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s)) d)*
        (P (p.restRestrict σ)-P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
          (p.restRestrict σ) (p.restSpin σ)))) x]
  exact native_actual_projected_placement_polarization T s star h hw φ ho p hp hh q R P x

theorem native_actual_projected_placement_original_polarization
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    (h : NativeTargetStarSingleton T s star)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : star<p.tree.splitIndex (p.embed s) p.mark)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) :
    let g:=nativeFreshAtSlot p.tree 0 (p.embed s) star
    g.tree.cavityLeft.disorderExpect w φ v q (fun σ=>
      (R (p.restSpin (g.restRestrict σ)) (g.restSpin σ)-
        R (T.cavityLeft.atSlot (p.restRestrict (g.restRestrict σ)) (T.cavityLeftSlot s)) (g.restSpin σ))*
        P (p.restRestrict (g.restRestrict σ))) x=
    (1/2:ℝ)*g.tree.cavityLeft.disorderExpect w φ v q (fun σ=>
      (R (p.restSpin (g.restRestrict σ)) (g.restSpin σ)-
        R (T.cavityLeft.atSlot (p.restRestrict (g.restRestrict σ)) (T.cavityLeftSlot s)) (g.restSpin σ))*
        (P (p.restRestrict (g.restRestrict σ))-
          P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
            (p.restRestrict (g.restRestrict σ)) (p.restSpin (g.restRestrict σ))))) x := by
  dsimp only
  rw [(nativeFreshAtSlot p.tree 0 (p.embed s) star).tree.cavityLeft.disorderExpect_integral hw φ ho,
    (nativeFreshAtSlot p.tree 0 (p.embed s) star).tree.cavityLeft.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  exact native_actual_projected_placement_full_fresh_polarization T s star h hw φ ho p hp hh
    _ R P (x+y)

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι : Type} [Fintype ι]

theorem native_actual_generated_high_gamma_mask_eq_full_row
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U k : ℕ}
    {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀)
    (ho : MassOrdered 0 as) (K : ℕ → ℝ) (F : MarkedPlacement T → ℝ) :
    (T.markedAttach 0 |>.map fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed P₀.live.test.target) p.mark*
      (if U≤p.tree.splitIndex (p.embed P₀.live.test.target) p.mark then F p else 0)).sum=
    (T.markedAttach 0 |>.map fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed P₀.live.test.target) p.mark*F p).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hh : U≤p.tree.splitIndex (p.embed P₀.live.test.target) p.mark
  · rw [ite_eq_left hh]
  · rw [ite_eq_right hh,fullScalarCutGamma_cross_zero p.tree ho U K
      (p.embed P₀.live.test.target) p.mark hP.highCut_le_length (by omega)]
    ring

def nativeActualOriginalProjectedDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K : ℕ → ℝ)
    (w : Spin n → ℝ) (φ : Spin n → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : Spin n → Spin n → ℝ) (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (T.markedAttach 0 |>.map fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark*
    if U≤p.tree.splitIndex (p.embed s) p.mark then
      let g:=nativeFreshAtSlot p.tree 0 (p.embed s) star
      g.tree.cavityLeft.disorderExpect w φ v q (fun σ=>
        (R (p.restSpin (g.restRestrict σ)) (g.restSpin σ)-
          R (T.cavityLeft.atSlot (p.restRestrict (g.restRestrict σ)) (T.cavityLeftSlot s)) (g.restSpin σ))*
          P (p.restRestrict (g.restRestrict σ))) x else 0).sum

def nativeActualOriginalProjectedResampling {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K : ℕ → ℝ)
    (w : Spin n → ℝ) (φ : Spin n → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : Spin n → Spin n → ℝ) (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (T.markedAttach 0 |>.map fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark*
    if U≤p.tree.splitIndex (p.embed s) p.mark then
      let g:=nativeFreshAtSlot p.tree 0 (p.embed s) star
      g.tree.cavityLeft.disorderExpect w φ v q (fun σ=>
        (R (p.restSpin (g.restRestrict σ)) (g.restSpin σ)-
          R (T.cavityLeft.atSlot (p.restRestrict (g.restRestrict σ)) (T.cavityLeftSlot s)) (g.restSpin σ))*
          (P (p.restRestrict (g.restRestrict σ))-
            P (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
              (p.restRestrict (g.restRestrict σ)) (p.restSpin (g.restRestrict σ))))) x else 0).sum

theorem native_actual_generated_original_projected_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U k : ℕ}
    {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    {w : Spin n → ℝ} (hw : ∀σ,0<w σ) (φ : Spin n → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (K : ℕ → ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : Spin n → Spin n → ℝ) (P : T.cavityLeft.Assignment → ℝ) (x : ι → ℝ) :
    nativeActualOriginalProjectedDisplacement T P₀.live.test.target star U K w φ v q R P x=
      (1/2:ℝ)*nativeActualOriginalProjectedResampling T P₀.live.test.target star U K w φ v q R P x := by
  unfold nativeActualOriginalProjectedDisplacement nativeActualOriginalProjectedResampling
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hh : U≤p.tree.splitIndex (p.embed P₀.live.test.target) p.mark
  · rw [ite_eq_left hh,ite_eq_left hh]
    dsimp only
    rw [native_actual_projected_placement_original_polarization T P₀.live.test.target star
      (hP.targetStarSingleton hi) hw φ ho p hp (hs.trans_le hh)]
    ring
  · rw [ite_eq_right hh,ite_eq_right hh]
    ring

end OAI.SKFluctuations.Cavity
