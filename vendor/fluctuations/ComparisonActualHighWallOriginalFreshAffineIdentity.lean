module

public import ComparisonActualHighWallCanonicalLowRestFactor
public import ComparisonSignedCavityOriginalFreshAffineIdentity
public import ComparisonSignedCavityActualSignedFreshRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def actualHighWallOriginalFreshAffineResidual (n : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (s e b : T.Slot) (star : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (Z : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 b star
  g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (fun σ=>Z (g.restRestrict σ)*
      (ActualNaturalBoundaryShape.actualHighWallLowRestFactor M g.mark (g.embed s) σ-
        ActualNaturalBoundaryShape.actualHighWallLowRestFactor M g.mark (g.embed e) σ)) 0

theorem actual_high_wall_original_fresh_affine_residual_eq_bond_mul
    (n : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s e b : T.Slot) (star : ℕ)
    (hhigh : star < T.splitIndex s e) (hlow : T.splitIndex s b≤ star)
    (q : ℕ→RestCoordinate n→ℝ) (Z : T.cavityLeft.Assignment→ℝ) :
    actualHighWallOriginalFreshAffineResidual n M T s e b star q Z=
      (M.bf (partitionPoint 0 as (T.splitIndex s b)):ℝ)*
        nativeOriginalFreshResidual n T s e b 0 star 0 q 0 Z := by
  have heb : T.splitIndex e b=T.splitIndex s b :=
    T.splitIndex_low_eq_of_high e s b (U:=star+1)
      (by rw [T.splitIndex_symm];omega) (by omega)
  have heblow : T.splitIndex e b≤ star:=by simpa only [heb] using hlow
  let g:=nativeFreshAtSlot T 0 b star
  have hgs : g.tree.splitIndex g.mark (g.embed s)=T.splitIndex s b:=
    native_fresh_low_pair_split T s b 0 star hlow
  have hge : g.tree.splitIndex g.mark (g.embed e)=T.splitIndex s b:=
    (native_fresh_low_pair_split T e b 0 star heblow).trans heb
  unfold actualHighWallOriginalFreshAffineResidual nativeOriginalFreshResidual
  dsimp only
  rw [←g.tree.cavityLeft.disorderExpect_const_mul (restWeight_pos n) (restFeature n) ho]
  congr 1
  funext σ
  change Z (g.restRestrict σ)*
    (ActualNaturalBoundaryShape.actualHighWallLowRestFactor M g.mark (g.embed s) σ-
      ActualNaturalBoundaryShape.actualHighWallLowRestFactor M g.mark (g.embed e) σ)=_
  unfold ActualNaturalBoundaryShape.actualHighWallLowRestFactor
  rw [hgs,hge]
  simp only [fullBoundaryAffineFactor,MarkedPlacement.restSpin]
  rw [←g.restRestrict_at σ s,←g.restRestrict_at σ e]
  dsimp only [g]
  ring

end OAI.SKFluctuations.Cavity
