module

public import ComparisonSignedCavityCanonicalSourceMoments
public import ComparisonSignedCavityLowAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def restProduct (G : ActualNaturalBoundaryShape n a T) (σ : T.cavityLeft.Assignment) : ℝ :=
  ∏e,fullBoundaryAffineFactor n (G.α e) (G.β e)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.j e)),false)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false)

theorem product_eq_restProduct (G : ActualNaturalBoundaryShape n a T) (σ : T.Assignment) :
    G.product σ=G.restProduct (T.cavityAssignment σ).1 := by
  unfold product fullBoundaryAffineProduct restProduct
  apply Finset.prod_congr rfl
  intro e _
  rw [ClockTree.atSlot_cavityLeft,ClockTree.atSlot_cavityLeft]
  simp [fullBoundaryAffineFactor,deletedOverlap,joinSpin]

theorem rest_moment_eq_full_decoupled (G : ActualNaturalBoundaryShape n a T)
    (ho : MassOrdered 0 as) (b h : ℕ→ℝ) (U d : ℕ) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
      (fun j=>Sum.elim (fun _=>b j) (fun _=>h j))
      (fun σ=>|G.restProduct σ|^d) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h 0 0) (fun σ=>|G.product σ|^d) 0 := by
  simp_rw [G.product_eq_restProduct]
  exact (native_decoupled_rest_expect n _ U b h (finitePhysicalMixedClock (n+1) as b h)
    T ho (fun σ=>|G.restProduct σ|^d)).symm

end ActualNaturalBoundaryShape

theorem eventually_actual_minimum_bare_canonical_rest_even_moment
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (Bclock Temp Cmass : ℝ)
    (hTemp : 0≤Temp) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp)→(∀u,M.h u=0)→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs≤x→x≤W→(∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (fun σ=>|(G.canonicalMinimumSource M f).restProduct σ|^(2*d)) 0≤
            (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_bare_canonical_square_even_moment
    a d ha hd Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial x W hxsx hxW hmass
  rw [(G.canonicalMinimumSource M f).rest_moment_eq_full_decoupled
    (finiteCutMasses_ordered us hus k) _ _ 0 (2*d)]
  exact hk 0 T 0 0 (by norm_num) (by norm_num) G f initial x W hxsx hxW hmass

end OAI.SKFluctuations.Cavity
