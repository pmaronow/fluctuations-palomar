module

public import ComparisonSignedCavityOriginalRestResamplingLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def restFactor (G : ActualNaturalBoundaryShape n a T) (e : Fin a)
    (σ : T.cavityLeft.Assignment) : ℝ :=
  fullBoundaryAffineFactor n (G.α e) (G.β e)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.j e)),false)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false)

def edgeShape (G : ActualNaturalBoundaryShape n a T) (e : Fin a) :
    ActualNaturalBoundaryShape n 1 T where
  α:=fun _=>G.α e
  β:=fun _=>G.β e
  i:=fun _=>G.i e
  j:=fun _=>G.j e
  distinct:=fun _=>G.distinct e
  lowInGrid:=fun _=>G.lowInGrid e

theorem edgeShape_restProduct (G : ActualNaturalBoundaryShape n a T) (e : Fin a)
    (σ : T.cavityLeft.Assignment) : (G.edgeShape e).restProduct σ=G.restFactor e σ := by
  simp [restProduct,edgeShape,restFactor]

def retarget (G : ActualNaturalBoundaryShape n a T) (j' : Fin a→T.Slot)
    (hne : ∀e,G.i e≠j' e) : ActualNaturalBoundaryShape n a T where
  α:=G.α
  β:=G.β
  i:=G.i
  j:=j'
  distinct:=hne
  lowInGrid:=fun _e=>T.splitIndex_le_clockLength _ _

theorem retarget_sourceLowMass (G : ActualNaturalBoundaryShape n a T)
    (j' : Fin a→T.Slot) (hne : ∀e,G.i e≠j' e)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) (e : Fin a) :
    (G.retarget j' hne).sourceLowMass e=G.sourceLowMass e := by
  simp only [sourceLowMass,retarget,←hlow e]

theorem retarget_canonicalMinimumSource {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (j' : Fin a→T.Slot) (hne : ∀e,G.i e≠j' e)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) :
    (G.retarget j' hne).canonicalMinimumSource M f=
      (G.canonicalMinimumSource M f).retarget j' hne := by
  have H : (G.retarget j' hne).sourceLowMass=G.sourceLowMass:=
    funext (G.retarget_sourceLowMass j' hne hlow)
  unfold canonicalMinimumSource
  simp only [H]
  rfl

end ActualNaturalBoundaryShape

theorem eventually_actual_minimum_canonical_rest_factor_moments
    (d : ℕ) (hd : 0 < d) (Bclock Temp Cmass : ℝ)
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
        ∀(a : ℕ) (T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs≤x→x≤W→(∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
        ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>|(G.canonicalMinimumSource M f).restFactor e σ|^(2*d)) 0≤
            (C*sourceFactorScale x W initial e)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_bare_canonical_rest_even_moment
    1 d (by norm_num) hd Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro a T G f initial x W hxsx hxW hmass e
  let r:=sourceFactorScale x W initial e
  have hr : M.xs≤r:=hxsx.trans (source_factor_scale_ge_initial hxW initial e)
  have He:=hk T (G.edgeShape e) (fun _=>f e) ∅ r r hr le_rfl (by
    intro j
    simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.edgeShape,
      r,sourceFactorScale,Finset.notMem_empty,↓reduceIte] using hmass e)
  simpa [ActualNaturalBoundaryShape.restProduct,ActualNaturalBoundaryShape.restFactor,
    ActualNaturalBoundaryShape.canonicalMinimumSource,ActualNaturalBoundaryShape.edgeShape,
    ActualNaturalBoundaryShape.sourceLowMass,sourceMonomialScale] using He

end OAI.SKFluctuations.Cavity
