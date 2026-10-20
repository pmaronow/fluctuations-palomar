module

public import ComparisonSignedCavityCanonicalRestFactorMoments
public import ComparisonSignedCavityInheritedCanonicalRestMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_rest_factor_moments
    (d : ℕ) (hd : 0 < d) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf→M.xs≤1→
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
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment
    1 d (by norm_num) hd Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with k hk
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
