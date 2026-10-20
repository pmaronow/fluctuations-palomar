module

public import ComparisonActualHighWallCanonicalRestMoments
public import ComparisonSignedCavityActualCanonicalExteriorMoments
public import ComparisonSignedCavityCanonicalExteriorPayload

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_canonical_source_base_eighth
    (a : ℕ) (Bclock Cmass : ℝ) (hCm : 0≤ Cmass) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1) →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm),(∀e,G.sourceLowMass e≤ Cmass*M.data.d) →
        ∀(b : ℕ) (GH : ActualNaturalBoundaryShape n b T) (s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n b pre mid tail T s GH 0 q 0),
          (∫z,nativeExteriorForestConditionalTest E.Ei E.Es E.D (restWeight n) (restFeature n)
            (fun j=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+j)))
            (fun η ζ δ=>(G.canonicalHighWallSource M forms).restProduct (E.read η ζ δ)^8)
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)≤
              (C^a*M.data.d^a)^8 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_canonical_rest_even_moment
    a 4 (by norm_num) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hfixed L us hus hret hmesh
  filter_upwards [hn M hfixed L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut T G forms hmass b GH s E
  rw [←E.whole_law (fun σ=>(G.canonicalHighWallSource M forms).restProduct σ^8)]
  have HK (bs : List PositiveMass) (HE : bs=finiteCutMasses us k)
      (V : ClockTree (Spin n×Bool) bs) (A : ActualNaturalBoundaryShape n a V)
      (f : Fin a→NativeSourceFactorForm) (hA : ∀e,A.sourceLowMass e≤ Cmass*M.data.d) :
      V.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
        (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
          (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
        (fun σ=>(A.canonicalHighWallSource M f).restProduct σ^8) 0≤(C^a*M.data.d^a)^8:=by
    subst bs
    simpa only [show 2*4=8 by norm_num,(show Even 8 by decide).pow_abs] using hk V A f hA
  exact HK (pre++(mid++tail)) hcut T G forms hmass

end OAI.SKFluctuations.Cavity
