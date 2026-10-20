module

public import ComparisonSignedCavityInheritedSourceBaseEighth
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_source_base_eighth_original_q
    (a : ℕ) (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (forms : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(b : ℕ) (GH : ActualNaturalBoundaryShape n b T) (s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n b pre mid tail T s GH 0 q 0),
          (∫z,nativeExteriorForestConditionalTest E.Ei E.Es E.D (restWeight n) (restFeature n)
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ δ=>(G.canonicalOriginalQSource M forms).restProduct (E.read η ζ δ)^8)
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C^a*sourceMonomialScale x W initial)^8 := by
  by_cases ha : a=0
  · subst a
    refine ⟨1,by norm_num,Filter.Eventually.of_forall ?_⟩
    intro n M hs0 hsxs hsource hxs L us hus hret hmesh
    apply Filter.Eventually.of_forall
    intro k
    dsimp only
    intro pre mid tail hcut T G forms initial x W hxsx hxW hmass b GH s E
    rw [←E.whole_law (fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ^8)]
    have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
    have hI : initial=∅:=Subsingleton.elim _ _
    simp [ActualNaturalBoundaryShape.restProduct,sourceMonomialScale,hI,
      T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho]
  · obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_original_q
      a 4 (by omega) (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro pre mid tail hcut T G forms initial x W hxsx hxW hmass b GH s E
    rw [←E.whole_law (fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ^8)]
    have HK (bs : List PositiveMass) (he : bs=finiteCutMasses us k)
        (V : ClockTree (Spin n×Bool) bs) (A : ActualNaturalBoundaryShape n a V)
        (hf : Fin a → NativeSourceFactorForm) (I : Finset (Fin a))
        (hA : ∀e,A.sourceLowMass e ≤ Cmass*sourceFactorScale x W I e) :
        V.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
          (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
            (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
          (fun σ=>(A.canonicalOriginalQSource M hf).restProduct σ^8) 0 ≤
          (C^a*sourceMonomialScale x W I)^8 := by
      subst bs
      simpa only [show 2*4=8 by norm_num,(show Even 8 by decide).pow_abs] using hk V A hf I x W hxsx hxW hA
    exact HK (pre++(mid++tail)) hcut T G forms initial hmass

end OAI.SKFluctuations.Cavity
