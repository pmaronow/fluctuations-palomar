module

public import ComparisonActualGeneralGeneratedPairedSource
public import ComparisonActualHighOnlyPairedFarGammaUniformRow

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_paired_source_eq_endpoint_retarget_high_only
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P.target star).tree.markedAttach 0)
    (hhigh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : p.tree.cavityLeft.Assignment) :
    let g:=nativeFreshAtSlot T 0 P.target star
    let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
    let GP:=nativeFreshObservedShape G P.target star p hp
    let js:=nativeFreshObservedReplacementSlots G P.target star p
    let Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
    nativeRestProjectedPairedTest T P.target star
      (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
      (nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))) p σ=
      nativeRestEndpointDifference n p.tree (p.embed g.mark) p.mark (p.embed (g.embed P.target)) σ*
        ((GP.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ-
          ((GP.retarget js Hgeom.2.1).canonicalHighOnlySource M
            (fun _=>NativeSourceFactorForm.centered)).restProduct σ) := by
  simpa only [ActualNaturalBoundaryShape.canonicalHighOnlySource,ActualNaturalBoundaryShape.canonicalPhysicalSource]
    using physical_generated_paired_source_eq_endpoint_retarget P hP hi hs hlen p hp hhigh M.bf M.hf σ

theorem eventually_actual_minimum_inherited_generated_paired_gamma_row_high_only
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(T : ClockTree (Spin n×Bool) as) (P : NativeGeneratedTest T)
          (i star U rBound : ℕ),NativeGeneratedTestAncestry i star P → P.edges.length=a →
          i ≤ star → star < U → U ≤ as.length →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        ∀(p : MarkedPlacement (nativeFreshAtSlot T 0 P.target star).tree),
          p∈(nativeFreshAtSlot T 0 P.target star).tree.markedAttach 0 → p.tree.leaves ≤ rBound →
          U ≤ p.tree.splitIndex (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark →
          p.mark≠p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target) →
        let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
        let center:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        |fullScalarCutGamma p.tree U K (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark*
          retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
            (nativeRestProjectedPairedTest T P.target star A (nativeRestGeneratedTestValue T P A center) p) []| ≤
          C*sourceMonomialScale M.xs W (nativeGeneratedCompleteInitial P i)*W^2*pairForkVariation rBound*
            (p.tree.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_paired_gamma_uniform_row_high_only
    (D:=D) a ha Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T P i star U rBound hP hdegree hi hs hlen hmacroW hsmall hmi hms p hp hleaves hhigh hne
  subst a
  let as:=finiteCutMasses us k
  let g:=nativeFreshAtSlot T 0 P.target star
  let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
  let GP:=nativeFreshObservedShape G P.target star p hp
  let js:=nativeFreshObservedReplacementSlots G P.target star p
  let Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
  have Hspl:=native_fresh_observed_endpoint_splits T P.target hs hlen p hp hhigh
  have Hmass l : GP.sourceLowMass l ≤ Cmass*sourceFactorScale M.xs
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs)))
      (nativeGeneratedCompleteInitial P i) l := by
    dsimp only [GP,nativeFreshObservedShape]
    rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass n P hP hi (hs.trans_le hlen) _ _ _ hmi hms l
  have HH:=hk U rBound (by omega) p.tree GP (fun _=>NativeSourceFactorForm.centered)
    (nativeGeneratedCompleteInitial P i) hleaves hmacroW hsmall Hmass js Hgeom.2.1 Hgeom.2.2.1
    (p.embed g.mark) p.mark (p.embed (g.embed P.target)) hne
    (Hspl.1.trans Hspl.2.symm)
    (by rw [Hspl.1,p.tree.splitIndex_symm];exact hs.trans_le hhigh)
    (by rw [Hspl.1];exact hms)
    (by
      intro l hl
      rw [Hgeom.2.2.2 l hl]
      exact p.tree.splitIndex_symm _ _)
  have HE:=funext (native_generated_paired_source_eq_endpoint_retarget_high_only P hP hi hs hlen p hp hhigh M)
  rw [HE,fullScalarCutGamma_symm p.tree _ _ (p.embed (g.embed P.target)) p.mark]
  exact HH

end OAI.SKFluctuations.Cavity
