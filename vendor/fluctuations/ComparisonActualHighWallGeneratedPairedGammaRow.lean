module

public import ComparisonActualHighWallPairedGammaUniformRow
public import ComparisonActualGeneralGeneratedPairedSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_generated_paired_gamma_row
    (a : ℕ) (ha : 0 < a) (Bclock Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=M.data.d
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
        let R:=M.data.highErrorEnvelope M.alpha as U
        |fullScalarCutGamma p.tree U K (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark*
          retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
            (nativeRestProjectedPairedTest T P.target star A (nativeRestGeneratedTestValue T P A center) p) []| ≤
          C*M.data.d^a*W^2*pairForkVariation rBound*
            (p.tree.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_canonical_paired_gamma_uniform_row
    (D:=D) a ha Bclock Cmass Rmacro F hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
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
  have Hmass l : GP.sourceLowMass l ≤ Cmass*M.data.d := by
    dsimp only [GP,nativeFreshObservedShape]
    rw [ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]
    exact (by
      simpa only [sourceFactorScale,ite_self] using native_generated_complete_source_mass n P hP hi
        (hs.trans_le hlen) Cmass M.data.d M.data.d (by simpa only [hwork] using hmi) hms l)
  have HH:=hk U rBound (by omega) p.tree GP (fun _=>NativeSourceFactorForm.centered) hleaves hmacroW hsmall Hmass js Hgeom.2.1 Hgeom.2.2.1
    (p.embed g.mark) p.mark (p.embed (g.embed P.target)) hne
    (Hspl.1.trans Hspl.2.symm)
    (by rw [Hspl.1,p.tree.splitIndex_symm];exact hs.trans_le hhigh)
    (by rw [Hspl.1];exact hms)
    (by
      intro l hl
      rw [Hgeom.2.2.2 l hl]
      exact p.tree.splitIndex_symm _ _)
  have HE:=funext (physical_generated_paired_source_eq_endpoint_retarget P hP hi hs hlen p hp hhigh M.bf M.hf)
  rw [HE,fullScalarCutGamma_symm p.tree _ _ (p.embed (g.embed P.target)) p.mark]
  exact HH

end OAI.SKFluctuations.Cavity
