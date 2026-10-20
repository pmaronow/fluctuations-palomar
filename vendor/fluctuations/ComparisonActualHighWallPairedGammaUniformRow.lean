module

public import ComparisonActualHighWallPairedGammaRows
public import ComparisonActualHighWallPairedFarGeometry
public import ComparisonActualGeneralPairedEndpointCanonicalShape

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_paired_gamma_uniform_row
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
        let bclock:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let hclock:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>hclock j+bclock j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>bclock j) (fun _=>hclock j)
        let W:=M.data.d
        ∀(U rBound : ℕ),0 < U →
        let R:=M.data.highErrorEnvelope M.alpha as U
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm),
          T.leaves ≤ rBound → W ≤ Rmacro/2 →
          (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(b s e : T.Slot),s≠e →
          T.splitIndex b s=T.splitIndex b e → T.splitIndex b s < T.splitIndex s e →
          partitionPoint 0 as (T.splitIndex b s) ≤ Cmass*W →
          (∀l,G.j l≠j' l → T.splitIndex (G.j l) (j' l)=T.splitIndex s e) →
        |fullScalarCutGamma T U K s e*
          retainedSignedJets n q U bclock hclock K [restHighKernel n U bclock hclock K] T
            (fun σ=>nativeRestEndpointDifference n T b s e σ*
              ((G.canonicalHighWallSource M f).restProduct σ-
                ((G.retarget j' hne).canonicalHighWallSource M f).restProduct σ)) []| ≤
          C*M.data.d^a*W^2*pairForkVariation rBound*
            (T.forkCost R+edgeBudget 0 as R) := by
  let Cnear:=8*cu*((Az+1/cl)*(1+Cmass))+4*cu+cu*Az+1
  have hnear0 : 0 ≤ Cnear:=by dsimp only [Cnear];positivity
  have hnear1 : 1 ≤ Cnear:=by
    have H1 : 0 ≤ 8*cu*((Az+1/cl)*(1+Cmass)):=by positivity
    have H2 : 0 ≤ cu*Az:=mul_nonneg hcu.le hAz
    dsimp only [Cnear]
    linarith
  obtain ⟨Cfar,hCfar,HF⟩:=eventually_actual_high_wall_canonical_paired_far_gamma_row
    (D:=D) a ha Bclock Cmass Rmacro F hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  obtain ⟨Cn,hCn,HN⟩:=eventually_actual_high_wall_canonical_paired_near_gamma_row
    (D:=D) a ha Bclock Cmass Cnear hCm hnear0 hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨max Cfar Cn,hCfar.trans_le (le_max_left _ _),?_⟩
  filter_upwards [HF,HN] with n hnF hnN
  intro M hwork L us hus hret hmesh
  filter_upwards [hnF M hwork L us hus hret hmesh,
    hnN M hwork L us hus hret hmesh] with k hkF hkN
  dsimp only at hkF hkN ⊢
  intro U rBound hU T G f hT hmacroW hsmall hmass j' hne hlow b s e hse hblow hbgap hbmass hchanged
  let as:=finiteCutMasses us k
  let W:=M.data.d
  let v:=partitionPoint 0 as (T.splitIndex s e)
  let R:=M.data.highErrorEnvelope M.alpha as U
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hxW : M.xs ≤ W:=hwork.le
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hx:=M.hxs
  have hscale : 0 ≤ M.data.d^a:=pow_nonneg M.data.hd.le _
  have Hconst (C : ℝ) (hC : C ≤ max Cfar Cn) :
      C*M.data.d^a*W^2*pairForkVariation rBound*
        (T.forkCost R+edgeBudget 0 as R) ≤
      max Cfar Cn*M.data.d^a*W^2*pairForkVariation rBound*
        (T.forkCost R+edgeBudget 0 as R):=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hscale) (sq_nonneg W))
      (pairForkVariation_nonneg rBound)) hcost
  by_cases Hnear : v ≤ Cnear*W
  · have hbs : b≠s := by
      intro H
      rw [H,T.splitIndex_self] at hbgap
      exact (not_lt_of_ge (T.splitIndex_le_clockLength s e)) hbgap
    have hbe : b≠e := by
      intro H
      rw [H,T.splitIndex_self] at hblow
      rw [H,hblow] at hbgap
      exact (not_lt_of_ge (T.splitIndex_le_clockLength s e)) hbgap
    let G₀:=nativeRestEndpointShape T b s hbs
    have H:=hkN T G f hmass j' hne hlow G₀ (fun _=>e) (fun _=>hbe)
      (fun _=>hblow) hbmass U rBound hU hT s e hse Hnear
    dsimp only [G₀] at H
    simp_rw [physical_rest_endpoint_canonical_difference T b s e hbs hbe hblow M.bf M.hf] at H
    exact H.trans (Hconst Cn (le_max_right _ _))
  · have Hfar : Cnear*W ≤ v:=(lt_of_not_ge Hnear).le
    have HW : W ≤ Cnear*W := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnear1 hW.le
    have HX : M.xs ≤ v:=hxW.trans (HW.trans Hfar)
    have HG:=M.actual_paired_far_radius_geometry hcl hcu hAz hCm hW hxW
      (show 8*cu*((Az+1/cl)*(1+Cmass))+4*cu+cu*Az+1 ≤ Cnear from le_rfl)
      hsmall (partitionPoint_mem as ho _) Hfar
    have H:=hkF U rBound hU T G f v hT HX hmacroW hmass j' hne hlow
      (by
        intro l hl
        rw [hchanged l hl]
        refine ⟨HG.1,HG.2.1,HG.2.2 _ (partitionPoint_mem as ho _) ?_,le_rfl⟩
        apply (hmass l).trans
        exact le_rfl)
      b s e hse hblow hbgap ⟨HG.1,HG.2.1,HG.2.2 _ (partitionPoint_mem as ho _) hbmass,le_rfl⟩ le_rfl
    exact H.trans (Hconst Cfar (le_max_left _ _))

end OAI.SKFluctuations.Cavity
