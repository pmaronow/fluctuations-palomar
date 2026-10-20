module

public import ComparisonSignedCavitySecondLowInheritedTwoLowCloneBudget
public import ComparisonActualHighOnlyClassifiedFarCanonicalTransport
public import ComparisonActualHighOnlyLowUnpairedResamplingSourceAlong
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonActualHighOnlyInheritedCanonicalRestCloneBudget
public import ComparisonSignedCavitySecondLowUnweightedCCanonicalSource
public import ComparisonSignedCavityRestRetainedCloneLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_two_LOW_rest_clone_budget_high_only
    (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(T : ClockTree (Spin n×Bool) as) (f c z : T.Slot) (cut : ℕ) (v : ℝ),
          0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          T.splitIndex c f < cut → T.splitIndex c z < cut →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          4*W ≤ M.R (partitionPoint 0 as cut) →
          M.z  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex f c))  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c))  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          v ≤ partitionPoint 0 as cut →
        let p:=nativeCloneBlockAtSlot T c cut
        let F0:=fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M f c σ*
          ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M z c σ
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>(F0 (p.restOldRestrict σ)-F0 (p.restNewRestrict σ))^2) 0 ≤
          (4*(1+Temp)*C^2*W*((n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v))^2 := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_canonical_rest_clone_budget_high_only
    (D:=D) 2 Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T f c z cut v hv hWmacro hcut Hcf Hcz Hmf Hmz Hhigh Hz Hrf Hrz Hvmass
  have Hfc:f≠c:=by
    intro H
    rw [H,T.splitIndex_self] at Hcf
    omega
  have Hzc:z≠c:=by
    intro H
    rw [H,T.splitIndex_self] at Hcz
    omega
  let G:=emptyNaturalBoundaryShape n T
  let GF:=G.consTwoLowC f c z Hfc Hzc
  let forms:=ActualNaturalBoundaryShape.twoLowCForms (Fin.elim0 : Fin 0→NativeSourceFactorForm)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  have hW:0 < W:=M.hxs.trans_le (le_max_left _ _)
  have Hout:∀e,T.splitIndex c (GF.i e) < cut:=by
    intro e
    refine Fin.cases Hcz (fun e=>?_) e
    exact Fin.cases Hcf (fun e=>e.elim0) e
  have Hmass:∀e,GF.sourceLowMass e ≤ Cmass*sourceFactorScale W W ∅ e:=by
    intro e
    have Hscale:sourceFactorScale W W (∅ : Finset (Fin 2)) e=W:=by simp [sourceFactorScale]
    rw [Hscale]
    refine Fin.cases Hmz (fun e=>?_) e
    exact Fin.cases Hmf (fun e=>e.elim0) e
  have Hlow:∀e,cut ≤ T.splitIndex c (GF.j e) →
      M.R (GF.sourceLowMass e)  ≤  min (M.R (partitionPoint 0 (finiteCutMasses us k) cut)/8) (Rmacro/4):=by
    intro e _
    refine Fin.cases Hrz (fun e=>?_) e
    exact Fin.cases Hrf (fun e=>e.elim0) e
  have HH:=hk T GF forms ∅ c cut W v (le_max_left _ _) (le_refl _) hv hWmacro hcut Hout Hmass
    Hhigh Hz Hlow Hvmass
  have HP:∀σ,(GF.canonicalHighOnlySource M forms).restProduct σ=
      ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M f c σ*
        ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M z c σ:=by
    intro σ
    rw [ActualNaturalBoundaryShape.consTwoLowC_canonical_restProduct_high_only]
    simp only [G,ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    ring
  simp_rw [HP] at HH
  have Hscale:sourceMonomialScale W W (∅ : Finset (Fin 2))=W^2:=by simp [sourceMonomialScale]
  rw [Hscale] at HH
  convert HH using 1
  congr 1
  field_simp
  ring

end OAI.SKFluctuations.Cavity
