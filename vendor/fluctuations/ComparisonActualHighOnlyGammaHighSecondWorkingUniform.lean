module

public import ComparisonActualHighOnlyGammaHighSecondWorkingRows
public import ComparisonActualHighOnlyPairedFarGammaUniformRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 30000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem eventually_actual_minimum_inherited_canonical_paired_gamma_high_second_uniform_row_working_scale_high_only
    (a rBound : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let bclock:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let hclock:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>hclock j+bclock j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>bclock j) (fun _=>hclock j)
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(U : ℕ),0 < U →
        ∀(x : ℝ), M.xs ≤ x → x ≤ W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)),
          T.leaves ≤ rBound → W ≤ Rmacro/2 →
          (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(b s e : T.Slot),s≠e →
          T.splitIndex b s=T.splitIndex b e → T.splitIndex b s < T.splitIndex s e →
          partitionPoint 0 as (T.splitIndex b s) ≤ Cmass*W →
          (∀l,G.j l≠j' l → T.splitIndex (G.j l) (j' l)=T.splitIndex s e) →
        |fullScalarCutGamma T U K s e*
          nativeRestPayloadHighSecondIntegral n q U bclock hclock K T
            (fun σ=>nativeRestEndpointDifference n T b s e σ*
              ((G.canonicalHighOnlySource M f).restProduct σ-
                ((G.retarget j' hne).canonicalHighOnlySource M f).restProduct σ))| ≤
          C*sourceMonomialScale x W initial*W^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  let Cnear:=8*cu*((Az+1/cl)*(1+Cmass))+4*cu+cu*Az+1
  have hnear0 : 0 ≤ Cnear:=by dsimp only [Cnear];positivity
  have hnear1 : 1 ≤ Cnear:=by
    have H1 : 0 ≤ 8*cu*((Az+1/cl)*(1+Cmass)):=by positivity
    have H2 : 0 ≤ cu*Az:=mul_nonneg hcu.le hAz
    dsimp only [Cnear]
    linarith
  obtain ⟨Cfar,hCfar,HF⟩:=eventually_actual_minimum_inherited_canonical_paired_far_gamma_high_second_row_working_scale_high_only
    (D:=D) a ha Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  obtain ⟨Cn,hCn,HN⟩:=eventually_actual_minimum_inherited_canonical_paired_near_gamma_high_second_row_working_scale_high_only
    (D:=D) a ha Bclock Temp Cf Cmass Cnear hTemp hCf hCm hnear0 hm hdelta hroom
    hcl hcu hAz hC0 hCt
  let Price:=nativeInheritedHighSecondL2Price rBound Temp Cf
  have hPrice : 0 ≤ Price:=nativeInheritedHighSecondL2Price_nonneg rBound Temp Cf hTemp
  let C:=max Cfar Cn*Price+1
  have hC : 0 < C := by
    have hmax : 0 < max Cfar Cn:=hCfar.trans_le (le_max_left _ _)
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HF,HN] with n hnF hnN
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hnF M hs0 hsxs hsource hxs hcompare L us hus hret hmesh,
    hnN M hs0 hsxs hsource hxs L us hus hret hmesh] with k hkF hkN
  dsimp only at hkF hkN ⊢
  intro U hU x hxsx hxW T G f initial hT hmacroW hsmall hmass j' hne hlow b s e hse hblow hbgap hbmass hchanged
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let v:=partitionPoint 0 as (T.splitIndex s e)
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
    (4*Cf+2*Temp) Temp
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hxsW : M.xs ≤ W:=le_max_left _ _
  have hW : 0 < W:=M.hxs.trans_le hxsW
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hx:=M.hxs.trans_le hxsx
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    unfold sourceMonomialScale
    positivity
  have Hconst (C₀ : ℝ) (hC₀ : C₀ ≤ max Cfar Cn) :
      C₀*sourceMonomialScale x W initial*W^2*Price*
        (T.forkCost R+edgeBudget 0 as R) ≤
      C*sourceMonomialScale x W initial*W^2*
        (T.forkCost R+edgeBudget 0 as R) := by
    have Hnum : C₀*Price ≤ C := by
      have H:=mul_le_mul_of_nonneg_right hC₀ hPrice
      dsimp only [C]
      linarith
    have H:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right Hnum hscale) (sq_nonneg W)) hcost
    convert H using 1
    ring
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
    have H:=hkN T G f initial x W hxsx hxW hmass j' hne hlow G₀ (fun _=>e) (fun _=>hbe)
      (fun _=>hblow) hbmass U rBound hU hT s e hse Hnear
    dsimp only [G₀] at H
    simp_rw [native_rest_endpoint_canonical_difference_high_only T b s e hbs hbe hblow M] at H
    exact H.trans (Hconst Cn (le_max_right _ _))
  · have Hfar : Cnear*W ≤ v:=(lt_of_not_ge Hnear).le
    have HW : W ≤ Cnear*W := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnear1 hW.le
    have HX : M.xs ≤ v:=hxsW.trans (HW.trans Hfar)
    have HG:=M.actual_paired_far_radius_geometry_high_only hsxs hcl hcu hAz hCm hW hxsW
      (show 8*cu*((Az+1/cl)*(1+Cmass))+4*cu+cu*Az+1 ≤ Cnear from le_rfl)
      hsmall (partitionPoint_mem as ho _) Hfar
    have H:=hkF U rBound hU x hxsx hxW T G f initial v hT HX hmacroW hmass j' hne hlow
      (by
        intro l hl
        rw [hchanged l hl]
        refine ⟨HG.1,HG.2.1,HG.2.2 _ (partitionPoint_mem as ho _) ?_,le_rfl⟩
        apply (hmass l).trans
        apply mul_le_mul_of_nonneg_left _ hCm
        unfold sourceFactorScale
        split_ifs
        · exact hxW
        · exact le_rfl)
      b s e hse hblow hbgap ⟨HG.1,HG.2.1,HG.2.2 _ (partitionPoint_mem as ho _) hbmass,le_rfl⟩ le_rfl
    exact H.trans (Hconst Cfar (le_max_left _ _))

end OAI.SKFluctuations.Cavity
