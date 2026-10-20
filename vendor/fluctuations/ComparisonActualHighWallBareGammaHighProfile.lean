module

public import ComparisonActualHighWallResourceGammaHighSecondFromMinimum
public import ComparisonActualGeneralFourGammaRestorationReadout
public import ComparisonActualHighWallActualScalarHessianBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_bare_gamma_HIGH_original_profile
    (degree rBound : ℕ) (Bclock Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
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
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star → star < U →
        U ≤ as.length → st.tree.leaves ≤ rBound → seed.length+st.generation ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        M.data.d ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*M.data.d ≤ Rmacro/4 →
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast M.bf M.hf U st .gammaHighRestoration| ≤
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^2*
            (st.tree.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_gamma_high_second_from_minimum
    (D:=D) degree (rBound+1) Bclock Cmass Rmacro F hCm hm hdelta hroom hcl hcu hAz hC0 hCt
    hmacro hRhalf hFmass hFradius
  let Cfinal:=2*C
  have hCfinal : 0 < Cfinal:=by dsimp only [Cfinal];positivity
  refine ⟨Cfinal,hCfinal,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U seed st hP hi hs hU hT hdepth hmi hms hmacroW hsmall
  let as:=finiteCutMasses us jGrid
  let R:=M.data.highErrorEnvelope M.alpha as U
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  have hdegree : st.term.resources.length ≤ degree:=by rw [hP.total_factor_depth];exact hdepth
  have H0:=hj st.tree i star U st.generation seed st.term hP hdegree hi hs hU
    (by omega) hmacroW hsmall (by simpa only [hwork] using hmi) hms
  have H1:=hj g.tree i star U st.generation seed (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree) hi hs hU hg hmacroW hsmall
    (by simpa only [hwork] using hmi) hms
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hlo l (hl : l<U) : R l=0:=by
    simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hl,ite_true]
  have Hfork:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs R hlo
  change g.tree.forkCost R=st.tree.forkCost R at Hfork
  change |(M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) true| ≤
    |st.term.coefficient| *C*nativeResourceScale M.xs M.data.d 1 seed*M.data.d^2*
      (g.tree.forkCost R+edgeBudget 0 as R) at H1
  rw [Hfork] at H1
  rw [hwork] at H0 H1
  let B:=|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
    (C*M.data.d^2*(st.tree.forkCost R+edgeBudget 0 as R))
  have H0' : |(M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term true| ≤ B:=by
    convert H0 using 1
    dsimp only [B,R,as]
    ring
  have H1' : |(M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) true| ≤ B:=by
    convert H1 using 1
    dsimp only [B,R,as]
    ring
  have hB : 0 ≤ B:=(abs_nonneg _).trans H0'
  have Hdiff : |(M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term true-
      (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) true)| ≤ 2*B:=by
    have HH:=abs_sub ((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term true)
      ((1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) true))
    rw [abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at HH
    linarith only [HH,H0',H1',hB]
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hchi : |chi| ≤ 1:=OAI.SKFluctuations.Cavity.ActualHighWallData.actual_scalar_boundary_chi_abs_le_one
    M.data M.alpha as ho U (by omega) hU
  have Heq:=actual_general_four_gamma_restoration_contrast_eq_resources M.bf M.hf U st ho true
  simp only [nativeActualGammaRestorationCategory,ite_true] at Heq
  rw [Heq]
  have Hring : (M.data.d⁻¹)^st.generation*(chi*
      (actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term true-(1/2:ℝ)*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) true))=
      chi*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term true-
        (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) true)):=by ring
  rw [Hring,abs_mul]
  exact (mul_le_mul hchi Hdiff (abs_nonneg _) zero_le_one).trans_eq (by dsimp only [B,Cfinal];ring)

end OAI.SKFluctuations.Cavity
