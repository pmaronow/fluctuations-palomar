module

public import ComparisonActualHighWallFreshLongitudinalFromMinimum
public import ComparisonActualGeneralFourLongitudinalRestorationReadout
public import ComparisonActualHighWallActualScalarHessianBounds
public import ComparisonActualHighWallContinuumClockMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_bare_longitudinal_original_profile
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
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
        U ≤ as.length → st.tree.leaves ≤ rBound →
        seed.length+st.generation ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀right : Bool,
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast M.bf M.hf U st (nativeActualLongitudinalCategory right)| ≤
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d*(st.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              M.data.d*(st.tree.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_fresh_longitudinal_restoration_from_minimum
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_high_wall_continuum_clock_mass_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cfinal:=2*CK*(1+Cmass)*C+1
  have hCfinal : 0 < Cfinal:=by dsimp only [Cfinal];positivity
  refine ⟨Cfinal,hCfinal,?_⟩
  filter_upwards [H,HK] with n hn hnK
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U seed st hP hi hs hU hT hdepth hmi hms hcut right
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  let R:=M.data.highErrorEnvelope M.alpha as U
  let f:=fun l=>(R l)^(4/p)
  let profile:=st.tree.forkCost f+edgeBudget 0 as f+M.data.d*(st.tree.forkCost R+edgeBudget 0 as R)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  have H0:=hj i star U st.generation seed st.tree st.term hP hi hs hU (by omega) hdepth hmi hms hcut right
  have H1:=hj i star U st.generation seed g.tree (st.term.retarget 0) hP.retarget hi hs hU hg hdepth hmi hms hcut right
  have hlo l (hl : l<U) : R l=0:=by simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hl,ite_true]
  have hflo l (hl : l<U) : f l=0:=by
    dsimp only [f]
    rw [hlo l hl,Real.zero_rpow (ne_of_gt (div_pos (by norm_num) (by linarith : 0<p)))]
  have HR:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs R hlo
  have HF:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs f hflo
  change g.tree.forkCost R=st.tree.forkCost R at HR
  change g.tree.forkCost f=st.tree.forkCost f at HF
  change |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U (st.term.retarget 0) right| ≤
    |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
      (C*(g.tree.forkCost f+edgeBudget 0 as f+M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))) at H1
  rw [HF,HR] at H1
  let B:=|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*profile)
  have H0' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U st.term right| ≤ B:=by
    convert H0 using 1
  have H1' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U (st.term.retarget 0) right| ≤ B:=by
    convert H1 using 1
  have hB : 0 ≤ B:=(abs_nonneg _).trans H0'
  have Hdiff : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U st.term right-
      (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U (st.term.retarget 0) right)| ≤ 2*B:=by
    have HH:=abs_sub ((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U st.term right)
      ((1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U (st.term.retarget 0) right))
    rw [abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at HH
    linarith only [HH,H0',H1',hB]
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hchi : |chi| ≤ 1:=OAI.SKFluctuations.Cavity.ActualHighWallData.actual_scalar_boundary_chi_abs_le_one
    M.data M.alpha as ho U (by omega) hU
  have hK0 : 0 ≤ K star:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho star
  have hK : K star ≤ CK*(1+Cmass)*M.data.d:=by
    have Hmass : M.xs+partitionPoint 0 as star ≤ (1+Cmass)*M.data.d:=by
      rw [hwork]
      dsimp only [as]
      linarith only [hms]
    exact (hnK M hwork as ho star).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hmass hCK.le)
  have hpre : |-chi*K star| ≤ CK*(1+Cmass)*M.data.d:=by
    rw [abs_mul,abs_neg,abs_of_nonneg hK0]
    exact (mul_le_mul hchi hK hK0 zero_le_one).trans_eq (by ring)
  rw [actual_general_four_longitudinal_contrast_eq_resources M.bf M.hf U st ho (hs.le.trans hU) right]
  have Hring : (M.data.d⁻¹)^st.generation*(-chi*K star*
      (actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U st.term right-
        (1/2:ℝ)*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U (st.term.retarget 0) right))=
      (-chi*K star)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U st.term right-
        (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalFreshResourceLongitudinalRestoration M.bf M.hf U (st.term.retarget 0) right)):=by ring
  rw [Hring,abs_mul]
  have HH:=mul_le_mul hpre Hdiff (abs_nonneg _)
    (mul_nonneg (mul_nonneg hCK.le (by linarith : 0 ≤ 1+Cmass)) M.data.hd.le)
  have hcoef : 2*CK*(1+Cmass)*C ≤ Cfinal:=by dsimp only [Cfinal];linarith
  have hR l : 0 ≤ R l:=M.data.highErrorEnvelope_nonneg M.alpha as U l
  have hprofile : 0 ≤ profile:=
    add_nonneg (add_nonneg (st.tree.forkCost_nonneg (fun l=>Real.rpow_nonneg (hR l) _))
      (edgeBudget_nonneg ho (fun l=>Real.rpow_nonneg (hR l) _)))
      (mul_nonneg M.data.hd.le (add_nonneg (st.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hscale : 0 ≤ |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed:=
    mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le
  apply HH.trans
  calc
    (CK*(1+Cmass)*M.data.d)*(2*B)=|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
      ((2*CK*(1+Cmass)*C)*M.data.d*profile):=by dsimp only [B];ring
    _ ≤ _:=by
      convert mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef M.data.hd.le) hprofile) hscale using 1

end OAI.SKFluctuations.Cavity
