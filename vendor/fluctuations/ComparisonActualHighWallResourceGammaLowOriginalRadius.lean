module

public import ComparisonActualHighWallGammaLowCanonicalOriginalRadius
public import ComparisonActualGeneralResourceGammaRestorationReadout
public import ComparisonActualHighWallRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

private theorem actual_wall_gamma_radius_raw_scale_fixed (rs : List NativeResourceMark) (d : ℝ) :
    nativeResourceScale d d 1 rs=d^rs.length := by
  induction rs with
  | nil=>simp [nativeResourceScale]
  | cons mark rs ih=>
    change mark.savedScale d d 1*nativeResourceScale d d 1 rs=d^(rs.length+1)
    rw [ih,pow_succ]
    cases mark <;> simp only [NativeResourceMark.savedScale,one_mul] <;> ring

theorem eventually_actual_high_wall_resource_gamma_LOW_original_radius_price
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
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
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        |(M.data.d⁻¹)^k*actualGeneralResourceGammaSecondRestoration M.bf M.hf U P false| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*(actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)))*M.data.d^2) := by
  classical
  have HC (a : Fin (degree+1)):=eventually_actual_high_wall_canonical_gamma_LOW_original_radius_price
    (D:=D) a.val rBound Bclock Cmass Ccut hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HC
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0≤∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0<Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a≤Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax];linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0<A:=zero_lt_one.trans_le hA
  refine ⟨A^degree*Cmax,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hnC hnA
  intro M hwork L us hus hret hmesh
  have Hgrids a:=hnC a M hwork L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hwork L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hlen : P.live.factors.length≤degree:=by
    have H:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at H
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  have hmass : ∀e,G.sourceLowMass e≤Cmass*M.data.d:=by
    have H:=native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass
      M.data.d M.data.d hmi hms
    simpa only [sourceFactorScale,ite_self] using H
  let rho:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ))
  have hrho : 0 ≤ rho:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _
    (M.data.hepsilon.1.trans M.data.hepsilon.2).le) (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HL:=hjC a U T hU hT hcut G (fun _=>.centered) hmass P.live.test.target star hs
  have HL' :
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let C:=nativePhysicalResourceCenter n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      |nativeGammaProjectedSecondRestoration false T P.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0)
        (G.canonicalPhysicalSource M.bf M.hf (fun _=>.centered)).restProduct|≤
          nativeResourceScale M.data.d M.data.d 1 P.live.tags*(Cmax*rho*M.data.d^2):=by
    have Hcenter : nativePhysicalResourceCenter n M.bf M.hf as=
        (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)):=by
      funext j
      exact (native_ordered_source_center_eq_completed n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)).symm
    dsimp only
    rw [Hcenter,actual_wall_gamma_radius_raw_scale_fixed]
    have Hmajor:=mul_le_mul_of_nonneg_right (hdom a)
      (mul_nonneg (mul_nonneg (pow_nonneg M.data.hd.le P.live.factors.length) hrho) (sq_nonneg M.data.d))
    apply HL.trans
    convert Hmajor using 1 <;>
      simp only [a,NativeResourceMonomial.tags,List.length_map]
    all_goals ring
  have HP:=hjA U i star T P (by rw [hP.total_factor_depth];omega)
    (hi.trans (hs.le.trans hU)) (hs.le.trans hU) hmi hms 1 1 (by norm_num) (by norm_num)
  have H:=actual_general_resource_gamma_second_restoration_normalized_profile_le M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP hdepth ho hi hs false
    hA M.data.hd le_rfl (mul_nonneg (mul_nonneg hCmax.le hrho) (sq_nonneg M.data.d)) HP HL'
  exact H.trans_eq (by dsimp only [rho];ring)

end OAI.SKFluctuations.Cavity
