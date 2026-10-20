module

public import ComparisonSignedCavityInheritedGeneratedGammaHighSecondWorking
public import ComparisonSignedCavityActualResourceGammaHighSecondKernel

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_resource_gamma_high_second_profile_working_scale
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(x : ℝ),M.xs ≤ x → x ≤ W →
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen : ℕ)
          (seed : List NativeResourceMark) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P → P.resources.length ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        |(W⁻¹)^kGen*nativeActualResourceGammaSecondRestoration M U P true| ≤
          |P.coefficient| *C*nativeResourceScale x W 1 seed*W^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cl,hCl,HL⟩:=eventually_actual_minimum_inherited_generated_high_second_bounded_degree_working_scale
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=A^degree*(Temp*Cl)+1
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HL,HA] with n hnL hnA
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hnL M hsource hxs hcompare L us hus hret hmesh,
    hnA M hsource hxs L us hus hret hmesh] with jGrid hjL hjA
  dsimp only at hjL hjA ⊢
  intro x hxsx hxW T i star U kGen seed P hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let scale:=sourceMonomialScale x W (nativeGeneratedCompleteInitial P.live.test i)
  let cost:=T.forkCost R+edgeBudget 0 as R
  let price:=Temp*Cl*W^2*cost
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hx:=M.hxs.trans_le hxsx
  have hW:=M.canonical_direct_test_band_pos
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ cost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hprice : 0 ≤ price:=by dsimp only [price];positivity
  have hscale : 0 ≤ scale:=by dsimp only [scale,sourceMonomialScale];positivity
  have hlive : P.live.test.edges.length ≤ degree:=by
    have HH:=P.live.realizes.length_eq
    have HL : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append]
      omega
    simp only [List.length_map,NativeResourceMonomial.tags] at HH HL
    omega
  have Hlive:=hjL x hxsx hxW T i star U kGen seed P hP hlive hi hs hlen hT hmacroW hsmall hmi hms
  have Hpair:=hjA U i star T P (by omega) (by omega) (by omega) x W hxsx hxW hmi hms
    1 1 (by norm_num) (by norm_num)
  have Hkernel :
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let C:=nativePhysicalResourceCenter n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
      |nativeGammaProjectedSecondRestoration true T P.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0)
        (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct| ≤
        nativeResourceScale x W 1 P.live.tags*price := by
    dsimp only
    change |nativeGammaProjectedHighSecondRestoration T P.live.test.target star U _ _ _ _ _ _| ≤ _
    have Heq:=funext (native_actual_resource_canonical_rest_product_eq_live P.live hi
      (hs.trans_le hP.highCut_le_length) M)
    rw [Heq,actual_minimum_generated_high_second_fixed_fork_kernel M T ho star U P.live.test,abs_mul,
      abs_of_nonneg (NNReal.coe_nonneg _)]
    have Hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ Temp:=by
      exact (hsource _ (partitionPoint_mem as ho star)).1
    have HH:=mul_le_mul Hlive Hb (NNReal.coe_nonneg _) (by
      exact mul_nonneg (mul_nonneg (mul_nonneg hCl.le hscale) (sq_nonneg W)) hcost)
    have Hscale:=P.live.canonical_live_scale_le hx hxW
    have Hscale':=mul_le_mul_of_nonneg_right Hscale hprice
    apply le_trans _ Hscale'
    convert HH using 1 <;> dsimp only [price,scale,cost,W,R,as] <;> ring
  have Hdepth : seed.length+kGen ≤ degree:=by rw [←hP.total_factor_depth];exact hdegree
  have Hnorm:=actual_resource_gamma_second_restoration_normalized_profile_le M hP Hdepth ho hi hs
    true hA hxsx hxW hprice Hpair Hkernel
  have hseed : 0 ≤ nativeResourceScale x W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos hx hW zero_lt_one).le
  have HC : A^degree*(Temp*Cl) ≤ C:=by dsimp only [C];linarith
  have Hfinal:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HC (abs_nonneg P.coefficient)) hseed)
    (mul_nonneg (sq_nonneg W) hcost)
  apply Hnorm.trans
  convert Hfinal using 1 <;> dsimp only [price,cost,W,R,as] <;> ring

theorem actual_inherited_resource_gamma_high_second_profile_working_scale_along
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(T : ClockTree (Spin (dim n)×Bool) as) (i star U k : ℕ)
          (seed : List NativeResourceMark) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P → seed.length+k ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          partitionPoint 0 as i ≤ Cmass*x n → partitionPoint 0 as star ≤ Cmass*W n →
        let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).bf (M n).hf as (4*Cf+2*Temp) Temp
        |((W n)⁻¹)^k*nativeActualResourceGammaSecondRestoration (M n) U P true| ≤
          |P.coefficient| *C*nativeResourceScale (x n) (W n) 1 seed*(W n)^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_resource_gamma_high_second_profile_working_scale
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu)
    hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*W n ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HC,Hsource,hcompare,HW,HG,hxsx,hxW] with n hn hs hc hw hg hnx hnW
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1 : (M n).xs ≤ 1:=by linarith
  intro L us hus hret hmesh
  filter_upwards [hn (M n) hs hx1 hc L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro T i star U k seed P hP hdepth hi hstar hU hT hmi hms
  have Hdegree : P.resources.length ≤ degree:=by rw [hP.total_factor_depth];exact hdepth
  rw [hcanonical] at hw hg hms ⊢
  exact hj (x n) hnx (by simpa only [←hcanonical] using hnW) T i star U k seed P hP Hdegree hi hstar hU hT
    (by norm_num at hw ⊢;exact hw) (by norm_num at hg ⊢;exact hg) hmi hms

end OAI.SKFluctuations.Cavity
