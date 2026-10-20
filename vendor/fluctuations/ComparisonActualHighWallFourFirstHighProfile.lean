module

public import ComparisonActualGeneralFourFirstHighResourceIdentity
public import ComparisonActualHighWallResourceFirstHighFromMinimum

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_four_first_high_profile
    (degree : ℕ) (Bclock Cmass Rmacro F cK : ℝ)
    (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.data.d
        ∀(i star U rBound : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
          st.term.resources.length  ≤  degree →
          i  ≤  star → star < U → U  ≤  as.length → st.tree.leaves  ≤  rBound →
          W  ≤  Rmacro/2 → (Az+1/cl)*(1+Cmass)*W  ≤  Rmacro/4 →
          partitionPoint 0 as i  ≤  Cmass*M.xs → partitionPoint 0 as star  ≤  Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        let R:=M.data.highErrorEnvelope M.alpha as U
        |actualGeneralFourFirstHighError M.bf M.hf U W st|  ≤
          |st.term.coefficient| *C*nativeResourceScale M.data.d W 1 seed*W*
            nativeGammaFirstHighVariation (rBound+1)*(st.tree.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C₀,hC₀,Hsource⟩:=eventually_actual_high_wall_resource_first_high_from_minimum
    (D:=D) degree Bclock Cmass Rmacro F hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  let C:=2*|Bclock| *C₀/cK+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U rBound seed st hP hdegree hi hs hU hleaf hmacroW hsmall hmi hms hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.data.d
  let R:=M.data.highErrorEnvelope M.alpha as U
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW : 0<W:=M.data.hd
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=st.tree.markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    dsimp only [g] at HH ⊢
    omega
  have H0:=hj st.tree i star U st.generation (rBound+1) seed st.term hP hdegree
    hi hs hU (by omega) hmacroW hsmall hmi hms
  have H1:=hj g.tree i star U st.generation (rBound+1) seed (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree)
    hi hs hU hg hmacroW hsmall hmi hms
  have hlo j (hj : j<U) : R j=0:=by simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hfork:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs R hlo
  change g.tree.forkCost R=st.tree.forkCost R at Hfork
  change |(W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U (st.term.retarget 0)| ≤
    |st.term.coefficient| *C₀*nativeResourceScale M.data.d W 1 seed*W^2*
      nativeGammaFirstHighVariation (rBound+1)*(g.tree.forkCost R+edgeBudget 0 as R) at H1
  rw [Hfork] at H1
  let B:=|st.term.coefficient| *C₀*nativeResourceScale M.data.d W 1 seed*W^2*
    nativeGammaFirstHighVariation (rBound+1)*(st.tree.forkCost R+edgeBudget 0 as R)
  change |(W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U st.term| ≤ B at H0
  change |(W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U (st.term.retarget 0)| ≤ B at H1
  have hB : 0 ≤ B:=(abs_nonneg _).trans H0
  have Hdiff : |(W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U (st.term.retarget 0))| ≤ 2*B:=by
    have HH:=abs_add_le ((W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U st.term)
      (-((1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceFirstHigh M.bf M.hf U (st.term.retarget 0))))
    simp only [←sub_eq_add_neg,abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at HH
    simp only [abs_mul] at H0 H1
    linarith
  have hk : 0<K star:=(mul_pos hcK hW).trans_le hstarK
  have hb : 0 ≤ (M.bf (partitionPoint 0 as star):ℝ):=NNReal.coe_nonneg _
  have Htotal:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho star)
  have Hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ |Bclock|:=by
    apply (show (M.bf (partitionPoint 0 as star):ℝ) ≤ Bclock from by
      linarith [M.hT,(M.hf (partitionPoint 0 as star)).coe_nonneg]).trans
    exact le_abs_self Bclock
  have Hratio : (M.bf (partitionPoint 0 as star):ℝ)/K star ≤ |Bclock|/(cK*W):=
    div_le_div₀ (abs_nonneg Bclock) Hb (mul_pos hcK hW) hstarK
  rw [actual_general_four_first_high_error_eq_resources M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) st hP hi hs ho W]
  rw [abs_mul,abs_neg,abs_div,abs_of_nonneg hb,abs_of_pos hk]
  apply (mul_le_mul Hratio Hdiff (abs_nonneg _) (by positivity)).trans
  have hseed : 0 ≤ nativeResourceScale M.data.d W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos M.data.hd hW zero_lt_one).le
  have hcost : 0 ≤ st.tree.forkCost R+edgeBudget 0 as R:=
    add_nonneg (st.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  calc
    |Bclock|/(cK*W)*(2*B)=|st.term.coefficient| *(2*|Bclock| *C₀/cK)*
        nativeResourceScale M.data.d W 1 seed*W*nativeGammaFirstHighVariation (rBound+1)*
          (st.tree.forkCost R+edgeBudget 0 as R):=by
      dsimp only [B]
      field_simp
    _ ≤ |st.term.coefficient| *C*nativeResourceScale M.data.d W 1 seed*W*
        nativeGammaFirstHighVariation (rBound+1)*(st.tree.forkCost R+edgeBudget 0 as R):=by
      have HC : 2*|Bclock| *C₀/cK ≤ C:=by dsimp only [C];linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left HC (abs_nonneg _)) hseed) hW.le)
          (nativeGammaFirstHighVariation_nonneg _)) hcost
    _=_:=rfl

end OAI.SKFluctuations.Cavity
