module

public import ComparisonActualHighWallSecondLowFullResourceAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_high_wall_four_second_low_cubic_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d→
      ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail)→
        ∀(U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
          NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term→
          st.term.resources.length ≤ degree→0 < mid.length→pre.length+mid.length < U→st.tree.leaves ≤ rBound→
          partitionPoint 0 as U ≤ Ccut*M.data.d→
        ∀(x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),M.xs ≤ x→x ≤ M.data.d→M.data.d ≤ Rmacro/2→
          partitionPoint 0 as pre.length ≤ Cmass*x→
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*M.data.d→
          4*M.data.d ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)→
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
          M.data.wallRadius M.alpha (partitionPoint 0 as pre.length) ≤
            min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤
            min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
          Cx*M.xs ≤ sourceMass→partitionPoint 0 as U=sourceMass→
          (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
        |(M.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast M.bf M.hf U st .secondLow| ≤
          |st.term.coefficient| *C*M.data.d^3*nativeResourceScale x M.data.d 1 seed := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_high_wall_second_low_full_resource_cubic_price_along
    (D:=D) degree (rBound+1) Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [HR] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro pre mid tail hparts U hU seed st hP hdegree hmid hs hT hcut
    x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let as:=pre++(mid++tail)
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    rw [←hparts]
    exact finiteCutMasses_ordered us hus jGrid
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target (pre.length+mid.length)
  have hg : g.tree.leaves ≤ rBound+1:=
    (st.tree.markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target (pre.length+mid.length))).trans
      (Nat.add_le_add_right hT 1)
  have H0:=hj pre mid tail hparts U st.generation st.tree hU seed st.term hP hdegree hmid hs
    (by omega) hcut x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have H1:=hj pre mid tail hparts U st.generation g.tree hU seed (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree) hmid hs hg
    hcut x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let B:=|st.term.coefficient| *C*M.data.d^3*nativeResourceScale x M.data.d 1 seed
  have hscale : 0 ≤ nativeResourceScale x M.data.d 1 seed:=
    (actual_resource_raw_scale_pos seed (M.hxs.trans_le hx) M.data.hd).le
  have hdpos : 0 < M.data.d:=M.data.hd
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have H0' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U st.term| ≤ B:=H0
  have H1' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U (st.term.retarget 0)| ≤ B:=by
    simpa only [NativeResourceTerm.retarget] using H1
  rw [actual_general_four_second_low_eq_two_full_resource_sources M.bf M.hf U hU ho hs st]
  rw [mul_sub]
  have Hring : (M.data.d⁻¹)^st.generation*((1/2:ℝ)*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U
      (st.term.retarget 0))=(1/2:ℝ)*((M.data.d⁻¹)^st.generation*
        actualGeneralOriginalCenteredResourceB0 M.bf M.hf U (st.term.retarget 0)):=by ring
  rw [Hring]
  rw [sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  apply (add_le_add H0' (mul_le_mul_of_nonneg_left H1' (by norm_num : (0:ℝ) ≤ 1/2))).trans
  dsimp only [B]
  nlinarith only [hB]

end OAI.SKFluctuations.Cavity
