module

public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonActualHighWallOriginalMeanCorrectionAlong
public import ComparisonActualGeneralFourSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_frozen_state_response_quartic_price_along
    (degree rBound : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0  <  C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin (dim n)×Bool) as i star),
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
          i ≤ star → star < U → U ≤ as.length → st.tree.leaves ≤ rBound → seed.length+st.generation ≤ degree →
          partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        |actualGeneralFourStateResponse M.bf M.hf U M.data.d st.freeze| ≤ 
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^4) := by
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cm,hCm0,HM⟩:=eventually_actual_high_wall_original_longitudinal_mean_quartic_price_along
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) rBound Bclock hm hC0 dim hdim
  refine ⟨A^degree*Cm,by have H:=zero_lt_one.trans_le hA;positivity,?_⟩
  filter_upwards [hdim.eventually HA,HM] with n hnA hnM
  intro M hwork L us hus hret hmesh
  filter_upwards [hnA M hwork L us hus hret hmesh,hnM M hwork us hus] with k hkA hkM
  dsimp only at hkA hkM ⊢
  intro i star U seed st hP hi hs hU hT hdegree hmi hms
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
  let C:=nativePhysicalResourceCenter (dim n) M.bf M.hf as
  have Hdepth : st.term.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hkA U i star st.tree st.term Hdepth (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    hmi hms 1 1 (by norm_num) (by norm_num)
  have Hmean:=hkM K st.tree U st.term.live.test.target hT
  have H:=nativeOriginalClockResourceResponse_freeze_abs_le hP (finiteCutMasses_ordered us hus k)
    K b h C A M.data.d M.data.d 1 (Cm*M.data.d^4)
    (zero_lt_one.trans_le hA) M.data.hd M.data.hd zero_lt_one hi (hs.trans_le hU) Hpair Hmean
  change |actualGeneralFourStateResponse M.bf M.hf U M.data.d st.freeze| ≤ 
    (|st.term.coefficient| *A^(seed.length+st.generation)*nativeResourceScale M.data.d M.data.d 1 seed*1^st.generation)*(Cm*M.data.d^4) at H
  simp only [one_pow,mul_one] at H
  apply H.trans
  have Hp : A^(seed.length+st.generation) ≤ A^degree:=pow_le_pow_right₀ hA hdegree
  have HS : 0 ≤ nativeResourceScale M.data.d M.data.d 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro b hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
    exact (a.savedScale_pos M.data.hd M.data.hd zero_lt_one).le
  have HH:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hp (abs_nonneg st.term.coefficient)) HS)
    (mul_nonneg hCm0.le (pow_nonneg M.data.hd.le 4))
  exact HH.trans_eq (by ring)

end OAI.SKFluctuations.Cavity
