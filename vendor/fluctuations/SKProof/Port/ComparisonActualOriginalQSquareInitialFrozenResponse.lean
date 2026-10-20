module

public import SKProof.Port.ComparisonActualOriginalQSquareResourceConsumerCore
public import ComparisonSignedCavityActualTargetInitialFrozenRate
public import ComparisonSignedCavityActualCenteredFourTerminalLaw

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_minimum_initial_four_resource_finite_iteration_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (depth : ℕ) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    nativeActualMinimumFourStateResponse_original_q M U W st+
      nativeActualMinimumFourStateResponse_original_q M U W st.freeze=
      nativeActualMinimumFourResidualSum_original_q M hs hU W depth [st]+
      nativeActualOriginalContinuumCenteredFourGFrontier_original_q M as W i star U hi hs hU depth := by
  dsimp only
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hv : ∀Q∈[st],NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    intro Q hQ
    obtain rfl:=List.mem_singleton.mp hQ
    exact hst
  have H:=actual_minimum_four_resource_finite_iteration_original_q M [st] Hv hi hs hU ho W hW hstarK depth
  simpa only [nativeActualOriginalContinuumCenteredFourGFrontier_original_q,st,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero] using H

end OAI.SKFluctuations.Cavity

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem actual_initial_resource_mean_abs_le_two_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i star : ℕ) (hi : i≤as.length)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 hi
    |st.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (st.term.value (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) x) x|≤2 := by
  dsimp only
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 hi
  let P:=st.term.value (fullWeight n) (fullFeature n) v q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) x
  have HP (σ : st.tree.Assignment) : |P σ|≤2 := by
    dsimp only [P,st,nativeActualInitialState,NativeResourceTerm.ofLive,nativeResourceSeed]
    simp only [NativeResourceTerm.value,NativeResourceTerm.scalar,List.map_nil,List.prod_nil,one_mul,
      NativeResourceMark.cut,nativeGeneratedSeed,NativeGeneratedTest.value,NativeGeneratedTest.edges,
      nativeGeneratedEdgeProduct,List.map_nil,List.nil_append,List.map_singleton,List.prod_singleton]
    have HC:=native_physical_resource_center_abs_le_one n M.sweepBf M.sweepHf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho
    let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
    have HD:=abs_deletedOverlap_le_one n
      (joinSpin (g.tree.atSlot σ (g.embed (singleSlot as)))) (joinSpin (g.tree.atSlot σ g.mark))
    exact (abs_sub _ _).trans (by
      have H:=add_le_add HD (HC (g.tree.splitIndex (g.embed (singleSlot as)) g.mark))
      simpa only [show (1:ℝ)+1=2 by norm_num] using H)
  have hw:=st.tree.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x
  change |st.tree.disorderExpect (fullWeight n) (fullFeature n) v q P x|≤2
  unfold ClockTree.disorderExpect
  calc
    _≤∑σ : st.tree.Assignment,|st.tree.disorderWeight (fullWeight n) (fullFeature n) v q σ x*P σ|:=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑σ : st.tree.Assignment,st.tree.disorderWeight (fullWeight n) (fullFeature n) v q σ x*2 := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul,abs_of_nonneg (hw.1 σ)]
      exact mul_le_mul_of_nonneg_left (HP σ) (hw.1 σ)
    _=2:=by rw [←Finset.sum_mul,hw.2,one_mul]

theorem eventually_actual_inherited_initial_frozen_response_cubic_original_q
    (Bclock Temp : ℝ) (hTemp : 0≤Temp)
    {m delta cl cu Az C0 Ct D : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp) → M.h 0=0 → M.xs≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U : ℕ) (hi : i≤as.length) (W x : ℝ),M.xs≤x →
          |nativeActualMinimumFourStateResponse_original_q M U W (nativeActualInitialState as i star 0 hi).freeze|≤
            ((n+1:ℕ):ℝ)^(-m)*x^3 := by
  have HL:=eventually_actual_inherited_original_clock_longitudinal_mean_saving_square_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    2 Bclock Temp hTemp hm hC0
  have Hdec:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2*C0^2) (d:=1) (q:=-(2*m)) (r:=-m) zero_lt_one (by linarith))
  filter_upwards [HL,Hdec] with n hn hdec
  intro M ht hroot hxs1 us hus
  filter_upwards [hn M ht hroot us hus] with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi W x hxs
  let as:=finiteCutMasses us jGrid
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 hi
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hleaves:=nativeActualInitialState_leaves_le (S:=Spin n×Bool) as i star 0 hi
  have Hmean:=actual_initial_resource_mean_abs_le_two_original_q M as ho i star hi 0 q 0
  have HL1:=hj K st.tree U st.term.live.test.target hleaves
  have HF:=nativeOriginalClockResourceResponse_freeze st.term ho U 0 K b C 0 q 0 0 q 0 W
  dsimp only at HF
  change nativeActualMinimumFourStateResponse_original_q M U W st.freeze= _ at HF
  have Hfreeze : |nativeActualMinimumFourStateResponse_original_q M U W st.freeze|≤
      2*(((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) := by
    rw [HF]
    dsimp only [q]
    simp only [pow_zero,neg_mul,one_mul,abs_neg,abs_mul,
      native_original_clock_constant_pairing_eq_mean]
    exact mul_le_mul Hmean HL1 (abs_nonneg _) (by norm_num)
  have Hnum:=M.actual_terminal_power_over_scale hC0 (show (0:ℝ)≤2 by norm_num)
    (gamma:=(1:ℝ)/3) 1
  simp only [ActualHighWallData.N,Nat.cast_one,mul_one,sub_self,zero_add] at Hnum
  have Hsave : 2*((n+1:ℕ):ℝ)^(-(1:ℝ)/3)≤((n+1:ℕ):ℝ)^(-m)*M.xs^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos M.hxs)).mp
    norm_num only at Hnum ⊢
    apply Hnum.trans
    simpa only [one_mul] using hdec
  have hx:=M.hxs.trans_le hxs
  have Hpow : M.xs^4≤x^3 := by
    have H1:=mul_le_mul_of_nonneg_left hxs1 (pow_nonneg M.hxs.le 3)
    have H3:=pow_le_pow_left₀ M.hxs.le hxs 3
    nlinarith only [H1,H3]
  have H1:=mul_le_mul_of_nonneg_right Hsave (sq_nonneg M.xs)
  have H2:=mul_le_mul_of_nonneg_left Hpow
    (show (0:ℝ)≤((n+1:ℕ):ℝ)^(-m) from Real.rpow_nonneg (by positivity) (-m))
  apply Hfreeze.trans
  nlinarith only [H1,H2]

end OAI.SKFluctuations.Cavity
