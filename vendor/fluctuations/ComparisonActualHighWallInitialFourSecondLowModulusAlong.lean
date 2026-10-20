module

public import ComparisonActualHighWallInitialAllLiveB0ModulusAlong
public import ComparisonActualHighWallSecondLowFrozenInitialAlong
public import ComparisonActualGeneralFourSecondLowB0Bridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

def actualHighWallInitialFullB0Envelope (degree : ℕ)
    (C CiU CiB CiM : Fin degree→ℝ) (Cf Cr E d N eta : ℝ) : ℝ :=
  actualHighWallInitialLiveB0Envelope degree C CiU CiB CiM E d N eta+
    Cf*(Cr*originalInitialLowMomentModulus E (Cr*d) (2*(degree+1))+d^3)

theorem eventually_actual_high_wall_initial_full_second_low_modulus_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C CiU CiB CiM : Fin degree→ℝ, ∃Cf Cr : ℝ,
      (∀a,0<C a ∧ 0<CiU a ∧ 0<CiB a ∧ 0<CiM a) ∧ 0<Cf ∧ 0<Cr ∧
      ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d→
      ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail)→
        ∀(U k : ℕ) (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (_hU : U ≤ (pre++(mid++tail)).length)
          (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
          NativeActualResourceGenerated pre.length (pre.length+mid.length) U [.initial] k T P→
          P.resources.length ≤ degree→0 < mid.length→pre.length+mid.length < U→T.leaves ≤ rBound→
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
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U P| ≤
          |P.coefficient| * M.data.d^4*
            actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
              (originalHighWallInitialPairErrorScale M as pre.length)
              M.data.d (dim n:ℝ) eta := by
  classical
  obtain ⟨C,CiU,CiB,CiM,hpositive,HL⟩:=
    eventually_actual_high_wall_initial_all_live_second_low_modulus_price_along
      (D:=D) degree rBound Bclock Cmass Ccut Rmacro F Cx
      hCx heta hCm hCcut hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cf,Cr,hCf,hCr,HF⟩:=
    eventually_actual_high_wall_second_low_frozen_initial_modulus_price_along
      (D:=D) degree rBound Bclock Cmass Ccut Rmacro F Cx
      hCx heta hCm hCcut hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,?_⟩
  filter_upwards [HL,HF] with n hnL hnF
  intro M hwork L us hus hret hmesh
  filter_upwards [hnL M hwork L us hus hret hmesh,
    hnF M hwork L us hus hret hmesh] with jGrid hjL hjF
  dsimp only at hjL hjF ⊢
  intro pre mid tail hparts U k T hU P hP hdegree hmid hs hT hcut
    x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let as:=pre++(mid++tail)
  let E:=originalHighWallInitialPairErrorScale M as pre.length
  let d:=M.data.d
  let N:=(dim n:ℝ)
  let live:=actualHighWallInitialLiveB0Envelope degree C CiU CiB CiM E d N eta
  let frozen:=Cf*(Cr*originalInitialLowMomentModulus E (Cr*d) (2*(degree+1))+d^3)
  have hE:0≤E:=original_high_wall_initial_pair_error_scale_nonneg M as pre.length
  have hN:0≤N:=Nat.cast_nonneg _
  have hLive:0≤live:=by
    dsimp only [live,actualHighWallInitialLiveB0Envelope]
    apply Finset.sum_nonneg
    intro a _
    have hU:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg (hpositive a).2.1.le M.data.hd.le) 8
    have hB:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg (hpositive a).2.2.1.le M.data.hd.le) 8
    have hM:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg (hpositive a).2.2.2.le M.data.hd.le) 4
    have hRate:0≤N^(-eta):=Real.rpow_nonneg hN _
    exact mul_nonneg (hpositive a).1.le (by linarith only [hU,hB,hM,hRate])
  have hMod:0≤originalInitialLowMomentModulus E (Cr*d) (2*(degree+1)):=
    original_initial_low_moment_modulus_nonneg hE (mul_nonneg hCr.le M.data.hd.le) _
  have hFrozen:0≤frozen:=by
    dsimp only [frozen]
    exact mul_nonneg hCf.le (add_nonneg (mul_nonneg hCr.le hMod)
      (pow_nonneg M.data.hd.le _))
  have hCoef:0≤|P.coefficient| * d^4:=
    mul_nonneg (abs_nonneg _) (pow_nonneg M.data.hd.le _)
  have HX:x=d:=le_antisymm hxW (by simpa only [d,hwork] using hx)
  have hScale:nativeResourceScale x d 1 [.initial]=d:=by
    simp [nativeResourceScale,NativeResourceMark.savedScale,HX,d]
  by_cases hMark:NativeResourceMark.initial∈P.live.tags
  · have H:=hjL pre mid tail hparts U k T hU P hP hMark hdegree hmid hs hT hcut
      x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
    rw [hparts] at H
    rw [hparts]
    dsimp only [actualHighWallInitialFullB0Envelope]
    calc
      |(d⁻¹)^k*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U P| ≤
          |P.coefficient| *nativeResourceScale x d 1 [.initial]*d^3*live:=by
            simpa only [as,E,d,N,live] using H
      _ = |P.coefficient| *d^4*live:=by rw [hScale];ring
      _ ≤ |P.coefficient| *d^4*(live+frozen):=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hFrozen) hCoef
  · have H:=hjF pre mid tail hparts U k T hU P hP hMark hdegree hmid hs hT hcut
      x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
    rw [hparts] at H
    rw [hparts]
    dsimp only [actualHighWallInitialFullB0Envelope]
    calc
      |(d⁻¹)^k*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U P| ≤
          |P.coefficient| *Cf*d^3*
            (Cr*d*originalInitialLowMomentModulus E (Cr*d) (2*(degree+1))+d^4):=by
              simpa only [as,E,d] using H
      _ = |P.coefficient| *d^4*frozen:=by dsimp only [frozen];ring
      _ ≤ |P.coefficient| *d^4*(live+frozen):=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hLive) hCoef

theorem eventually_actual_high_wall_initial_four_second_low_modulus_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C CiU CiB CiM : Fin degree→ℝ, ∃Cf Cr : ℝ,
      (∀a,0<C a ∧ 0<CiU a ∧ 0<CiB a ∧ 0<CiM a) ∧ 0<Cf ∧ 0<Cr ∧
      ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d→
      ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail)→
        ∀(U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
          (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
          NativeActualResourceGenerated pre.length (pre.length+mid.length) U [.initial]
            st.generation st.tree st.term→
          st.term.resources.length ≤ degree→0 < mid.length→pre.length+mid.length < U→
          st.tree.leaves ≤ rBound→partitionPoint 0 as U ≤ Ccut*M.data.d→
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
        |(M.data.d⁻¹)^st.generation*
          actualGeneralFourCategoryContrast M.bf M.hf U st .secondLow| ≤
          2*(|st.term.coefficient| * M.data.d^4*
            actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
              (originalHighWallInitialPairErrorScale M as pre.length)
              M.data.d (dim n:ℝ) eta) := by
  obtain ⟨C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,HR⟩:=
    eventually_actual_high_wall_initial_full_second_low_modulus_price_along
      (D:=D) degree (rBound+1) Bclock Cmass Ccut Rmacro F Cx
      hCx heta hCm hCcut hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,?_⟩
  filter_upwards [HR] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro pre mid tail hparts U hU st hP hdegree hmid hs hT hcut
    x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let as:=pre++(mid++tail)
  have ho:MassOrdered 0 as:=by
    dsimp only [as]
    rw [←hparts]
    exact finiteCutMasses_ordered us hus jGrid
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target (pre.length+mid.length)
  have hg:g.tree.leaves≤rBound+1:=
    (st.tree.markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target (pre.length+mid.length))).trans
      (Nat.add_le_add_right hT 1)
  have H0:=hj pre mid tail hparts U st.generation st.tree hU st.term hP hdegree hmid hs
    (by omega) hcut x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have H1:=hj pre mid tail hparts U st.generation g.tree hU (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree) hmid hs hg
    hcut x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let B:=|st.term.coefficient| * M.data.d^4*
    actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
      (originalHighWallInitialPairErrorScale M (finiteCutMasses us jGrid) pre.length)
      M.data.d (dim n:ℝ) eta
  have H0':|(M.data.d⁻¹)^st.generation*
      actualGeneralOriginalCenteredResourceB0 M.bf M.hf U st.term|≤B:=H0
  have H1':|(M.data.d⁻¹)^st.generation*
      actualGeneralOriginalCenteredResourceB0 M.bf M.hf U (st.term.retarget 0)|≤B:=by
    simpa only [NativeResourceTerm.retarget] using H1
  have hB:0≤B:=(abs_nonneg _).trans H0'
  exact actual_general_four_second_low_abs_le_of_full_B0 M.bf M.hf ho hU hs st
    ((M.data.d⁻¹)^st.generation) B hB H0' H1'

end OAI.SKFluctuations.Cavity
