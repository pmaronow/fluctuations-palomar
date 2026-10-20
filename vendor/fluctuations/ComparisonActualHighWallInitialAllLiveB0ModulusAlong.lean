module

public import ComparisonActualHighWallInitialLiveB0ModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

def actualHighWallInitialLiveB0Envelope (degree : ℕ)
    (C CiU CiB CiM : Fin degree→ℝ) (E d N eta : ℝ) : ℝ :=
  ∑a : Fin degree,C a*(
    originalInitialLowMomentModulus E (CiU a*d) 8+
    originalInitialLowMomentModulus E (CiB a*d) 8+
    originalInitialLowMomentModulus E (CiM a*d) 4+
    N^(-eta))

theorem eventually_actual_high_wall_initial_all_live_second_low_modulus_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C CiU CiB CiM : Fin degree→ℝ,
      (∀a,0<C a ∧ 0<CiU a ∧ 0<CiB a ∧ 0<CiM a) ∧
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
          NativeResourceMark.initial∈P.live.tags→
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
          |P.coefficient| *nativeResourceScale x M.data.d 1 [.initial]*M.data.d^3*
            actualHighWallInitialLiveB0Envelope degree C CiU CiB CiM
              (originalHighWallInitialPairErrorScale M as pre.length)
              M.data.d (dim n:ℝ) eta := by
  classical
  have HP (a : Fin degree):=
    eventually_actual_high_wall_initial_live_second_low_modulus_price_along
      (D:=D) degree (a.val+1) rBound (by omega) Bclock Cmass Ccut Rmacro F Cx
      hCx heta hCm hCcut hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      hmacro hRhalf hFmass hFradius dim hdim
  choose C CiU CiB CiM hC hCiU hCiB hCiM HC using HP
  refine ⟨C,CiU,CiB,CiM,fun a=>⟨hC a,hCiU a,hCiB a,hCiM a⟩,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr (fun a : Fin degree=>hn a M hwork L us hus hret hmesh)]
    with jGrid hg
  dsimp only at hg ⊢
  intro pre mid tail hparts U k T hU P hP hLiveMark hdegree hmid hs hT hcut
    x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let as:=pre++(mid++tail)
  let E:=originalHighWallInitialPairErrorScale M as pre.length
  let d:=M.data.d
  let N:=(dim n:ℝ)
  let envelope:=actualHighWallInitialLiveB0Envelope degree C CiU CiB CiM E d N eta
  have ho:MassOrdered 0 as:=by
    dsimp only [as]
    rw [←hparts]
    exact finiteCutMasses_ordered us hus jGrid
  have hi:pre.length≤pre.length+mid.length:=by omega
  have hstar:pre.length+mid.length<as.length:=hs.trans_le hU
  have hE:0≤E:=original_high_wall_initial_pair_error_scale_nonneg M as pre.length
  have hN:0≤N:=Nat.cast_nonneg _
  have hterm (a : Fin degree):0≤C a*(
      originalInitialLowMomentModulus E (CiU a*d) 8+
      originalInitialLowMomentModulus E (CiB a*d) 8+
      originalInitialLowMomentModulus E (CiM a*d) 4+N^(-eta)):=by
    have hU:=original_initial_low_moment_modulus_nonneg hE (mul_nonneg (hCiU a).le M.data.hd.le) 8
    have hB:=original_initial_low_moment_modulus_nonneg hE (mul_nonneg (hCiB a).le M.data.hd.le) 8
    have hM:=original_initial_low_moment_modulus_nonneg hE (mul_nonneg (hCiM a).le M.data.hd.le) 4
    have hRate:0≤N^(-eta):=Real.rpow_nonneg hN _
    exact mul_nonneg (hC a).le (by linarith only [hU,hB,hM,hRate])
  have hEnv:0≤envelope:=Finset.sum_nonneg (fun a _=>hterm a)
  have hLivePos:0<P.live.factors.length:=by
    obtain ⟨factor,hfactor,_⟩:=List.mem_map.mp hLiveMark
    obtain ⟨e0,_⟩:=List.mem_iff_get.mp hfactor
    have := e0.isLt
    omega
  ·
    have hLiveLe:P.live.factors.length≤degree:=by
      have HH:P.live.tags.length≤P.resources.length:=by
        simp only [NativeResourceTerm.resources,List.length_append];omega
      simpa only [NativeResourceMonomial.tags,List.length_map] using HH.trans hdegree
    let a:Fin degree:=⟨P.live.factors.length-1,by omega⟩
    have hCount:P.live.factors.length=a.val+1:=by dsimp only [a];omega
    have Hsource:=hg a pre mid tail hparts U k T hU P hP hLiveMark hCount hdegree hmid hs hT hcut
      x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
    rw [hparts] at Hsource
    have Hsum:C a*(
      originalInitialLowMomentModulus E (CiU a*d) 8+
      originalInitialLowMomentModulus E (CiB a*d) 8+
      originalInitialLowMomentModulus E (CiM a*d) 4+N^(-eta))≤envelope:=by
      exact Finset.single_le_sum (fun b _=>hterm b) (Finset.mem_univ a)
    have Hscale:0≤nativeResourceScale x d 1 [.initial]:=
      (actual_resource_raw_scale_pos [.initial] (M.hxs.trans_le hx) M.data.hd).le
    have Hfactor:0≤|P.coefficient| *nativeResourceScale x d 1 [.initial]*d^3:=
      mul_nonneg (mul_nonneg (abs_nonneg _) Hscale) (pow_nonneg M.data.hd.le _)
    have Hprice:=mul_le_mul_of_nonneg_left Hsum Hfactor
    rw [hparts]
    apply Hsource.trans
    convert Hprice using 1; dsimp only [as,E,d,N,envelope]; ring

end OAI.SKFluctuations.Cavity
