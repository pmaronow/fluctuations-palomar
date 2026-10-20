module

public import ComparisonActualGeneralResourceFullB0Geometry
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonActualHighWallSecondLowFreshCenteredInitialNonemptyAlong
public import ComparisonActualHighWallDistinguishedInitialSourceFactor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_initial_live_second_low_modulus_price_along
    (degree liveCount rBound : ℕ) (hLiveCount : 0 < liveCount)
    (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C CiU CiB CiM : ℝ,0 < C ∧ 0 < CiU ∧ 0 < CiB ∧ 0 < CiM ∧ ∀ᶠn : ℕ in atTop,
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
          NativeResourceMark.initial ∈ P.live.tags→
          P.live.factors.length=liveCount→
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
          |P.coefficient| *C*nativeResourceScale x M.data.d 1 [.initial]*M.data.d^3*(
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as pre.length) (CiU*M.data.d) 8+
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as pre.length) (CiB*M.data.d) 8+
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as pre.length) (CiM*M.data.d) 4+
            (dim n:ℝ)^(-eta)) := by
  classical
  obtain ⟨Cp,CiU,CiB,CiM,hCp,hCiU,hCiB,hCiM,HC⟩:=
    eventually_actual_high_wall_second_low_fresh_centered_initial_nonempty_modulus_price_along
    (D:=D) liveCount rBound hLiveCount Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨A^degree*Cp,CiU,CiB,CiM,by positivity,hCiU,hCiB,hCiM,?_⟩
  filter_upwards [HC,hdim.eventually HA] with n hnC hnA
  intro M hwork L us hus hret hmesh
  filter_upwards [hnC M hwork L us hus hret hmesh,
    hnA M hwork L us hus hret hmesh] with jGrid hgC hgA
  dsimp only at hgC hgA ⊢
  intro pre mid tail hparts U k T hU P hP hLiveMark hLiveCountEq hdegree hmid hs hT hcut
    x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have Hdyadic:=native_second_low_coarse_readout_from_retained_nodes sourceMass hsourceMass us hus Hnodes
    jGrid U (by simpa only [hparts] using hU) HsourceMass
  rw [hparts] at hgC hgA hcut hmi hms Hhigh Hz Hri Hrs Hdyadic
  let as:=pre++(mid++tail)
  have hi : pre.length ≤ pre.length+mid.length:=by omega
  have hstar : pre.length+mid.length < as.length:=hs.trans_le hU
  have hdepth : ([.initial] : List NativeResourceMark).length+k ≤ degree:=by
    rw [←hP.total_factor_depth];exact hdegree
  have hLive : P.live.factors.length ≤ degree:=by
    have HH : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append];omega
    simp only [NativeResourceMonomial.tags,List.length_map] at HH
    exact HH.trans hdegree
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let initial:=nativeActualResourceInitialFactors P.live
  rw [←hLiveCountEq] at hgC
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    rw [←hparts]
    exact finiteCutMasses_ordered us hus jGrid
  have HX : x=M.data.d:=le_antisymm hxW (hwork ▸ hx)
  have Hpair:=hgA U pre.length (pre.length+mid.length) T P (hdegree.trans (by omega))
    (hi.trans hstar.le) hstar.le (hmi.trans (mul_le_mul_of_nonneg_left hxW hCm)) hms
    1 1 (by norm_num) (by norm_num)
  obtain ⟨factor,hfactor,htag⟩:=List.mem_map.mp hLiveMark
  obtain ⟨e0,he0⟩:=List.mem_iff_get.mp hfactor
  have htag' : (P.live.factors.get e0).1=.initial:=by rw [he0];exact htag
  have hInitialSplit:=actual_resource_distinguished_initial_factor_cut P.live hi hstar e0 htag'
  have Hlive:=hgC pre mid tail rfl T G (fun _=>NativeSourceFactorForm.centered) initial
    P.live.test.target U hU x sourceMass hsourceMass hmid hs (hP.persistentLowForks hi) hT hcut
    hx hxW hWmacro (native_actual_resource_canonical_factors_LOW P.live hi hs hU)
    (native_actual_resource_canonical_source_mass P.live hi hstar Cmass x M.data.d hmi hms)
    e0 pre.length rfl hInitialSplit
    (hmi.trans (mul_le_mul_of_nonneg_left hxW hCm)) hms Hhigh Hz
    (actual_general_resource_canonical_source_radius_gate (M.data.wallRadius M.alpha)
      P.live hi hstar _ Hri Hrs) Hri Hrs HCx Hdyadic
  rw [native_actual_resource_live_scale_eq_annotations] at Hlive
  have Hpair' : P.PairMomentBudget (fullWeight (dim n)) (fullFeature (dim n)) 0
      (finitePhysicalCavitySquareVariance (dim n) U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter (dim n) M.bf M.hf as) 0 A x M.data.d 1:=by
    rw [HX]
    exact Hpair
  have herror:=original_high_wall_initial_pair_error_scale_nonneg M as pre.length
  have hetaU:=original_initial_low_moment_modulus_nonneg herror
    (mul_nonneg hCiU.le M.data.hd.le) 8
  have hetaB:=original_initial_low_moment_modulus_nonneg herror
    (mul_nonneg hCiB.le M.data.hd.le) 8
  have hetaM:=original_initial_low_moment_modulus_nonneg herror
    (mul_nonneg hCiM.le M.data.hd.le) 4
  have hrate : 0≤(dim n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have HB:=actual_general_resource_full_B0_normalized_profile_le M.bf M.hf hP hdepth ho hi hstar
    hA (M.hxs.trans_le hx) hxW
    (show 0 ≤ Cp*M.data.d^3*(
      originalInitialLowMomentModulus
        (originalHighWallInitialPairErrorScale M as pre.length) (CiU*M.data.d) 8+
      originalInitialLowMomentModulus
        (originalHighWallInitialPairErrorScale M as pre.length) (CiB*M.data.d) 8+
      originalInitialLowMomentModulus
        (originalHighWallInitialPairErrorScale M as pre.length) (CiM*M.data.d) 4+
      (dim n:ℝ)^(-eta)) by
        have Hsum : 0≤
          originalInitialLowMomentModulus
            (originalHighWallInitialPairErrorScale M as pre.length) (CiU*M.data.d) 8+
          originalInitialLowMomentModulus
            (originalHighWallInitialPairErrorScale M as pre.length) (CiB*M.data.d) 8+
          originalInitialLowMomentModulus
            (originalHighWallInitialPairErrorScale M as pre.length) (CiM*M.data.d) 4+
          (dim n:ℝ)^(-eta):=by linarith only [hetaU,hetaB,hetaM,hrate]
        exact mul_nonneg (mul_nonneg hCp.le (pow_nonneg M.data.hd.le _)) Hsum) Hpair' (by
      dsimp only
      rw [show nativeContinuumMixedClock (dim n) M.bf M.hf as=
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)) by rfl]
      simpa only [G,as,mul_assoc,mul_comm,mul_left_comm] using Hlive)
  rw [hparts]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using HB

end OAI.SKFluctuations.Cavity
