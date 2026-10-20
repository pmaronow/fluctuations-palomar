module

public import ComparisonActualGeneralFrozenInitialB0Readout
public import ComparisonActualHighWallFractionalInitialResourcePairBudget
public import ComparisonActualHighWallSecondLowFreshCenteredCubicAlong
public import ComparisonActualGeneralResourceFullB0Geometry
public import ComparisonSignedCavitySecondLowGeneratedFullB0Geometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_frozen_initial_modulus_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C Cr : ℝ,0 < C ∧ 0 < Cr ∧ ∀ᶠn : ℕ in atTop,
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
          NativeResourceMark.initial∉P.live.tags→
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
        let eta:=originalInitialLowMomentModulus
          (originalHighWallInitialPairErrorScale M as pre.length) (Cr*M.data.d) (2*(degree+1))
        |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceB0 M.bf M.hf U P| ≤
          |P.coefficient| *C*M.data.d^3*(Cr*M.data.d*eta+M.data.d^4) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_high_wall_second_low_fresh_centered_cubic_price_along
    (D:=D) a.val rBound Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  choose Cp hCp HC using HP
  obtain ⟨A,Cr,hA,hCr,HA⟩:=eventually_actual_high_wall_fractional_initial_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let Csum:=1+∑a,Cp a
  have hCsum : 0 < Csum:=by
    have HH : 0 ≤ ∑a : Fin (degree+1),Cp a:=Finset.sum_nonneg (fun a _=>(hCp a).le)
    dsimp only [Csum];linarith
  refine ⟨A^(degree+1)*Csum,Cr,by positivity,hCr,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,hdim.eventually HA] with n hnC hnA
  intro M hwork L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr (fun a : Fin (degree+1)=>hnC a M hwork L us hus hret hmesh),
    hnA M hwork L us hus hret hmesh] with jGrid hgC hgA
  dsimp only at hgC hgA ⊢
  intro pre mid tail hparts U k T hU P hP hNo hdegree hmid hs hT hcut
    x sourceMass hsourceMass hx hxW hWmacro hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have Hdyadic:=native_second_low_coarse_readout_from_retained_nodes sourceMass hsourceMass us hus Hnodes
    jGrid U (by simpa only [hparts] using hU) HsourceMass
  rw [hparts] at hgC hgA hcut hmi hms Hhigh Hz Hri Hrs Hdyadic
  let as:=pre++(mid++tail)
  have hi : pre.length ≤ pre.length+mid.length:=by omega
  have hstar : pre.length+mid.length < as.length:=hs.trans_le hU
  have hdepth : 1+k ≤ degree+1:=by
    have HH:=hP.total_factor_depth
    simp only [List.length_singleton] at HH
    omega
  have hLive : P.live.factors.length ≤ degree:=by
    have HH : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append];omega
    simp only [NativeResourceMonomial.tags,List.length_map] at HH
    exact HH.trans hdegree
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let initial:=nativeActualResourceInitialFactors P.live
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    rw [←hparts]
    exact finiteCutMasses_ordered us hus jGrid
  have HX : x=M.data.d:=le_antisymm hxW (hwork ▸ hx)
  have Hpair:=hgA U pre.length (pre.length+mid.length) k T P hP hdepth
    hi hstar.le (hmi.trans (mul_le_mul_of_nonneg_left hxW hCm)) hms
  have Hlive:=hgC a pre mid tail rfl T G (fun _=>NativeSourceFactorForm.centered) initial
    P.live.test.target U hU x sourceMass hsourceMass hmid hs (hP.persistentLowForks hi) hT hcut
    hx hxW hWmacro (native_actual_resource_canonical_factors_LOW P.live hi hs hU)
    (native_actual_resource_canonical_source_mass P.live hi hstar Cmass x M.data.d hmi hms)
    (hmi.trans (mul_le_mul_of_nonneg_left hxW hCm)) hms Hhigh Hz
    (actual_general_resource_canonical_source_radius_gate (M.data.wallRadius M.alpha)
      P.live hi hstar _ Hri Hrs) Hri Hrs HCx Hdyadic
  rw [native_actual_resource_live_scale_eq_annotations] at Hlive
  rw [HX] at Hlive
  let eta:=originalInitialLowMomentModulus
    (originalHighWallInitialPairErrorScale M as pre.length) (Cr*M.data.d) (2*(degree+1))
  let xsmall:=Cr*M.data.d*eta+M.data.d^4
  have Hpair' : P.PairMomentBudget (fullWeight (dim n)) (fullFeature (dim n)) 0
      (finitePhysicalCavitySquareVariance (dim n) U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter (dim n) M.bf M.hf as) 0 A xsmall M.data.d 1:=by
    simpa only [as,xsmall,eta] using Hpair
  have hdpos : 0 < M.data.d:=M.data.hd
  have hCpa:=hCp a
  have herror:=original_high_wall_initial_pair_error_scale_nonneg M as pre.length
  have heta : 0≤eta:=original_initial_low_moment_modulus_nonneg herror
    (mul_nonneg hCr.le M.data.hd.le) _
  have hxsmall : 0<xsmall:=by
    dsimp only [xsmall]
    have hh : 0≤Cr*M.data.d*eta:=mul_nonneg (mul_nonneg hCr.le M.data.hd.le) heta
    have hd4 : 0<M.data.d^4:=pow_pos M.data.hd _
    linarith
  have HB:=actual_general_frozen_initial_full_B0_normalized_profile_le M.bf M.hf hP hdepth hNo ho hi hstar
    hA hxsmall M.data.hd (by positivity : 0 ≤ Cp a*M.data.d^3) Hpair' (by
      dsimp only
      rw [show nativeContinuumMixedClock (dim n) M.bf M.hf as=
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)) by rfl]
      simpa only [G,as,mul_assoc,mul_comm,mul_left_comm] using Hlive)
  have HCa : Cp a ≤ Csum:=by
    have HH:=Finset.single_le_sum (fun a _=>(hCp a).le) (Finset.mem_univ a)
    dsimp only [Csum];linarith
  apply HB.trans
  have HH:=mul_le_mul_of_nonneg_left HCa
    (show 0 ≤ |P.coefficient| *A^(degree+1)*xsmall*M.data.d^3 by positivity)
  calc
    |P.coefficient| * A^(degree+1)*xsmall*(Cp a*M.data.d^3)
        = |P.coefficient| * A^(degree+1)*xsmall*M.data.d^3*Cp a:=by ring
    _ ≤ |P.coefficient| * A^(degree+1)*xsmall*M.data.d^3*Csum:=HH
    _ = _:=by
      dsimp only [xsmall,eta,as]
      rw [hparts]
      ring

end OAI.SKFluctuations.Cavity
