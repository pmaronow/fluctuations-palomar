module

public import ComparisonSignedCavitySecondLowStarOnlyFreshB0ModuloUnweightedAlong
public import ComparisonSignedCavitySecondLowActualStarOccupiedOldCBaselineBudgetAlong
public import ComparisonSignedCavitySecondLowInheritedOccupiedCReplacementBudgetAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

def ActualSecondLowStarOnlyFullRawB0BudgetOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Couter Rmacro Cx Cerr Cmoving Cstar Crep : ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(mid tail : List PositiveMass) (_hparts : as=mid++tail)
          (T : ClockTree (Spin (dim n)×Bool) (mid++tail))
          (G : ActualNaturalBoundaryShape (dim n) degree T)
          (forms : Fin degree→NativeSourceFactorForm) (initial : Finset (Fin degree))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (mid++tail).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          mid.length=retainedMassPrefixIndex (w n).star.val as →
          0 < mid.length → mid.length < U →
          NativePersistentLowForks mid.length mid.length U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Couter*(W n) →
          (M n).xs ≤ x → x ≤ (W n) →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
          partitionPoint 0 as (mid.length) ≤ Cmass*(W n) →
          4*(W n) ≤ (M n).R (partitionPoint 0 as U) →
          (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,(M n).R (G.sourceLowMass e) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          (M n).R (partitionPoint 0 as (mid.length)) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*(M n).xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (mid++tail) U →
        let P:=(G.canonicalMinimumSource (M n) forms).restProduct
        let g:=nativeFreshAtSlot T 0 s mid.length
        let p0:=sourceMonomialScale x (W n) initial
        let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+partitionPoint 0 as U/(dim n+1:ℕ)
        |nativeSecondLowJointLedger (dim n) q U b h K g.tree
          (fun σ=>P (g.restRestrict σ)) [g.embed s,g.mark]/2| ≤
          Cstar*((dim n+1:ℕ):ℝ)^(-saving)*(W n)*(M n).xs^2*p0+
          Cmoving*(W n)*Cerr*rho*p0+
          Crep*(dim n:ℝ)^(-eta)*(W n)*(M n).xs^2*p0

theorem actual_second_low_star_only_full_raw_B0_budget_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (heta : 0 < eta) (hTemp : 0≤Temp) (hCf : 0≤Cf)
    (hCm : 0≤Cmass) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cm Cstar Crep : ℝ,0<Cm ∧ 0<Cstar ∧ 0<Crep ∧
      ActualSecondLowStarOnlyFullRawB0BudgetOnEveryFinalNetAlong degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cm Cstar Crep dim M W w := by
  obtain ⟨Cm,Cobs,hCmRate,hCobs,Hmod⟩:=actual_second_low_star_only_fresh_B0_modulo_unweighted_budget_along
    degree rBound Cmass Couter Ccal hTemp hCf hCm hCouter hCcal heta.le
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcompare hw
  obtain ⟨Cbase,hCbase,Hbase⟩:=actual_second_low_star_occupied_old_c_baseline_budget_along
    degree rBound Cmass Couter hTemp hCf hCm hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w Hsource hw
  obtain ⟨Crep,hCrep,Hrep⟩:=eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨Cm,16+Cbase,Cobs+Crep,hCmRate,by positivity,add_pos hCobs hCrep,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have HWmacro:=hWlim.eventually (eventually_le_nhds (by linarith : (0:ℝ)<Rmacro/2))
  filter_upwards [Hmod,Hbase,Hrep,Hsource,Hcompare,HW1,HWmacro] with n hnM hnB hnR hs hc hw1 hmacroW
  have hxsW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have hWdef:W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=by
    rw [hcanonical];rfl
  intro L us hus hStarNode hret hmesh
  filter_upwards [hnM L us hus hStarNode hret hmesh,hnB L us hus hStarNode hret hmesh,
    hnR (M n) hs (hxsW.trans hw1) hc L us hus hret hmesh] with k hkM hkB hkR
  dsimp only at hkM hkB hkR ⊢
  rw [←hWdef] at hkR
  intro mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hindex hmid hstar hpersistent hLeaves houter hxsx hxW hLOW hmass Hms Hhigh Hz Hrlow Hrs HCx Hdyadic
  rw [hparts] at hkM hkB hkR hindex houter Hms Hhigh Hz Hrlow Hrs ⊢
  rw [←hindex] at hkB
  let as:=mid++tail
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalMinimumSource (M n) forms).restProduct
  let g:=nativeFreshAtSlot T 0 s mid.length
  let Pg:=fun σ=>P (g.restRestrict σ)
  let p0:=sourceMonomialScale x (W n) initial
  have ho:MassOrdered 0 as:=by change MassOrdered 0 (mid++tail);rw [←hparts];exact finiteCutMasses_ordered us hus k
  have hW:0<W n:=(M n).hxs.trans_le (hxsx.trans hxW)
  have HWU:W n≤(M n).R (partitionPoint 0 as U):=by linarith [Hhigh,hW]
  have Hhalf:(M n).R (partitionPoint 0 as mid.length)≤(M n).R (partitionPoint 0 as U)/2:=by
    have HH:=Hrs.trans (min_le_left _ _);linarith [Hhigh,hW]
  have HZhalf:(M n).z≤(M n).R (partitionPoint 0 as U)/2:=by
    have HH:=Hz.trans (min_le_left _ _);linarith [Hhigh,hW]
  have BM:=hkM mid tail rfl hindex U T hU hmid hstar hpersistent hLeaves houter HWU Hhalf HZhalf
    G forms initial x hxsx hxW hmass s
  have BB:=hkB U T hU hstar hLeaves hpersistent houter G forms initial x hxsx hxW hmass s
  have Hweak:NativePersistentLowForks 0 mid.length U T:=by
    intro a z;rcases hpersistent a z with H|H|H
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr H)
  have Hmi:partitionPoint 0 as 0≤Cmass*W n:=by
    have HH:partitionPoint 0 as 0=0:=by simp [partitionPoint]
    rw [HH];exact mul_nonneg hCm hW.le
  have HR0:(M n).R 0=0:=comparisonSweepQuantile_zero (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha
  have Hri:(M n).R (partitionPoint 0 as 0)≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4):=by
    have HH:partitionPoint 0 as 0=0:=by simp [partitionPoint]
    rw [HH,HR0]
    apply le_min <;> linarith [Hhigh,hW]
  have HRlocal:=hkR [] mid tail
  simp only [List.length_nil,Nat.zero_add,List.nil_append] at HRlocal
  have BR:=HRlocal trivial T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar Hweak hLeaves hxsx hxW hmacroW hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:|χ^2|≤1:=by
    rw [abs_pow];exact (pow_le_pow_left₀ (abs_nonneg χ) (native_second_low_original_chi_abs_le_one ho U K) 2).trans_eq (by norm_num)
  have BC:|χ^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s mid.length hU P|≤
      Cbase*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0:=by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans_eq (one_mul _)).trans BB
  have RC:|χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s mid.length hU P|≤
      Crep*(dim n:ℝ)^(-eta)*W n*(M n).xs^2*p0:=by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans_eq (one_mul _)).trans BR
  have Hjoin:=native_second_low_fresh_occupied_unweighted_eq_old_baseline_add_replacement
    (dim n) q U b h K T ho s mid.length hstar hU P
  have HE:nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2=
      (nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
        χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s mid.length hU P)+
      χ^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s mid.length hU P+
      χ^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s mid.length hU P:=by
    rw [Hjoin];ring
  change |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2|≤_
  rw [HE]
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_add_le _ _).trans (add_le_add BM BC)) RC).trans_eq
  dsimp only [p0,q,b,h,K,as,χ,P,Pg]
  ring

end OAI.SKFluctuations.Cavity
