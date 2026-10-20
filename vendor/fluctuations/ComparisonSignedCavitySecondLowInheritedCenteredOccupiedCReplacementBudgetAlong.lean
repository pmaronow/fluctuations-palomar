module

public import ComparisonSignedCavitySecondLowInheritedOccupiedCReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowInheritedOriginalMeanBudget
public import ComparisonSignedCavitySecondLowCenteredReplacementSource
public import ComparisonSignedCavitySecondLowInheritedTwoLowCloneBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_second_low_centered_occupied_c_replacement_budget_along
    (a rBound : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (s : T.Slot) (U : ℕ) (hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as pre.length ≤ Cmass*W →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          4*W ≤ M.R (partitionPoint 0 as U) →
          M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,M.R (G.sourceLowMass e) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          M.R (partitionPoint 0 as pre.length) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (pre.length+mid.length)) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s
          (pre.length+mid.length) hU (nativeOriginalCenteredRestTest (dim n) q U b h K T
            (G.canonicalMinimumSource M forms).restProduct)| ≤
          C*(dim n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along
    (D:=D) a rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Czero,hCzero,H0⟩:=eventually_actual_minimum_inherited_second_low_occupied_c_replacement_budget_along
    (D:=D) 0 rBound Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_minimum_inherited_second_low_original_mean_budget
    (D:=D) a rBound Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^a
  have hCmean:0 < Cmean:=by dsimp [Cmean];positivity
  refine ⟨Ca+Cmean*Czero,by positivity,?_⟩
  filter_upwards [HA,H0,hdim.eventually Hmean] with n hnA hn0 hnm
  intro M HS hxs hcompare L us hus hret hmesh
  filter_upwards [hnA M HS hxs hcompare L us hus hret hmesh,
    hn0 M HS hxs hcompare L us hus hret hmesh,
    hnm M HS hxs L us hus hret hmesh] with k hkA hk0 hkm
  dsimp only at hkA hk0 hkm ⊢
  intro pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hT hLeaves hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let P:=(G.canonicalMinimumSource M forms).restProduct
  let p0:=sourceMonomialScale x W initial
  let rate:=(dim n:ℝ)^(-eta)*W*M.xs^2
  have hp0:0 ≤ p0:=by
    have hx:0 < x:=M.hxs.trans_le hxsx
    have hW:0 < W:=hx.trans_le hxW
    dsimp [p0]
    unfold sourceMonomialScale
    positivity
  have Hm:|nativeOriginalRestTestExpectation (dim n) q U b h K T P| ≤ Cmean*p0:=by
    rw [hparts] at hkm
    simpa only [Cmean,P,p0,W,q,b,h,K,hparts,mul_assoc] using
      hkm U T hLeaves G forms initial x W hxsx hxW hmass
  have HP:|nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P| ≤
      Ca*rate*p0:=by
    simpa only [P,p0,rate,mul_assoc] using
      hkA pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass hmid hstar hT
        hLeaves hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let G0:=emptyNaturalBoundaryShape (dim n) T
  have Hp0:sourceMonomialScale x W (∅ : Finset (Fin 0))=1:=by
    rw [←source_factor_scale_product]
    exact Fin.prod_univ_zero _
  have H1:|nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU (fun _=>1)| ≤
      Czero*rate:=by
    have HH:=hk0 pre mid tail hparts T G0 Fin.elim0 ∅ s U hU x sourceMass hsourceMass
      hmid hstar hT hLeaves hxsx hxW hWmacro (fun e=>e.elim0) (fun e=>e.elim0)
      Hmi Hms Hhigh Hz (fun e=>e.elim0) Hri Hrs HCx Hdyadic
    have HP0:(G0.canonicalMinimumSource M Fin.elim0).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    rw [HP0] at HH
    dsimp only [W] at Hp0
    simpa only [rate,W,Hp0,mul_one,mul_assoc] using HH
  change |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU
    (nativeOriginalCenteredRestTest (dim n) q U b h K T P)| ≤ _
  change |nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU
    (fun σ=>P σ-nativeOriginalRestTestExpectation (dim n) q U b h K T P)| ≤ _
  rw [native_second_low_fresh_occupied_c_replacement_sub_const,sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul]
  apply (add_le_add HP (mul_le_mul Hm H1 (abs_nonneg _) (mul_nonneg hCmean.le hp0))).trans_eq
  dsimp only [rate,p0]
  ring

end OAI.SKFluctuations.Cavity
