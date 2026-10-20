module

public import ComparisonActualHighWallSecondLowFreshRawCubicAlong
public import ComparisonActualHighWallSecondLowOriginalMean
public import ComparisonSignedCavitySecondLowCenteredReplacementSource
public import ComparisonActualHighWallSecondLowTwoLowCloneBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization 
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_fresh_centered_cubic_price_along
    (degree rBound : ℕ) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) degree T)
          (forms : Fin degree→NativeSourceFactorForm) (initial : Finset (Fin degree))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as pre.length ≤ Cmass*W →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          4*W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) →
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)) →
          M.data.wallRadius M.alpha (partitionPoint 0 as pre.length) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowFreshFullB0Source (dim n) q U b h K T s
          (pre.length+mid.length) (nativeOriginalCenteredRestTest (dim n) q U b h K T
            (G.canonicalHighWallSource M forms).restProduct)| ≤
          C*M.data.d^3*sourceMonomialScale x W initial := by
  obtain ⟨Ca,hCa,HA⟩:=eventually_actual_high_wall_second_low_fresh_raw_cubic_price_along
    (D:=D) degree rBound Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Czero,hCzero,H0⟩:=eventually_actual_high_wall_second_low_fresh_raw_cubic_price_along
    (D:=D) 0 rBound Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨Cp,hCp,Hmean⟩:=eventually_actual_high_wall_second_low_original_mean_budget
    (D:=D) degree rBound Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^degree
  have hCmean:0 < Cmean:=by dsimp [Cmean];positivity
  refine ⟨Ca+Cmean*Czero,by positivity,?_⟩
  filter_upwards [HA,H0,hdim.eventually Hmean] with n hnA hn0 hnm
  intro M hwork L us hus hret hmesh
  filter_upwards [hnA M hwork L us hus hret hmesh,
    hn0 M hwork L us hus hret hmesh,
    hnm M hwork L us hus hret hmesh] with k hkA hk0 hkm
  dsimp only at hkA hk0 hkm ⊢
  intro pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass
    hmid hstar hT hLeaves hcut hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let W:=M.data.d
  let P:=(G.canonicalHighWallSource M forms).restProduct
  let p0:=sourceMonomialScale x W initial
  let rate:=M.data.d^3
  have hp0:0 ≤ p0:=by
    have hx:0 < x:=M.hxs.trans_le hxsx
    have hW:0 < W:=hx.trans_le hxW
    dsimp [p0]
    unfold sourceMonomialScale
    positivity
  have Hm:|nativeOriginalRestTestExpectation (dim n) q U b h K T P| ≤ Cmean*p0:=by
    have hxEq : x=M.data.d:=le_antisymm hxW (hwork ▸ hxsx)
    have Hmass : ∀e,G.sourceLowMass e≤Cmass*M.data.d:=by
      intro e
      simpa only [hxEq,sourceFactorScale,ite_self] using hmass e
    have Hp0Eq : p0=M.data.d^degree:=by dsimp only [p0,W];rw [hxEq,sourceMonomialScale_self]
    rw [Hp0Eq]
    rw [hparts] at hkm
    simpa only [Cmean,P,p0,W,q,b,h,K,hparts,mul_assoc] using
      hkm U T hLeaves G forms Hmass
  have HP:|nativeSecondLowFreshFullB0Source (dim n) q U b h K T s star P| ≤
      Ca*rate*p0:=by
    simpa only [P,p0,rate,mul_assoc] using
      hkA pre mid tail hparts T G forms initial s U hU x sourceMass hsourceMass hmid hstar hT
        hLeaves hcut hxsx hxW hWmacro hLOW hmass Hmi Hms Hhigh Hz Hrlow Hri Hrs HCx Hdyadic
  let G0:=emptyNaturalBoundaryShape (dim n) T
  have Hp0:sourceMonomialScale x W (∅ : Finset (Fin 0))=1:=by
    rw [←source_factor_scale_product]
    exact Fin.prod_univ_zero _
  have H1:|nativeSecondLowFreshFullB0Source (dim n) q U b h K T s star (fun _=>1)| ≤
      Czero*rate:=by
    have HH:=hk0 pre mid tail hparts T G0 Fin.elim0 ∅ s U hU x sourceMass hsourceMass
      hmid hstar hT hLeaves hcut hxsx hxW hWmacro (fun e=>e.elim0) (fun e=>e.elim0)
      Hmi Hms Hhigh Hz (fun e=>e.elim0) Hri Hrs HCx Hdyadic
    have HP0:(G0.canonicalHighWallSource M Fin.elim0).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    rw [HP0] at HH
    dsimp only [W] at Hp0
    simpa only [rate,W,Hp0,mul_one,mul_assoc] using HH
  change |nativeSecondLowFreshFullB0Source (dim n) q U b h K T s star
    (nativeOriginalCenteredRestTest (dim n) q U b h K T P)| ≤ _
  change |nativeSecondLowFreshFullB0Source (dim n) q U b h K T s star
    (fun σ=>P σ-nativeOriginalRestTestExpectation (dim n) q U b h K T P)| ≤ _
  rw [actual_general_fresh_full_B0_sub_const,sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul]
  apply (add_le_add HP (mul_le_mul Hm H1 (abs_nonneg _) (mul_nonneg hCmean.le hp0))).trans_eq
  dsimp only [rate,p0]
  ring

end OAI.SKFluctuations.Cavity
