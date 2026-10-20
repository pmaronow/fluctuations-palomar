module

public import ComparisonActualHighWallFreshHighTaylorFromMinimum
public import ComparisonActualHighWallResourceThirdLowPrice
public import ComparisonActualGeneralResourceTaylorBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_fresh_resource_Taylor_original_profile
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^k*actualGeneralOriginalFreshResourceTaylorRemainder M.bf M.hf U P| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*(M.data.d*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R))+M.data.d^3)) := by
  obtain ⟨CH,hCH,HH⟩:=eventually_actual_high_wall_fresh_resource_HIGH_parts_from_minimum
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CL,hCL,HL⟩:=eventually_actual_high_wall_fresh_resource_third_LOW_cubic_price
    (D:=D) degree rBound Bclock Cmass Ccut hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=2*CH+CL+1
  have hC : 0 < C:=by dsimp only [C];positivity
  have hcoefH : 2*CH ≤ C:=by dsimp only [C];linarith only [hCL]
  have hcoefL : CL/2 ≤ C:=by dsimp only [C];linarith only [hCH,hCL]
  refine ⟨C,hC,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hwork L us hus hret hmesh
  filter_upwards [hnH M hwork L us hus hret hmesh,hnL M hwork L us hus hret hmesh] with jGrid hjH hjL
  dsimp only at hjH hjL ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut
  let as:=finiteCutMasses us jGrid
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=T.forkCost (fun l=>(R l)^(4/p))+edgeBudget 0 as (fun l=>(R l)^(4/p))+
    M.data.d*(T.forkCost R+edgeBudget 0 as R)
  let scale:=|P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed
  let Hprice:=scale*(CH*M.data.d*profile)
  let Lprice:=scale*(CL*M.data.d^3)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR l : 0 ≤ R l:=M.data.highErrorEnvelope_nonneg M.alpha as U l
  have hprofile : 0 ≤ profile:=
    add_nonneg (add_nonneg (T.forkCost_nonneg (fun l=>Real.rpow_nonneg (hR l) _))
      (edgeBudget_nonneg ho (fun l=>Real.rpow_nonneg (hR l) _)))
      (mul_nonneg M.data.hd.le (add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hscale : 0 ≤ scale:=mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le
  have hHprice : 0 ≤ Hprice:=mul_nonneg hscale (mul_nonneg (mul_nonneg hCH.le M.data.hd.le) hprofile)
  have hLprice : 0 ≤ Lprice:=mul_nonneg hscale (mul_nonneg hCL.le (pow_nonneg M.data.hd.le 3))
  have HH' l t hl ht part:=hjH i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut l t hl ht part
  have HL' l t hl ht:=hjL i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut l t hl ht
  have H:=actual_general_normalized_fresh_resource_Taylor_abs_le M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) U k P ho M.data.hd hHprice hLprice
    (by
      intro l t hl ht part
      convert HH' l t hl ht part using 1
      )
    (by
      intro l t hl ht
      exact HL' l t hl ht)
  apply H.trans
  calc
    2*Hprice+Lprice/2=scale*((2*CH)*(M.data.d*profile)+(CL/2)*M.data.d^3):=by
      dsimp only [Hprice,Lprice];ring
    _ ≤ scale*(C*(M.data.d*profile)+C*M.data.d^3):=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hcoefH (mul_nonneg M.data.hd.le hprofile))
        (mul_le_mul_of_nonneg_right hcoefL (pow_nonneg M.data.hd.le 3))) hscale
    _ = _:=by dsimp only [scale,profile,R,as];ring

end OAI.SKFluctuations.Cavity
