module

public import SKProof.Port.ComparisonActualOriginalQActualDyadicCutCountAlong
public import ComparisonSignedCavitySecondLowInheritedClassifiedDyadicFoldSaving
public import SKProof.Port.ComparisonActualOriginalQClassifiedFarCanonicalTransport
public import SKProof.Port.ComparisonActualOriginalQLowUnpairedResamplingSourceAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQSecondLowInheritedClassifiedDyadicFoldRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum

private theorem dyadic_depth_nat_saved_factor_original_q (n : ℕ) (hn : 1 ≤ n) (eta count : ℝ)
    (heta : 0 ≤ eta) (hcount : count ≤ ((n+1:ℕ):ℝ)^eta) :
    (count+1)*((n:ℝ)^(-eta))^2 ≤ (2^eta+1)*(n:ℝ)^(-eta) := by
  have hn1 : (1:ℝ) ≤ n:=by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ):=by linarith
  have HN : ((n+1:ℕ):ℝ) ≤ 2*(n:ℝ):=by push_cast;linarith
  have Hpow:=Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ((n+1:ℕ):ℝ)) HN heta
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn0.le] at Hpow
  have Hp : 1 ≤ (n:ℝ)^eta:=Real.one_le_rpow hn1 heta
  have Hcoef : count+1 ≤ (2^eta+1)*(n:ℝ)^eta:=by nlinarith only [hcount,Hpow,Hp]
  have HE : (n:ℝ)^eta*((n:ℝ)^(-eta))^2=(n:ℝ)^(-eta) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hn0,←Real.rpow_add hn0]
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_right Hcoef (sq_nonneg _)).trans_eq
  rw [mul_assoc,HE]

theorem eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_saving_original_q
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U : ℕ) (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass)
          (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ (pre++(mid++tail)).length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          T.splitIndex f c < U → T.splitIndex c z < U →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀(d : E.source.D.Slot) e,T.splitIndex (E.originalSlot d) (G.i e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.sweepRadius (partitionPoint 0 as U) →
          M.z ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,U ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.sweepRadius (G.sourceLowMass e) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.sweepRadius (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.sweepRadius (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass →
          NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowClassifiedCompleteCFold E U q
          (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)+
            (M.sweepBf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j))
          (G.canonicalOriginalQSource M forms).restProduct| ≤
          C*(E.source.D.leaves:ℝ)^2*(n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_rate_original_q
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C*(2^eta+1),by positivity,?_⟩
  filter_upwards [H,eventually_actual_dyadic_cut_depth_power_bound_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 hCx heta,eventually_ge_atTop (1:ℕ)] with n hn hnDepth hn1
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz hfloor Hchain
  have HH:=hk pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz Hchain
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  have ha1 : sourceMass ≤ 1:=by rw [←Hchain.literal_source_mass];exact (partitionPoint_mem _ ho U).2
  have HD:=hnDepth M sourceMass hfloor ha1
  have Hsaved:=dyadic_depth_nat_saved_factor_original_q n hn1 eta (nativeDyadicCutDepth sourceMass) heta.le
    (by simpa only [ActualHighWallData.N] using HD)
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have hW : 0 < max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs)):=hx.trans_le hxW
  have hp0 : 0 ≤ sourceMonomialScale x
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))) initial:=by
    unfold sourceMonomialScale
    positivity
  apply HH.trans
  have HM:=mul_le_mul_of_nonneg_right Hsaved
    (show 0 ≤ C*(E.source.D.leaves:ℝ)^2*
      max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))*M.xs^2*
        sourceMonomialScale x (max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))) initial by positivity)
  convert HM using 1 <;> ring

end OAI.SKFluctuations.Cavity
