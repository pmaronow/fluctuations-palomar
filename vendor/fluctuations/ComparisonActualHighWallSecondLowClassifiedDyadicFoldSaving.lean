module

public import ComparisonActualHighWallSecondLowClassifiedDyadicFoldRate
public import ComparisonActualHighWallDyadicCutCount

@[expose] public section

noncomputable section
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization 

private theorem dyadic_depth_nat_saved_factor (n : ℕ) (hn : 1 ≤ n) (eta count : ℝ)
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

theorem eventually_actual_high_wall_second_low_classified_dyadic_fold_saving
    (a : ℕ) (Bclock Cmass Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
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
          4*W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) →
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,U ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass →
          NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowClassifiedCompleteCFold E U q
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))
          (G.canonicalHighWallSource M forms).restProduct| ≤
          C*(E.source.D.leaves:ℝ)^2*(n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_second_low_classified_dyadic_fold_rate
    (D:=D) a Bclock Cmass Rmacro F hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  refine ⟨C*(2^eta+1),by positivity,?_⟩
  filter_upwards [H,ActualHighWallOverlapMinimum.eventually_actual_high_wall_dyadic_cut_depth_power_bound
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 hCx heta,eventually_ge_atTop (1:ℕ)] with n hn hnDepth hn1
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz hfloor Hchain
  have HH:=hk pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz Hchain
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  have ha1 : sourceMass ≤ 1:=by rw [←Hchain.literal_source_mass];exact (partitionPoint_mem _ ho U).2
  have HD:=hnDepth M sourceMass hfloor ha1
  have Hsaved:=dyadic_depth_nat_saved_factor n hn1 eta (nativeDyadicCutDepth sourceMass) heta.le
    (by simpa only [] using HD)
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have hW : 0 < M.data.d:=hx.trans_le hxW
  have hp0 : 0 ≤ sourceMonomialScale x
      (M.data.d) initial:=by
    unfold sourceMonomialScale
    positivity
  apply HH.trans
  have HM:=mul_le_mul_of_nonneg_right Hsaved
    (show 0 ≤ C*(E.source.D.leaves:ℝ)^2*
      M.data.d*M.xs^2*
        sourceMonomialScale x (M.data.d) initial by positivity)
  convert HM using 1 <;> ring

end OAI.SKFluctuations.Cavity
