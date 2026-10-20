module

public import ComparisonActualHighWallOriginalTargetTaylorProfileAlong
public import ComparisonActualHighWallOriginalFreshHighContractionAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000

theorem eventually_actual_high_wall_original_target_Taylor_cubic_along
    (dOrder : ℕ) (hd : 0< dOrder) (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤ (dOrder:ℝ))
    (Bclock Cmass Ccut Rmacro F Cx : ℝ) {eta : ℝ}
    (hCm : 0≤ Cmass) (hCcut : 0≤ Ccut) (hCx : 0< Cx) (heta : 0< eta)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta< 3*m) (hgap : 2*eta< 6*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hmacro : 0< Rmacro) (hRhalf : Rmacro≤ 1/2)
    (hFmass : 1+2*cu≤ F) (hFradius : 1+1/Rmacro≤ F)
    (c : ℝ) (hc : 0 < c) (hcout : cu*Az < c)
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤ (M n).xs→∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(mid tail : List PositiveMass),as=mid++tail→0< mid.length→
      ∀(U : ℕ),mid.length< U→U≤ as.length→
      partitionPoint 0 as mid.length≤ Cmass*(M n).data.d→partitionPoint 0 as U≤ Ccut*(M n).data.d→
      2*c*(M n).data.d ≤ partitionPoint 0 as U→
      (M n).data.d≤ Rmacro/2→4*(M n).data.d≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)→
      (M n).z≤ min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as 0)≤
        min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as mid.length)≤
        min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      ∀sourceMass : ℝ,∀hsourceMass : 0< sourceMass,
      Cx*(M n).xs≤ sourceMass→partitionPoint 0 as U=sourceMass→
      (∀j≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
      |actualGeneralTargetOriginalTaylorPart (n:=dim n) (M n).bf (M n).hf as mid.length U| ≤
        C*(M n).data.d^3 := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_original_target_Taylor_profile_along
    (D:=D) dOrder hd p hp hOrder Bclock Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  have HH:=eventually_actual_high_wall_original_fresh_HIGH_profile_contraction_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout dim hdim M
    (fun n=>(hfixed n).le) hdlim hsRatio
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [HC,HH] with n hnC hnH
  intro L us hus hret hmesh
  filter_upwards [hnC (M n) (hfixed n) L us hus hret hmesh,hnH] with j hjC hjH
  dsimp only at hjC ⊢
  intro mid tail hparts hmid U hs hU hmass hcut hcutlo hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  have HT:=hjC mid tail hparts hmid U hs hU hmass hcut hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  have HP:=hjH us hus mid.length U hs hU hcutlo (4/p) htheta1 htheta2 hdeficit 0
  dsimp only at HP
  let as:=finiteCutMasses us j
  let R:=(M n).data.highErrorEnvelope (M n).alpha as U
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) mid.length
  let profile:=g.tree.forkCost (fun k=>(R k)^(4/p))+edgeBudget 0 as (fun k=>(R k)^(4/p))+
    (M n).data.d*(g.tree.forkCost R+edgeBudget 0 as R)
  let saving:=(M n).data.N^(-(actualMassSavingExponent m delta/256))
  have hN1 : 1 ≤ (M n).data.N:=by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast (by omega : 1 ≤ dim n+1)
  have hsaving : saving ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos hN1
    (by have H:=actualMassSavingExponent_pos hm hdelta;linarith)
  have HPrice : (M n).data.d*profile ≤ (M n).data.d^3:=by
    have H1:=mul_le_mul_of_nonneg_left HP (M n).data.hd.le
    have H2:=mul_le_mul_of_nonneg_right hsaving (pow_nonneg (M n).data.hd.le 3)
    change profile ≤ saving*(M n).data.d^2 at HP
    calc
      _ ≤ saving*(M n).data.d^3:=by convert H1 using 1;dsimp only [saving,profile,R,g,as];ring
      _ ≤ _:=by simpa only [one_mul] using H2
  apply HT.trans
  change C*((M n).data.d^3+(M n).data.d*profile) ≤ (2*C)*(M n).data.d^3
  have H:=mul_le_mul_of_nonneg_left HPrice hC.le
  linarith only [H]

end OAI.SKFluctuations.Cavity
