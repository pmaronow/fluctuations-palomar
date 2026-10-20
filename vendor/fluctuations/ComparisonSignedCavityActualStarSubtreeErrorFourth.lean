module

public import ComparisonSignedCavityRestCenteredPairTransport
public import ComparisonSignedCavityActualAnchorPrimitives

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_star_subtree_centered_fourth_bound
    (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n) tail) (e f : T.Slot),e ≠ f →
          let j:=pre.length+mid.length+T.splitIndex e f
          let center:=orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
          (∫z,T.expect (restWeight n) (restFeature n) (nativeStarSuffixClock n pre mid q)
            (fun σ=>(deletedOverlap n (joinSpin (T.atSlot σ e,false))
              (joinSpin (T.atSlot σ f,false))-center)^4) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(M.xs+partitionPoint 0 as j))^4 := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_bare_centered_pair_even_moment
    (D:=D) 2 (by norm_num) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut T e f hef
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let j:=pre.length+mid.length+T.splitIndex e f
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hj:j ≤ (pre++(mid++tail)).length:=by
    have H:=T.splitIndex_le_clockLength e f
    dsimp only [j]
    simp only [List.length_append]
    omega
  have HM:=native_common_star_subtree_pair_marginal n pre mid tail ho T e f hef 0 q
    (fun σ τ=>(deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-S j)^4) 0
  change (∫z,T.expect (restWeight n) (restFeature n) (nativeStarSuffixClock n pre mid q)
    (fun σ=>(deletedOverlap n (joinSpin (T.atSlot σ e,false))
      (joinSpin (T.atSlot σ f,false))-S j)^4) (exteriorForestStarRoot z) ∂_ ) ≤ _
  unfold nativeStarSuffixClock
  rw [HM]
  have HT:=native_rest_centered_pair_eq_decoupled n 2 hn0 ho b h K 0 j hj (S j)
  simp only [show 2*2=4 by norm_num,show Even 4 by decide |>.pow_abs] at HT
  rw [HT]
  have HK (bs : List PositiveMass) (hbs:bs=as) :
      (ClockTree.pairClock bs j).disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q 0 0 0 b h K)
        (fun σ=>(deletedOverlap n (joinSpin (ClockTree.pairSpin bs j σ).1)
          (joinSpin (ClockTree.pairSpin bs j σ).2)-S j)^4) 0 ≤
        (C*(M.xs+partitionPoint 0 as j))^4 := by
    subst bs
    simpa only [show 2*2=4 by norm_num,show Even 4 by decide |>.pow_abs,q,b,h,K,S,as] using
      hk 0 0 0 (by norm_num) (by norm_num) j (by simpa only [hcut] using hj)
  exact HK (pre++(mid++tail)) hcut

end OAI.SKFluctuations.Cavity
