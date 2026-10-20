module

public import ComparisonSignedCavityActualStarRootAnchorRaw
public import ComparisonSignedCavityInheritedRestRawMoments

@[expose] public section
noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_star_exterior_fourth_bound
    (Bclock Temp Cf : ℝ) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Es : ClockTree (Spin n) tail) (e : Es.Slot),
          (∫z,(Es.fork Es).expect (restWeight n) (restFeature n)
            (nativeStarSuffixClock n pre mid q)
            (fun η=>|deletedOverlap n (joinSpin (Es.atSlot η.1 e,false))
              (joinSpin (Es.atSlot η.2 e,false))|^4) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(M.xs+partitionPoint 0 as (pre.length+mid.length)))^4 := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_inherited_rest_even_bound
    (D:=D) 2 (by norm_num) Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HR] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut Es e
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  unfold nativeStarSuffixClock
  rw [native_common_star_pair_marginal n pre mid tail ho Es e 0 q
    (fun σ τ=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^4) 0]
  apply (native_pair_deleted_even_le_ordered n 2 ho (pre.length+mid.length) 0 _ 0).trans
  have hj : pre.length+mid.length ≤ (finiteCutMasses us k).length := by
    rw [←hcut]
    simp only [List.length_append]
    omega
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) :
      (ClockTree.pairClock bs (pre.length+mid.length)).disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>|orderedOverlap n (ClockTree.pairSpin bs (pre.length+mid.length) σ).1
          (ClockTree.pairSpin bs (pre.length+mid.length) σ).2|^4) 0 ≤
        (C*(M.xs+partitionPoint 0 (finiteCutMasses us k) (pre.length+mid.length)))^4 := by
    subst bs
    simpa only [q,show 2*2=4 by norm_num] using hk (pre.length+mid.length) hj
  exact HK (pre++(mid++tail)) hcut

end OAI.SKFluctuations.Cavity
