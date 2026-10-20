module

public import ComparisonSignedCavityTwoLevelIRootMarginal
public import ComparisonSignedCavityActualRestRawMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem deleted_overlap_even_le_ordered (n l : ℕ) (σ τ : Spin n) :
    |deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^(2*l) ≤
      |orderedOverlap n σ τ|^(2*l) := by
  have hc0 : 0 ≤ (n:ℝ)/(n+1 : ℕ) := by positivity
  have hc1 : (n:ℝ)/(n+1 : ℕ) ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < (n+1 : ℕ))).2
    exact_mod_cast Nat.le_succ n
  rw [deleted_overlap_join_eq_scaled,abs_mul,abs_of_nonneg hc0,mul_pow]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hc0 hc1) (by positivity)).trans_eq (one_mul _)

theorem native_pair_deleted_even_le_ordered (n l : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (j : ℕ)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) v q
      (fun σ=>|deletedOverlap n (joinSpin ((ClockTree.pairSpin as j σ).1,false))
        (joinSpin ((ClockTree.pairSpin as j σ).2,false))|^(2*l)) x ≤
    (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) v q
      (fun σ=>|orderedOverlap n (ClockTree.pairSpin as j σ).1
        (ClockTree.pairSpin as j σ).2|^(2*l)) x := by
  have hw:=(ClockTree.pairClock (S:=Spin n) as j).disorderWeight_probability
    (restWeight_pos n) (restFeature n) ho v q x
  exact Finset.sum_le_sum fun σ _=>mul_le_mul_of_nonneg_left
    (deleted_overlap_even_le_ordered n l _ _) (hw.1 σ)

theorem eventually_actual_minimum_i_exterior_fourth_bound
    (Bclock Temp : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Ei : ClockTree (Spin n) (mid++tail)) (e : Ei.Slot),
          (∫z,(Ei.fork Ei).expect (restWeight n) (restFeature n)
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun η=>|deletedOverlap n (joinSpin (Ei.atSlot η.1 e,false))
              (joinSpin (Ei.atSlot η.2 e,false))|^4) (exteriorForestIRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(M.xs+partitionPoint 0 as pre.length))^4 := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_bare_rest_even_bound
    (D:=D) 2 (by norm_num) Bclock Temp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HR] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut Ei e
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  rw [native_common_i_pair_marginal n pre mid tail ho Ei e 0 q
    (fun σ τ=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^4) 0]
  apply (native_pair_deleted_even_le_ordered n 2 ho pre.length 0 _ 0).trans
  have hj : pre.length ≤ (finiteCutMasses us k).length := by
    rw [←hcut]
    simp only [List.length_append]
    omega
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) :
      (ClockTree.pairClock bs pre.length).disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>|orderedOverlap n (ClockTree.pairSpin bs pre.length σ).1
          (ClockTree.pairSpin bs pre.length σ).2|^4) 0 ≤
        (C*(M.xs+partitionPoint 0 (finiteCutMasses us k) pre.length))^4 := by
    subst bs
    simpa only [q,show 2*2=4 by norm_num] using hk pre.length hj
  exact HK (pre++(mid++tail)) hcut

end OAI.SKFluctuations.Cavity
