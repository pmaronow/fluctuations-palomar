module

public import ComparisonSignedCavityActualAnchorPrimitives
public import ComparisonSignedCavityInheritedRestRawMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_fresh_star_exterior_fourth_bound
    (Bclock Temp Cf Cmass : ℝ) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(pre mid tail : List PositiveMass),pre ++ (mid ++ tail)=as →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          nativeTwinStarExteriorFourth n pre mid tail 0 q 0 ≤ (C*W)^4 ∧
          nativeCommonStarExteriorFourth n pre mid tail 0 q 0 ≤ (C*W)^4 := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_inherited_rest_even_bound 2 (by norm_num) Bclock Temp Cf hCf hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨Cr*(1+Cmass),by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut W hW hmass
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre ++ (mid ++ tail)) := hcut.symm ▸ ho
  have hj : pre.length+mid.length ≤ as.length := by
    change pre.length+mid.length ≤ (finiteCutMasses us k).length
    rw [←hcut]
    simp
  have Hraw:=hk (pre.length+mid.length) hj
  norm_num only [show 2*2=4 by norm_num] at Hraw
  have hsize : M.xs+partitionPoint 0 as (pre.length+mid.length) ≤ (1+Cmass)*W := by
    linarith
  have hbase : 0 ≤ Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length)) :=
    mul_nonneg hCr.le (add_nonneg M.hxs.le (partitionPoint_mem as ho _).1)
  have HB := Hraw.trans (pow_le_pow_left₀ hbase
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsize hCr.le) 4)
  rw [native_twin_star_exterior_fourth_eq_original_pair n hn0 pre mid tail hop,
    native_common_star_exterior_fourth_eq_original_pair n hn0 pre mid tail hop,hcut]
  constructor <;> simpa only [mul_assoc] using HB

end OAI.SKFluctuations.Cavity
