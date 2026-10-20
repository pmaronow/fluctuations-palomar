module

public import ComparisonSignedCavityActualAnchorRaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeStarSuffixClock (n : ℕ) (pre mid : List PositiveMass)
    (q : ℕ → RestCoordinate n → ℝ) : ℕ → RestCoordinate n → ℝ≥0 :=
  fun j => cumulativeIncrements (q 0) (fun k => q (k+1)) (pre.length+(mid.length+j))

def nativeTwinStarExteriorFourth (n : ℕ) (pre mid tail : List PositiveMass)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) : ℝ :=
  physicalOverlapMoment n 2
    (clockSteps tail (fun j => restFiniteVariance n (nativeStarSuffixClock n pre mid q j)))
    (nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)
    (fun z => restFiniteState n (twinPrefixBRoot z))
    ((restFiniteState_measurable n).comp twinPrefixBRoot_measurable) 0

def nativeCommonStarExteriorFourth (n : ℕ) (pre mid tail : List PositiveMass)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) : ℝ :=
  physicalOverlapMoment n 2
    (clockSteps tail (fun j => restFiniteVariance n (nativeStarSuffixClock n pre mid q j)))
    (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)
    (fun z => restFiniteState n (exteriorForestStarRoot z))
    ((restFiniteState_measurable n).comp departedAnchorExteriorRoot_measurable) 0

theorem native_twin_star_exterior_fourth_eq_original_pair (n : ℕ) (hn : 0 < n)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    nativeTwinStarExteriorFourth n pre mid tail v q x =
    (ClockTree.pairClock (pre ++ (mid ++ tail)) (pre.length+mid.length)).disorderExpect
      (restWeight n) (restFeature n) v q
      (fun σ => |orderedOverlap n (ClockTree.pairSpin _ _ σ).1
        (ClockTree.pairSpin _ _ σ).2|^4) x := by
  let := nativeTwinPrefixDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  unfold nativeTwinStarExteriorFourth
  rw [physical_exterior_fourth_eq_native_original_root n hn (ClockTree.single tail)
    ho.suffix_end.suffix_end (ClockTree.singleSlot tail) _ _ _ twinPrefixBRoot_measurable]
  exact native_twin_star_pair_marginal n pre mid tail ho (ClockTree.single tail)
    (ClockTree.singleSlot tail) v q (fun σ τ => |orderedOverlap n σ τ|^4) x

theorem native_common_star_exterior_fourth_eq_original_pair (n : ℕ) (hn : 0 < n)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    nativeCommonStarExteriorFourth n pre mid tail v q x =
    (ClockTree.pairClock (pre ++ (mid ++ tail)) (pre.length+mid.length)).disorderExpect
      (restWeight n) (restFeature n) v q
      (fun σ => |orderedOverlap n (ClockTree.pairSpin _ _ σ).1
        (ClockTree.pairSpin _ _ σ).2|^4) x := by
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  unfold nativeCommonStarExteriorFourth
  rw [physical_exterior_fourth_eq_native_original_root n hn (ClockTree.single tail)
    ho.suffix_end.suffix_end (ClockTree.singleSlot tail) (nativeStarSuffixClock n pre mid q) _
    (exteriorForestStarRoot (ι:=RestCoordinate n) (P:=RestCoordinate n → ℝ))
    (show Measurable (exteriorForestStarRoot (ι:=RestCoordinate n) (P:=RestCoordinate n → ℝ))
      from departedAnchorExteriorRoot_measurable)]
  exact native_common_star_pair_marginal n pre mid tail ho (ClockTree.single tail)
    (ClockTree.singleSlot tail) v q (fun σ τ => |orderedOverlap n σ τ|^4) x

theorem native_twin_star_fresh_hweight_eighth_eq_one (n : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    (∫ z,(ClockTree.single (S:=Spin n) tail).expect (restWeight n) (restFeature n)
      (nativeStarSuffixClock n pre mid q) (fun _ => |(1:ℝ)|^8) (twinPrefixBRoot z)
      ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)=1 := by
  let := nativeTwinPrefixDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  exact native_fresh_anchor_hweight_eighth_eq_one n (ClockTree.single tail)
    ho.suffix_end.suffix_end _ _ _

theorem native_common_star_fresh_hweight_eighth_eq_one (n : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    (∫ z,(ClockTree.single (S:=Spin n) tail).expect (restWeight n) (restFeature n)
      (nativeStarSuffixClock n pre mid q) (fun _ => |(1:ℝ)|^8) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)=1 := by
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  exact native_fresh_anchor_hweight_eighth_eq_one n (ClockTree.single tail)
    ho.suffix_end.suffix_end _ _ _

theorem eventually_actual_minimum_bare_star_exterior_fourth_bound
    (Bclock Temp Cmass : ℝ) (hCmass : 0 ≤ Cmass) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
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
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_bare_rest_fourth_bound Bclock Temp hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨Cr*(1+Cmass),by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
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
