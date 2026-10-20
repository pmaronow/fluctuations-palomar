module

public import PhysicalWeightedContactBudget
public import ComparisonCapContactVarianceLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped BigOperators NNReal ENNReal Topology
set_option maxHeartbeats 1800000

def finiteRadiusWeight {ι : Type*} [Fintype ι]
    (left right weight : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i, (Ioc (left i) (right i)).indicator (fun _ => weight i) r

theorem finiteRadiusWeight_measurable {ι : Type*} [Fintype ι]
    (left right weight : ι → ℝ) : Measurable (finiteRadiusWeight left right weight) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator measurableSet_Ioc

theorem finiteRadiusWeight_nonneg {ι : Type*} [Fintype ι]
    (left right weight : ι → ℝ) (hw : ∀i, 0 ≤ weight i) (r : ℝ) :
    0 ≤ finiteRadiusWeight left right weight r := by
  exact Finset.sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => hw i) r)

theorem finiteRadiusWeight_le_sum {ι : Type*} [Fintype ι]
    (left right weight : ι → ℝ) (hw : ∀i, 0 ≤ weight i) (r : ℝ) :
    finiteRadiusWeight left right weight r ≤ ∑ i, weight i := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hr : r ∈ Ioc (left i) (right i)
  · simp [hr]
  · simp [hr, hw i]

theorem inverse_cell_weight_integral {A : ℝ≥0} (f R : ℝ → ℝ)
    (hf : LipschitzOnWith A f (Icc (0:ℝ) 1)) (hR : Monotone R)
    (hRb : ∀u∈Icc (0:ℝ) 1, R u∈Icc (0:ℝ) 1)
    (hinv : ∀u∈Icc (0:ℝ) 1, f (R u)=u)
    {u v : ℝ} (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u ≤ v)
    (weight : ℝ) :
    Integrable (fun r => deriv f r*(Ioc (R u) (R v)).indicator (fun _ => weight) r) ∧
    (∫r, deriv f r*(Ioc (R u) (R v)).indicator (fun _ => weight) r) = (v-u)*weight := by
  have hRuv := hR huv
  have hsub : uIcc (R u) (R v) ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hRuv]
    exact Icc_subset_Icc (hRb u hu).1 (hRb v hv).2
  have hac : AbsolutelyContinuousOnInterval f (R u) (R v) :=
    (hf.mono hsub).absolutelyContinuousOnInterval
  have hI : IntegrableOn (deriv f) (Ioc (R u) (R v)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hRuv).mp hac.intervalIntegrable_deriv
  have heq : (fun r=>deriv f r*(Ioc (R u) (R v)).indicator (fun _=>weight) r)=
      (Ioc (R u) (R v)).indicator (fun r=>deriv f r*weight) := by
    funext r
    by_cases hr:r∈Ioc (R u) (R v) <;> simp [hr]
  constructor
  · rw [heq]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (hI.mul_const weight)
  · rw [heq, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hRuv,
      intervalIntegral.integral_mul_const, hac.integral_deriv_eq_sub, hinv v hv, hinv u hu]

theorem inverse_finite_weight_integral {ι : Type*} [Fintype ι]
    {A : ℝ≥0} (f R : ℝ → ℝ)
    (hf : LipschitzOnWith A f (Icc (0:ℝ) 1)) (hR : Monotone R)
    (hRb : ∀u∈Icc (0:ℝ) 1, R u∈Icc (0:ℝ) 1)
    (hinv : ∀u∈Icc (0:ℝ) 1, f (R u)=u)
    (left right weight : ι → ℝ)
    (hl : ∀i, left i∈Icc (0:ℝ) 1) (hr : ∀i, right i∈Icc (0:ℝ) 1)
    (hlr : ∀i, left i ≤ right i) :
    Integrable (fun r => deriv f r*finiteRadiusWeight (R∘left) (R∘right) weight r) ∧
    (∫r, deriv f r*finiteRadiusWeight (R∘left) (R∘right) weight r) =
      ∑i, (right i-left i)*weight i := by
  have hi i := inverse_cell_weight_integral f R hf hR hRb hinv (hl i) (hr i) (hlr i) (weight i)
  have heq : (fun r=>deriv f r*finiteRadiusWeight (R∘left) (R∘right) weight r)=
      fun r=>∑i, deriv f r*(Ioc (R (left i)) (R (right i))).indicator (fun _=>weight i) r := by
    funext r
    simp only [finiteRadiusWeight, Function.comp_apply, Finset.mul_sum]
  rw [heq]
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hi i).1)
  · rw [integral_finsetSum _ (fun i _ => (hi i).1)]
    exact Finset.sum_congr rfl (fun i _ => (hi i).2)

theorem inverse_finite_weight_subset_integral_le {ι : Type*} [Fintype ι]
    {A : ℝ≥0} (f R : ℝ → ℝ)
    (hf : LipschitzOnWith A f (Icc (0:ℝ) 1)) (hfm : Monotone f) (hR : Monotone R)
    (hRb : ∀u∈Icc (0:ℝ) 1, R u∈Icc (0:ℝ) 1)
    (hinv : ∀u∈Icc (0:ℝ) 1, f (R u)=u)
    (left right weight : ι → ℝ)
    (hl : ∀i, left i∈Icc (0:ℝ) 1) (hr : ∀i, right i∈Icc (0:ℝ) 1)
    (hlr : ∀i, left i ≤ right i) (hw : ∀i, 0 ≤ weight i) (C : Set ℝ) :
    (∫r in C, deriv f r*finiteRadiusWeight (R∘left) (R∘right) weight r) ≤
      ∑i, (right i-left i)*weight i := by
  have hi := inverse_finite_weight_integral f R hf hR hRb hinv left right weight hl hr hlr
  exact (integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ (fun r=>mul_nonneg hfm.deriv_nonneg (finiteRadiusWeight_nonneg _ _ _ hw r)))
    hi.1).trans_eq hi.2

open WholeUnitSideKernel

def sideSquareColumn (x : ℕ → ℝ) (δ width : ℝ) (i : ℕ) : ℝ :=
  (∫t in δ..width-δ, (left 0 (x i) (x (i+1)) t)^2) +
  (∫t in δ..width-δ, (right width (x i) (x (i+1)) t)^2)

theorem sideSquareColumn_nonneg (x : ℕ → ℝ) {δ width : ℝ}
    (hwidth : 2*δ ≤ width) (i : ℕ) : 0 ≤ sideSquareColumn x δ width i := by
  exact add_nonneg
    (intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _))
    (intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _))

theorem sideSquareColumn_mass_sum_le (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hstart : x 0=0) (hend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1)) :
    (∑i : Fin K, (x (i.val+1)-x i.val)*sideSquareColumn x δ width i.val) ≤
      2*Real.log (width/δ) := by
  have hL := left_mass_square_columns_le_log x K hstart hend hδ hwidth hx
  have hR := right_mass_square_columns_le_log x K hstart hend hδ hwidth hx
  simp only [sideSquareColumn, mul_add, Finset.sum_add_distrib]
  linarith

def sideSquareRadiusWeight (R : ℝ → ℝ) (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ)
    (δ width r : ℝ) : ℝ :=
  finiteRadiusWeight (fun i : Fin K => R (v0+x i.val))
    (fun i : Fin K => R (v0+x (i.val+1)))
    (fun i : Fin K => sideSquareColumn x δ width i.val) r

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_sideSquareRadiusWeight_mass_le
    (α : inverseIntegralConstraints 0 0 k M) (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ)
    {δ width : ℝ} (hv0 : 0 ≤ v0) (hv1 : v0+width ≤ 1)
    (hstart : x 0=0) (hend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1))
    (hxb : ∀i≤K, x i∈Icc (0:ℝ) width) (C : Set ℝ) :
    (∫r in C, deriv α.val.val r*
      sideSquareRadiusWeight (comparisonSweepQuantile hc hk hkc hm hM α) v0 x K δ width r) ≤
      2*Real.log (width/δ) := by
  let lo := fun i : Fin K => v0+x i.val
  let hi := fun i : Fin K => v0+x (i.val+1)
  have hlo i : lo i∈Icc (0:ℝ) 1 := by
    have hh := hxb i.val (Nat.le_of_lt i.isLt)
    constructor <;> dsimp only [lo] <;> linarith [hh.1, hh.2]
  have hhi i : hi i∈Icc (0:ℝ) 1 := by
    have hh := hxb (i.val+1) (by omega)
    constructor <;> dsimp only [hi] <;> linarith [hh.1, hh.2]
  have ht := inverse_finite_weight_subset_integral_le α.val.val
    (comparisonSweepQuantile hc hk hkc hm hM α)
    (inverseIntegralConstraints_lipschitz hm hM α.property) α.val.property.2
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
    (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
    (fun u hu => comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu)
    lo hi (fun i : Fin K => sideSquareColumn x δ width i.val) hlo hhi
    (fun i => by dsimp only [lo, hi]; linarith [hx i])
    (fun i => sideSquareColumn_nonneg x hwidth i.val) C
  have he : (∑i : Fin K, (hi i-lo i)*sideSquareColumn x δ width i.val)=
      ∑i : Fin K, (x (i.val+1)-x i.val)*sideSquareColumn x δ width i.val := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [hi, lo]
    ring
  rw [he] at ht
  exact ht.trans (sideSquareColumn_mass_sum_le x K hstart hend hδ hwidth hx)

theorem comparisonPhysicalContactSideSquareTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hpartEnd : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))

    (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hv0 : 0 ≤ v0) (hv1 : v0+width ≤ 1)
    (hstart : x 0=0) (hxend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1))
    (hxb : ∀i≤K, x i∈Icc (0:ℝ) width)
    {ε : ℝ} (hε : 0 < ε) :
    let A := {r | r∈Ioo a z ∧ H r=0}
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᶠ j in atTop,
      (∫r in A, deriv α.val.val r*sideSquareRadiusWeight R v0 x K δ width r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
        Real.log (width/δ)+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let w := sideSquareRadiusWeight R v0 x K δ width
  let col := fun i : Fin K => sideSquareColumn x δ width i.val
  have hcol i : 0 ≤ col i := sideSquareColumn_nonneg x hwidth i.val
  have hw : Measurable w := finiteRadiusWeight_measurable _ _ _
  have hw0 r : 0 ≤ w r := finiteRadiusWeight_nonneg _ _ _ hcol r
  have hwb r : ‖w r‖ ≤ ∑i : Fin K, col i := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 r)]
    exact finiteRadiusWeight_le_sum _ _ _ hcol r
  have ht := comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    as mesh ho hpartEnd hmesh hmesh0 hlim ha haz hz Kb Kh hparent hfield
    w hw (∑i : Fin K, col i) (fun r _ _ => hwb r) (fun r _ _ => hw0 r) hε
  let A := {r | r∈Ioo a z ∧ H r=0}
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  have hmass : (∫r in A, deriv α.val.val r*w r) ≤ 2*Real.log (width/δ) :=
    comparison_sideSquareRadiusWeight_mass_le hc hk hkc hm hM α v0 x K
      hv0 hv1 hstart hxend hδ hwidth hx hxb A
  have hlogpos : 0 < Real.log N := by linarith
  have hgpos := laplaceComparisonStrength_pos d hlam z
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) hlogpos) hgpos)
  have hcoef : 0 ≤ (9*Real.log N)/F := div_nonneg (by positivity) hF.le
  have hconst : ((9*Real.log N)/F)*(2*Real.log (width/δ)) =
      (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
        Real.log (width/δ) := by
    dsimp only [F]
    field_simp [hlogpos.ne', hgpos.ne']
    <;> ring
  filter_upwards [ht] with j hj
  have hrate := mul_le_mul_of_nonneg_left hmass hcoef
  rw [hconst] at hrate
  dsimp only [F, A] at hrate
  exact hj.trans (by linarith)

end

theorem exists_constantComparison_contactSideSquareTrace
    {N δcap U L E d lam T : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hLU : L ≤ U) (hE : 0 < E) (hd : 0 < d) (hq : 2 ≤ N^δcap)
    (hNlarge : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2) (hlT : lam ≤ T)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j, MassOrdered 0 (as j)) (hpartEnd : ∀j, partitionEnd 0 (as j)=1)
    (hmesh : ∀j, PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j, 0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hv0 : 0 ≤ v0) (hv1 : v0+width ≤ 1)
    (hstart : x 0=0) (hxend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1))
    (hxb : ∀i≤K, x i∈Icc (0:ℝ) width) {ε : ℝ} (hε : 0 < ε) :
    let k := comparisonFloor N δcap U
    let M := comparisonCap N δcap U L E d
    let c := k 1
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δcap) hN hU (r₀:=0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1) =>
      comparisonFloor_lower_on (δ:=δcap) hN hU le_rfl hr
    let hm := comparisonCap_monotoneOn (δ:=δcap) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δcap) hN hU.le hL hE hd.le zero_le_one
    ∃ (α : inverseIntegralConstraints 0 0 k M) (H : ℝ → ℝ),
      (∀γ : inverseIntegralConstraints 0 0 k M,
        comparisonVariableEndpointObjective hc hk hkc hm hM (n+1)
          (fun _=>T) (fun _=>0) d lam α ≤
        comparisonVariableEndpointObjective hc hk hkc hm hM (n+1)
          (fun _=>T) (fun _=>0) d lam γ) ∧
      let R := comparisonSweepQuantile hc hk hkc hm hM α
      let g := laplaceComparisonStrength d lam
      let bf := fun u=>(T-g (R u)).toNNReal
      let hf := fun u=>((0:ℝ)+g (R u)*R u).toNNReal
      let S := orderedPathS (n+1) bf hf
      let B := orderedPathB (n+1) bf hf
      let J := inverseControlFactor 0 (fun r=>inverseControlWeight α.val.val k M r*
        comparisonCapSlope N δcap U L E d (α.val.val r))
      AbsolutelyContinuousOnInterval H 0 1 ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
        (J r*radiusComparisonGradient g α.val.val S B r) r) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→
        (H r<0→deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r→deriv α.val.val r=k r)) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
        radiusComparisonGradient g α.val.val S B r=0 ∧
        S (α.val.val r)≤r ∧
        (S (α.val.val r)-r)^2≤B (α.val.val r)-(S (α.val.val r))^2) ∧
      let A := {r | r∈Ioo a z ∧ H r=0}
      ∀ᶠ j in atTop,
        (∫r in A, deriv α.val.val r*sideSquareRadiusWeight R v0 x K δ width r
          ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
            n dphys e d lam (fun _=>T) (fun _=>0) α (as j) (ho j)) ≤
        (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
          Real.log (width/δ)+ε := by
  dsimp only
  let k := comparisonFloor N δcap U
  let M := comparisonCap N δcap U L E d
  have hc : 0 < k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hk : ContinuousOn k (Icc (0:ℝ) 1) :=
    comparisonFloor_continuousOn (δ:=δcap) hN hU le_rfl
  have hkc : ∀r∈Icc (0:ℝ) 1, k 1 ≤ k r :=
    fun r hr => comparisonFloor_lower_on (δ:=δcap) hN hU le_rfl hr
  have hm : MonotoneOn M (Icc (0:ℝ) 1) :=
    comparisonCap_monotoneOn (δ:=δcap) hN hU.le hL hE hd.le
  have hM : 0 ≤ M 1 :=
    comparisonCap_nonneg (δ:=δcap) hN hU.le hL hE hd.le zero_le_one
  have hb : MonotoneOn (fun _ : ℝ => T) (Icc (0:ℝ) 1) := fun _ _ _ _ _ => le_rfl
  have hh : MonotoneOn (fun _ : ℝ => (0:ℝ)) (Icc (0:ℝ) 1) := fun _ _ _ _ _ => le_rfl
  obtain ⟨α,H,hmin,hH,hD,hbang,hzero⟩ := exists_concrete_variableEndpoint_optimizer_potential
    hN hU hL hLU hE hd hq hlam (fun _=>T) (fun _=>0) hb hlT hh (by norm_num)
    (n+1) (by omega)
  refine ⟨α,H,hmin,hH,hD,hbang,hzero,?_⟩
  apply comparisonPhysicalContactSideSquareTrace_eventually hc hk hkc hm hM
    hNlarge hlog hd hnd hlam hld n dphys e (fun _=>T) (fun _=>0) hb hh
    (by norm_num) hlT α H hH ?_ as mesh ho hpartEnd hmesh hmesh0 hlim
    ha haz hz 0 0 (LipschitzWith.const T).lipschitzOnWith
    (LipschitzWith.const (0:ℝ)).lipschitzOnWith v0 x K hv0 hv1 hstart hxend
    hδ hwidth hx hxb hε
  filter_upwards [hzero] with r hr h01 hHr
  exact (hr h01 hHr).1

end OAI.SKFluctuations.LaplaceWindowFormalization
