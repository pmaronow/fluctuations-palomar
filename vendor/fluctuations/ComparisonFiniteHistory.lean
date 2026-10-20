module

public import PhysicalComparisonClockRegularity
public import FullMassComparisonMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

structure ComparisonHistoryTerm where
  c : ℝ
  k : ℝ→ℝ
  M : ℝ→ℝ
  hc : 0 < c
  hk : ContinuousOn k (Icc (0:ℝ) 1)
  hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r
  hm : MonotoneOn M (Icc (0:ℝ) 1)
  hM : 0 ≤ M 1
  α : inverseIntegralConstraints 0 0 k M
  d : ℝ
  lam : ℝ

def ComparisonHistoryTerm.quantile (t : ComparisonHistoryTerm) : ℝ→ℝ :=
  comparisonSweepQuantile t.hc t.hk t.hkc t.hm t.hM t.α
def ComparisonHistoryTerm.matrixReduction (t : ComparisonHistoryTerm) (u : ℝ) : ℝ :=
  laplaceComparisonStrength t.d t.lam (t.quantile u)
def ComparisonHistoryTerm.fieldAddition (t : ComparisonHistoryTerm) (u : ℝ) : ℝ :=
  laplaceComparisonStrength t.d t.lam (t.quantile u)*t.quantile u

theorem ComparisonHistoryTerm.matrixReduction_lipschitz (t : ComparisonHistoryTerm) :
    ∃K,LipschitzWith K t.matrixReduction :=
  comparisonSweepStrength_lipschitz t.hc t.hk t.hkc t.hm t.hM t.α t.d t.lam

theorem ComparisonHistoryTerm.fieldAddition_lipschitz (t : ComparisonHistoryTerm) :
    ∃K,LipschitzWith K t.fieldAddition := by
  obtain ⟨K,hK⟩ := ((laplaceComparisonStrength_contDiff t.d t.lam).mul contDiff_id).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  have htc := t.hc
  refine ⟨K*⟨1/t.c,by positivity⟩,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hh := hK.dist_le_mul _ (comparisonSweepQuantile_bounds t.hc t.hk t.hkc t.hm t.hM t.α x)
    _ (comparisonSweepQuantile_bounds t.hc t.hk t.hkc t.hm t.hM t.α y)
  have hq := (comparisonSweepQuantile_lipschitz t.hc t.hk t.hkc t.hm t.hM t.α).dist_le_mul x y
  change dist (t.quantile x) (t.quantile y) ≤ (1/t.c)*dist x y at hq
  change dist (t.fieldAddition x) (t.fieldAddition y) ≤ (K:ℝ)*dist (t.quantile x) (t.quantile y) at hh
  apply hh.trans
  change (K:ℝ)*dist _ _ ≤ (K:ℝ)*(1/t.c)*dist x y
  convert mul_le_mul_of_nonneg_left hq K.coe_nonneg using 1 <;> ring

theorem real_lipschitz_add {f g : ℝ→ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf+Kg) (fun x=>f x+g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hhf := hf.dist_le_mul x y
  have hhg := hg.dist_le_mul x y
  simp only [Real.dist_eq] at hhf hhg ⊢
  have he : f x+g x-(f y+g y)=(f x-f y)+(g x-g y) := by ring
  rw [he]
  change |(f x-f y)+(g x-g y)| ≤ ((Kf:ℝ)+(Kg:ℝ))*|x-y|
  exact (abs_add_le _ _).trans (by nlinarith)

def historyMatrixReduction : List ComparisonHistoryTerm→ℝ→ℝ
  | [],_=>0
  | t::ts,u=>t.matrixReduction u+historyMatrixReduction ts u
def historyFieldAddition : List ComparisonHistoryTerm→ℝ→ℝ
  | [],_=>0
  | t::ts,u=>t.fieldAddition u+historyFieldAddition ts u

theorem historyMatrixReduction_lipschitz (ts : List ComparisonHistoryTerm) :
    ∃K,LipschitzWith K (historyMatrixReduction ts) := by
  induction ts with
  | nil=>exact ⟨0,LipschitzWith.const 0⟩
  | cons t ts ih=>
    obtain ⟨Kt,ht⟩ := t.matrixReduction_lipschitz
    obtain ⟨Ks,hs⟩ := ih
    exact ⟨Kt+Ks,real_lipschitz_add ht hs⟩

theorem historyFieldAddition_lipschitz (ts : List ComparisonHistoryTerm) :
    ∃K,LipschitzWith K (historyFieldAddition ts) := by
  induction ts with
  | nil=>exact ⟨0,LipschitzWith.const 0⟩
  | cons t ts ih=>
    obtain ⟨Kt,ht⟩ := t.fieldAddition_lipschitz
    obtain ⟨Ks,hs⟩ := ih
    exact ⟨Kt+Ks,real_lipschitz_add ht hs⟩

def historyMatrixClock (T ε s : ℝ) (ts : List ComparisonHistoryTerm) (u : ℝ) : ℝ :=
  initialShellMatrixClock T ε s u-historyMatrixReduction ts u
def historyFieldClock (ts : List ComparisonHistoryTerm) (u : ℝ) : ℝ :=
  historyFieldAddition ts u

theorem historyMatrixClock_inverse_lipschitz
    {c : ℝ} {k M : ℝ→ℝ} (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M)
    (T ε s : ℝ) (ts : List ComparisonHistoryTerm) {a z : ℝ}
    (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hbranch : α.val.val z < s ∨ s ≤ α.val.val a) :
    ∃K,LipschitzOnWith K (fun r=>historyMatrixClock T ε s ts (α.val.val r)) (Icc a z) := by
  obtain ⟨K,hK⟩ := historyMatrixReduction_lipschitz ts
  have hα := inverseIntegralConstraints_lipschitz hm hM α.property
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hz
  refine ⟨K*Real.toNNReal (M 1),LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxbranch : initialShellMatrixClock T ε s (α.val.val x)=
      initialShellMatrixClock T ε s (α.val.val y) := by
    rcases hbranch with hlow|hhigh
    · have hxlow := (α.val.property.2 hx.2).trans_lt hlow
      have hylow := (α.val.property.2 hy.2).trans_lt hlow
      simp only [initialShellMatrixClock,if_pos hxlow,if_pos hylow]
    · have hxhigh := hhigh.trans (α.val.property.2 hx.1)
      have hyhigh := hhigh.trans (α.val.property.2 hy.1)
      simp only [initialShellMatrixClock,if_neg (not_lt.mpr hxhigh),if_neg (not_lt.mpr hyhigh)]
  have hbnd := hK.dist_le_mul (α.val.val x) (α.val.val y)
  have hαb := hα.dist_le_mul x (hsub hx) y (hsub hy)
  change dist (α.val.val x) (α.val.val y) ≤ M 1*dist x y at hαb
  have hh := mul_le_mul_of_nonneg_left hαb K.coe_nonneg
  have he : dist (historyMatrixClock T ε s ts (α.val.val x))
      (historyMatrixClock T ε s ts (α.val.val y))=
      dist (historyMatrixReduction ts (α.val.val x)) (historyMatrixReduction ts (α.val.val y)) := by
    simp only [historyMatrixClock,hxbranch,Real.dist_eq]
    have hh : initialShellMatrixClock T ε s (α.val.val y)-historyMatrixReduction ts (α.val.val x)-
        (initialShellMatrixClock T ε s (α.val.val y)-historyMatrixReduction ts (α.val.val y))=
        -(historyMatrixReduction ts (α.val.val x)-historyMatrixReduction ts (α.val.val y)) := by ring
    rw [hh,abs_neg]
  rw [he]
  apply hbnd.trans
  change (K:ℝ)*dist (α.val.val x) (α.val.val y) ≤ (K:ℝ)*(Real.toNNReal (M 1):ℝ)*dist x y
  rw [Real.coe_toNNReal _ hM]
  convert hh using 1 <;> ring

theorem historyFieldClock_inverse_lipschitz
    {c : ℝ} {k M : ℝ→ℝ} (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (ts : List ComparisonHistoryTerm)
    {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) :
    ∃K,LipschitzOnWith K (fun r=>historyFieldClock ts (α.val.val r)) (Icc a z) := by
  obtain ⟨K,hK⟩ := historyFieldAddition_lipschitz ts
  have hα := inverseIntegralConstraints_lipschitz hm hM α.property
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hz
  refine ⟨K*Real.toNNReal (M 1),LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hbnd := hK.dist_le_mul (α.val.val x) (α.val.val y)
  have hαb := hα.dist_le_mul x (hsub hx) y (hsub hy)
  change dist (α.val.val x) (α.val.val y) ≤ M 1*dist x y at hαb
  have hh := mul_le_mul_of_nonneg_left hαb K.coe_nonneg
  apply hbnd.trans
  change (K:ℝ)*dist (α.val.val x) (α.val.val y) ≤ (K:ℝ)*(Real.toNNReal (M 1):ℝ)*dist x y
  rw [Real.coe_toNNReal _ hM]
  convert hh using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
