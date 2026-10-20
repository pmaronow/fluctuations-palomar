module

public import RadiusCellEnergyDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def finiteRadiusCellDensity (n : ℕ) (x C : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (Ioc (x i) (x (i+1))).indicator (fun _ => C i) r

def finiteInnerRadiusCellDensity (n : ℕ) (x C : ℕ → ℝ) (p q r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    if p ≤ x i ∧ x (i+1) ≤ q then (Ioc (x i) (x (i+1))).indicator (fun _ => C i) r else 0

theorem finiteRadiusCellDensity_nonneg {n : ℕ} {x C : ℕ → ℝ}
    (hC : ∀ i < n, 0 ≤ C i) (r : ℝ) : 0 ≤ finiteRadiusCellDensity n x C r := by
  apply Finset.sum_nonneg
  intro i hi
  exact indicator_nonneg (fun _ _ => hC i (Finset.mem_range.mp hi)) r

theorem radiusCellEnergyDensity_eq_finite_sum
    (R : ℝ → ℝ) (u : ℝ) (as : List PositiveMass) (C : ℕ → ℝ) (r : ℝ) :
    radiusCellEnergyDensity R u as C r = finiteRadiusCellDensity as.length
      (fun j => R (partitionPoint u as j)) C r := by
  induction as generalizing u C with
  | nil => simp [radiusCellEnergyDensity,finiteRadiusCellDensity]
  | cons a as ih =>
    rw [radiusCellEnergyDensity,ih]
    simp only [finiteRadiusCellDensity,List.length_cons,Finset.sum_range_succ',
      partitionPoint,partitionValues]
    simp only [partitionValues_zero,id_eq,add_comm]

theorem finiteInnerRadiusCellDensity_nonneg {n : ℕ} {x C : ℕ → ℝ}
    (hC : ∀ i < n, 0 ≤ C i) (p q r : ℝ) :
    0 ≤ finiteInnerRadiusCellDensity n x C p q r := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact indicator_nonneg (fun _ _ => hC i (Finset.mem_range.mp hi)) r
  · exact le_rfl

theorem finite_cell_boundary_strips {n : ℕ} {x C : ℕ → ℝ} {p q δ : ℝ}
    (hC : ∀ i < n, 0 ≤ C i)
    (hwidth : ∀ i < n, x (i+1)-x i ≤ δ)
    (hbound : ∀ r, finiteRadiusCellDensity n x C r ≤ 1)
    (r : ℝ) (hr : r ∈ Ioc p q) :
    finiteRadiusCellDensity n x C r ≤ finiteInnerRadiusCellDensity n x C p q r +
      (Ioc p (p+δ)).indicator (fun _ => (1:ℝ)) r +
      (Ioc (q-δ) q).indicator (fun _ => (1:ℝ)) r := by
  have hi := finiteInnerRadiusCellDensity_nonneg (x := x) hC p q r
  have hl : 0 ≤ (Ioc p (p+δ)).indicator (fun _ => (1:ℝ)) r :=
    indicator_nonneg (fun _ _ => zero_le_one) r
  have hz : 0 ≤ (Ioc (q-δ) q).indicator (fun _ => (1:ℝ)) r :=
    indicator_nonneg (fun _ _ => zero_le_one) r
  by_cases hleft : r ∈ Ioc p (p+δ)
  · rw [indicator_of_mem hleft]
    linarith [hbound r]
  by_cases hright : r ∈ Ioc (q-δ) q
  · rw [indicator_of_mem hright]
    linarith [hbound r]
  have hrl : p+δ < r := lt_of_not_ge (fun hh => hleft ⟨hr.1,hh⟩)
  have hrq : r ≤ q-δ := le_of_not_gt (fun hh => hright ⟨hh,hr.2⟩)
  have heq : finiteRadiusCellDensity n x C r = finiteInnerRadiusCellDensity n x C p q r := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hri : r ∈ Ioc (x i) (x (i+1))
    · have hw := hwidth i (Finset.mem_range.mp hi)
      have hp : p ≤ x i := by linarith [hri.2]
      have hq : x (i+1) ≤ q := by linarith [hri.1]
      rw [if_pos ⟨hp,hq⟩]
    · rw [indicator_of_notMem hri]
      split_ifs <;> simp only [indicator_of_notMem hri]
  rw [heq,indicator_of_notMem hleft,indicator_of_notMem hright,add_zero,add_zero]

private def clipRadiusOverlap (lo hi y : ℝ) : ℝ := max lo (min hi y)

private theorem clipRadiusOverlap_bounds {lo hi : ℝ} (hle : lo ≤ hi) (y : ℝ) :
    lo ≤ clipRadiusOverlap lo hi y ∧ clipRadiusOverlap lo hi y ≤ hi :=
  ⟨le_max_left _ _,max_le hle (min_le_left _ _)⟩

private theorem clipRadiusOverlap_mono (lo hi : ℝ) : Monotone (clipRadiusOverlap lo hi) := by
  intro u v huv
  unfold clipRadiusOverlap
  gcongr

private theorem clipRadiusOverlap_eq {lo hi y : ℝ} (hy : y ∈ Icc lo hi) :
    clipRadiusOverlap lo hi y=y := by
  rw [clipRadiusOverlap,min_eq_right hy.2,max_eq_right hy.1]

private theorem sum_radius_increments (n : ℕ) (y : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (y (i+1)-y i))=y n-y 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih];ring

theorem finite_inner_cell_energy_le {n : ℕ} {x y C : ℕ → ℝ}
    {S : ℝ → ℝ} {p q e F : ℝ} (hx : Monotone x) (hy : Monotone y)
    (hS : Monotone S) (hpq : p ≤ q) (he : 0 ≤ e) (hF : 0 < F)
    (hnode : ∀ i ≤ n, x i ∈ Icc p q → |y i-S (x i)| ≤ e)
    (hinc : ∀ i < n, p ≤ x i → x (i+1) ≤ q →
      (x (i+1)-x i)*C i ≤ (y (i+1)-y i)/F) :
    (∑ i ∈ Finset.range n, if p ≤ x i ∧ x (i+1) ≤ q
      then (x (i+1)-x i)*C i else 0) ≤ (S q-S p+2*e)/F := by
  let lo := S p-e
  let hi := S q+e
  let z := fun i => clipRadiusOverlap lo hi (y i)
  have hlh : lo ≤ hi := by dsimp [lo,hi];linarith [hS hpq]
  have hzmono : Monotone z := (clipRadiusOverlap_mono lo hi).comp hy
  have hlocal (i : ℕ) (hin : i ≤ n) (hxi : x i ∈ Icc p q) : z i=y i := by
    apply clipRadiusOverlap_eq
    have hno := abs_le.mp (hnode i hin hxi)
    dsimp [lo,hi]
    constructor <;> linarith [hS hxi.1,hS hxi.2]
  have hsum : (∑ i ∈ Finset.range n, if p ≤ x i ∧ x (i+1) ≤ q
      then (x (i+1)-x i)*C i else 0) ≤ ∑ i ∈ Finset.range n, (z (i+1)-z i)/F := by
    apply Finset.sum_le_sum
    intro i hiN
    have hin : i < n := Finset.mem_range.mp hiN
    split_ifs with hw
    · have hxi : x i ∈ Icc p q := ⟨hw.1,(hx (Nat.le_succ i)).trans hw.2⟩
      have hxj : x (i+1) ∈ Icc p q := ⟨hw.1.trans (hx (Nat.le_succ i)),hw.2⟩
      rw [hlocal i (by omega) hxi,hlocal (i+1) (by omega) hxj]
      exact hinc i hin hw.1 hw.2
    · exact div_nonneg (sub_nonneg.mpr (hzmono (Nat.le_succ i))) hF.le
  rw [← Finset.sum_div, sum_radius_increments] at hsum
  apply hsum.trans
  apply div_le_div_of_nonneg_right _ hF.le
  have hzn := clipRadiusOverlap_bounds hlh (y n)
  have hz0 := clipRadiusOverlap_bounds hlh (y 0)
  dsimp only [z,lo,hi] at hzn hz0 ⊢
  linarith

private theorem cell_indicator_integrable (a b C : ℝ) :
    Integrable ((Ioc a b).indicator (fun _ : ℝ => C)) :=
  (integrableOn_const (by simp : volume (Ioc a b) ≠ ⊤)).integrable_indicator measurableSet_Ioc

theorem finiteRadiusCellDensity_integrable (n : ℕ) (x C : ℕ → ℝ) :
    Integrable (finiteRadiusCellDensity n x C) :=
  integrable_finsetSum _ (fun i _ => cell_indicator_integrable _ _ _)

theorem finiteInnerRadiusCellDensity_integrable (n : ℕ) (x C : ℕ → ℝ) (p q : ℝ) :
    Integrable (finiteInnerRadiusCellDensity n x C p q) := by
  apply integrable_finsetSum
  intro i _
  by_cases hi : p ≤ x i ∧ x (i+1) ≤ q
  · simp only [hi,ite_true]
    exact cell_indicator_integrable _ _ _
  · simp only [hi,ite_false]
    exact integrable_zero _ _ _

theorem finiteInnerRadiusCellDensity_integral {n : ℕ} {x C : ℕ → ℝ}
    (hx : Monotone x) (p q : ℝ) :
    (∫ r, finiteInnerRadiusCellDensity n x C p q r) =
      ∑ i ∈ Finset.range n, if p ≤ x i ∧ x (i+1) ≤ q
        then (x (i+1)-x i)*C i else 0 := by
  unfold finiteInnerRadiusCellDensity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p ≤ x i ∧ x (i+1) ≤ q
    · simp only [if_pos hi]
      rw [integral_indicator_const _ measurableSet_Ioc,
        Real.volume_real_Ioc_of_le (hx (Nat.le_succ i))]
      simp only [smul_eq_mul]
    · simp only [if_neg hi,integral_zero]
  · intro i _
    by_cases hi : p ≤ x i ∧ x (i+1) ≤ q
    · simp only [hi,ite_true]
      exact cell_indicator_integrable _ _ _
    · simp only [hi,ite_false]
      exact integrable_zero _ _ _

theorem finite_radius_cell_interval_energy_le {n : ℕ} {x y C : ℕ → ℝ}
    {S : ℝ → ℝ} {p q e F δ : ℝ} (hx : Monotone x) (hy : Monotone y)
    (hS : Monotone S) (hpq : p ≤ q) (he : 0 ≤ e) (hF : 0 < F) (hδ : 0 ≤ δ)
    (hC : ∀ i < n, 0 ≤ C i)
    (hwidth : ∀ i < n, x (i+1)-x i ≤ δ)
    (hbound : ∀ r, finiteRadiusCellDensity n x C r ≤ 1)
    (hnode : ∀ i ≤ n, x i ∈ Icc p q → |y i-S (x i)| ≤ e)
    (hinc : ∀ i < n, p ≤ x i → x (i+1) ≤ q →
      (x (i+1)-x i)*C i ≤ (y (i+1)-y i)/F) :
    (∫ r in Ioc p q, finiteRadiusCellDensity n x C r) ≤ (S q-S p+2*e)/F+2*δ := by
  let inner := finiteInnerRadiusCellDensity n x C p q
  let left := (Ioc p (p+δ)).indicator (fun _ : ℝ => (1:ℝ))
  let right := (Ioc (q-δ) q).indicator (fun _ : ℝ => (1:ℝ))
  have hii : Integrable inner := finiteInnerRadiusCellDensity_integrable n x C p q
  have hil : Integrable left := cell_indicator_integrable _ _ _
  have hir : Integrable right := cell_indicator_integrable _ _ _
  have hpoint : ∀ r ∈ Ioc p q, finiteRadiusCellDensity n x C r ≤ inner r+left r+right r :=
    finite_cell_boundary_strips hC hwidth hbound
  have hmain := setIntegral_mono_on (finiteRadiusCellDensity_integrable n x C).integrableOn
    ((hii.add hil).add hir).integrableOn measurableSet_Ioc hpoint
  have hiinner : (∫ r in Ioc p q, inner r) ≤ ∫ r, inner r :=
    integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (finiteInnerRadiusCellDensity_nonneg (x := x) hC p q)) hii
  have hleft : (∫ r in Ioc p q, left r) ≤ δ := by
    have hh : (∫ r in Ioc p q, left r) ≤ ∫ r, left r :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (indicator_nonneg (fun _ _ => zero_le_one))) hil
    have heq : (∫ r, left r)=δ := by
      rw [integral_indicator_const _ measurableSet_Ioc,
        Real.volume_real_Ioc_of_le (by linarith : p ≤ p+δ)]
      simp
    exact hh.trans_eq heq
  have hright : (∫ r in Ioc p q, right r) ≤ δ := by
    have hh : (∫ r in Ioc p q, right r) ≤ ∫ r, right r :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (indicator_nonneg (fun _ _ => zero_le_one))) hir
    have heq : (∫ r, right r)=δ := by
      rw [integral_indicator_const _ measurableSet_Ioc,
        Real.volume_real_Ioc_of_le (by linarith : q-δ ≤ q)]
      simp
    exact hh.trans_eq heq
  have hinner : (∫ r, inner r) ≤ (S q-S p+2*e)/F := by
    rw [finiteInnerRadiusCellDensity_integral hx]
    exact finite_inner_cell_energy_le hx hy hS hpq he hF hnode hinc
  change (∫ r in Ioc p q, finiteRadiusCellDensity n x C r) ≤
    ∫ r in Ioc p q, (inner r+left r)+right r at hmain
  rw [integral_add (f := fun r => inner r+left r) (g := right)
    (hii.add hil).integrableOn hir.integrableOn,
    integral_add (f := inner) (g := left) hii.integrableOn hil.integrableOn] at hmain
  linarith

theorem finite_radius_cell_measure_interval_le {n : ℕ} {x y C : ℕ → ℝ}
    {S : ℝ → ℝ} {p q e F δ : ℝ} (hx : Monotone x) (hy : Monotone y)
    (hS : Monotone S) (hpq : p ≤ q) (he : 0 ≤ e) (hF : 0 < F) (hδ : 0 ≤ δ)
    (hC : ∀ i < n, 0 ≤ C i)
    (hwidth : ∀ i < n, x (i+1)-x i ≤ δ)
    (hbound : ∀ r, finiteRadiusCellDensity n x C r ≤ 1)
    (hnode : ∀ i ≤ n, x i ∈ Icc p q → |y i-S (x i)| ≤ e)
    (hinc : ∀ i < n, p ≤ x i → x (i+1) ≤ q →
      (x (i+1)-x i)*C i ≤ (y (i+1)-y i)/F) :
    (volume.withDensity (fun r => ENNReal.ofReal (finiteRadiusCellDensity n x C r))) (Ioo p q) ≤
      ENNReal.ofReal ((S q-S p)/F)+ENNReal.ofReal (2*e/F+2*δ) := by
  have hh := finite_radius_cell_interval_energy_le hx hy hS hpq he hF hδ hC hwidth hbound hnode hinc
  have hmain : 0 ≤ (S q-S p)/F := div_nonneg (sub_nonneg.mpr (hS hpq)) hF.le
  have herr : 0 ≤ 2*e/F+2*δ := by positivity
  have hsplit : (S q-S p+2*e)/F+2*δ = (S q-S p)/F+(2*e/F+2*δ) := by ring
  apply (measure_mono Ioo_subset_Ioc_self).trans
  rw [withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (finiteRadiusCellDensity_integrable n x C).integrableOn
      (ae_of_all _ (finiteRadiusCellDensity_nonneg (x := x) hC))]
  rw [hsplit] at hh
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (ENNReal.ofReal_add hmain herr)

end OAI.SKFluctuations.LaplaceWindowFormalization
