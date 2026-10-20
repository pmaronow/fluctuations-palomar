module
public import SKConstants.ScalarProcessLagGrowingBudget
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def growingQueryTime (δ : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | j+1 => growingQueryTime δ j + δ*(Real.exp ((growingQueryTime δ j:ℝ)/4)).toNNReal

def growingQueryDuration (δ : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  δ*(Real.exp ((growingQueryTime δ j:ℝ)/4)).toNNReal

lemma growingQueryTime_zero (δ : ℝ≥0) : growingQueryTime δ 0=0 := rfl

lemma growingQueryTime_succ (δ : ℝ≥0) (j : ℕ) :
    growingQueryTime δ (j+1)=growingQueryTime δ j+growingQueryDuration δ j := rfl

lemma growingQueryDuration_coe (δ : ℝ≥0) (j : ℕ) :
    (growingQueryDuration δ j:ℝ)=(δ:ℝ)*Real.exp ((growingQueryTime δ j:ℝ)/4) := by
  simp [growingQueryDuration,Real.toNNReal_of_nonneg (Real.exp_pos _).le]

lemma growingQueryDuration_pos (δ : ℝ≥0) (hδ : 0<δ) (j : ℕ) :
    0<growingQueryDuration δ j := by
  rw [← NNReal.coe_pos, growingQueryDuration_coe]
  exact mul_pos (by exact_mod_cast hδ) (Real.exp_pos _)

lemma growingQueryTime_strictMono (δ : ℝ≥0) (hδ : 0<δ) : StrictMono (growingQueryTime δ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [growingQueryTime_succ]
  exact lt_add_of_pos_right _ (growingQueryDuration_pos δ hδ j)

lemma growingQueryDuration_ge_mesh (δ : ℝ≥0) (j : ℕ) : δ≤growingQueryDuration δ j := by
  apply NNReal.coe_le_coe.mp
  rw [growingQueryDuration_coe]
  have he : 1≤Real.exp ((growingQueryTime δ j:ℝ)/4) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  simpa using mul_le_mul_of_nonneg_left he δ.coe_nonneg

lemma growingQueryTime_ge_linear (δ : ℝ≥0) (j : ℕ) : (j:ℝ≥0)*δ≤growingQueryTime δ j := by
  induction j with
  | zero => simp [growingQueryTime]
  | succ j ih =>
    rw [growingQueryTime_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add ih (growingQueryDuration_ge_mesh δ j)

lemma growingQueryTime_reaches (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0) :
    ∃ j, T≤growingQueryTime δ j := by
  obtain ⟨j,hj⟩ := exists_nat_ge ((T:ℝ)/(δ:ℝ))
  have hl : T≤(j:ℝ≥0)*δ := by
    exact_mod_cast ((div_le_iff₀ (by exact_mod_cast hδ : (0:ℝ)<δ)).1 hj)
  exact ⟨j, hl.trans (growingQueryTime_ge_linear δ j)⟩

def growingQueryStop (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0) : ℕ :=
  Nat.find (growingQueryTime_reaches δ hδ T)

lemma growingQueryStop_reaches (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0) :
    T≤growingQueryTime δ (growingQueryStop δ hδ T) :=
  Nat.find_spec (growingQueryTime_reaches δ hδ T)

lemma growingQueryStop_before (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0) (j : ℕ)
    (hj : j<growingQueryStop δ hδ T) : growingQueryTime δ j<T :=
  lt_of_not_ge (Nat.find_min (growingQueryTime_reaches δ hδ T) hj)

lemma growingQueryDuration_before_le (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0) (j : ℕ)
    (hj : j<growingQueryStop δ hδ T) :
    (growingQueryDuration δ j:ℝ)≤(δ:ℝ)*Real.exp ((T:ℝ)/4) := by
  rw [growingQueryDuration_coe]
  apply mul_le_mul_of_nonneg_left _ δ.coe_nonneg
  exact Real.exp_le_exp.mpr (by exact_mod_cast (div_le_div_of_nonneg_right
    (growingQueryStop_before δ hδ T j hj).le (by norm_num : (0:ℝ)≤4)))

lemma growingQueryTime_sub (δ : ℝ≥0) (j : ℕ) :
    (growingQueryTime δ (j+1):ℝ)-(growingQueryTime δ j:ℝ)=(growingQueryDuration δ j:ℝ) := by
  rw [growingQueryTime_succ,NNReal.coe_add]
  ring

lemma growingQuery_finite_weight_budget (δ : ℝ≥0) (hδ : 0<δ) (k : ℕ)
    (hsmall : ∀ j<k, growingQueryDuration δ j≤1) :
    (∑ j ∈ Finset.range k, (growingQueryDuration δ j:ℝ)^2*
      (Real.exp (-(growingQueryTime δ j:ℝ)/4))^2)≤8*(δ:ℝ) := by
  simpa only [growingQueryTime_sub] using scalarLag_growing_weight_budget (δ:ℝ)
    (by exact_mod_cast hδ) (fun j => (growingQueryTime δ j:ℝ)) (by rfl) k
    (fun j _ => by rw [growingQueryTime_sub,growingQueryDuration_coe])
    (fun j hj => by rw [growingQueryTime_sub]; exact_mod_cast hsmall j hj)

lemma growingQuery_finite_count_bound (δ : ℝ≥0) (_hδ : 0<δ) (k : ℕ)
    (hsmall : ∀ j<k, growingQueryDuration δ j≤1) : (k:ℝ)*(δ:ℝ)≤8 := by
  have hterm (j : ℕ) (hj : j<k) :
      (δ:ℝ)≤8*(Real.exp (-(growingQueryTime δ j:ℝ)/4)-
        Real.exp (-(growingQueryTime δ (j+1):ℝ)/4)) := by
    have hd := scalarLag_exp_drop (growingQueryDuration δ j:ℝ)
      (growingQueryDuration δ j).coe_nonneg (by exact_mod_cast hsmall j hj)
    have hm := mul_le_mul_of_nonneg_left hd (Real.exp_pos (-(growingQueryTime δ j:ℝ)/4)).le
    have hmax : (growingQueryDuration δ j:ℝ)*Real.exp (-(growingQueryTime δ j:ℝ)/4)=(δ:ℝ) := by
      rw [growingQueryDuration_coe]
      exact scalarLag_growing_weight_max _ _
    have hexp : Real.exp (-(growingQueryTime δ j:ℝ)/4)*Real.exp (-(growingQueryDuration δ j:ℝ)/4)=
        Real.exp (-(growingQueryTime δ (j+1):ℝ)/4) := by
      rw [growingQueryTime_succ,NNReal.coe_add,← Real.exp_add]
      congr 1
      ring
    calc
      _ = Real.exp (-(growingQueryTime δ j:ℝ)/4)*(growingQueryDuration δ j:ℝ) := by rw [mul_comm,hmax]
      _ ≤ _ := hm
      _ = _ := by rw [← hexp]; ring
  calc
    _ = ∑ j ∈ Finset.range k, (δ:ℝ) := by simp
    _ ≤ ∑ j ∈ Finset.range k, 8*(Real.exp (-(growingQueryTime δ j:ℝ)/4)-
        Real.exp (-(growingQueryTime δ (j+1):ℝ)/4)) :=
      Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
    _ = 8*(1-Real.exp (-(growingQueryTime δ k:ℝ)/4)) := by
      rw [← Finset.mul_sum,Finset.sum_range_sub']
      simp [growingQueryTime_zero]
    _ ≤ 8 := by have hp := Real.exp_pos (-(growingQueryTime δ k:ℝ)/4); linarith

lemma growingQueryStop_small (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0)
    (hscale : (δ:ℝ)*Real.exp ((T:ℝ)/4)≤1) :
    ∀ j<growingQueryStop δ hδ T, growingQueryDuration δ j≤1 := by
  intro j hj
  exact_mod_cast (growingQueryDuration_before_le δ hδ T j hj).trans hscale

lemma growingQueryStop_count_bound (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0)
    (hscale : (δ:ℝ)*Real.exp ((T:ℝ)/4)≤1) :
    (growingQueryStop δ hδ T:ℝ)≤8/(δ:ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hδ : (0:ℝ)<δ)).2
  exact growingQuery_finite_count_bound δ hδ _ (growingQueryStop_small δ hδ T hscale)

lemma growingQueryStop_overshoot (δ : ℝ≥0) (hδ : 0<δ) (T : ℝ≥0) :
    (growingQueryTime δ (growingQueryStop δ hδ T):ℝ)≤(T:ℝ)+(δ:ℝ)*Real.exp ((T:ℝ)/4) := by
  cases hk : growingQueryStop δ hδ T with
  | zero => simp [growingQueryTime_zero]; positivity
  | succ j =>
    have hj : j<growingQueryStop δ hδ T := by omega
    have hb : (growingQueryTime δ j:ℝ)<(T:ℝ) := by exact_mod_cast growingQueryStop_before δ hδ T j hj
    have hd := growingQueryDuration_before_le δ hδ T j hj
    rw [growingQueryTime_succ,NNReal.coe_add]
    linarith


end SKConstants
