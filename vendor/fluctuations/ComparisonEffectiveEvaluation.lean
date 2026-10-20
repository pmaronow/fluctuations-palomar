module

public import ComparisonActualNoiseAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set Hierarchy
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def evaluationDensity {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (i : I) (t : ℝ) : ℝ :=
  (Ico (x (unit i)) (x ((unit i).val+1))).indicator
    (fun _=>mass i/(x ((unit i).val+1)-x (unit i))) t

theorem evaluationDensity_nonneg {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ)
    (hmass : ∀i,0 ≤ mass i) (hx : ∀u:Fin K,x u < x (u.val+1)) (i : I) (t : ℝ) :
    0 ≤ evaluationDensity mass unit x i t := by
  by_cases ht:t∈Ico (x (unit i)) (x ((unit i).val+1))
  · simp only [evaluationDensity,indicator_of_mem ht]
    exact div_nonneg (hmass i) (sub_pos.mpr (hx _)).le
  · simp only [evaluationDensity,indicator_of_notMem ht]; exact le_rfl

theorem evaluationDensity_sum_eq_one {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {a b t : ℝ}
    (hstart : x 0=a) (hend : x K=b)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u)
    (ht : t∈Ico a b) : (∑i,evaluationDensity mass unit x i t)=1 := by
  have he i : evaluationDensity mass unit x i t=mass i*
      ((Ico (x (unit i)) (x ((unit i).val+1))).indicator (fun _ : ℝ=>(1:ℝ)) t /
        (x ((unit i).val+1)-x (unit i))) := by
    by_cases hti:t∈Ico (x (unit i)) (x ((unit i).val+1)) <;> simp [evaluationDensity,hti,div_eq_mul_inv]
  simp_rw [he]
  rw [sum_grouped_by_unit mass unit (fun u=>
    (Ico (x u) (x (u.val+1))).indicator (fun _ : ℝ=>(1:ℝ)) t /
      (x (u.val+1)-x u))]
  have hu u : unitTotalMass mass unit u*
      ((Ico (x u) (x (u.val+1))).indicator (fun _ : ℝ=>(1:ℝ)) t /
        (x (u.val+1)-x u))=(Ico (x u) (x (u.val+1))).indicator (fun _ : ℝ=>(1:ℝ)) t := by
    rw [hmass]
    field_simp [(sub_pos.mpr (hx u)).ne']
  simp_rw [hu]
  rw [Fin.sum_univ_eq_sum_range
    (fun u=>(Ico (x u) (x (u+1))).indicator (fun _ : ℝ=>(1:ℝ)) t)]
  rw [sum_unit_indicators x (fun u hu=>(hx ⟨u,by omega⟩).le),hstart,hend]
  exact indicator_of_mem ht _

theorem evaluationDensity_intervalIntegrable {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (i : I) (p q : ℝ) :
    IntervalIntegrable (evaluationDensity mass unit x i) volume p q :=
  intervalIntegrable_indicator_Ico intervalIntegrable_const

theorem evaluationDensity_left_integral_eq_fineCoupling {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (a p q : ℝ)
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u) (i j : I) :
    (∫t in p..q,evaluationDensity mass unit x i t*
      (mass j*left a (x (unit j)) (x ((unit j).val+1)) t))=
      fineCoupling mass unit (fun u v=>coarseLeft x a p q u v) i j := by
  have he t : evaluationDensity mass unit x i t*
      (mass j*left a (x (unit j)) (x ((unit j).val+1)) t)=
      (mass i/(x ((unit i).val+1)-x (unit i))*mass j)*
        (Ico (x (unit i)) (x ((unit i).val+1))).indicator
          (left a (x (unit j)) (x ((unit j).val+1))) t := by
    by_cases ht:t∈Ico (x (unit i)) (x ((unit i).val+1))
    · simp only [evaluationDensity,indicator_of_mem ht]; ring
    · simp only [evaluationDensity,indicator_of_notMem ht,mul_zero,zero_mul]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  unfold fineCoupling coarseLeft
  rw [hmass]

theorem evaluationDensity_right_integral_eq_fineCoupling {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (b p q : ℝ)
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u) (i j : I) :
    (∫t in p..q,evaluationDensity mass unit x i t*
      (mass j*right b (x (unit j)) (x ((unit j).val+1)) t))=
      fineCoupling mass unit (fun u v=>coarseRight x b p q u v) i j := by
  have he t : evaluationDensity mass unit x i t*
      (mass j*right b (x (unit j)) (x ((unit j).val+1)) t)=
      (mass i/(x ((unit i).val+1)-x (unit i))*mass j)*
        (Ico (x (unit i)) (x ((unit i).val+1))).indicator
          (right b (x (unit j)) (x ((unit j).val+1))) t := by
    by_cases ht:t∈Ico (x (unit i)) (x ((unit i).val+1))
    · simp only [evaluationDensity,indicator_of_mem ht]; ring
    · simp only [evaluationDensity,indicator_of_notMem ht,mul_zero,zero_mul]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  unfold fineCoupling coarseRight
  rw [hmass]

theorem evaluationDensity_integral_le_mass {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {p q : ℝ}
    (hmass : ∀i,0 ≤ mass i) (hx : ∀u:Fin K,x u < x (u.val+1))
    (hpq : p ≤ q) (i : I) :
    (∫t in p..q,evaluationDensity mass unit x i t) ≤ mass i := by
  have he t : evaluationDensity mass unit x i t=
      (mass i/(x ((unit i).val+1)-x (unit i)))*
        (Ico (x (unit i)) (x ((unit i).val+1))).indicator (fun _ : ℝ=>(1:ℝ)) t := by
    by_cases ht:t∈Ico (x (unit i)) (x ((unit i).val+1)) <;> simp [evaluationDensity,ht]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hc := mul_le_mul_of_nonneg_left (unit_indicator_integral_le hpq (hx (unit i)).le)
    (div_nonneg (hmass i) (sub_pos.mpr (hx (unit i))).le)
  exact hc.trans_eq (div_mul_cancel₀ _ (sub_pos.mpr (hx _)).ne')

end OAI.SKFluctuations.WholeUnitSideKernel
