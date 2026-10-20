module

public import ComparisonEvaluationEdges

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set Hierarchy
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem intervalIntegrable_univ_sum {I : Type*} [Fintype I]
    (F : I → ℝ → ℝ) {p q : ℝ} (hF : ∀i,IntervalIntegrable (F i) volume p q) :
    IntervalIntegrable (fun t=>∑i,F i t) volume p q := by
  have h := IntervalIntegrable.sum Finset.univ (fun i _=>hF i)
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

theorem evaluationDensity_left_product_intervalIntegrable {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {a δ p q : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q)
    (hx : ∀u:Fin K,x u < x (u.val+1)) (i j : I) :
    IntervalIntegrable (fun t=>evaluationDensity mass unit x i t*
      (mass j*left a (x (unit j)) (x ((unit j).val+1)) t)) volume p q := by
  have he : (fun t=>evaluationDensity mass unit x i t*
      (mass j*left a (x (unit j)) (x ((unit j).val+1)) t))=
      (Ico (x (unit i)) (x ((unit i).val+1))).indicator
        (fun t=>(mass i/(x ((unit i).val+1)-x (unit i))*mass j)*
          left a (x (unit j)) (x ((unit j).val+1)) t) := by
    funext t
    by_cases ht:t∈Ico (x (unit i)) (x ((unit i).val+1))
    · simp only [evaluationDensity,indicator_of_mem ht]; ring
    · simp only [evaluationDensity,indicator_of_notMem ht,zero_mul]
  rw [he]
  exact intervalIntegrable_indicator_Ico
    ((left_middle_intervalIntegrable (b:=q) hδ hp hpq (hx (unit j))).const_mul _)

theorem evaluationDensity_right_product_intervalIntegrable {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {b δ p q : ℝ}
    (hδ : 0 < δ) (hq : q ≤ b-δ) (hpq : p ≤ q)
    (hx : ∀u:Fin K,x u < x (u.val+1)) (i j : I) :
    IntervalIntegrable (fun t=>evaluationDensity mass unit x i t*
      (mass j*right b (x (unit j)) (x ((unit j).val+1)) t)) volume p q := by
  have he : (fun t=>evaluationDensity mass unit x i t*
      (mass j*right b (x (unit j)) (x ((unit j).val+1)) t))=
      (Ico (x (unit i)) (x ((unit i).val+1))).indicator
        (fun t=>(mass i/(x ((unit i).val+1)-x (unit i))*mass j)*
          right b (x (unit j)) (x ((unit j).val+1)) t) := by
    funext t
    by_cases ht:t∈Ico (x (unit i)) (x ((unit i).val+1))
    · simp only [evaluationDensity,indicator_of_mem ht]; ring
    · simp only [evaluationDensity,indicator_of_notMem ht,zero_mul]
  rw [he]
  exact intervalIntegrable_indicator_Ico
    ((right_middle_intervalIntegrable (a:=p) hδ hq hpq (hx (unit j))).const_mul _)

theorem evaluation_left_array_intervalIntegrable {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (A : I → I → ℝ) {a δ p q : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    IntervalIntegrable (fun t=>∑i,evaluationDensity mass unit x i t*
      (∑j,(mass j*left a (x (unit j)) (x ((unit j).val+1)) t)*A i j)) volume p q := by
  simp only [Finset.mul_sum,← mul_assoc]
  apply intervalIntegrable_univ_sum
  intro i
  apply intervalIntegrable_univ_sum
  intro j
  simpa only [mul_assoc] using (evaluationDensity_left_product_intervalIntegrable mass unit x hδ hp hpq hx i j).mul_const (A i j)

theorem evaluation_right_array_intervalIntegrable {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (A : I → I → ℝ) {b δ p q : ℝ}
    (hδ : 0 < δ) (hq : q ≤ b-δ) (hpq : p ≤ q)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    IntervalIntegrable (fun t=>∑i,evaluationDensity mass unit x i t*
      (∑j,(mass j*right b (x (unit j)) (x ((unit j).val+1)) t)*A i j)) volume p q := by
  simp only [Finset.mul_sum,← mul_assoc]
  apply intervalIntegrable_univ_sum
  intro i
  apply intervalIntegrable_univ_sum
  intro j
  simpa only [mul_assoc] using (evaluationDensity_right_product_intervalIntegrable mass unit x hδ hq hpq hx i j).mul_const (A i j)

theorem evaluation_left_array_integral_eq {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (A : I → I → ℝ) {a δ p q : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u) :
    (∫t in p..q,∑i,evaluationDensity mass unit x i t*
      (∑j,(mass j*left a (x (unit j)) (x ((unit j).val+1)) t)*A i j))=
      ∑i,∑j,fineCoupling mass unit (fun u v=>coarseLeft x a p q u v) i j*A i j := by
  have hI i j : IntervalIntegrable (fun t=>evaluationDensity mass unit x i t*mass j*
      left a (x (unit j)) (x ((unit j).val+1)) t*A i j) volume p q := by
    simpa only [mul_assoc] using (evaluationDensity_left_product_intervalIntegrable mass unit x hδ hp hpq hx i j).mul_const (A i j)
  simp only [Finset.mul_sum,← mul_assoc]
  rw [intervalIntegral.integral_finsetSum (fun i _=>intervalIntegrable_univ_sum _ (fun j=>hI i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _=>hI i j)]
  simp only [intervalIntegral.integral_mul_const]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he t : evaluationDensity mass unit x i t*mass j*
      left a (x (unit j)) (x ((unit j).val+1)) t=
      evaluationDensity mass unit x i t*(mass j*left a (x (unit j)) (x ((unit j).val+1)) t) := by ring
  simp_rw [he]
  exact evaluationDensity_left_integral_eq_fineCoupling mass unit x a p q hmass i j

theorem evaluation_right_array_integral_eq {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (A : I → I → ℝ) {b δ p q : ℝ}
    (hδ : 0 < δ) (hq : q ≤ b-δ) (hpq : p ≤ q)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u) :
    (∫t in p..q,∑i,evaluationDensity mass unit x i t*
      (∑j,(mass j*right b (x (unit j)) (x ((unit j).val+1)) t)*A i j))=
      ∑i,∑j,fineCoupling mass unit (fun u v=>coarseRight x b p q u v) i j*A i j := by
  have hI i j : IntervalIntegrable (fun t=>evaluationDensity mass unit x i t*mass j*
      right b (x (unit j)) (x ((unit j).val+1)) t*A i j) volume p q := by
    simpa only [mul_assoc] using (evaluationDensity_right_product_intervalIntegrable mass unit x hδ hq hpq hx i j).mul_const (A i j)
  simp only [Finset.mul_sum,← mul_assoc]
  rw [intervalIntegral.integral_finsetSum (fun i _=>intervalIntegrable_univ_sum _ (fun j=>hI i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _=>hI i j)]
  simp only [intervalIntegral.integral_mul_const]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he t : evaluationDensity mass unit x i t*mass j*
      right b (x (unit j)) (x ((unit j).val+1)) t=
      evaluationDensity mass unit x i t*(mass j*right b (x (unit j)) (x ((unit j).val+1)) t) := by ring
  simp_rw [he]
  exact evaluationDensity_right_integral_eq_fineCoupling mass unit x b p q hmass i j

end OAI.SKFluctuations.WholeUnitSideKernel
