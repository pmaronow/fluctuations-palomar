module

public import ComparisonEffectiveEvaluation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set Hierarchy
open scoped BigOperators

def evaluationIntegral {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (p q : ℝ) (F : I → ℝ) : ℝ :=
  ∫t in p..q,∑i,evaluationDensity mass unit x i t*F i

theorem evaluationIntegral_eq_sum {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) (p q : ℝ) (F : I → ℝ) :
    evaluationIntegral mass unit x p q F=
      ∑i,(∫t in p..q,evaluationDensity mass unit x i t)*F i := by
  unfold evaluationIntegral
  rw [intervalIntegral.integral_finsetSum
    (fun i _=>(evaluationDensity_intervalIntegrable mass unit x i p q).mul_const (F i))]
  simp only [intervalIntegral.integral_mul_const]

theorem evaluationDensity_integral_total {I : Type*} [Fintype I] {K : ℕ}
    (mass : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {a b p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u)
    (hap : a < p) (hpq : p ≤ q) (hqb : q < b) :
    (∑i,∫t in p..q,evaluationDensity mass unit x i t)=q-p := by
  rw [← intervalIntegral.integral_finsetSum
    (fun i _=>evaluationDensity_intervalIntegrable mass unit x i p q)]
  have he : (∫t in p..q,∑i,evaluationDensity mass unit x i t)=∫t in p..q,(1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc p q := by simpa only [uIcc_of_le hpq] using ht
    exact evaluationDensity_sum_eq_one mass unit x hstart hend hx hmass
      ⟨by linarith [ht'.1],by linarith [ht'.2]⟩
  rw [he]
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one]

theorem evaluationIntegral_nonneg {I : Type*} [Fintype I] {K : ℕ}
    (mass F : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {p q : ℝ}
    (hmass : ∀i,0 ≤ mass i) (hx : ∀u:Fin K,x u < x (u.val+1))
    (hF : ∀i,0 ≤ F i) (hpq : p ≤ q) :
    0 ≤ evaluationIntegral mass unit x p q F := by
  apply intervalIntegral.integral_nonneg hpq
  intro t _
  exact Finset.sum_nonneg (fun i _=>mul_nonneg (evaluationDensity_nonneg mass unit x hmass hx i t) (hF i))

theorem evaluationIntegral_le_full_sum {I : Type*} [Fintype I] {K : ℕ}
    (mass F : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {p q : ℝ}
    (hmass : ∀i,0 ≤ mass i) (hx : ∀u:Fin K,x u < x (u.val+1))
    (hF : ∀i,0 ≤ F i) (hpq : p ≤ q) :
    evaluationIntegral mass unit x p q F ≤ ∑i,mass i*F i := by
  rw [evaluationIntegral_eq_sum]
  exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right
    (evaluationDensity_integral_le_mass mass unit x hmass hx hpq i) (hF i))

theorem full_sum_le_evaluationIntegral_and_edges {I : Type*} [Fintype I] {K : ℕ}
    (mass F : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ) {a b p q M : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u)
    (hmass0 : ∀i,0 ≤ mass i) (hmassv : ∑i,mass i=b-a)
    (hF : ∀i,F i ≤ M) (hap : a < p) (hpq : p ≤ q) (hqb : q < b) :
    (∑i,mass i*F i) ≤ evaluationIntegral mass unit x p q F+M*(b-a-(q-p)) := by
  let mi := fun i=>∫t in p..q,evaluationDensity mass unit x i t
  have hmi i : mi i ≤ mass i := evaluationDensity_integral_le_mass mass unit x hmass0 hx hpq i
  have hmisum : ∑i,mi i=q-p := evaluationDensity_integral_total mass unit x hstart hend hx hmass hap hpq hqb
  have he : (∑i,mass i*F i)=evaluationIntegral mass unit x p q F+∑i,(mass i-mi i)*F i := by
    rw [evaluationIntegral_eq_sum]
    simp only [sub_mul,Finset.sum_sub_distrib,mi]
    ring
  rw [he]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑i,(mass i-mi i)*M := Finset.sum_le_sum (fun i _=>
      mul_le_mul_of_nonneg_left (hF i) (sub_nonneg.mpr (hmi i)))
    _ = _ := by rw [← Finset.sum_mul,Finset.sum_sub_distrib,hmassv,hmisum]; ring

end OAI.SKFluctuations.WholeUnitSideKernel
