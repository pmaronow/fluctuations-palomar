module

public import ComparisonEvaluationArrays

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set Hierarchy
open scoped BigOperators

theorem integrated_evaluation_score_ledger {I : Type*} [Fintype I] {K : ℕ}
    (mass D C : I → ℝ) (unit : I → Fin K) (x : ℕ → ℝ)
    (AL AR : I → I → ℝ) (VL VR : ℝ → ℝ) {a b δ p q eta : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) (hmass0 : ∀i,0 ≤ mass i)
    (hmass : ∀u:Fin K,unitTotalMass mass unit u=x (u.val+1)-x u)
    (hC : ∀i,0 ≤ C i)
    (hVL : IntervalIntegrable VL volume p q) (hVR : IntervalIntegrable VR volume p q)
    (hscore : ∀t∈Icc p q,∀i,mass i≠0 → D i ≤
      24*VL t+24*VR t+6*eta^2+
        (∑j,(mass j*left a (x (unit j)) (x ((unit j).val+1)) t)*AL i j)+
        (∑j,(mass j*right b (x (unit j)) (x ((unit j).val+1)) t)*AR i j)+C i) :
    evaluationIntegral mass unit x p q D ≤
      24*(∫t in p..q,VL t)+24*(∫t in p..q,VR t)+6*eta^2*(q-p)+
        (∑i,∑j,fineCoupling mass unit (fun u v=>coarseLeft x a p q u v) i j*AL i j)+
        (∑i,∑j,fineCoupling mass unit (fun u v=>coarseRight x b p q u v) i j*AR i j)+
        ∑i,mass i*C i := by
  let ρ := evaluationDensity mass unit x
  let V : ℝ → ℝ := fun t=>24*VL t+24*VR t+6*eta^2
  let FL : ℝ → ℝ := fun t=>∑i,ρ i t*
    (∑j,(mass j*left a (x (unit j)) (x ((unit j).val+1)) t)*AL i j)
  let FR : ℝ → ℝ := fun t=>∑i,ρ i t*
    (∑j,(mass j*right b (x (unit j)) (x ((unit j).val+1)) t)*AR i j)
  let FC : ℝ → ℝ := fun t=>∑i,ρ i t*C i
  let FD : ℝ → ℝ := fun t=>∑i,ρ i t*D i
  have hρ i : IntervalIntegrable (ρ i) volume p q := evaluationDensity_intervalIntegrable mass unit x i p q
  have hV : IntervalIntegrable V volume p q := ((hVL.const_mul 24).add (hVR.const_mul 24)).add intervalIntegrable_const
  have hFL : IntervalIntegrable FL volume p q := evaluation_left_array_intervalIntegrable mass unit x AL hδ hp hpq hx
  have hFR : IntervalIntegrable FR volume p q := evaluation_right_array_intervalIntegrable mass unit x AR hδ hq hpq hx
  have hFC : IntervalIntegrable FC volume p q := intervalIntegrable_univ_sum _ (fun i=>(hρ i).mul_const (C i))
  have hFD : IntervalIntegrable FD volume p q := intervalIntegrable_univ_sum _ (fun i=>(hρ i).mul_const (D i))
  have hpoint t (ht : t∈Icc p q) : FD t ≤ V t+FL t+FR t+FC t := by
    have hsumρ : ∑i,ρ i t=1 := evaluationDensity_sum_eq_one mass unit x hstart hend hx hmass
      ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hterm i : ρ i t*D i ≤ ρ i t*(V t+
        (∑j,(mass j*left a (x (unit j)) (x ((unit j).val+1)) t)*AL i j)+
        (∑j,(mass j*right b (x (unit j)) (x ((unit j).val+1)) t)*AR i j)+C i) := by
      by_cases hi:mass i=0
      · simp [ρ,evaluationDensity,hi]
      · exact mul_le_mul_of_nonneg_left (hscore t ht i hi)
          (evaluationDensity_nonneg mass unit x hmass0 hx i t)
    have hm := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset I))=>hterm i)
    simp only [mul_add,Finset.sum_add_distrib] at hm
    have he : (∑i,ρ i t*V t)=V t := by rw [← Finset.sum_mul,hsumρ,one_mul]
    rw [he] at hm
    exact hm
  have hle := intervalIntegral.integral_mono_on hpq hFD (((hV.add hFL).add hFR).add hFC) hpoint
  have h1 := intervalIntegral.integral_add ((hV.add hFL).add hFR) hFC
  have h2 := intervalIntegral.integral_add (hV.add hFL) hFR
  have h3 := intervalIntegral.integral_add hV hFL
  try simp only [Pi.add_apply] at h1 h2 h3
  rw [h1,h2,h3] at hle
  have hv1 := intervalIntegral.integral_add (hVL.const_mul 24) (hVR.const_mul 24)
  have hv2 := intervalIntegral.integral_add ((hVL.const_mul 24).add (hVR.const_mul 24))
    (intervalIntegrable_const (a:=p) (b:=q) (c:=6*eta^2))
  try simp only [Pi.add_apply] at hv1 hv2
  have hVe : (∫t in p..q,V t)=24*(∫t in p..q,VL t)+24*(∫t in p..q,VR t)+6*eta^2*(q-p) := by
    change (∫t in p..q,24*VL t+24*VR t+6*eta^2)=_
    rw [hv2,hv1,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hFLe := evaluation_left_array_integral_eq mass unit x AL hδ hp hpq hx hmass
  have hFRe := evaluation_right_array_integral_eq mass unit x AR hδ hq hpq hx hmass
  change (∫t in p..q,FL t)=_ at hFLe
  change (∫t in p..q,FR t)=_ at hFRe
  rw [hVe,hFLe,hFRe] at hle
  have hCe : (∫t in p..q,FC t) ≤ ∑i,mass i*C i :=
    evaluationIntegral_le_full_sum mass C unit x hmass0 hx hC hpq
  exact hle.trans (add_le_add le_rfl hCe)

end OAI.SKFluctuations.WholeUnitSideKernel
