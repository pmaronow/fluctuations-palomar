module

public import ComparisonContinuumSideKernel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def coarseLeft (x : ℕ → ℝ) (a p q : ℝ) (u v : ℕ) : ℝ :=
  ∫t in p..q, (Ico (x u) (x (u+1))).indicator (left a (x v) (x (v+1))) t

def coarseRight (x : ℕ → ℝ) (b p q : ℝ) (u v : ℕ) : ℝ :=
  ∫t in p..q, (Ico (x u) (x (u+1))).indicator (right b (x v) (x (v+1))) t

theorem unitPoints_monotoneOn (x : ℕ → ℝ) {K : ℕ}
    (hx : ∀u<K,x u ≤ x (u+1)) : MonotoneOn x (Icc 0 K) := by
  apply monotoneOn_of_le_succ ordConnected_Icc
  intro u _ hu hv
  apply hx
  simp only [Order.succ_eq_add_one,mem_Icc] at hv
  omega

theorem consecutive_indicator_add (f : ℝ → ℝ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (t : ℝ) :
    (Ico a b).indicator f t+(Ico b c).indicator f t=(Ico a c).indicator f t := by
  by_cases hta : a ≤ t
  · by_cases htb : t < b
    · simp [hta,htb,show t<c from htb.trans_le hbc,show ¬b≤t from not_le.mpr htb]
    · have hbt : b ≤ t := le_of_not_gt htb
      by_cases htc : t < c <;> simp [hta,htb,hbt,htc]
  · have htb : ¬b ≤ t := by intro h; exact hta (hab.trans h)
    simp [hta,htb]

theorem sum_unit_indicators (x : ℕ → ℝ) {K : ℕ}
    (hx : ∀u<K,x u ≤ x (u+1)) (f : ℝ → ℝ) (t : ℝ) :
    (∑u∈Finset.range K,(Ico (x u) (x (u+1))).indicator f t)=
      (Ico (x 0) (x K)).indicator f t := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ,ih (fun u hu=>hx u (by omega))]
    apply consecutive_indicator_add
    · exact unitPoints_monotoneOn x (fun u hu=>hx u (by omega))
        (by simp) (by simp) (by omega)
    · exact hx K (by omega)

theorem intervalIntegrable_indicator_Ico {f : ℝ → ℝ} {p q L R : ℝ}
    (hf : IntervalIntegrable f volume p q) :
    IntervalIntegrable ((Ico L R).indicator f) volume p q := by
  exact ⟨hf.1.indicator measurableSet_Ico,hf.2.indicator measurableSet_Ico⟩

theorem unit_indicator_integral_le {p q L R : ℝ} (hpq : p ≤ q) (hLR : L ≤ R) :
    (∫t in p..q,(Ico L R).indicator (fun _ : ℝ => (1:ℝ)) t) ≤ R-L := by
  have hi : Integrable ((Ico L R).indicator (fun _ : ℝ => (1:ℝ))) volume := by
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact integrableOn_const (by simp)
  rw [intervalIntegral.integral_of_le hpq]
  have hn : 0 ≤ᵐ[volume] (Ico L R).indicator (fun _ : ℝ => (1:ℝ)) :=
    Filter.Eventually.of_forall (fun t=>by by_cases ht:t∈Ico L R <;> simp [ht])
  have hb := setIntegral_le_integral (s:=Ioc p q) hi hn
  simpa [integral_indicator_const,Real.volume_real_Ico_of_le hLR] using hb

theorem left_middle_intervalIntegrable {a b δ p q L R : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q) (hLR : L < R) :
    IntervalIntegrable (left a L R) volume p q := by
  exact ((left_continuousOn (b:=q) hδ hLR).mono
    (Icc_subset_Icc hp le_rfl)).intervalIntegrable_of_Icc hpq

theorem right_middle_intervalIntegrable {a b δ p q L R : ℝ}
    (hδ : 0 < δ) (hq : q ≤ b-δ) (hpq : p ≤ q) (hLR : L < R) :
    IntervalIntegrable (right b L R) volume p q := by
  exact ((right_continuousOn (a:=p) hδ hLR).mono
    (Icc_subset_Icc le_rfl hq)).intervalIntegrable_of_Icc hpq

theorem coarseLeft_nonneg (x : ℕ → ℝ) {a δ p q : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q) (u v : ℕ)
    (hv : x v < x (v+1)) : 0 ≤ coarseLeft x a p q u v := by
  apply intervalIntegral.integral_nonneg hpq
  intro t ht
  by_cases hu:t∈Ico (x u) (x (u+1))
  · simpa only [indicator_of_mem hu] using (left_bounds hv (by linarith [ht.1])).1
  · simp only [indicator_of_notMem hu]; exact le_rfl

theorem coarseRight_nonneg (x : ℕ → ℝ) {b δ p q : ℝ}
    (hδ : 0 < δ) (hq : q ≤ b-δ) (hpq : p ≤ q) (u v : ℕ)
    (hv : x v < x (v+1)) : 0 ≤ coarseRight x b p q u v := by
  apply intervalIntegral.integral_nonneg hpq
  intro t ht
  by_cases hu:t∈Ico (x u) (x (u+1))
  · simpa only [indicator_of_mem hu] using (right_bounds hv (by linarith [ht.2])).1
  · simp only [indicator_of_notMem hu]; exact le_rfl

theorem coarseLeft_row_le (x : ℕ → ℝ) {K : ℕ} {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀v∈Finset.range K,x v < x (v+1)) (u : ℕ)
    (hu : u∈Finset.range K) :
    (∑v∈Finset.range K,(x (v+1)-x v)*coarseLeft x a p q u v) ≤ x (u+1)-x u := by
  have hi v hv := left_middle_intervalIntegrable (b:=b) hδ hp hpq (hx v hv)
  unfold coarseLeft
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun v hv=>
    (intervalIntegrable_indicator_Ico (hi v hv)).const_mul (x (v+1)-x v))]
  have he : (∫t in p..q,∑v∈Finset.range K,(x (v+1)-x v)*
      (Ico (x u) (x (u+1))).indicator (left a (x v) (x (v+1))) t)=
      ∫t in p..q,(Ico (x u) (x (u+1))).indicator (fun _ : ℝ=>(1:ℝ)) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc p q := by
      simpa [uIcc_of_le hpq] using ht
    by_cases htu : t∈Ico (x u) (x (u+1))
    · simp only [indicator_of_mem htu]
      exact left_row_normalized x K hstart hend (by linarith [ht'.1])
        (by linarith [ht'.2]) hx
    · simp only [indicator_of_notMem htu,mul_zero,Finset.sum_const_zero]
  rw [he]
  exact unit_indicator_integral_le hpq (hx u hu).le

theorem coarseRight_row_le (x : ℕ → ℝ) {K : ℕ} {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀v∈Finset.range K,x v < x (v+1)) (u : ℕ)
    (hu : u∈Finset.range K) :
    (∑v∈Finset.range K,(x (v+1)-x v)*coarseRight x b p q u v) ≤ x (u+1)-x u := by
  have hi v hv := right_middle_intervalIntegrable (a:=a) hδ hq hpq (hx v hv)
  unfold coarseRight
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun v hv=>
    (intervalIntegrable_indicator_Ico (hi v hv)).const_mul (x (v+1)-x v))]
  have he : (∫t in p..q,∑v∈Finset.range K,(x (v+1)-x v)*
      (Ico (x u) (x (u+1))).indicator (right b (x v) (x (v+1))) t)=
      ∫t in p..q,(Ico (x u) (x (u+1))).indicator (fun _ : ℝ=>(1:ℝ)) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc p q := by
      simpa [uIcc_of_le hpq] using ht
    by_cases htu : t∈Ico (x u) (x (u+1))
    · simp only [indicator_of_mem htu]
      exact right_row_normalized x K hstart hend (by linarith [ht'.1])
        (by linarith [ht'.2]) hx
    · simp only [indicator_of_notMem htu,mul_zero,Finset.sum_const_zero]
  rw [he]
  exact unit_indicator_integral_le hpq (hx u hu).le

theorem coarseLeft_column_le (x : ℕ → ℝ) {K : ℕ} {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u∈Finset.range K,x u < x (u+1)) (v : ℕ)
    (hv : v∈Finset.range K) :
    (∑u∈Finset.range K,coarseLeft x a p q u v) ≤ Real.log ((b-a)/δ) := by
  have hi := left_middle_intervalIntegrable (b:=b) hδ hp hpq (hx v hv)
  unfold coarseLeft
  rw [← intervalIntegral.integral_finsetSum (fun _ _=>intervalIntegrable_indicator_Ico hi)]
  simp_rw [sum_unit_indicators x (fun u hu=>(hx u (Finset.mem_range.mpr hu)).le),hstart,hend]
  have he : (∫t in p..q,(Ico a b).indicator (left a (x v) (x (v+1))) t)=
      ∫t in p..q,left a (x v) (x (v+1)) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc p q := by simpa [uIcc_of_le hpq] using ht
    exact indicator_of_mem (by constructor <;> linarith [ht'.1,ht'.2]) _
  rw [he]
  have hδb : δ ≤ b-a := by linarith
  refine (intervalIntegral.integral_mono_interval hp hpq (by linarith : q ≤ b) ?_
    (left_intervalIntegrable hδ hδb (hx v hv))).trans (left_column_integral_le hδ hδb (hx v hv))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (left_bounds (hx v hv) (by linarith [ht.1])).1

theorem coarseRight_column_le (x : ℕ → ℝ) {K : ℕ} {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u∈Finset.range K,x u < x (u+1)) (v : ℕ)
    (hv : v∈Finset.range K) :
    (∑u∈Finset.range K,coarseRight x b p q u v) ≤ Real.log ((b-a)/δ) := by
  have hi := right_middle_intervalIntegrable (a:=a) hδ hq hpq (hx v hv)
  unfold coarseRight
  rw [← intervalIntegral.integral_finsetSum (fun _ _=>intervalIntegrable_indicator_Ico hi)]
  simp_rw [sum_unit_indicators x (fun u hu=>(hx u (Finset.mem_range.mpr hu)).le),hstart,hend]
  have he : (∫t in p..q,(Ico a b).indicator (right b (x v) (x (v+1))) t)=
      ∫t in p..q,right b (x v) (x (v+1)) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc p q := by simpa [uIcc_of_le hpq] using ht
    exact indicator_of_mem (by constructor <;> linarith [ht'.1,ht'.2]) _
  rw [he]
  have hδb : δ ≤ b-a := by linarith
  refine (intervalIntegral.integral_mono_interval (by linarith : a ≤ p) hpq hq ?_
    (right_intervalIntegrable hδ hδb (hx v hv))).trans (right_column_integral_le hδ hδb (hx v hv))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (right_bounds (hx v hv) (by linarith [ht.2])).1

theorem coarseLeft_fin_bounds (x : ℕ → ℝ) {K : ℕ} {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    (∀u v:Fin K,0 ≤ coarseLeft x a p q u v) ∧
    (∀u:Fin K,(∑v:Fin K,(x (v.val+1)-x v)*coarseLeft x a p q u v) ≤ x (u.val+1)-x u) ∧
    (∀v:Fin K,(∑u:Fin K,coarseLeft x a p q u v) ≤ Real.log ((b-a)/δ)) := by
  have hx' : ∀u∈Finset.range K,x u < x (u+1) := fun u hu=>hx ⟨u,Finset.mem_range.mp hu⟩
  refine ⟨fun u v=>coarseLeft_nonneg x hδ hp hpq u v (hx v),?_,?_⟩
  · intro u
    rw [Fin.sum_univ_eq_sum_range (fun v:ℕ=>(x (v+1)-x v)*coarseLeft x a p q u v)]
    exact coarseLeft_row_le x hstart hend hδ hp hpq hq hx' u (Finset.mem_range.mpr u.isLt)
  · intro v
    rw [Fin.sum_univ_eq_sum_range (fun u:ℕ=>coarseLeft x a p q u v)]
    exact coarseLeft_column_le x hstart hend hδ hp hpq hq hx' v (Finset.mem_range.mpr v.isLt)

theorem coarseRight_fin_bounds (x : ℕ → ℝ) {K : ℕ} {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    (∀u v:Fin K,0 ≤ coarseRight x b p q u v) ∧
    (∀u:Fin K,(∑v:Fin K,(x (v.val+1)-x v)*coarseRight x b p q u v) ≤ x (u.val+1)-x u) ∧
    (∀v:Fin K,(∑u:Fin K,coarseRight x b p q u v) ≤ Real.log ((b-a)/δ)) := by
  have hx' : ∀u∈Finset.range K,x u < x (u+1) := fun u hu=>hx ⟨u,Finset.mem_range.mp hu⟩
  refine ⟨fun u v=>coarseRight_nonneg x hδ hq hpq u v (hx v),?_,?_⟩
  · intro u
    rw [Fin.sum_univ_eq_sum_range (fun v:ℕ=>(x (v+1)-x v)*coarseRight x b p q u v)]
    exact coarseRight_row_le x hstart hend hδ hp hpq hq hx' u (Finset.mem_range.mpr u.isLt)
  · intro v
    rw [Fin.sum_univ_eq_sum_range (fun u:ℕ=>coarseRight x b p q u v)]
    exact coarseRight_column_le x hstart hend hδ hp hpq hq hx' v (Finset.mem_range.mpr v.isLt)

end OAI.SKFluctuations.WholeUnitSideKernel
