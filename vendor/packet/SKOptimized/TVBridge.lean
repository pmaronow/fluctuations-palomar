module

public import SKOptimized.Model

/-!
# Heat-bath normalization and the sign-passage to TV bridge

The elementary finite proofs are adapted from the OpenAI SKBarriers
HeatBathChoice and TVSignBridge modules at the pinned source revision.
The bridge is extended from threshold 1/4 to every threshold below 1/2.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SKOptimized.Model

def siteChoice {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) : ℝ :=
  Real.exp (β*spin b*localField J x i)/(2*Real.cosh (β*localField J x i))

theorem siteChoice_pos {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    0 < siteChoice β J x i b := by
  apply div_pos (Real.exp_pos _)
  exact mul_pos (by norm_num) (Real.cosh_pos _)

theorem siteChoice_sum {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) :
    ∑ b : Bool, siteChoice β J x i b = 1 := by
  simp only [siteChoice,Fintype.sum_bool,spin,Bool.false_eq_true,ite_false,ite_true,mul_one,
    mul_neg_one,neg_mul]
  rw [← add_div,Real.cosh_eq]
  have H : Real.exp (β*localField J x i)+Real.exp (-(β*localField J x i)) ≠ 0 := by positivity
  field_simp

theorem siteChoice_fiber {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) (i : Fin n) :
    (∑ b : Bool, if Function.update x i b = y then siteChoice β J x i b else 0) =
      if Function.update x i (y i) = y then siteChoice β J x i (y i) else 0 := by
  classical
  apply Finset.sum_eq_single (y i)
  · intro b _ hbi
    have H : Function.update x i b ≠ y := by
      intro he
      have he' := congrFun he i
      exact hbi (by simpa only [Function.update_self] using he')
    simp only [ite_eq_right H]
  · simp

theorem heatBath_eq_siteChoice {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    heatBath β J x y = (∑ i : Fin n, ∑ b : Bool,
      if Function.update x i b = y then siteChoice β J x i b else 0)/(n:ℝ) := by
  unfold heatBath
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [siteChoice_fiber]
  rfl

theorem heatBath_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    0 ≤ heatBath β J x y := by
  rw [heatBath_eq_siteChoice]
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact (siteChoice_pos β J x i b).le
  · rfl

theorem heatBath_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (x : Config n) :
    ∑ y : Config n, heatBath β J x y = 1 := by
  classical
  simp only [heatBath_eq_siteChoice]
  rw [← Finset.sum_div,Finset.sum_comm]
  have HS : (∑ i : Fin n, ∑ y : Config n, ∑ b : Bool,
      if Function.update x i b = y then siteChoice β J x i b else 0) = (n:ℝ) := by
    calc
      _ = ∑ i : Fin n, ∑ b : Bool, siteChoice β J x i b := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp
      _ = _ := by simp only [siteChoice_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one]
  rw [HS]
  exact div_self (by exact_mod_cast hn.ne')

theorem discreteKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (k : ℕ) (x y : Config n) :
    0 ≤ discreteKernel β J k x y := by
  induction k generalizing x y with
  | zero => simp only [discreteKernel]; split_ifs <;> norm_num
  | succ k ih =>
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (heatBath_nonneg β J x z) (ih z y))

theorem discreteKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (k : ℕ) (x : Config n) :
    ∑ y : Config n, discreteKernel β J k x y = 1 := by
  classical
  induction k generalizing x with
  | zero => simp [discreteKernel]
  | succ k ih =>
    simp only [discreteKernel]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,ih,mul_one]
    exact heatBath_sum hn β J x

theorem discreteKernel_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) (x y : Config n) : discreteKernel β J k x y ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  exact Finset.single_le_sum (fun z _ => discreteKernel_nonneg β J k x z) (Finset.mem_univ y)


theorem finite_event_le_tv {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) ≤
      (1/2:ℝ)*∑ x, |p x-q x| := by
  have hsum : ∑ x, (q x-p x) = 0 := by rw [Finset.sum_sub_distrib,hq,hp,sub_self]
  have ht (x : Ω) : 2*(if A x then q x-p x else 0)-(q x-p x) ≤ |q x-p x| := by
    by_cases hx : A x
    · simp only [ite_eq_left hx]
      linarith [le_abs_self (q x-p x)]
    · simp only [ite_eq_right hx,mul_zero,zero_sub]
      exact neg_le_abs (q x-p x)
  have H := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => ht x)
  have he : (∑ x, if A x then q x-p x else 0) =
      (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hsum,sub_zero,he] at H
  have ha : (∑ x, |q x-p x|) = ∑ x, |p x-q x| := by
    apply Finset.sum_congr rfl
    intro x _
    exact abs_sub_comm _ _
  rw [ha] at H
  linarith

theorem gibbs_nonpositive_overlap_mass {n : ℕ} (β : ℝ) (J : Disorder n) (v : Config n) :
    (1/2:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
  classical
  let e : Config n ≃ Config n := ⟨flip,flip,flip_flip,flip_flip⟩
  have he : (∑ y : Config n, if -overlap v y ≤ 0 then gibbs β J y else 0) =
      ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
    calc
      _ = ∑ y : Config n, if overlap v (e y) ≤ 0 then gibbs β J (e y) else 0 := by
        change _ = ∑ y : Config n, if overlap v (flip y) ≤ 0 then gibbs β J (flip y) else 0
        simp only [overlap_flip_right,gibbs_flip]
      _ = _ := Equiv.sum_comp e (fun y => if overlap v y ≤ 0 then gibbs β J y else 0)
  have ht (y : Config n) : gibbs β J y ≤
      (if overlap v y ≤ 0 then gibbs β J y else 0)+
      (if -overlap v y ≤ 0 then gibbs β J y else 0) := by
    by_cases h : overlap v y ≤ 0
    · simp only [ite_eq_left h]
      split_ifs <;> linarith [gibbs_pos β J y]
    · have h' : -overlap v y ≤ 0 := by linarith [lt_of_not_ge h]
      simp only [ite_eq_right h,ite_eq_left h',zero_add,le_refl]
  have H := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => ht y)
  rw [gibbs_sum,Finset.sum_add_distrib,he] at H
  linarith


/-- If total variation is at most tau, the nonpositive-overlap event has
transition probability at least 1/2-tau. No passage estimate is assumed. -/
theorem discrete_sign_mass_of_tv_threshold {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) (x v : Config n) (k : ℕ) (τ : ℝ)
    (hTV : discreteDistance β J x k ≤ τ) :
    (1 / 2 : ℝ) - τ ≤
      ∑ y : Config n, if overlap v y ≤ 0 then discreteKernel β J k x y else 0 := by
  have H := finite_event_le_tv (discreteKernel β J k x) (gibbs β J)
    (discreteKernel_sum hn β J k x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ discreteDistance β J x k at H
  linarith

/-- An explicit small sign-event bound gives a strict actual-model TV bound. -/
theorem discrete_tv_of_sign_mass {n : ℕ} (hn : 0 < n)
    (β : ℝ) (J : Disorder n) (x v : Config n) (k : ℕ) (τ : ℝ)
    (hpass : (∑ y : Config n, if overlap v y ≤ 0
      then discreteKernel β J k x y else 0) < (1 / 2 : ℝ) - τ) :
    τ < discreteDistance β J x k := by
  by_contra h
  have H := discrete_sign_mass_of_tv_threshold hn β J x v k τ (le_of_not_gt h)
  linarith

end SKOptimized.Model
