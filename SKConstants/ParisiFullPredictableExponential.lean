module
public import SKConstants.ParisiFullPredictableMGF
public import SKConstants.ParisiFullRowSecondMoment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullPredictableExponential_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def actualParisiPastMagnetization (β : ℝ) (a : ℝ≥0) (p : ScalarContinuousPath a) : ℝ :=
  actualParisiFullMagnetization β a (p ⟨a,a.coe_nonneg,le_rfl⟩)
lemma measurable_actualParisiPastMagnetization (β : ℝ) (a : ℝ≥0) : Measurable (actualParisiPastMagnetization β a) :=
  (((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable).comp
    (ContinuousMap.measurable_eval _)
lemma actualParisiPastMagnetization_abs_le (β : ℝ) (a : ℝ≥0) (p : ScalarContinuousPath a) :
    |actualParisiPastMagnetization β a p|≤1 := (actualParisiFullMagnetization_curvature_bounds β a _).1

def actualParisiPredictableExponential (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (A : (k : ℕ) → ScalarContinuousPath (t k) → ℝ) (θ : ℝ) :
    (n : ℕ) → ScalarContinuousPath (t n) → ℝ
  | 0 => fun _=>1
  | n+1 => fun p =>
      let q := scalarContinuousPathRestrict (t n) (t (n+1)) (ht (Nat.le_succ _)) p
      actualParisiPredictableExponential β t ht A θ n q*
        Real.exp (θ*A n q*(actualParisiPastMagnetization β (t (n+1)) p-actualParisiPastMagnetization β (t n) q)-
          θ^2*(A n q)^2*((t (n+1):ℝ)-(t n:ℝ))/2)

def actualParisiPredictableExponentialBound (D : ℕ → ℝ) (θ : ℝ) : ℕ → ℝ
  | 0=>1
  | n+1=>actualParisiPredictableExponentialBound D θ n*Real.exp (2* |θ| *D n)

lemma measurable_actualParisiPredictableExponential (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (A : (k : ℕ) → ScalarContinuousPath (t k) → ℝ) (hA : ∀k,Measurable (A k)) (θ : ℝ) (n : ℕ) :
    Measurable (actualParisiPredictableExponential β t ht A θ n) := by
  induction n with
  | zero=>exact measurable_const
  | succ n ih=>
    have hR := measurable_scalarContinuousPathRestrict (t n) (t (n+1)) (ht (Nat.le_succ _))
    exact (ih.comp hR).mul (Real.continuous_exp.measurable.comp
      (((((hA n).comp hR).const_mul θ).mul
        ((measurable_actualParisiPastMagnetization β _).sub ((measurable_actualParisiPastMagnetization β _).comp hR))).sub
          (((((hA n).comp hR).pow_const 2).const_mul (θ^2)).mul_const _ |>.div_const 2)))

lemma actualParisiPredictableExponential_bounds (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (A : (k : ℕ) → ScalarContinuousPath (t k) → ℝ) (D : ℕ → ℝ)
    (hD : ∀k,0≤D k) (hAD : ∀k p,|A k p|≤D k) (θ : ℝ) (n : ℕ) :
    0<actualParisiPredictableExponentialBound D θ n ∧
      ∀p,0≤actualParisiPredictableExponential β t ht A θ n p ∧
        actualParisiPredictableExponential β t ht A θ n p≤actualParisiPredictableExponentialBound D θ n := by
  induction n with
  | zero=>simp [actualParisiPredictableExponential,actualParisiPredictableExponentialBound]
  | succ n ih=>
    refine ⟨mul_pos ih.1 (Real.exp_pos _),?_⟩
    intro p
    let q := scalarContinuousPathRestrict (t n) (t (n+1)) (ht (Nat.le_succ _)) p
    have hq := ih.2 q
    have hd : 0≤(t (n+1):ℝ)-(t n:ℝ) := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ _)))
    have hd0 := hD n
    have hm : |actualParisiPastMagnetization β (t (n+1)) p-actualParisiPastMagnetization β (t n) q|≤2 := by
      have h1 := abs_le.mp (actualParisiPastMagnetization_abs_le β (t (n+1)) p)
      have h0 := abs_le.mp (actualParisiPastMagnetization_abs_le β (t n) q)
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hexp : θ*A n q*(actualParisiPastMagnetization β (t (n+1)) p-actualParisiPastMagnetization β (t n) q)-
        θ^2*(A n q)^2*((t (n+1):ℝ)-(t n:ℝ))/2≤2* |θ| *D n := by
      have hs := mul_nonneg (mul_nonneg (sq_nonneg θ) (sq_nonneg (A n q))) hd
      have hab := mul_le_mul (mul_le_mul_of_nonneg_left (hAD n q) (abs_nonneg θ)) hm (abs_nonneg _) (by positivity)
      rw [← abs_mul,← abs_mul] at hab
      have hh := le_abs_self (θ*A n q*(actualParisiPastMagnetization β (t (n+1)) p-actualParisiPastMagnetization β (t n) q))
      nlinarith
    exact ⟨mul_nonneg hq.1 (Real.exp_pos _).le,
      mul_le_mul hq.2 (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le ih.1.le⟩

lemma actualParisiPastMagnetization_version (W : BrownianSystem Ω) (β : ℝ) (a : ℝ≥0) :
    (fun w=>actualParisiPastMagnetization β a (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w))=ᵐ[W.law]
      actualParisiMagnetizationObservable W β a := by
  filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) a] with w hw
  dsimp only [actualParisiPastMagnetization]
  rw [hw]
  rfl

theorem actualParisiPredictableExponential_integral_le_one
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (A : (k : ℕ) → ScalarContinuousPath (t k) → ℝ) (hA : ∀k,Measurable (A k))
    (D : ℕ → ℝ) (hD : ∀k,0≤D k) (hAD : ∀k p,|A k p|≤D k) (θ : ℝ) (n : ℕ) :
    (∫w,actualParisiPredictableExponential β t ht A θ n
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t n) w) ∂W.law)≤1 := by
  induction n with
  | zero=>simp [actualParisiPredictableExponential]
  | succ n ih=>
    let b := actualParisiFullScalarDrift β
    let P k := boundedDriftPastPath W b (t k)
    let E := actualParisiPredictableExponential β t ht A θ n
    let C := actualParisiPredictableExponentialBound D θ n
    let d := t (n+1)-t n
    have hdt : t n+d=t (n+1) := add_tsub_cancel_of_le (ht (Nat.le_succ _))
    have hdc : (d:ℝ)=(t (n+1):ℝ)-(t n:ℝ) := NNReal.coe_sub (ht (Nat.le_succ _))
    have hb := actualParisiPredictableExponential_bounds β t ht A D hD hAD θ n
    have hEm := measurable_actualParisiPredictableExponential β t ht A hA θ n
    let F : ScalarContinuousPath (t n) → ℝ := fun p=>E p*Real.exp (-θ^2*(A n p)^2*(d:ℝ)/2)
    have hFm : Measurable F := hEm.mul (Real.continuous_exp.measurable.comp
      ((((hA n).pow_const 2).const_mul (-θ^2)).mul_const (d:ℝ) |>.div_const 2))
    have hF0 (p) : 0≤F p := mul_nonneg (hb.2 p).1 (Real.exp_pos _).le
    have hFC (p) : F p≤C := by
      apply (mul_le_mul_of_nonneg_left (show Real.exp (-θ^2*(A n p)^2*(d:ℝ)/2)≤1 from ?_) (hb.2 p).1).trans
      · simpa only [mul_one] using (hb.2 p).2
      · rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hs := mul_nonneg (mul_nonneg (sq_nonneg θ) (sq_nonneg (A n p))) d.coe_nonneg
        nlinarith
    have H := actualParisiFullProcess_predictable_mgf_test W β hβ (t n) d F (A n) hFm (hA n) hF0 C (D n)
      hb.1.le (hD n) hFC (hAD n) θ
    rw [hdt] at H
    have hdtc : (t n:ℝ)+(d:ℝ)=(t (n+1):ℝ) := by exact_mod_cast hdt
    rw [hdtc] at H
    have hR := boundedDriftPastPath_restrict W b (t n) (t (n+1)) (ht (Nat.le_succ _))
    have hEq : (fun w=>actualParisiPredictableExponential β t ht A θ (n+1) (P (n+1) w))=ᵐ[W.law]
        (fun w=>F (P n w)*Real.exp (θ*A n (P n w)*actualParisiMagnetizationIncrement W β (t n) (t (n+1)) w)) := by
      filter_upwards [hR,actualParisiPastMagnetization_version W β (t n),
        actualParisiPastMagnetization_version W β (t (n+1))] with w hr hmn hms
      dsimp only [actualParisiPredictableExponential,P] at *
      rw [hr,hmn,hms]
      dsimp only [F,E,actualParisiMagnetizationIncrement]
      conv_rhs => rw [mul_assoc,← Real.exp_add]
      congr 2
      rw [hdc]
      ring
    change (∫w,F (P n w)*Real.exp (θ*A n (P n w)*actualParisiMagnetizationIncrement W β (t n) (t (n+1)) w) ∂W.law)≤
      ∫w,F (P n w)*Real.exp (θ^2*A n (P n w)^2*(d:ℝ)/2) ∂W.law at H
    rw [integral_congr_ae hEq]
    have he (w) : F (P n w)*Real.exp (θ^2*A n (P n w)^2*(d:ℝ)/2)=E (P n w) := by
      dsimp only [F]
      rw [mul_assoc,← Real.exp_add]
      ring_nf
      simp
    simp_rw [he] at H
    exact H.trans ih

end SKConstants
