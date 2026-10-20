module
public import SKConstants.ConcentrationMGF
public import SKConstants.SubGaussianSquares
public import SKConstants.ScalarProcessLagMGFLimit

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SKConstants.Concentration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {A : Type*} [MeasurableSpace A]

theorem bounded_pinning_centered_localMGF (μ : Measure A) [IsProbabilityMeasure μ]
    (Y : A → ℝ) (hY : Measurable Y) (hRange : ∀ u, Y u ∈ Icc (0:ℝ) 4)
    (ε : ℝ) (hMean : (∫ u,Y u ∂μ) ≤ ε) :
    LocalQuadraticMGF (centeredObservable μ Y) μ (4*ε) (1/4) := by
  let p := ∫ u,Y u ∂μ
  have hi : Integrable Y μ := Integrable.of_bound hY.aestronglyMeasurable 4
    (ae_of_all _ (fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (hRange u).1]; exact (hRange u).2))
  have hi2 : Integrable (fun u => Y u^2) μ := by
    apply Integrable.of_bound (f := fun u => Y u^2) (hY.pow_const 2).aestronglyMeasurable 16
    exact ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [(hRange u).1,(hRange u).2])
  have hp0 : 0 ≤ p := integral_nonneg (fun u => (hRange u).1)
  have hp4 : p ≤ 4 := by
    have H := integral_mono hi (integrable_const 4) (fun u => (hRange u).2)
    simpa only [integral_const,probReal_univ,one_smul] using H
  have h2 : (∫ u,Y u^2 ∂μ) ≤ 4*p := by
    calc
      _ ≤ ∫ u,4*Y u ∂μ := integral_mono hi2 (hi.const_mul 4) (fun u => by
        nlinarith [(hRange u).1,(hRange u).2])
      _ = _ := integral_const_mul _ _
  have hcB : ∀ u, |centeredObservable μ Y u| ≤ 4 := by
    intro u
    change |Y u-p|≤4
    exact abs_le.mpr ⟨by linarith [(hRange u).1],by linarith [(hRange u).2]⟩
  have hcMean : (∫ u,centeredObservable μ Y u ∂μ)=0 := by
    unfold centeredObservable
    rw [integral_sub hi (integrable_const _)]
    simp
  have hcVariance : (∫ u,(centeredObservable μ Y u)^2 ∂μ) ≤ 4*ε := by
    have hp (u : A) : (centeredObservable μ Y u)^2=Y u^2-2*p*Y u+p^2 := by
      change (Y u-p)^2=_
      ring
    simp_rw [hp]
    rw [integral_add (f := fun u => Y u^2-2*p*Y u) (g := fun _ : A => p^2)
      (hi2.sub (hi.const_mul (2*p))) (integrable_const _),
      integral_sub (f := fun u => Y u^2) (g := fun u => 2*p*Y u)
        hi2 (hi.const_mul (2*p)),integral_const_mul,integral_const,
      probReal_univ,one_smul]
    change (∫ u,Y u^2 ∂μ)-2*p*p+p^2≤4*ε
    nlinarith [hMean,sq_nonneg p]
  exact localQuadraticMGF_of_bounded_variance (hY.sub_const _) (by norm_num)
    (ae_of_all _ hcB) hcMean hcVariance

theorem bounded_pinning_iid_tail (μ : Measure A) [IsProbabilityMeasure μ]
    (Y : A → ℝ) (hY : Measurable Y) (hRange : ∀ u, Y u ∈ Icc (0:ℝ) 4)
    (n : ℕ) (hn : 0<n) (ε η : ℝ) (hε : 0<ε) (hη : 0<η)
    (hMean : (∫ u,Y u ∂μ) ≤ ε) (hSmall : 2*ε≤η) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | 2*η ≤ (∑ i : Fin n,Y (ω i))/(n:ℝ)} ≤
      2*Real.exp (-(n:ℝ)*η/8) := by
  let X := centeredObservable μ Y
  let P := Measure.pi (fun _ : Fin n => μ)
  have hX : Measurable X := hY.sub_const _
  have hIndep : iIndepFun (fun i : Fin n => fun ω : Fin n → A => X (ω i)) P :=
    iIndepFun_pi (fun _ => hX.aemeasurable)
  have hRows (i : Fin n) : LocalQuadraticMGF (fun ω : Fin n → A => X (ω i)) P (4*ε) (1/4) := by
    have hl : HasLaw (Function.eval i) μ P :=
      ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq⟩
    exact (bounded_pinning_centered_localMGF μ Y hY hRange ε hMean).comp_hasLaw hl
  have ht := independent_average_bernstein hn hIndep
    (fun i => hX.comp (measurable_pi_apply i)) hRows (by positivity) (by norm_num) hη
  have hmin : (1/4:ℝ)*η/2 ≤ η^2/(4*(4*ε)) := by
    apply (le_div_iff₀ (by positivity : 0<4*(4*ε))).mpr
    nlinarith [mul_le_mul_of_nonneg_right hSmall hη.le]
  rw [min_eq_right hmin] at ht
  have hnr : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he (ω : Fin n → A) : (∑ i : Fin n,X (ω i))/(n:ℝ) =
      (∑ i : Fin n,Y (ω i))/(n:ℝ)-(∫ u,Y u ∂μ) := by
    simp only [X,centeredObservable,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hs : {ω : Fin n → A | 2*η ≤ (∑ i : Fin n,Y (ω i))/(n:ℝ)} ⊆
      {ω | η ≤ |(∑ i : Fin n,X (ω i))/(n:ℝ)|} := by
    intro ω hω
    change 2*η ≤ (∑ i : Fin n,Y (ω i))/(n:ℝ) at hω
    change η ≤ |(∑ i : Fin n,X (ω i))/(n:ℝ)|
    rw [he]
    exact (by linarith : η ≤ (∑ i : Fin n,Y (ω i))/(n:ℝ)-(∫ u,Y u ∂μ)).trans (le_abs_self _)
  exact (measureReal_mono hs).trans (by convert ht using 1 <;> congr 1 <;> ring)

end SKConstants.Concentration
