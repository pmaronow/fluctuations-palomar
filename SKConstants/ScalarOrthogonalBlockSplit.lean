module

public import SKConstants.ScalarWeightedGaussianFamilies
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

def scalarBlockSplitCoefficients {d m : ℕ} (ρ σ : Fin (d*m) → ℝ) :
    (Fin d ⊕ Fin d) → (Fin (d*m) ⊕ Fin (d*m)) → ℝ
  | .inl k => Sum.elim (fun j => if j.divNat=k then ρ j else 0)
      (fun j => if j.divNat=k then σ j else 0)
  | .inr k => Sum.elim (fun j => if j.divNat=k then σ j else 0)
      (fun j => if j.divNat=k then -ρ j else 0)

theorem scalarBlockIndicator_sum {d m : ℕ} (k : Fin d) (c : ℝ) :
    (∑ j : Fin (d*m), if j.divNat=k then c else 0) = (m : ℝ)*c := by
  have he (p : Fin d × Fin m) : (finProdFinEquiv p).divNat=p.1 :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply p)
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  change (∑ i : Fin d,∑ _j : Fin m,if i=k then c else 0) = _
  have hinner (i : Fin d) : (∑ _j : Fin m,if i=k then c else 0) =
      (m : ℝ)*(if i=k then c else 0) := by simp
  simp_rw [hinner,mul_ite,mul_zero]
  simp

theorem scalarBlockSelected_sum {d m : ℕ} (k : Fin d) (w X : Fin (d*m) → ℝ) :
    (∑ j : Fin (d*m),(if j.divNat=k then w j else 0)*X j) =
      ∑ i : Fin m,w (finProdFinEquiv (k,i))*X (finProdFinEquiv (k,i)) := by
  have he (p : Fin d × Fin m) : (finProdFinEquiv p).divNat=p.1 :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply p)
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  have hinner (j : Fin d) :
      (∑ i : Fin m,(if j=k then w (finProdFinEquiv (j,i)) else 0)*X (finProdFinEquiv (j,i))) =
        if j=k then ∑ i : Fin m,w (finProdFinEquiv (j,i))*X (finProdFinEquiv (j,i)) else 0 := by
    by_cases hj : j=k <;> simp [hj]
  simp_rw [hinner]
  simp

theorem scalarBlockSplitCoefficients_dot {d m : ℕ} (ρ σ : Fin (d*m) → ℝ)
    (hunit : ∀ j, (ρ j)^2+(σ j)^2=1) (δ : ℝ) (i k : Fin d ⊕ Fin d) :
    (∑ j : Fin (d*m) ⊕ Fin (d*m),
      scalarBlockSplitCoefficients ρ σ i j*scalarBlockSplitCoefficients ρ σ k j*δ) =
      if i=k then (m : ℝ)*δ else 0 := by
  have hdiag (i : Fin d) :
      (∑ j : Fin (d*m),
        ((if j.divNat=i then ρ j else 0)^2+(if j.divNat=i then σ j else 0)^2)*δ) =
        (m : ℝ)*δ := by
    convert scalarBlockIndicator_sum i δ using 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.divNat=i
    · simp only [hj,ite_true,hunit,one_mul]
    · simp [hj]
  have hoff (i k : Fin d) (hik : i ≠ k) (a b : Fin (d*m) → ℝ) :
      (∑ j : Fin (d*m),(if j.divNat=i then a j else 0)*(if j.divNat=k then b j else 0)*δ)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.divNat=i
    · have hk : j.divNat ≠ k := by simpa only [hj] using hik
      simp [hk]
    · simp [hj]
  cases i with
  | inl i =>
    cases k with
    | inl k =>
      by_cases hik : i=k
      · subst k
        simpa only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inl.injEq,ite_true,← sq,← Finset.sum_add_distrib,← add_mul] using hdiag i
      · simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inl.injEq,hik,ite_false]
        rw [hoff i k hik ρ ρ,hoff i k hik σ σ,zero_add]
    | inr k =>
      by_cases hik : i=k
      · subst k
        simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inl_ne_inr,ite_false,← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j.divNat=i <;> simp [hj] <;> ring
      · simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inl_ne_inr,ite_false]
        rw [hoff i k hik ρ σ,hoff i k hik σ (fun j => -ρ j),zero_add]
  | inr i =>
    cases k with
    | inl k =>
      by_cases hik : i=k
      · subst k
        simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inr_ne_inl,ite_false,← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j.divNat=i <;> simp [hj] <;> ring
      · simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inr_ne_inl,ite_false]
        rw [hoff i k hik σ ρ,hoff i k hik (fun j => -ρ j) σ,zero_add]
    | inr k =>
      by_cases hik : i=k
      · subst k
        simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inr.injEq,ite_true,← Finset.sum_add_distrib]
        convert hdiag i using 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.divNat=i <;> simp [hj] <;> ring
      · simp only [scalarBlockSplitCoefficients,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          Sum.inr.injEq,hik,ite_false]
        rw [hoff i k hik σ σ,hoff i k hik (fun j => -ρ j) (fun j => -ρ j),zero_add]

def scalarBrownianAffineTime (a δ : ℝ≥0) (i : ℕ) : ℝ≥0 := a+(i : ℝ≥0)*δ

theorem scalarBrownianAffineTime_mono (a δ : ℝ≥0) : Monotone (scalarBrownianAffineTime a δ) := by
  intro i j hij
  change a+(i : ℝ≥0)*δ ≤ a+(j : ℝ≥0)*δ
  simpa only [add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij)
      (show (0 : ℝ≥0) ≤ δ from zero_le)) a

theorem brownianMeshVariance_scalarBrownianAffineTime (a δ : ℝ≥0) (i : ℕ) :
    brownianMeshVariance (scalarBrownianAffineTime a δ) i=δ := by
  apply NNReal.eq
  rw [brownianMeshVariance,NNReal.coe_sub ((scalarBrownianAffineTime_mono a δ) (by omega))]
  simp only [scalarBrownianAffineTime,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,
    Nat.cast_add,Nat.cast_one,NNReal.coe_one]
  ring

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem scalarOrthogonalRefiningBlocks_hasLaw {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (a δ : ℝ≥0) (ρ σ : Fin (d*m) → ℝ) (hunit : ∀ j,(ρ j)^2+(σ j)^2=1) :
    HasLaw (fun u k => ∑ j, scalarBlockSplitCoefficients ρ σ k j*
      scalarTwoBrownianMeshFamily B C (scalarBrownianAffineTime a δ) (d*m) u j)
      (Measure.pi (fun _ : Fin d ⊕ Fin d => gaussianReal 0 ((m : ℝ≥0)*δ))) (P.prod Q) := by
  have h := scalarTwoBrownianMeshFamily_linearForms_hasLaw P Q B C hB hC _
    (scalarBrownianAffineTime_mono a δ) (d*m) (scalarBlockSplitCoefficients ρ σ) (by
      intro i k hik
      simp only [brownianMeshVariance_scalarBrownianAffineTime]
      have he (j : Fin (d*m) ⊕ Fin (d*m)) :
          Sum.elim (fun _ : Fin (d*m) => (δ : ℝ)) (fun _ : Fin (d*m) => (δ : ℝ)) j=δ := by
        cases j <;> rfl
      simpa only [he,scalarBlockSplitCoefficients_dot ρ σ hunit,ite_eq_right hik])
  have he (j : Fin (d*m) ⊕ Fin (d*m)) :
      Sum.elim (fun _ : Fin (d*m) => (δ : ℝ)) (fun _ : Fin (d*m) => (δ : ℝ)) j=δ := by
    cases j <;> rfl
  have hv (k : Fin d ⊕ Fin d) :
      (∑ j,(scalarBlockSplitCoefficients ρ σ k j)^2*
        Sum.elim (fun i : Fin (d*m) => (brownianMeshVariance (scalarBrownianAffineTime a δ) i : ℝ))
          (fun i : Fin (d*m) => (brownianMeshVariance (scalarBrownianAffineTime a δ) i : ℝ)) j).toNNReal =
        (m : ℝ≥0)*δ := by
    simp only [brownianMeshVariance_scalarBrownianAffineTime,he,pow_two,
      scalarBlockSplitCoefficients_dot ρ σ hunit,ite_true]
    change (((m : ℝ≥0)*δ : ℝ≥0) : ℝ).toNNReal = _
    exact Real.toNNReal_coe
  simpa only [hv] using h

end SKConstants
