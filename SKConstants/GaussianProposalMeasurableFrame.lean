module

public import SKConstants.GaussianProposalBasisAssembly
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[expose] def householderMatrix (v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then 1 else 0) - (2 * (dot v v)⁻¹) * v i * v j

theorem householderMatrix_orthogonal (v : ι → ℝ) (i j : ι) :
    dot (householderMatrix v i) (householderMatrix v j) = if i = j then 1 else 0 := by
  let a : ℝ := 2 * (dot v v)⁻¹
  have ha : a ^ 2 * dot v v = 2 * a := by
    by_cases hs : dot v v = 0
    · simp [a, hs]
    · dsimp [a]
      field_simp
  have hterm (k : ι) :
      householderMatrix v i k * householderMatrix v j k =
      (if k = i ∧ k = j then (1 : ℝ) else 0) -
        (a * v i) * (if k = j then v k else 0) -
        (a * v j) * (if k = i then v k else 0) +
        (a ^ 2 * v i * v j) * (v k * v k) := by
    by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp [householderMatrix, a, hik, hjk, eq_comm] <;> ring
  have hsum : dot (householderMatrix v i) (householderMatrix v j) =
      (if i = j then 1 else 0) - (a * v i) * v j - (a * v j) * v i +
        (a ^ 2 * v i * v j) * dot v v := by
    unfold dot
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp [ite_and]
  rw [hsum]
  calc
    _ = (if i = j then 1 else 0) - (2 * a - a ^ 2 * dot v v) * v i * v j := by ring
    _ = _ := by rw [ha]; ring

theorem householderMatrix_symmetric (v : ι → ℝ) : (householderMatrix v).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, householderMatrix]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [hij, Ne.symm hij]
    ring

@[expose] def completionFrame (p : ι) (u : ι → ℝ) : Matrix ι ι ℝ :=
  householderMatrix (fun j => canonicalBasis p j - u j)

theorem completionFrame_orthogonal (p : ι) (u : ι → ℝ) (i j : ι) :
    dot (completionFrame p u i) (completionFrame p u j) = if i = j then 1 else 0 :=
  householderMatrix_orthogonal _ i j

theorem completionFrame_designated_row (p : ι) (u : ι → ℝ) (hu : dot u u = 1) (j : ι) :
    completionFrame p u p j = u j := by
  let v : ι → ℝ := fun l => canonicalBasis p l - u l
  have hD : dot v v = 2 * (1 - u p) := by
    change (canonicalBasis p - u) ⬝ᵥ (canonicalBasis p - u) = _
    have hnorm : u ⬝ᵥ u = 1 := hu
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hnorm]
    simp [canonicalBasis, dotProduct]
    ring
  have hvp : v p = 1 - u p := by simp [v, canonicalBasis]
  by_cases hs : dot v v = 0
  · have hvzero : v j = 0 := by
      have hsum : ∑ l, v l * v l = 0 := hs
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun l (_ : l ∈ Finset.univ) => mul_self_nonneg (v l))).mp hsum
      exact (mul_eq_zero.mp (hz j (Finset.mem_univ j))).elim id id
    have hj : canonicalBasis p j = u j := sub_eq_zero.mp hvzero
    change householderMatrix v p j = u j
    simp only [householderMatrix, hs, inv_zero, mul_zero, zero_mul, sub_zero]
    exact hj
  · have havp : (2 * (dot v v)⁻¹) * v p = 1 := by
      calc
        _ = (dot v v) * (dot v v)⁻¹ := by rw [hD, hvp]; ring
        _ = 1 := mul_inv_cancel₀ hs
    change (if p = j then 1 else 0) - (2 * (dot v v)⁻¹) * v p * v j = u j
    rw [havp, one_mul]
    change canonicalBasis p j - (canonicalBasis p j - u j) = u j
    ring

@[expose] def queryFrameUpdate (basis : Matrix ι ι ℝ) (p : ι) (u : ι → ℝ) : Matrix ι ι ℝ :=
  completionFrame p (basis *ᵥ u) * basis

theorem queryFrameUpdate_orthogonal (basis : Matrix ι ι ℝ) (p : ι) (u : ι → ℝ)
    (hB : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) (i j : ι) :
    dot (queryFrameUpdate basis p u i) (queryFrameUpdate basis p u j) =
      if i = j then 1 else 0 := by
  let H := completionFrame p (basis *ᵥ u)
  have hBB : basis * basisᵀ = 1 := by
    ext k l
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using hB k l
  have hHH : H * Hᵀ = 1 := by
    ext k l
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using
      completionFrame_orthogonal p (basis *ᵥ u) k l
  have hprod : (H * basis) * (H * basis)ᵀ = 1 := by
    calc
      _ = (H * (basis * basisᵀ)) * Hᵀ := by rw [Matrix.transpose_mul]; noncomm_ring
      _ = 1 := by rw [hBB, Matrix.mul_one, hHH]
  have hentry := congrArg (fun M : Matrix ι ι ℝ => M i j) hprod
  simpa only [queryFrameUpdate, H, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, dot] using hentry

theorem queryFrameUpdate_designated_row (basis : Matrix ι ι ℝ) (p : ι) (u : ι → ℝ)
    (hB : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0)
    (hu : dot u u = 1) (j : ι) : queryFrameUpdate basis p u p j = u j := by
  have hcols : basisᵀ * basis = 1 := by
    ext k l
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using
      orthogonalBasis_columns basis hB k l
  have hback : (basis *ᵥ u) ᵥ* basis = u := by
    rw [Matrix.vecMul_mulVec, hcols, Matrix.vecMul_one]
  have hw : dot (basis *ᵥ u) (basis *ᵥ u) = 1 := by
    change (basis *ᵥ u) ⬝ᵥ (basis *ᵥ u) = 1
    rw [Matrix.dotProduct_mulVec, hback]
    exact hu
  unfold queryFrameUpdate
  rw [Matrix.mul_apply]
  simp_rw [completionFrame_designated_row p (basis *ᵥ u) hw]
  exact congrArg (fun v : ι → ℝ => v j) hback

theorem queryFrameUpdate_preserves_row (basis : Matrix ι ι ℝ) (p : ι) (u : ι → ℝ)
    (i : ι) (hip : i ≠ p) (horth : dot (basis i) u = 0) (j : ι) :
    queryFrameUpdate basis p u i j = basis i j := by
  have hw : (basis *ᵥ u) i = 0 := horth
  have hrow (k : ι) : completionFrame p (basis *ᵥ u) i k = canonicalBasis i k := by
    simp [completionFrame, householderMatrix, canonicalBasis, Ne.symm hip, hw]
  unfold queryFrameUpdate
  rw [Matrix.mul_apply]
  simp_rw [hrow]
  simp [canonicalBasis]

@[expose] def finiteQueryFrame (n : ℕ) (queries : ℕ → Fin n → ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | K + 1 => if h : K < n then
      queryFrameUpdate (finiteQueryFrame n queries K) ⟨K, h⟩ (queries K)
    else finiteQueryFrame n queries K

theorem finiteQueryFrame_completed (n : ℕ) (queries : ℕ → Fin n → ℝ)
    (K : ℕ) (hK : K ≤ n)
    (hunit : ∀ k, k < K → dot (queries k) (queries k) = 1)
    (horth : ∀ k l, k < l → l < K → dot (queries k) (queries l) = 0) :
    (∀ i j, dot (finiteQueryFrame n queries K i) (finiteQueryFrame n queries K j) =
      if i = j then 1 else 0) ∧
    (∀ i : Fin n, i.val < K → ∀ j, finiteQueryFrame n queries K i j = queries i.val j) := by
  induction K with
  | zero =>
    constructor
    · intro i j
      simp [finiteQueryFrame, dot, Matrix.one_apply]
    · intro i hi
      omega
  | succ K ih =>
    have hkn : K < n := by omega
    obtain ⟨hB, hprefix⟩ := ih (by omega)
      (fun k hk => hunit k (by omega)) (fun k l hkl hl => horth k l hkl (by omega))
    let p : Fin n := ⟨K, hkn⟩
    have hstep : finiteQueryFrame n queries (K + 1) =
        queryFrameUpdate (finiteQueryFrame n queries K) p (queries K) := by
      simp [finiteQueryFrame, p, hkn]
    rw [hstep]
    constructor
    · exact queryFrameUpdate_orthogonal _ p (queries K) hB
    · intro i hi j
      by_cases hipval : i.val = K
      · have hip : i = p := Fin.ext hipval
        subst i
        exact queryFrameUpdate_designated_row _ p (queries K) hB (hunit K (by omega)) j
      · have hilt : i.val < K := by omega
        have hip : i ≠ p := by
          intro heq
          exact hipval (congrArg Fin.val heq)
        have hkilled : dot (finiteQueryFrame n queries K i) (queries K) = 0 := by
          have hrow : finiteQueryFrame n queries K i = queries i.val :=
            funext (hprefix i hilt)
          rw [hrow]
          exact horth i.val K hilt (by omega)
        rw [queryFrameUpdate_preserves_row _ p (queries K) i hip hkilled]
        exact hprefix i hilt j

theorem finiteQueryFrame_prefix_eq (n : ℕ) (queries other : ℕ → Fin n → ℝ) (K : ℕ)
    (hprefix : ∀ k, k < K → queries k = other k) :
    finiteQueryFrame n queries K = finiteQueryFrame n other K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hprev : finiteQueryFrame n queries K = finiteQueryFrame n other K :=
      ih (fun k hk => hprefix k (by omega))
    have hquery : queries K = other K := hprefix K (by omega)
    by_cases hkn : K < n
    · simp only [finiteQueryFrame, dite_eq_left hkn, hprev, hquery]
    · simp only [finiteQueryFrame, dite_eq_right hkn, hprev]

variable {Past : Type*} [MeasurableSpace Past]

theorem completionFrame_measurable (p : ι) (u : Past → ι → ℝ)
    (hu : ∀ j, Measurable (fun a => u a j)) (i j : ι) :
    Measurable (fun a => completionFrame p (u a) i j) := by
  unfold completionFrame householderMatrix dot
  fun_prop

theorem queryFrameUpdate_measurable (basis : Past → Matrix ι ι ℝ)
    (p : ι) (u : Past → ι → ℝ)
    (hB : ∀ i j, Measurable (fun a => basis a i j))
    (hu : ∀ i, Measurable (fun a => u a i)) (i j : ι) :
    Measurable (fun a => queryFrameUpdate (basis a) p (u a) i j) := by
  have hw (k : ι) : Measurable (fun a => (basis a *ᵥ u a) k) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hH (k l : ι) : Measurable (fun a => completionFrame p (basis a *ᵥ u a) k l) :=
    completionFrame_measurable p (fun a => basis a *ᵥ u a) hw k l
  unfold queryFrameUpdate
  simp only [Matrix.mul_apply]
  fun_prop

theorem finiteQueryFrame_measurable (n : ℕ) (queries : Past → ℕ → Fin n → ℝ)
    (hqueries : ∀ K i, Measurable (fun a => queries a K i))
    (K : ℕ) (i j : Fin n) :
    Measurable (fun a => finiteQueryFrame n (queries a) K i j) := by
  induction K generalizing i j with
  | zero =>
    change Measurable (fun _ : Past => (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    exact measurable_const
  | succ K ih =>
    by_cases hkn : K < n
    · simp only [finiteQueryFrame, dite_eq_left hkn]
      exact queryFrameUpdate_measurable (fun a => finiteQueryFrame n (queries a) K)
        ⟨K, hkn⟩ (fun a => queries a K) ih (hqueries K) i j
    · simpa only [finiteQueryFrame, dite_eq_right hkn] using ih i j

theorem completedQuery_actual_GOE_law (μ : Measure Past) [SFinite μ]
    (sigma : ℝ) (p : ι) (u : Past → ι → ℝ)
    (hu : ∀ j, Measurable (fun a => u a j)) :
    (μ.prod (gaussianUpperLaw sigma ι)).map
      (fun x : Past × (UpperPair ι → ℝ) =>
        (x.1, basisAssembly (completionFrame p (u x.1)) x.2)) =
      μ.prod ((primitiveGaussian (ι × ι)).map (goeMatrix sigma)) := by
  exact adaptiveAssembly_joint_law μ sigma (fun a => completionFrame p (u a))
    (completionFrame_measurable p u hu) (fun a => completionFrame_orthogonal p (u a))

end SKConstants.GaussianProposal
