module

public import SKBarriers2.Corner.TerminalJets
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

noncomputable section
open scoped BigOperators ContDiff Topology
open Set MeasureTheory ProbabilityTheory

namespace SKBarriers2.Corner

def squareJetPolynomial (β : ℝ) (α : ℝ → ℝ) (j : ℕ) (t z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    jet β α (i + 1) t z * jet β α (j - i + 1) t z

def jetTimeDrift (β : ℝ) (α : ℝ → ℝ) (j : ℕ) (t z : ℝ) : ℝ :=
  -(β ^ 2 / 2) * (jet β α (j + 2) t z + α t * squareJetPolynomial β α j t z)

theorem iteratedDeriv_jet_one (β : ℝ) (α : ℝ → ℝ) (j : ℕ) (t z : ℝ) :
    iteratedDeriv j (fun y => jet β α 1 t y) z = jet β α (j + 1) t z := by
  change iteratedDeriv j (iteratedDeriv 1 (Phi β α t)) z =
    iteratedDeriv (j + 1) (Phi β α t) z
  rw [iteratedDeriv_one, iteratedDeriv_succ']

theorem scalarData_jet_hasDerivAt {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (z : ℝ) :
    HasDerivAt (fun y => jet β (cdf (D.μ : Measure ℝ)) j t y)
      (jet β (cdf (D.μ : Measure ℝ)) (j + 1) t z) z := by
  change HasDerivAt (iteratedDeriv j (Phi β (cdf (D.μ : Measure ℝ)) t))
    (iteratedDeriv (j + 1) (Phi β (cdf (D.μ : Measure ℝ)) t) z) z
  rw [iteratedDeriv_succ]
  exact ((scalarData_phi_contDiff D ht).differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top j) z).hasDerivAt

theorem scalarData_squareJet_eq {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (z : ℝ) :
    iteratedDeriv j (fun y => jet β (cdf (D.μ : Measure ℝ)) 1 t y ^ 2) z =
      squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z := by
  have hs : ContDiff ℝ j (fun y => jet β (cdf (D.μ : Measure ℝ)) 1 t y) := by
    simpa only [jet, iteratedDeriv_one] using
      ((contDiff_infty_iff_deriv.mp (scalarData_phi_contDiff D ht)).2.of_le (by simp) :
        ContDiff ℝ j (deriv (Phi β (cdf (D.μ : Measure ℝ)) t)))
  simp only [pow_two]
  rw [iteratedDeriv_fun_mul hs.contDiffAt hs.contDiffAt]
  simp only [squareJetPolynomial, iteratedDeriv_jet_one]

private theorem physical_time {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) D.q) : t ∈ Icc (0 : ℝ) 1 := by
  exact ⟨ht.1.le, ht.2.le.trans D.q_mem.2.le⟩

theorem scalarData_time_hasDerivAt {β : ℝ} (D : ScalarData β) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) D.q) (j : ℕ) (z : ℝ) :
    HasDerivAt (fun τ => jet β (cdf (D.μ : Measure ℝ)) j τ z)
      (jetTimeDrift β (cdf (D.μ : Measure ℝ)) j t z) t := by
  simpa only [jetTimeDrift, scalarData_squareJet_eq D (physical_time D ht)] using
    D.time_deriv j t ht z

def squareJetCoefficient (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)

theorem squareJetCoefficient_nonneg (j : ℕ) : 0 ≤ squareJetCoefficient j := by
  exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)

theorem squareJetPolynomial_bound {β : ℝ} (D : ScalarData β) (j : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    |squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z| ≤
      squareJetCoefficient j * scalarTerminalJetBound D (j + 2) ^ 2 := by
  let B : ℝ := scalarTerminalJetBound D (j + 2)
  have hB : 0 ≤ B := scalarTerminalJetBound_nonneg D _
  calc
    |squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z| ≤
        ∑ i ∈ Finset.range (j + 1), |(j.choose i : ℝ) *
          jet β (cdf (D.μ : Measure ℝ)) (i + 1) t z *
          jet β (cdf (D.μ : Measure ℝ)) (j - i + 1) t z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (j.choose i : ℝ) * B * B := by
          gcongr
          · exact scalarData_jet_le D (by omega) (by omega) ht z
          · exact scalarData_jet_le D (by omega) (by omega) ht z
        _ = (j.choose i : ℝ) * B ^ 2 := by ring
    _ = squareJetCoefficient j * B ^ 2 := by rw [squareJetCoefficient, Finset.sum_mul]

def jetTimeBound {β : ℝ} (D : ScalarData β) (j : ℕ) : ℝ :=
  β ^ 2 / 2 * (scalarTerminalJetBound D (j + 2) +
    squareJetCoefficient j * scalarTerminalJetBound D (j + 2) ^ 2)

theorem jetTimeBound_nonneg {β : ℝ} (D : ScalarData β) (j : ℕ) :
    0 ≤ jetTimeBound D j := by
  exact mul_nonneg (div_nonneg (sq_nonneg β) (by norm_num))
    (add_nonneg (scalarTerminalJetBound_nonneg D _) (mul_nonneg
      (squareJetCoefficient_nonneg j) (sq_nonneg _)))

theorem jetTimeDrift_bound {β : ℝ} (D : ScalarData β) (j : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    |jetTimeDrift β (cdf (D.μ : Measure ℝ)) j t z| ≤ jetTimeBound D j := by
  rw [jetTimeDrift, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ β ^ 2 / 2)
  calc
    _ ≤ |jet β (cdf (D.μ : Measure ℝ)) (j + 2) t z| +
        |cdf (D.μ : Measure ℝ) t * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z| :=
      abs_add_le _ _
    _ ≤ scalarTerminalJetBound D (j + 2) +
        squareJetCoefficient j * scalarTerminalJetBound D (j + 2) ^ 2 := by
      apply add_le_add (scalarData_jet_le D (by omega) le_rfl ht z)
      rw [abs_mul, abs_of_nonneg (cdf_nonneg _ _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cdf_le_one _ _)).trans
        (squareJetPolynomial_bound D j ht z)

theorem scalarData_jet_time_sub_le {β : ℝ} (D : ScalarData β) (j : ℕ)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) D.q) (ht : t ∈ Ioo (0 : ℝ) D.q) (z : ℝ) :
    |jet β (cdf (D.μ : Measure ℝ)) j t z - jet β (cdf (D.μ : Measure ℝ)) j s z| ≤
      jetTimeBound D j * |t - s| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo (0 : ℝ) D.q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun τ hτ => (scalarData_time_hasDerivAt D hτ j z).hasDerivWithinAt)
      (fun τ hτ => by
        simpa only [Real.norm_eq_abs] using jetTimeDrift_bound D j (physical_time D hτ) z)
      hs ht

theorem scalarData_jet_timeShift {β : ℝ} (D : ScalarData β) (j : ℕ)
    {s h : ℝ} (hs : s ∈ Ioo (0 : ℝ) D.q) (hh : 0 ≤ h) (ht : s + 4 * h < D.q)
    (z : ℝ) :
    |jet β (cdf (D.μ : Measure ℝ)) j (s + 4 * h) z -
      jet β (cdf (D.μ : Measure ℝ)) j s z| ≤ (4 * jetTimeBound D j) * h := by
  have H := scalarData_jet_time_sub_le D j hs ⟨by linarith [hs.1], ht⟩ z
  calc
    _ ≤ jetTimeBound D j * |s + 4 * h - s| := H
    _ = (4 * jetTimeBound D j) * h := by
      rw [add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ 4 * h)]
      ring

theorem scalarData_jet_timeShift_hasDerivAt {β : ℝ} (D : ScalarData β) (j : ℕ)
    {s h : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    HasDerivAt (fun y => jet β (cdf (D.μ : Measure ℝ)) j (s + 4 * h) y -
        jet β (cdf (D.μ : Measure ℝ)) j s y)
      (jet β (cdf (D.μ : Measure ℝ)) (j + 1) (s + 4 * h) z -
        jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z) z := by
  exact (scalarData_jet_hasDerivAt D ht j z).sub (scalarData_jet_hasDerivAt D hs j z)

def jetTimeEnvelope {β : ℝ} (D : ScalarData β) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), jetTimeBound D j

theorem jetTimeEnvelope_nonneg {β : ℝ} (D : ScalarData β) (r : ℕ) :
    0 ≤ jetTimeEnvelope D r := by
  exact Finset.sum_nonneg (fun j _ => jetTimeBound_nonneg D j)

theorem jetTimeBound_le_envelope {β : ℝ} (D : ScalarData β) {j r : ℕ} (hj : j ≤ r) :
    jetTimeBound D j ≤ jetTimeEnvelope D r := by
  exact Finset.single_le_sum (fun i _ => jetTimeBound_nonneg D i)
    (Finset.mem_range.mpr (by omega))

private theorem product_time_sub_le {a b c d B M δ : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (ha : |a| ≤ B) (hd : |d| ≤ B) (hac : |a - c| ≤ M * δ)
    (hbd : |b - d| ≤ M * δ) : |a * b - c * d| ≤ (2 * B * M) * δ := by
  calc
    |a * b - c * d| = |a * (b - d) + (a - c) * d| := by ring_nf
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = |a| * |b - d| + |a - c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ B * (M * δ) + (M * δ) * B := by gcongr
    _ = (2 * B * M) * δ := by ring

theorem squareJetPolynomial_time_sub_le {β : ℝ} (D : ScalarData β) (j : ℕ)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) D.q) (ht : t ∈ Ioo (0 : ℝ) D.q) (z : ℝ) :
    |squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z -
      squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z| ≤
      (squareJetCoefficient j * (2 * scalarTerminalJetBound D (j + 2) *
        jetTimeEnvelope D (j + 2))) * |t - s| := by
  let B : ℝ := scalarTerminalJetBound D (j + 2)
  let M : ℝ := jetTimeEnvelope D (j + 2)
  have hB : 0 ≤ B := scalarTerminalJetBound_nonneg D _
  have hM : 0 ≤ M := jetTimeEnvelope_nonneg D _
  have hjets (n : ℕ) (hn : n ≤ j + 2) :
      |jet β (cdf (D.μ : Measure ℝ)) n t z -
        jet β (cdf (D.μ : Measure ℝ)) n s z| ≤ M * |t - s| :=
    (scalarData_jet_time_sub_le D n hs ht z).trans
      (mul_le_mul_of_nonneg_right (jetTimeBound_le_envelope D hn) (abs_nonneg _))
  simp only [squareJetPolynomial, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), |(j.choose i : ℝ) *
        jet β (cdf (D.μ : Measure ℝ)) (i + 1) t z *
        jet β (cdf (D.μ : Measure ℝ)) (j - i + 1) t z -
        (j.choose i : ℝ) * jet β (cdf (D.μ : Measure ℝ)) (i + 1) s z *
        jet β (cdf (D.μ : Measure ℝ)) (j - i + 1) s z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ((2 * B * M) * |t - s|) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [mul_assoc, mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact product_time_sub_le hB hM (abs_nonneg _)
        (scalarData_jet_le D (by omega) (by omega) (physical_time D ht) z)
        (scalarData_jet_le D (by omega) (by omega) (physical_time D hs) z)
        (hjets (i + 1) (by omega)) (hjets (j - i + 1) (by omega))
    _ = (squareJetCoefficient j * (2 * B * M)) * |t - s| := by
      rw [← Finset.sum_mul, ← mul_assoc]
      rfl

def jetTimeDriftLipschitz {β : ℝ} (D : ScalarData β) (j : ℕ) (A : ℝ) : ℝ :=
  β ^ 2 / 2 * (jetTimeEnvelope D (j + 2) + squareJetCoefficient j *
    (A * scalarTerminalJetBound D (j + 2) ^ 2 +
      2 * scalarTerminalJetBound D (j + 2) * jetTimeEnvelope D (j + 2)))

theorem jetTimeDriftLipschitz_nonneg {β : ℝ} (D : ScalarData β) (j : ℕ)
    {A : ℝ} (hA : 0 ≤ A) : 0 ≤ jetTimeDriftLipschitz D j A := by
  dsimp only [jetTimeDriftLipschitz]
  have hB := scalarTerminalJetBound_nonneg D (j + 2)
  have hM := jetTimeEnvelope_nonneg D (j + 2)
  have hS := squareJetCoefficient_nonneg j
  positivity

theorem jetTimeDrift_time_sub_le {β : ℝ} (D : ScalarData β) (j : ℕ)
    {A s t : ℝ} (hA : 0 ≤ A)
    (hs : s ∈ Ioo (0 : ℝ) D.q) (ht : t ∈ Ioo (0 : ℝ) D.q)
    (hα : |cdf (D.μ : Measure ℝ) t - cdf (D.μ : Measure ℝ) s| ≤ A * |t - s|) (z : ℝ) :
    |jetTimeDrift β (cdf (D.μ : Measure ℝ)) j t z -
      jetTimeDrift β (cdf (D.μ : Measure ℝ)) j s z| ≤
      jetTimeDriftLipschitz D j A * |t - s| := by
  let B : ℝ := scalarTerminalJetBound D (j + 2)
  let M : ℝ := jetTimeEnvelope D (j + 2)
  let S : ℝ := squareJetCoefficient j
  have hB : 0 ≤ B := scalarTerminalJetBound_nonneg D _
  have hM : 0 ≤ M := jetTimeEnvelope_nonneg D _
  have hS : 0 ≤ S := squareJetCoefficient_nonneg j
  have hJ : |jet β (cdf (D.μ : Measure ℝ)) (j + 2) t z -
      jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z| ≤ M * |t - s| :=
    (scalarData_jet_time_sub_le D (j + 2) hs ht z).trans
      (mul_le_mul_of_nonneg_right (jetTimeBound_le_envelope D le_rfl) (abs_nonneg _))
  have hP := squareJetPolynomial_time_sub_le D j hs ht z
  have hPs := squareJetPolynomial_bound D j (physical_time D hs) z
  have hprod : |cdf (D.μ : Measure ℝ) t * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z -
      cdf (D.μ : Measure ℝ) s * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z| ≤
      (S * (A * B ^ 2 + 2 * B * M)) * |t - s| := by
    calc
      _ = |cdf (D.μ : Measure ℝ) t *
          (squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z -
            squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z) +
          (cdf (D.μ : Measure ℝ) t - cdf (D.μ : Measure ℝ) s) *
            squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z| := by ring_nf
      _ ≤ |cdf (D.μ : Measure ℝ) t| *
          |squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z -
            squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z| +
          |cdf (D.μ : Measure ℝ) t - cdf (D.μ : Measure ℝ) s| *
            |squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z| := by
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
      _ ≤ 1 * ((S * (2 * B * M)) * |t - s|) + (A * |t - s|) * (S * B ^ 2) := by
        gcongr
        · rw [abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
      _ = (S * (A * B ^ 2 + 2 * B * M)) * |t - s| := by ring
  rw [jetTimeDrift, jetTimeDrift, ← mul_sub, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
  calc
    _ ≤ β ^ 2 / 2 * (|jet β (cdf (D.μ : Measure ℝ)) (j + 2) t z -
        jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z| +
        |cdf (D.μ : Measure ℝ) t * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z -
          cdf (D.μ : Measure ℝ) s * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ β ^ 2 / 2)
      calc
        _ = |(jet β (cdf (D.μ : Measure ℝ)) (j + 2) t z -
            jet β (cdf (D.μ : Measure ℝ)) (j + 2) s z) +
            (cdf (D.μ : Measure ℝ) t * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j t z -
              cdf (D.μ : Measure ℝ) s * squareJetPolynomial β (cdf (D.μ : Measure ℝ)) j s z)| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ β ^ 2 / 2 * (M * |t - s| + (S * (A * B ^ 2 + 2 * B * M)) * |t - s|) := by
      gcongr
    _ = jetTimeDriftLipschitz D j A * |t - s| := by
      dsimp only [jetTimeDriftLipschitz, B, M, S]
      ring

theorem scalarData_cdf_time_lipschitz {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ Icc l u, ∀ t ∈ Icc l u,
      |cdf (D.μ : Measure ℝ) t - cdf (D.μ : Measure ℝ) s| ≤ A * |t - s| := by
  have hsub : Icc l u ⊆ Ioo (0 : ℝ) D.q :=
    fun _ ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hu⟩
  obtain ⟨A, hA⟩ := (D.smooth.mono hsub).exists_lipschitzOnWith
    (by simp : (∞ : ℕ∞ω) ≠ 0) (convex_Icc l u) isCompact_Icc
  refine ⟨A, A.coe_nonneg, ?_⟩
  intro s hs t ht
  simpa only [Real.dist_eq] using hA.dist_le_mul t ht s hs

private theorem time_taylor_remainder {f df : ℝ → ℝ} {s t L : ℝ}
    (hst : s ≤ t) (hL : 0 ≤ L)
    (hd : ∀ τ ∈ Icc s t, HasDerivAt f (df τ) τ)
    (hdf : ∀ τ ∈ Icc s t, |df τ - df s| ≤ L * |τ - s|) :
    |f t - f s - df s * (t - s)| ≤ L * (t - s) ^ 2 := by
  let R : ℝ → ℝ := fun τ => f τ - f s - df s * (τ - s)
  have hR (τ : ℝ) (hτ : τ ∈ Icc s t) : HasDerivAt R (df τ - df s) τ := by
    simpa only [R, Pi.sub_apply, id_eq, mul_one] using! ((hd τ hτ).sub_const (f s)).sub
      (((hasDerivAt_id τ).sub_const s).const_mul (df s))
  have hbound (τ : ℝ) (hτ : τ ∈ Icc s t) : |df τ - df s| ≤ L * (t - s) := by
    apply (hdf τ hτ).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hτ.1)]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hτ.2 s) hL
  have H := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun τ hτ => (hR τ hτ).hasDerivWithinAt)
    (fun τ hτ => by simpa only [Real.norm_eq_abs] using hbound τ hτ)
    (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  simpa only [R, sub_self, mul_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst), mul_assoc, ← pow_two] using H

theorem scalarData_jet_timeTaylor_uniform {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (j : ℕ) (s h z : ℝ),
      s ∈ Icc l u → 0 ≤ h → s + 4 * h ≤ u →
      |jet β (cdf (D.μ : Measure ℝ)) j (s + 4 * h) z -
        jet β (cdf (D.μ : Measure ℝ)) j s z -
        jetTimeDrift β (cdf (D.μ : Measure ℝ)) j s z * (4 * h)| ≤ C j * h ^ 2 := by
  obtain ⟨A, hA, hα⟩ := scalarData_cdf_time_lipschitz D hl hu
  refine ⟨fun j => 16 * jetTimeDriftLipschitz D j A,
    fun j => mul_nonneg (by norm_num) (jetTimeDriftLipschitz_nonneg D j hA), ?_⟩
  intro j s h z hs hh ht
  have hst : s ≤ s + 4 * h := by linarith
  have hsub : Icc s (s + 4 * h) ⊆ Icc l u :=
    fun _ hτ => ⟨hs.1.trans hτ.1, hτ.2.trans ht⟩
  have hphys (τ : ℝ) (hτ : τ ∈ Icc l u) : τ ∈ Ioo (0 : ℝ) D.q :=
    ⟨hl.trans_le hτ.1, hτ.2.trans_lt hu⟩
  have H := time_taylor_remainder hst (jetTimeDriftLipschitz_nonneg D j hA)
    (fun τ hτ => scalarData_time_hasDerivAt D (hphys τ (hsub hτ)) j z)
    (fun τ hτ => jetTimeDrift_time_sub_le D j hA (hphys s hs) (hphys τ (hsub hτ))
      (hα s hs τ (hsub hτ)) z)
  rw [add_sub_cancel_left] at H
  exact H.trans_eq (by ring)

def secondJetTimeCoefficient (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) : ℝ :=
  jet β α 4 s z + 2 * α s * jet β α 2 s z ^ 2 +
    2 * α s * jet β α 1 s z * jet β α 3 s z

def thirdJetTimeCoefficient (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) : ℝ :=
  jet β α 5 s z + 6 * α s * jet β α 2 s z * jet β α 3 s z +
    2 * α s * jet β α 1 s z * jet β α 4 s z

theorem squareJetPolynomial_two (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) :
    squareJetPolynomial β α 2 s z =
      2 * (jet β α 2 s z ^ 2 + jet β α 1 s z * jet β α 3 s z) := by
  norm_num [squareJetPolynomial, Finset.sum_range_succ]
  ring

theorem squareJetPolynomial_three (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) :
    squareJetPolynomial β α 3 s z =
      6 * jet β α 2 s z * jet β α 3 s z + 2 * jet β α 1 s z * jet β α 4 s z := by
  norm_num [squareJetPolynomial, Finset.sum_range_succ]
  ring

theorem jetTimeDrift_two (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) :
    jetTimeDrift β α 2 s z = -(β ^ 2 / 2) * secondJetTimeCoefficient β α s z := by
  rw [jetTimeDrift, squareJetPolynomial_two, secondJetTimeCoefficient]
  ring

theorem jetTimeDrift_three (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) :
    jetTimeDrift β α 3 s z = -(β ^ 2 / 2) * thirdJetTimeCoefficient β α s z := by
  rw [jetTimeDrift, squareJetPolynomial_three, thirdJetTimeCoefficient]
  ring

theorem scalarData_timeShift_second_third_uniform {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s h z : ℝ),
      s ∈ Icc l u → 0 ≤ h → s + 4 * h ≤ u →
      (|jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z -
          jet β (cdf (D.μ : Measure ℝ)) 2 s z +
          2 * h * β ^ 2 * secondJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z| ≤ C * h ^ 2) ∧
      (|jet β (cdf (D.μ : Measure ℝ)) 3 (s + 4 * h) z -
          jet β (cdf (D.μ : Measure ℝ)) 3 s z +
          2 * h * β ^ 2 * thirdJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z| ≤ C * h ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := scalarData_jet_timeTaylor_uniform D hl hu
  refine ⟨C 2 + C 3, add_nonneg (hC 2) (hC 3), ?_⟩
  intro s h z hs hh ht
  have h₂ := hbound 2 s h z hs hh ht
  have h₃ := hbound 3 s h z hs hh ht
  rw [jetTimeDrift_two] at h₂
  rw [jetTimeDrift_three] at h₃
  have he₂ : jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z -
      jet β (cdf (D.μ : Measure ℝ)) 2 s z +
      2 * h * β ^ 2 * secondJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z =
      jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z -
      jet β (cdf (D.μ : Measure ℝ)) 2 s z -
      (-(β ^ 2 / 2) * secondJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z) * (4 * h) := by ring
  have he₃ : jet β (cdf (D.μ : Measure ℝ)) 3 (s + 4 * h) z -
      jet β (cdf (D.μ : Measure ℝ)) 3 s z +
      2 * h * β ^ 2 * thirdJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z =
      jet β (cdf (D.μ : Measure ℝ)) 3 (s + 4 * h) z -
      jet β (cdf (D.μ : Measure ℝ)) 3 s z -
      (-(β ^ 2 / 2) * thirdJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z) * (4 * h) := by ring
  constructor
  · rw [he₂]
    exact h₂.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hC 3)) (sq_nonneg h))
  · rw [he₃]
    exact h₃.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hC 2)) (sq_nonneg h))

theorem scalarData_secondJetTimeCoefficient_hasDerivAt {β : ℝ} (D : ScalarData β)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    HasDerivAt (secondJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s)
      (thirdJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z) z := by
  have h₁ := scalarData_jet_hasDerivAt D hs 1 z
  have h₂ := scalarData_jet_hasDerivAt D hs 2 z
  have h₃ := scalarData_jet_hasDerivAt D hs 3 z
  have h₄ := scalarData_jet_hasDerivAt D hs 4 z
  have H := (h₄.add ((h₂.pow 2).const_mul (2 * cdf (D.μ : Measure ℝ) s))).add
    (((h₁.mul h₃).const_mul (2 * cdf (D.μ : Measure ℝ) s)))
  convert H using 1
  · ext y
    dsimp only [secondJetTimeCoefficient, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · dsimp only [thirdJetTimeCoefficient]
    norm_num
    ring

theorem scalarData_timeShift_remainder_hasDerivAt {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    HasDerivAt (fun y => jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) y -
        jet β (cdf (D.μ : Measure ℝ)) 2 s y +
        2 * h * β ^ 2 * secondJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s y)
      (jet β (cdf (D.μ : Measure ℝ)) 3 (s + 4 * h) z -
        jet β (cdf (D.μ : Measure ℝ)) 3 s z +
        2 * h * β ^ 2 * thirdJetTimeCoefficient β (cdf (D.μ : Measure ℝ)) s z) z := by
  exact ((scalarData_jet_hasDerivAt D ht 2 z).sub
    (scalarData_jet_hasDerivAt D hs 2 z)).add
      ((scalarData_secondJetTimeCoefficient_hasDerivAt D hs z).const_mul (2 * h * β ^ 2))

end SKBarriers2.Corner
