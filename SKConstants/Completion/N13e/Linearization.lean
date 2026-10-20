module

public import SKConstants.Completion.LGram.All

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13e
open GaussianProposal LC5 LGram NormedSpace InnerProductSpace

def energyLinearPart {k : ℕ} (EA EH : Matrix (Fin k) (Fin k) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin k)) : ℝ :=
  inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) (halfUpperTruncation EA) b) +
    inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) (fullUpperTruncation EH) s)

theorem energyLinearPart_padding {k m : ℕ} (EA EH : Matrix (Fin k) (Fin k) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin k)) :
    energyLinearPart (padMatrix m EA 0) (padMatrix m EH 0)
      (padVector m s) (padVector m eq) (padVector m b) (padVector m ev) =
      energyLinearPart EA EH s eq b ev := by
  simp only [energyLinearPart, padMatrix_halfUpper, padMatrix_fullUpper,
    padMatrix_apply, padVector_inner]

theorem upper_cholesky_quadratic_remainder
    (R : ℕ) (η : ℝ)
    (EA C H0 EH : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2^R)))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b -
      energyLinearPart EA EH s eq b ev| ≤ 1400 * ((R+1 : ℕ) : ℝ)^4 * η^2 := by
  obtain ⟨D, hDu, hDp, hDg, _, _, _, hbound⟩ :=
    exists_upper_cholesky_with_quadratic_energy_bound R η EA H0 EH s eq b ev
      hη hsmall hEA hsym hH0 hEH
  have hCD : C = D := upper_cholesky_unique C D hCu hDu hCp hDp (hCg.trans hDg.symm)
  change |queryEnergyNormalForm D (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b -
    energyLinearPart EA EH s eq b ev| ≤
      200 * ((R+1 : ℕ) : ℝ) * sevenErrorSum R EA EH s eq b ev at hbound
  rw [← hCD] at hbound
  have hQ := sevenErrorSum_le_of_operator_errors R η EA EH s eq b ev
    hη hEA hEH heq hev hs hb
  calc
    _ ≤ 200 * ((R+1 : ℕ) : ℝ) * sevenErrorSum R EA EH s eq b ev := hbound
    _ ≤ 200 * ((R+1 : ℕ) : ℝ) * (7 * ((R+1 : ℕ) : ℝ)^3 * η^2) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = _ := by ring

theorem upper_cholesky_quadratic_remainder_dim
    (R n : ℕ) (hdim : n = 2^R) (η : ℝ)
    (EA C H0 EH : Matrix (Fin n) (Fin n) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin n))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b -
      energyLinearPart EA EH s eq b ev| ≤ 1400 * ((R+1 : ℕ) : ℝ)^4 * η^2 := by
  subst n
  exact upper_cholesky_quadratic_remainder R η EA C H0 EH s eq b ev
    hη hsmall hEA hsym hCu hCp hCg hH0 hEH heq hev hs hb

theorem upper_cholesky_quadratic_remainder_padded
    (R k m : ℕ) (hdim : k+m = 2^R) (η : ℝ)
    (EA C H0 EH : Matrix (Fin k) (Fin k) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin k))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA) (hCunit : IsUnit C)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b -
      energyLinearPart EA EH s eq b ev| ≤ 1400 * ((R+1 : ℕ) : ℝ)^4 * η^2 := by
  have hgram : (padMatrix m C 1).transpose * padMatrix m C 1 =
      1 + padMatrix m EA 0 := by
    rw [padMatrix_transpose, padMatrix_mul, hCg]
    simpa only [one_mul, add_zero, padMatrix_add, padMatrix_one]
      using (padMatrix_add (m := m) 1 EA 1 0)
  have h := upper_cholesky_quadratic_remainder_dim R (k+m) hdim η
    (padMatrix m EA 0) (padMatrix m C 1) (padMatrix m H0 0) (padMatrix m EH 0)
    (padVector m s) (padVector m eq) (padVector m b) (padVector m ev)
    hη hsmall (by rwa [padMatrix_norm])
    (by rw [padMatrix_transpose, hsym]) (padMatrix_upper C hCu)
    (padMatrix_positive C hCp) hgram (padMatrix_strictLower H0 hH0)
    (by rwa [padMatrix_norm]) (by rwa [padVector_norm]) (by rwa [padVector_norm])
    (by rwa [padVector_norm]) (by rwa [padVector_norm])
  simpa only [← padMatrix_add, zero_add, ← padVector_add,
    query_energy_padding C (H0+EH) hCunit, padVector_inner,
    energyLinearPart_padding] using h

theorem projectedQueryEnergy_quadratic_remainder_padded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R k m : ℕ) (hdim : k+m = 2^R) (η : ℝ) (T g : Fin k → E) (x : E)
    (s b : EuclideanSpace ℝ (Fin k)) (H0 : Matrix (Fin k) (Fin k) ℝ)
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖familyGram T-1‖ ≤ η)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖familyCross T g-H0‖ ≤ η)
    (heq : ‖familyCoordinates T x-s‖ ≤ η)
    (hev : ‖familyCoordinates g x-b‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |projectedQueryEnergy (gramSchmidtNormed ℝ T) g x - inner (𝕜 := ℝ) s b -
      energyLinearPart (familyGram T-1) (familyCross T g-H0)
        s (familyCoordinates T x-s) b (familyCoordinates g x-b)| ≤
      1400 * ((R+1 : ℕ) : ℝ)^4 * η^2 := by
  have hd : 1 ≤ ((R+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hηsmall : η ≤ 3/4 := by
    have hm := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ ((R+1 : ℕ) : ℝ)^2 by nlinarith) hη
    nlinarith
  have hGram := hEA.trans hηsmall
  have hsym : (familyGram T-1).transpose = familyGram T-1 := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, familyGram, Matrix.one_apply]
    rw [real_inner_comm]
    split_ifs <;> simp_all
  have hg : (gramSchmidtCholesky T).transpose*gramSchmidtCholesky T =
      1+(familyGram T-1) := by rw [gramSchmidtCholesky_gram T hGram]; abel
  have h := upper_cholesky_quadratic_remainder_padded R k m hdim η (familyGram T-1)
    (gramSchmidtCholesky T) H0 (familyCross T g-H0) s (familyCoordinates T x-s)
    b (familyCoordinates g x-b) hη hsmall hEA hsym (gramSchmidtCholesky_upper T)
    (gramSchmidtCholesky_positive T hGram) hg (gramSchmidtCholesky_isUnit T hGram)
    hH0 hEH heq hev hs hb
  rw [projectedQueryEnergy_eq_cholesky T g hGram x]
  simpa only [add_sub_cancel] using h

theorem actualPaper_query_energy_quadratic_remainder {Past : Type*}
    (r K R m : ℕ) (hdim : K+m = 2^R) (N η : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ)
    (s b : EuclideanSpace ℝ (Fin K)) (H0 : Matrix (Fin K) (Fin K) ℝ) :
    let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (paperTargetTrace r (r+K) target update K (a,1) z j)
    let g := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
      (fun l => paperEndpointTrace (r+K) K z j (.inl l))
    let x0 := (Real.sqrt N)⁻¹ • WithLp.toLp 2 x
    0 ≤ η → 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1 →
    ‖familyGram T-1‖ ≤ η → (∀ i j, i ≤ j → H0 i j = 0) →
    ‖familyCross T g-H0‖ ≤ η → ‖familyCoordinates T x0-s‖ ≤ η →
    ‖familyCoordinates g x0-b‖ ≤ η → ‖s‖ ≤ 1 → ‖b‖ ≤ 1 →
    |paperQueryEnergy r (r+K) N target update K (a,1) z x - inner (𝕜 := ℝ) s b -
      energyLinearPart (familyGram T-1) (familyCross T g-H0)
        s (familyCoordinates T x0-s) b (familyCoordinates g x0-b)| ≤
      1400 * ((R+1 : ℕ) : ℝ)^4 * η^2 := by
  dsimp only
  intro hη hsmall hEA hH0 hEH heq hev hs hb
  let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
    (paperTargetTrace r (r+K) target update K (a,1) z j)
  let U := fun j => WithLp.toLp 2
    (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
  have hd : 1 ≤ ((R+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hηsmall : η ≤ 3/4 := by
    have hm := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ ((R+1 : ℕ) : ℝ)^2 by nlinarith) hη
    nlinarith
  have hGram := hEA.trans hηsmall
  have hU : U = gramSchmidtNormed ℝ T := funext fun j =>
    actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z (Real.sqrt N)⁻¹
      (inv_pos.mpr (Real.sqrt_pos.mpr hN)) hGram j
  rw [paperQueryEnergy_eq_projected r K N hN]
  change |projectedQueryEnergy U _ _ - _ - _| ≤ _
  rw [hU]
  exact projectedQueryEnergy_quadratic_remainder_padded R K m hdim η T _ _ s b H0
    hη hsmall hEA hH0 hEH heq hev hs hb

open SKConstantsOAI.ZeroTemperatureSK

def sourceEnergyLinearPart {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : ℝ :=
  let N : ℝ := (r+K:ℕ)
  let T := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
    (paperTargetTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
      (M1.Initial δ r K u.2,1) (M1.Original δ r K u.2) j)
  let g := fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
    (fun l => paperEndpointTrace (r+K) K (M1.Original δ r K u.2) j (.inl l))
  let x := (Real.sqrt N)⁻¹ • WithLp.toLp 2 (fun i => scalarHiddenSign (u.1 i))
  let s := populationTargetSpin W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))
  let b := populationQuerySpin W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))
  let H0 := populationCross W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) K (growingQueryTime δ (K+1))
  energyLinearPart (familyGram T-1) (familyCross T g-H0)
    s (familyCoordinates T x-s) b (familyCoordinates g x-b)

theorem actualSource_query_energy_quadratic_remainder
    {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K R m : ℕ) (hdim : K+m=2^R)
    (hN : 0 < r+K) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : 16 * ((R+1:ℕ):ℝ)^2 * η ≤ 1)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hu : u ∈ sourceWholeGramEvent W β hβ δ r K η) :
    |paperQueryEnergy r (r+K) (r+K:ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (M1.Initial δ r K u.2,1) (M1.Original δ r K u.2) (fun i => scalarHiddenSign (u.1 i)) -
      inner (𝕜 := ℝ)
        (populationTargetSpin W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
          K (growingQueryTime δ (K+1)))
        (populationQuerySpin W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
          K (growingQueryTime δ (K+1))) - sourceEnergyLinearPart W β hβ δ r K u| ≤
      1400 * ((R+1:ℕ):ℝ)^4 * η^2 := by
  have h := actualSource_good_blocks W β hβ δ hδ r K η u hu
  exact actualPaper_query_energy_quadratic_remainder r K R m hdim (r+K:ℕ) η
    (Nat.cast_pos.mpr hN) _ _ _ _ _ _ _ _ hη hsmall h.1
    (populationCross_shifted_upper W W β hβ _ (growingQueryTime_strictMono δ hδ).monotone K _)
    h.2.1 h.2.2.1 h.2.2.2
    (populationTargetSpin_norm_le_one W W β hβ _ (growingQueryTime_strictMono δ hδ) _ K _)
    (populationQuerySpin_norm_le_one W W β hβ _ _
      ((growingQueryTime_strictMono δ hδ).comp (fun _ _ h => Nat.add_lt_add_right h 1)) K _)

end SKConstants.Completion.N13e
