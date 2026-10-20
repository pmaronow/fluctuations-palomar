module

public import SKBarriers2.Interfaces
public import SKBarriers2.Overshoot.Defs
public import OAI.Probability.SKBarriers.Hierarchy.HierarchyAtomCoordinates

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
open OAI OAI.SK OAI.SK.Analytic

namespace SKBarriers2

def fractionalBlockMass (M N k : ℕ) (s : ℝ) (w : Fin (k + 1) → ℝ) :
    Fin (blockDimension M N k) → ℝ :=
  fun i => s + weightedBlockMass M N k w i

private theorem hierarchyAtom_shift (n : ℕ) (m : Fin n → ℝ) (s u : ℝ)
    (j : Fin (n + 1)) :
    hierarchyAtom n (fun i => s + m i) (s + u) j =
      hierarchyAtom n m u j + if j = 0 then s else 0 := by
  induction n generalizing u with
  | zero => simp [hierarchyAtom, Fin.eq_zero j, add_comm]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [hierarchyAtom, Fin.lastCases_last]
      simp
    · simp only [hierarchyAtom, Fin.lastCases_castSucc]
      rw [ih]
      simp

theorem fractionalBlockMass_valid (M N k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (w : Fin (k + 1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hsum : ∑ b, w b = 1 - s) :
    (∀ i, fractionalBlockMass M N k s w i ∈ Icc (0 : ℝ) 1) ∧
      Monotone (fractionalBlockMass M N k s w) := by
  have hlo := massFromAtoms_nonneg _ _ (weightedBlockAtom_nonneg M N k w hw)
  have hhi := massFromAtoms_le_sum _ _ (weightedBlockAtom_nonneg M N k w hw)
  refine ⟨fun i => ⟨add_nonneg hs (hlo i), ?_⟩, ?_⟩
  · have H := hhi i
    rw [weightedBlockAtom_sum, hsum] at H
    change weightedBlockMass M N k w i ≤ 1 - s at H
    change s + weightedBlockMass M N k w i ≤ 1
    linarith
  · intro i j hij
    exact add_le_add_right
      (massFromAtoms_monotone _ _ (weightedBlockAtom_nonneg M N k w hw) hij) s

theorem hierarchyAtom_fractionalBlockMass (M N k : ℕ) (s : ℝ)
    (w : Fin (k + 1) → ℝ) (hsum : ∑ b, w b = 1 - s)
    (j : Fin (blockDimension M N k + 1)) :
    hierarchyAtom (blockDimension M N k) (fractionalBlockMass M N k s w) 1 j =
      weightedBlockAtom M N k w j + if j = 0 then s else 0 := by
  rw [show (1 : ℝ) = s + (1 - s) by ring]
  unfold fractionalBlockMass
  rw [hierarchyAtom_shift]
  congr 1
  rw [← hsum, ← weightedBlockAtom_sum M N k w]
  exact hierarchyAtom_massFromAtoms _ _ j

private theorem weightedBlockAtom_zero (M N k : ℕ) (hN : 0 < N)
    (w : Fin (k + 1) → ℝ) : weightedBlockAtom M N k w 0 = 0 := by
  unfold weightedBlockAtom
  apply Finset.sum_eq_zero
  intro b _
  apply ite_eq_right
  intro h
  have H := congrArg Fin.val h
  change M + (b.val + 1) * N = 0 at H
  have hp := Nat.mul_pos (Nat.succ_pos b.val) hN
  exact (Nat.ne_of_gt (Nat.add_pos_right M hp)) H

section Comparison
variable {S : Type} [Fintype S] [Nonempty S]
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fractionalBlockObservable_compare {M N k : ℕ} (hN : 0 < N)
    (s : ℝ) (hs : 0 ≤ s) (H : Fin M → S → ℝ)
    (F : Fin (k + 1) → Fin N → S → ℝ) (c : S → ℝ)
    (w : Fin (k + 1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hsum : ∑ b, w b = 1 - s)
    (A : ℝ) (C : Fin (k + 1) → ℝ)
    (hdiag : ∀ a, (1 / 2 : ℝ) * (∑ i, (H i a) ^ 2) -
      (1 / 2 : ℝ) * (∑ b, ∑ i, (F b i a) ^ 2) ≤ A)
    (hkernel : ∀ b a a', -C b ≤ (1 / 2 : ℝ) * (∑ i, H i a * H i a') -
      (1 / 2 : ℝ) * (∑ l, if l ≤ b then ∑ i, F l i a * F l i a' else 0)) :
    let n := blockDimension M N k
    let m := fractionalBlockMass M N k s w
    let I := blockInterpolationChoice M N k
    hierarchyPressure n m
      (affineLogPartition c (observableExponent n (blockObservable H F)
        (interpolationCoefficient n I 1))) 0 ≤
    hierarchyPressure n m
      (affineLogPartition c (observableExponent n (blockObservable H F)
        (interpolationCoefficient n I 0))) 0 + A + ∑ b, w b * C b := by
  have hm := fractionalBlockMass_valid M N k s hs w hw hsum
  have HC := observablePressure_covariance_comparison (blockDimension M N k)
    (blockObservable H F) c (fractionalBlockMass M N k s w)
    (blockInterpolationChoice M N k) hm.1 hm.2 A (weightedBlockAtom M N k C)
    (fun a => by simpa only [pow_two, blockObservable_covariance] using hdiag a)
    (fun j hj a a' => by
      by_cases hj0 : j = 0
      · subst j
        simp [weightedBlockAtom_zero M N k hN, partialObservableCovariance]
      · rw [hierarchyAtom_fractionalBlockMass M N k s w hsum,
          ite_eq_right hj0, add_zero] at hj
        obtain ⟨b, rfl⟩ := weightedBlockAtom_ne_zero M N k w j hj
        rw [weightedBlockAtom_at M N k C hN, blockObservable_partial_covariance]
        exact hkernel b a a')
  simp_rw [hierarchyAtom_fractionalBlockMass M N k s w hsum,
    add_mul, Finset.sum_add_distrib] at HC
  have hz : (∑ j : Fin (blockDimension M N k + 1),
      (if j = 0 then s else 0) * weightedBlockAtom M N k C j) = 0 := by
    simp [ite_mul, weightedBlockAtom_zero M N k hN]
  rw [hz, add_zero, weightedBlockAtom_sum_mul] at HC
  simpa only [weightedBlockAtom_at M N k C hN] using HC

theorem fractionalMatrixFiniteInterpolation_offset {M N d r k : ℕ}
    (hN : 0 < N) (hr : 0 < r) (β s : ℝ) (hs : 0 ≤ s)
    (B : Fin (k + 1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (H : Fin M → S → ℝ) (C : ℝ)
    (hcov : ∀ a a', (∑ u, H u a * H u a') =
      ((N : ℝ) * β ^ 2 / 2) * matrixSquare d (replicaCrossOverlap N d (X a) (X a')) - C)
    (D : Fin d → Fin d → ℝ)
    (hself : ∀ a, replicaCrossOverlap N d (X a) (X a) = D)
    (c : S → ℝ) (w : Fin (k + 1) → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hsum : ∑ b, w b = 1 - s) :
    let n := blockDimension M (N * r) k
    let F := matrixFieldObservables N d r k β B X
    let m := fractionalBlockMass M (N * r) k s w
    let I := blockInterpolationChoice M (N * r) k
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 1))) 0 + C * s / 2 ≤
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 0))) 0 +
      ((N : ℝ) * β ^ 2 / 4) *
        (matrixSquare d D - 2 * matrixInner d (factorPath d r k B (Fin.last k)) D +
          ∑ j, w j * matrixSquare d (factorPath d r k B j)) := by
  let K : ℝ := (N : ℝ) * β ^ 2 / 4
  have hK : 0 ≤ K := by positivity
  have HC := fractionalBlockObservable_compare (Nat.mul_pos hN hr) s hs H
    (matrixFieldObservables N d r k β B X) c w hw hsum
    (K * (matrixSquare d D - 2 * matrixInner d (factorPath d r k B (Fin.last k)) D) - C / 2)
    (fun j => K * matrixSquare d (factorPath d r k B j) + C / 2)
    (fun a => by
      simp only [pow_two]
      rw [hcov]
      have HF := matrixFieldObservables_prefix β B X (Fin.last k) a a
      simp only [Fin.le_last, ite_true] at HF
      rw [HF, hself a]
      dsimp only [K]
      ring_nf
      exact le_rfl)
    (fun j a a' => by
      rw [hcov, matrixFieldObservables_prefix]
      have HK := mul_le_mul_of_nonneg_left
        (matrixCovariance_lower d (replicaCrossOverlap N d (X a) (X a'))
          (factorPath d r k B j)) hK
      dsimp only [K] at HK ⊢
      nlinarith)
  have he : (∑ j, w j * (K * matrixSquare d (factorPath d r k B j) + C / 2)) =
      K * (∑ j, w j * matrixSquare d (factorPath d r k B j)) + (1 - s) * (C / 2) := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at HC
  dsimp only
  dsimp only [K] at HC
  linarith

end Comparison

section Endpoints
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_const_mass (n : ℕ) (s : ℝ) (hs : s ≠ 0)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPressure n (fun _ => s) f x =
      Real.log (∫ z, Real.exp (s * f z) ∂fiberGaussian n x) / s := by
  let A := hierarchyPressure n (fun _ => s) f x
  have hw : hierarchyPathWeight n (fun _ => s) f =ᵐ[fiberGaussian n x]
      (fun z => Real.exp (s * f z) / Real.exp (s * A)) := by
    filter_upwards [parameter_ae_fiberGaussian n x] with z hz
    rw [hierarchyPathWeight_const, hz, mul_sub, Real.exp_sub]
  have hZ : (∫ z, Real.exp (s * f z) ∂fiberGaussian n x) = Real.exp (s * A) := by
    have hn := (hierarchyPathWeight_normalized n (fun _ => s) f hf x).2
    rw [integral_congr_ae hw, integral_div] at hn
    exact (div_eq_one_iff_eq (Real.exp_ne_zero _)).mp hn
  rw [hZ, Real.log_exp, mul_div_cancel_left₀ A hs]

variable {S : Type} [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem fractionalBlockObservable_root_one {M N k : ℕ} (s : ℝ)
    (H : Fin M → S → ℝ) (F : Fin (k + 1) → Fin N → S → ℝ)
    (c : S → ℝ) (w : Fin (k + 1) → ℝ) :
    hierarchyPressure (blockDimension M N k) (fractionalBlockMass M N k s w)
      (affineLogPartition c (observableExponent (blockDimension M N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension M N k) (blockInterpolationChoice M N k) 1))) 0 =
    hierarchyPressure M (fun _ => s)
      (affineLogPartition c (fun a => coordinateLinear M (fun i => H i a))) 0 := by
  rw [hierarchyPressure_split]
  have he : (fun z => affineLogPartition c
      (observableExponent (blockDimension M N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension M N k) (blockInterpolationChoice M N k) 1))
          (parameterAppend M ((k + 1) * N) z)) =
      fun z => affineLogPartition c (fun a => coordinateLinear M (fun i => H i a))
        (cascadeRoot (E := ParameterSpace M) ((k + 1) * N) z) := by
    funext z
    simp only [affineLogPartition, blockObservable_endpoint_one,
      coordinateProjection_append_prefix, coordinateLinear_apply]
  rw [he, cascadePressure_root]
  simp only [fractionalBlockMass, weightedBlockMass_at_disorder, add_zero]

variable {A : Type} [Fintype A] [Nonempty A]

theorem fractionalSiteBlock_root_zero_le {M N r k : ℕ} (hN : 0 < N)
    (s : ℝ) (hs : 0 ≤ s) (e : S → Fin N → A) (he : Function.Injective e)
    (H : Fin M → S → ℝ) (V : Fin ((k + 1) * r) → A → ℝ)
    (c : A → ℝ) (w : Fin (k + 1) → ℝ) (hw : ∀ b, 0 ≤ w b) :
    hierarchyPressure (blockDimension M (N * r) k) (fractionalBlockMass M (N * r) k s w)
      (affineLogPartition (fun a => ∑ i, c (e a i))
        (observableExponent (blockDimension M (N * r) k)
          (blockObservable H (fun b p a => siteBlockObservables V b p (e a)))
          (interpolationCoefficient (blockDimension M (N * r) k)
            (blockInterpolationChoice M (N * r) k) 0))) 0 ≤
    (N : ℝ) * vectorHierarchy ((k + 1) * r) (fun j => s + siteBlockMass r k w j)
      V (siteValueTerminal c) 0 := by
  let L : (Fin N → A) → ParameterSpace (blockDimension M (N * r) k) →L[ℝ] ℝ :=
    fun a => ∑ i, embeddedSiteExponent (blockSiteEmbedding M N r k i) V (a i)
  have hL : observableExponent (blockDimension M (N * r) k)
      (blockObservable H (fun b p a => siteBlockObservables V b p (e a)))
      (interpolationCoefficient (blockDimension M (N * r) k)
        (blockInterpolationChoice M (N * r) k) 0) = L ∘ e := by
    funext a
    ext z
    rw [blockObservable_endpoint_zero]
    exact siteBlock_fields_sum V (e a) z
  rw [hL]
  have hmon := hierarchyPressure_mono (blockDimension M (N * r) k)
    (fractionalBlockMass M (N * r) k s w)
    (fun i => add_nonneg hs
      (massFromAtoms_nonneg _ _ (weightedBlockAtom_nonneg M (N * r) k w hw) i))
    (affineLogPartition_boundedDerivs (fun a => ∑ i, c (e a i)) (L ∘ e))
    (affineLogPartition_boundedDerivs (fun a : Fin N → A => ∑ i, c (a i)) L)
    (fun z => affineLogPartition_restrict e he (fun a : Fin N → A => ∑ i, c (a i)) L z) 0
  have ht := embeddedSites_tensorizes (fun i => blockSiteEmbedding M N r k i)
    (fun i => blockSiteEmbedding_strictMono M N r k i)
    (blockSiteOwner (D := M) (r := r) (k := k) ⟨0, hN⟩)
    (fun i j => blockSiteOwner_embedding ⟨0, hN⟩ i j)
    (fractionalBlockMass M (N * r) k s w) (fun j => s + siteBlockMass r k w j)
    (fun i j => congrArg (s + ·) (blockSiteEmbedding_mass M N r k w i j)) V c 0
  exact hmon.trans_eq (by simpa only [Fintype.card_fin, L] using ht)

theorem fractionalMatrixSK_endpoint (N d : ℕ) (β s : ℝ) (hs : s ≠ 0)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D)) :
    hierarchyPressure (Fintype.card (Edge N)) (fun _ => s)
      (affineLogPartition (fun _ : MatrixStates N d D => 0)
        (fun a => coordinateLinear (Fintype.card (Edge N))
          (fun u => matrixSKObservables N d β (fun a : MatrixStates N d D => a.val) u a))) 0 =
      Real.log (∫ J, constrainedPartition N d β D J ^ s ∂disorderLaw N) / s := by
  let := hD
  rw [hierarchyPressure_const_mass _ s hs _ (affineLogPartition_boundedDerivs _ _) 0]
  congr 2
  simp only [affineLogPartition, matrixSKObservables_exponent, zero_add]
  have he (z : ParameterSpace (Fintype.card (Edge N))) :
      Real.exp (s * Real.log (∑ a : MatrixStates N d D,
        Real.exp (β * ∑ b, hamiltonian (enumeratedDisorder N z) (fun i => a.val i b)))) =
      constrainedPartition N d β D (enumeratedDisorder N z) ^ s := by
    rw [constrainedPartition, Real.rpow_def_of_pos
      (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)]
    congr 1
    ring
  simp_rw [he]
  have H := enumeratedDisorder_measurePreserving N 0
  rw [← H.map_eq, integral_map H.measurable.aemeasurable]
  exact (Real.continuous_exp.comp ((matrixSKLogPartition_continuous N d β
    (fun a : MatrixStates N d D => a.val)).const_mul s)).aestronglyMeasurable.congr
    (ae_of_all _ fun J => by
      change Real.exp (s * Real.log (constrainedPartition N d β D J)) =
        constrainedPartition N d β D J ^ s
      have hp : 0 < constrainedPartition N d β D J :=
        Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
      rw [Real.rpow_def_of_pos hp]
      congr 1
      ring)

end Endpoints

theorem fractionalMatrixConstrainedPressure_le {N d r k : ℕ}
    (hN : 0 < N) (hr : 0 < r) (β s : ℝ) (hs : 0 < s)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (B : Fin (k + 1) → Fin r → Fin d → ℝ)
    (w : Fin (k + 1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hsum : ∑ b, w b = 1 - s) :
    fractionalPressure N d β s D + β ^ 2 * (d : ℝ) ^ 2 * s / (4 * (N : ℝ)) ≤
      vectorHierarchy ((k + 1) * r) (fun j => s + siteBlockMass r k w j)
        (matrixSiteVector β B (fun (a : Config d) u => spin (a u)))
        (siteValueTerminal (fun _ : Config d => 0)) 0 +
      (β ^ 2 / 4) * (matrixSquare d D -
        2 * matrixInner d (factorPath d r k B (Fin.last k)) D +
        ∑ j, w j * matrixSquare d (factorPath d r k B j)) := by
  let := hD
  let e : MatrixStates N d D → Fin N → Config d := fun a => a.val
  let X : MatrixStates N d D → Fin N → Fin d → ℝ := fun a i u => spin (e a i u)
  let H := matrixSKObservables N d β e
  let v : Config d → Fin d → ℝ := fun a u => spin (a u)
  have hinter := fractionalMatrixFiniteInterpolation_offset hN hr β s hs.le B X H
    (β ^ 2 * (d : ℝ) ^ 2 / 2) (matrixSKObservables_covariance hN β e)
    D (fun a => a.property) (fun _ => 0) w hw hsum
  dsimp only at hinter
  rw [fractionalBlockObservable_root_one, fractionalMatrixSK_endpoint N d β s hs.ne' D hD]
    at hinter
  have hz := fractionalSiteBlock_root_zero_le hN s hs.le e Subtype.val_injective H
    (matrixSiteVector β B v) (fun _ => 0) w hw
  rw [← matrixSiteVector_observables] at hz
  simp only [Finset.sum_const_zero] at hz
  have htotal := hinter.trans (add_le_add hz le_rfl)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf : fractionalPressure N d β s D * (N : ℝ) =
      Real.log (∫ J, constrainedPartition N d β D J ^ s ∂disorderLaw N) / s := by
    unfold fractionalPressure
    field_simp
  dsimp only [e, X, H, v] at htotal ⊢
  have hcor : β ^ 2 * (d : ℝ) ^ 2 * s / (4 * (N : ℝ)) * (N : ℝ) =
      β ^ 2 * (d : ℝ) ^ 2 / 2 * s / 2 := by
    field_simp
    ring
  apply (mul_le_mul_iff_left₀ hNr).mp
  simp only [add_mul, hf, hcor]
  nlinarith

end SKBarriers2
