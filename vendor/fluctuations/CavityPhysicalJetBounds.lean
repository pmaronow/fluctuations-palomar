module

public import CavityRowErrorKernel
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRootMarginal

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem fullFeature_single_any_decidable (n : ℕ) [DecidableEq (FullCoordinate n)]
    (σ : Spin n × Bool) (i : FullCoordinate n) :
    fullFeature n σ (Pi.single i 1) = fullCoefficient n σ i := by
  convert fullFeature_single n σ i using 1
  congr 1
  ext j
  simp [Pi.single_apply]

theorem fullVariance_row_covariance (n : ℕ) (b h K t : ℝ)
    (σ τ : Spin n × Bool) :
    rowCovarianceKernel n (fullVariance n 0 t b h K) σ τ =
      spinValue σ.2*spinValue τ.2*((1-t)*K+t*(h+b*deletedOverlap n (joinSpin σ) (joinSpin τ))) := by
  unfold rowCovarianceKernel
  simp_rw [fullFeature_single]
  simp only [fullVariance,fullCoefficient,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_one,one_mul]
  have hr (i : Fin n) : dormantCoefficient n σ (.inl i) =
      rowInteractionCoefficient n (joinSpin σ) i := by
    simp [dormantCoefficient,rowInteractionCoefficient,joinSpin]
  have ht (i : Fin n) : dormantCoefficient n τ (.inl i) =
      rowInteractionCoefficient n (joinSpin τ) i := by
    simp [dormantCoefficient,rowInteractionCoefficient,joinSpin]
  simp_rw [hr,ht]
  rw [rowInteraction_covariance]
  simp only [dormantCoefficient,joinSpin_last,Fin.sum_univ_one]
  ring

theorem fullVariance_row_covariance_abs_le (n : ℕ) (b h K : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (σ τ : Spin n × Bool) :
    |rowCovarianceKernel n (fullVariance n 0 t b h K) σ τ| ≤ |K|+|h|+|b| := by
  rw [fullVariance_row_covariance,abs_mul,abs_mul,abs_spinValue,abs_spinValue,one_mul,one_mul]
  have htk : |(1-t)*K| ≤ |K| := by
    rw [abs_mul,abs_of_nonneg (by linarith [ht.2] : 0≤1-t)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [ht.1])
  have htb : |t*(h+b*deletedOverlap n (joinSpin σ) (joinSpin τ))| ≤ |h|+|b| := by
    rw [abs_mul,abs_of_nonneg ht.1]
    apply (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_deletedOverlap_le_one n _ _)
  exact (abs_add_le _ _).trans (by linarith)

theorem cutLSlope_coordinateProfile_abs_le (n U : ℕ) (b h K : ℕ → ℝ)
    {t M : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hM : 0 ≤ M)
    (hbound : ∀ j < U, |K j|+|h j|+|b j| ≤ M) :
    ∀ j σ τ, |ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ| ≤ M := by
  intro j σ τ
  have he : ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ =
      rowCovarianceKernel n (cutLSlope n U t b h K j) σ τ := by
    classical
    simp only [ReplicaTree.coordinateProfile,rowCovarianceKernel,fullFeature_single]
    apply Finset.sum_congr rfl
    intro i _
    rw [fullFeature_single_any_decidable,fullFeature_single_any_decidable]
  rw [he]
  unfold cutLSlope
  split_ifs with hj
  · exact (fullVariance_row_covariance_abs_le n (b j) (h j) (K j) ht σ τ).trans (hbound j hj)
  · simpa only [rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero,abs_zero] using hM

theorem cutLowJet_abs_le_finiteVariation (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r : ℕ} (hT : T.leaves ≤ r) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : ∀ σ, |P σ| ≤ C) (hbound : ∀ j < U, |K j|+|h j|+|b j| ≤ M)
    (k : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |cutLowJet n q U b h K T P x k l t| ≤ ClockTree.jetVariation r k*C*M^k := by
  rw [cutLowJet_eq_profileJets n q U b h K T ho P x hq0 hq hb hh hK hbm hhm hKm k hl ht]
  have H := ClockTree.disorderProfileJets_abs_le (fullWeight_pos n) (fullFeature n) ho
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K)))
    T hT P hC hM hP
    (fun L hL j σ τ => by
      have he := List.mem_replicate.mp hL
      rw [he.2]
      exact cutLSlope_coordinateProfile_abs_le n U b h K ht hM hbound j σ τ)
    0 (cutFullVariance n q U l t b h K) x
  simpa only [List.length_replicate] using H

end OAI.SKFluctuations.Cavity
