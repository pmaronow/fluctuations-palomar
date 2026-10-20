module

public import CavityQuantitativeClosure

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Hierarchy

theorem finite_weighted_cauchy_schwarz {A : Type*} [Fintype A]
    (w P Q : A → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a*P a*Q a)^2 ≤ (∑ a, w a*(P a)^2)*(∑ a, w a*(Q a)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (w a)*P a) (fun a => Real.sqrt (w a)*Q a)
  have hPQ (a : A) : (Real.sqrt (w a)*P a)*(Real.sqrt (w a)*Q a) = w a*P a*Q a := by
    calc
      _ = (Real.sqrt (w a))^2*(P a*Q a) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw a)]; ring
  have hP (a : A) : (Real.sqrt (w a)*P a)^2 = w a*(P a)^2 := by
    rw [mul_pow, Real.sq_sqrt (hw a)]
  have hQ (a : A) : (Real.sqrt (w a)*Q a)^2 = w a*(Q a)^2 := by
    rw [mul_pow, Real.sq_sqrt (hw a)]
  simpa only [hPQ, hP, hQ] using h

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem ReplicaTree.expect_mul_sq_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    (T.expect w φ (fun σ => P σ*Q σ) x)^2 ≤
      T.expect w φ (fun σ => (P σ)^2) x*T.expect w φ (fun σ => (Q σ)^2) x := by
  simpa only [expect, mul_assoc] using
    finite_weighted_cauchy_schwarz (fun σ => T.weight w φ σ x) P Q
      (fun σ => T.weight_nonneg hw φ ha σ x)

theorem ReplicaTree.expect_mul_abs_le_sqrt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    |T.expect w φ (fun σ => P σ*Q σ) x| ≤
      Real.sqrt (T.expect w φ (fun σ => (P σ)^2) x*T.expect w φ (fun σ => (Q σ)^2) x) := by
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg
    (T.expect_nonneg hw φ ha (fun σ => sq_nonneg _) x)
    (T.expect_nonneg hw φ ha (fun σ => sq_nonneg _) x))).mpr
  rw [sq_abs]
  exact T.expect_mul_sq_le hw φ ha P Q x

theorem ClockTree.disorderExpect_mul_sq_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    (T.disorderExpect w φ v q (fun σ => P σ*Q σ) x)^2 ≤
      T.disorderExpect w φ v q (fun σ => (P σ)^2) x*
        T.disorderExpect w φ v q (fun σ => (Q σ)^2) x := by
  simpa only [disorderExpect, mul_assoc] using
    finite_weighted_cauchy_schwarz (fun σ => T.disorderWeight w φ v q σ x) P Q
      (T.disorderWeight_probability hw φ ho v q x).1

theorem ClockTree.disorderExpect_abs_pow_le_square {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C) (k : ℕ) (x : ι → ℝ) :
    T.disorderExpect w φ v q (fun σ => |P σ|^(k+2)) x ≤
      C^k*T.disorderExpect w φ v q (fun σ => (P σ)^2) x := by
  unfold disorderExpect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hpower : |P σ|^(k+2) ≤ C^k*(P σ)^2 := by
    rw [pow_add, sq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hP σ) k) (sq_nonneg _)
  have hweight := (T.disorderWeight_probability hw φ ho v q x).1 σ
  nlinarith [mul_le_mul_of_nonneg_left hpower hweight]

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations.Hierarchy.ReplicaTree
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

def profilePairCauchyLedger {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (a : ℝ) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.markedAttach a).map fun p => |p.coeff| *
    ((p.tree.markedAttach a).map fun q => |q.coeff| *
      Real.sqrt (q.tree.expect w φ (fun σ => (P (p.restrict (q.restrict σ)))^2) x*
        q.tree.expect w φ (fun σ =>
          (K (q.tree.splitIndex (q.embed p.mark) q.mark)
            (p.spin (q.restrict σ)) (q.spin σ))^2) x)).sum).sum

theorem list_weighted_absolute_bound {A : Type*} (ps : List A) (c F B : A → ℝ)
    (hF : ∀ p ∈ ps, |F p| ≤ B p) :
    |(ps.map fun p => c p*F p).sum| ≤ (ps.map fun p => |c p| * B p).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hF p List.mem_cons_self) (abs_nonneg _)
    · exact ih (fun q hq => hF q (List.mem_cons_of_mem _ hq))

theorem profilePairExpectation_abs_le_cauchyLedger {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    |T.profilePairExpectation w φ a P K x| ≤ T.profilePairCauchyLedger w φ a P K x := by
  unfold profilePairExpectation profilePairCauchyLedger
  apply list_weighted_absolute_bound
  intro p hp
  apply list_weighted_absolute_bound
  intro q hq
  exact q.tree.expect_mul_abs_le_sqrt hw φ ha _ _ x

end OAI.SKFluctuations.Hierarchy.ReplicaTree
