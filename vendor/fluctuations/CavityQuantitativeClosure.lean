module

public import SKFluctuationsOAI.Probability.SKFluctuations.CavityGraphParity

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus

variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

def ClockExpr.absoluteEnvelope : {as : List PositiveMass} → ClockExpr S as → ℝ
  | _, .leaf P => ∑ σ, |P σ|
  | _, .step _ E => E.absoluteEnvelope
  | _, .add E F => E.absoluteEnvelope + F.absoluteEnvelope
  | _, .scale c E => |c| * E.absoluteEnvelope
  | _, .mul E F => E.absoluteEnvelope * F.absoluteEnvelope

theorem ClockExpr.absoluteEnvelope_nonneg {as : List PositiveMass} (E : ClockExpr S as) :
    0 ≤ E.absoluteEnvelope := by
  induction E with
  | leaf P => exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  | step a E ih => exact ih
  | add E F ihE ihF => exact add_nonneg ihE ihF
  | scale c E ih => exact mul_nonneg (abs_nonneg _) ih
  | mul E F ihE ihF => exact mul_nonneg ihE ihF

theorem ClockExpr.eval_abs_le_absoluteEnvelope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    |E.eval w φ q x| ≤ E.absoluteEnvelope := by
  induction E generalizing a q x with
  | leaf P =>
    exact gaussianHierarchyMean_abs_le hw φ
      (fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (P τ)) (Finset.mem_univ σ))
      [] (a := 0) ⟨le_rfl, zero_le_one⟩ x
  | @step b bs E ih =>
    have hi := gaussianHierarchy_integrable hw φ
      (clockSteps bs (fun j i => Real.toNNReal (q (j+1) i)))
      (clockSteps_ordered ho.2.2 _) b.val (fun i => Real.toNNReal (q 0 i)) x
    have h := shiftedMean_abs_mono
      (E.eval_smooth hw φ ho.2.2 (fun j => q (j+1)) 0)
      (BddSmooth.const 0 E.absoluteEnvelope) (fun y => ih ho.2.2 (fun j => q (j+1)) y) hi
    rw [shiftedMean_const _ hi] at h
    exact h
  | add E F ihE ihF =>
    exact (abs_add_le _ _).trans (add_le_add (ihE ho q x) (ihF ho q x))
  | scale c E ih =>
    simpa only [ClockExpr.eval, ClockExpr.absoluteEnvelope, abs_mul] using
      mul_le_mul_of_nonneg_left (ih ho q x) (abs_nonneg c)
  | mul E F ihE ihF =>
    simpa only [ClockExpr.eval, ClockExpr.absoluteEnvelope, abs_mul] using
      mul_le_mul (ihE ho q x) (ihF ho q x) (abs_nonneg _) E.absoluteEnvelope_nonneg

theorem ClockExpr.rootEval_abs_le_absoluteEnvelope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    {n : ℕ} (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    |E.rootEval w φ q₀ q x| ≤ E.absoluteEnvelope := by
  rw [ClockExpr.rootEval, varianceTest_zero_root]
  exact zeroContinuation_abs_le (E.eval_abs_le_absoluteEnvelope hw φ ho q) (fun i => Real.toNNReal (q₀ i)) x

def polynomialUnitEnvelope (p : Polynomial ℝ) : ℝ := p.sum fun _ c => |c|

theorem polynomialUnitEnvelope_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialUnitEnvelope p := by
  unfold polynomialUnitEnvelope
  rw [Polynomial.sum_def]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem polynomial_eval_abs_le_unitEnvelope (p : Polynomial ℝ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) : |p.eval t| ≤ polynomialUnitEnvelope p := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  unfold polynomialUnitEnvelope
  rw [Polynomial.sum_def]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_pow, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht.1 ht.2)

def ClockPolynomial.unitEnvelope {as : List PositiveMass} (P : ClockPolynomial S as) : ℝ :=
  (P.map fun p => polynomialUnitEnvelope p.1 * p.2.absoluteEnvelope).sum

theorem ClockPolynomial.unitEnvelope_nonneg {as : List PositiveMass}
    (P : ClockPolynomial S as) : 0 ≤ P.unitEnvelope := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (polynomialUnitEnvelope_nonneg _) p.2.absoluteEnvelope_nonneg

theorem ClockPolynomial.rootEval_abs_le_unitEnvelope {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) {n : ℕ} (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (P : ClockPolynomial S as) {a : ℝ} (ho : MassOrdered a as)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    |P.rootEval w φ t q₀ q x| ≤ P.unitEnvelope := by
  induction P with
  | nil => simp [rootEval, unitEnvelope]
  | cons p P ih =>
    simp only [rootEval, unitEnvelope, List.map_cons, List.sum_cons] at ih ⊢
    apply (abs_add_le _ _).trans
    apply add_le_add _ ih
    rw [abs_mul]
    exact mul_le_mul (polynomial_eval_abs_le_unitEnvelope _ ht)
      (p.2.rootEval_abs_le_absoluteEnvelope hw φ ho q₀ q x)
      (abs_nonneg _) (polynomialUnitEnvelope_nonneg _)

variable [Nonempty ι]

theorem ClockPolynomial.finiteEval_abs_le_unitEnvelope {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (P : ClockPolynomial S as) {a : ℝ} (ho : MassOrdered a as)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    |P.finiteEval w φ t v q x| ≤ P.unitEnvelope :=
  P.rootEval_abs_le_unitEnvelope hw (reindexFeature (finiteJetEquiv ι) φ) ho ht _ _ _

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem ClockPolynomial.rootEval_insert_direction_linear {n : ℕ} {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (P : ClockPolynomial S as) {a : ℝ} (ho : MassOrdered a as)
    (d₀ e₀ q₀ : Fin (n+1) → ℝ) (d e q : ℕ → Fin (n+1) → ℝ)
    (c t : ℝ) (x : Fin (n+1) → ℝ) :
    (P.insert φ (fun i => d₀ i+c*e₀ i) (fun j i => d j i+c*e j i)).rootEval w φ t q₀ q x =
      (P.insert φ d₀ d).rootEval w φ t q₀ q x+
      c*(P.insert φ e₀ e).rootEval w φ t q₀ q x := by
  induction P with
  | nil => simp [insert, rootEval]
  | cons p P ih =>
    simp only [insert, rootEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [p.2.rootCov_rootEval_direction_linear hw φ ho]
    nlinarith

def ClockPolynomial.finiteMixedEnvelope {as : List PositiveMass}
    (E : ClockExpr S as) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (b c d : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  let P := finiteLowJet E φ b d k
  P.coeffDeriv.unitEnvelope + (P.finiteInsert φ c).unitEnvelope +
    (P.finiteInsert φ d).unitEnvelope

theorem ClockPolynomial.finiteMixedEval_abs_le_envelope {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) {a : ℝ} (ho : MassOrdered a as)
    (b c d : ℕ → ι → ℝ) (k : ℕ) {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    |(finiteMixedJet E φ b c d l k).finiteEval w φ t v q x| ≤
      finiteMixedEnvelope E φ b c d k := by
  let P := finiteLowJet E φ b d k
  have he : (finiteMixedJet E φ b c d l k).finiteEval w φ t v q x =
      P.coeffDeriv.finiteEval w φ t v q x+
      (P.finiteInsert φ c).finiteEval w φ t v q x+
      l*(P.finiteInsert φ d).finiteEval w φ t v q x := by
    unfold finiteMixedJet finiteEval finiteInsert
    rw [rootEval_append, rootEval_insert_direction_linear hw _ _ ho]
    dsimp only [P]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add ((abs_add_le _ _).trans (add_le_add
    (P.coeffDeriv.finiteEval_abs_le_unitEnvelope hw φ ho ht v q x)
    ((P.finiteInsert φ c).finiteEval_abs_le_unitEnvelope hw φ ho ht v q x)))
  rw [abs_mul, abs_of_nonneg hl.1]
  exact (mul_le_mul_of_nonneg_left
    ((P.finiteInsert φ d).finiteEval_abs_le_unitEnvelope hw φ ho ht v q x) hl.1).trans
    (mul_le_of_le_one_left (P.finiteInsert φ d).unitEnvelope_nonneg hl.2)

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations.Cavity
open Hierarchy GaussianCalculus

theorem productJet3_abs_le (g f : Fin 4 → ℝ) (k : Fin 4) :
    |productJet3 g f k| ≤ productJet3 (fun i => |g i|) (fun i => |f i|) k := by
  fin_cases k
  · simp [productJet3, abs_mul]
  · simpa only [productJet3, abs_mul] using abs_add_le (g 0*f 1) (g 1*f 0)
  · simpa only [productJet3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] using
      (abs_add_le (g 0*f 2+2*g 1*f 1) (g 2*f 0)).trans
        (add_le_add (abs_add_le (g 0*f 2) (2*g 1*f 1)) le_rfl)
  · simpa only [productJet3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] using
      (abs_add_le (g 0*f 3+3*g 1*f 2+3*g 2*f 1) (g 3*f 0)).trans
        (add_le_add ((abs_add_le (g 0*f 3+3*g 1*f 2) (3*g 2*f 1)).trans
          (add_le_add (abs_add_le (g 0*f 3) (3*g 1*f 2)) le_rfl)) le_rfl)

theorem productJet3_mono {g f G F : Fin 4 → ℝ}
    (hg0 : ∀ i, 0 ≤ g i) (hf0 : ∀ i, 0 ≤ f i)
    (hg : ∀ i, g i ≤ G i) (hf : ∀ i, f i ≤ F i) (k : Fin 4) :
    productJet3 g f k ≤ productJet3 G F k := by
  have hprod (i j : Fin 4) : g i*f j ≤ G i*F j :=
    mul_le_mul (hg i) (hf j) (hf0 j) ((hg0 i).trans (hg i))
  fin_cases k <;> simp only [productJet3]
  · exact hprod _ _
  · exact add_le_add (hprod _ _) (hprod _ _)
  · nlinarith [hprod 0 2, hprod 1 1, hprod 2 0]
  · nlinarith [hprod 0 3, hprod 1 2, hprod 2 1, hprod 3 0]

section
variable (n U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
  (T : ClockTree (Spin n × Bool) as)

def cutFrozenEnvelope (P : T.Assignment → ℝ) (k r : ℕ) : ℝ :=
  ((ClockPolynomial.finiteLowJet (T.testExpr P) (fullFeature n)
    (cutLSlope n U 0 b h K) (cutLowError n U b h K) k).finiteIterInsert
    (fullFeature n) (cutTSlope n U 0 b h K) r).unitEnvelope

def cutMixedEnvelope (P : T.Assignment → ℝ) (k : ℕ) : ℝ :=
  ClockPolynomial.finiteMixedEnvelope (T.testExpr P) (fullFeature n)
    (cutLSlope n U 0 b h K) (cutTSlope n U 0 b h K)
    (cutLowError n U b h K) k

variable (q : ℕ → RestCoordinate n → ℝ) (ho : MassOrdered 0 as)
include ho

theorem cutFrozenLowHighJet_abs_le (P : T.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (k r : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |cutFrozenLowHighJet n q U b h K T P x k r t| ≤ cutFrozenEnvelope n U b h K T P k r :=
  ClockPolynomial.finiteEval_abs_le_unitEnvelope (fullWeight_pos n) (fullFeature n) _ ho
    (by norm_num) _ _ _

theorem cutLowJet_abs_le (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (k : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |cutLowJet n q U b h K T P x k l t| ≤ cutFrozenEnvelope n U b h K T P k 0 :=
  ClockPolynomial.finiteEval_abs_le_unitEnvelope (fullWeight_pos n) (fullFeature n) _ ho ht _ _ _

theorem cutMixedJet_abs_le (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (k : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |cutMixedJet n q U b h K T P x k l t| ≤ cutMixedEnvelope n U b h K T P k :=
  ClockPolynomial.finiteMixedEval_abs_le_envelope (fullWeight_pos n) (fullFeature n) _ ho
    _ _ _ k hl ht _ _ _

variable (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
  (x : ActiveCoordinate n → ℝ)

def cutFrozenCenteredEnvelope (k : Fin 4) (r : ℕ) : ℝ :=
  cutFrozenEnvelope n U b h K T
      (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2) k r +
    productJet3
      (fun i => cutFrozenEnvelope n U b h K T (fun σ => Q (T.cavityAssignment σ).2) i 0)
      (fun i => cutFrozenEnvelope n U b h K T (fun σ => P (T.cavityAssignment σ).1) i r) k

def cutMixedCenteredEnvelope (k : Fin 4) : ℝ :=
  cutMixedEnvelope n U b h K T
      (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2) k +
    productJet3
      (fun i => cutFrozenEnvelope n U b h K T (fun σ => Q (T.cavityAssignment σ).2) i 0)
      (fun i => cutMixedEnvelope n U b h K T (fun σ => P (T.cavityAssignment σ).1) i) k

theorem cutFrozenCenteredJet_abs_le (k : Fin 4) (r : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    |cutFrozenCenteredJet n q U b h K T P Q x k r t| ≤
      cutFrozenCenteredEnvelope n U b h K T P Q k r := by
  unfold cutFrozenCenteredJet cutFrozenCenteredEnvelope
  apply (abs_sub _ _).trans
  apply add_le_add (cutFrozenLowHighJet_abs_le n U b h K T q ho _ _ _ _ ht)
  apply (productJet3_abs_le _ _ _).trans
  apply productJet3_mono (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (fun i => cutLowJet_abs_le n U b h K T q ho _ _ i (by norm_num) (by norm_num))
    (fun i => cutFrozenLowHighJet_abs_le n U b h K T q ho _ _ i r ht)

theorem cutCenteredMixedJet_abs_le (k : Fin 4) {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |cutCenteredMixedJet n q U b h K T P Q x k l t| ≤
      cutMixedCenteredEnvelope n U b h K T P Q k := by
  unfold cutCenteredMixedJet cutMixedCenteredEnvelope
  apply (abs_sub _ _).trans
  apply add_le_add (cutMixedJet_abs_le n U b h K T q ho _ _ _ hl ht)
  apply (productJet3_abs_le _ _ _).trans
  apply productJet3_mono (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (fun i => cutLowJet_abs_le n U b h K T q ho _ _ i hl (by norm_num))
    (fun i => cutMixedJet_abs_le n U b h K T q ho _ _ i hl ht)

end
end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy GaussianCalculus

theorem weighted_unit_integral_abs_le {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ t ∈ Icc (0:ℝ) 1, |f t| ≤ C) (k : ℕ) :
    |∫ t in (0:ℝ)..1, (1-t)^k*f t| ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
    (a := (0:ℝ)) (b := 1) (f := fun t => (1-t)^k*f t) (fun t ht => by
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have ht0 := ht'.1
      have ht1 := ht'.2
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (by linarith : 0 ≤ 1-t)]
      exact (mul_le_mul_of_nonneg_left (hf t ht') (pow_nonneg (by linarith) _)).trans
        (mul_le_of_le_one_left hC (pow_le_one₀ (by linarith) (by linarith))))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
  (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
  (x : ActiveCoordinate n → ℝ)

def cutFrozenRemainder : ℝ :=
  (∫ t in (0:ℝ)..1, (1-t)*cutFrozenCenteredJet n q U b h K T P Q x 1 2 t)+
  (1/2:ℝ)*(∫ t in (0:ℝ)..1, cutFrozenCenteredJet n q U b h K T P Q x 2 1 t)+
  (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*∫ t in (0:ℝ)..1,
    cutCenteredMixedJet n q U b h K T P Q x 3 l t

theorem cutFrozenRemainder_abs_le (ho : MassOrdered 0 as) :
    |cutFrozenRemainder n q U b h K T P Q x| ≤
      cutFrozenCenteredEnvelope n U b h K T P Q 1 2+
      (1/2:ℝ)*cutFrozenCenteredEnvelope n U b h K T P Q 2 1+
      (1/2:ℝ)*cutMixedCenteredEnvelope n U b h K T P Q 3 := by
  have hA := cutFrozenCenteredJet_abs_le n U b h K T q ho P Q x 1 2 (by norm_num : (0:ℝ) ∈ Icc 0 1)
  have hB := cutFrozenCenteredJet_abs_le n U b h K T q ho P Q x 2 1 (by norm_num : (0:ℝ) ∈ Icc 0 1)
  have hC := cutCenteredMixedJet_abs_le n U b h K T q ho P Q x 3
    (by norm_num : (0:ℝ) ∈ Icc 0 1) (by norm_num : (0:ℝ) ∈ Icc 0 1)
  have hA0 := (abs_nonneg _).trans hA
  have hB0 := (abs_nonneg _).trans hB
  have hC0 := (abs_nonneg _).trans hC
  have hAI := weighted_unit_integral_abs_le hA0
    (fun t ht => cutFrozenCenteredJet_abs_le n U b h K T q ho P Q x 1 2 ht) 1
  have hBI := weighted_unit_integral_abs_le hB0
    (fun t ht => cutFrozenCenteredJet_abs_le n U b h K T q ho P Q x 2 1 ht) 0
  have hCI := weighted_unit_integral_abs_le hC0
    (fun l hl => by
      simpa only [pow_zero, one_mul] using weighted_unit_integral_abs_le hC0
        (fun t ht => cutCenteredMixedJet_abs_le n U b h K T q ho P Q x 3 hl ht) 0) 2
  unfold cutFrozenRemainder
  have ha := abs_add_le
    ((∫ t in (0:ℝ)..1, (1-t)*cutFrozenCenteredJet n q U b h K T P Q x 1 2 t)+
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, cutFrozenCenteredJet n q U b h K T P Q x 2 1 t))
    ((1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*∫ t in (0:ℝ)..1,
      cutCenteredMixedJet n q U b h K T P Q x 3 l t)
  apply ha.trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    apply add_le_add
    · simpa only [pow_one] using hAI
    · simpa only [pow_zero, one_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
        using mul_le_mul_of_nonneg_left hBI (by norm_num : (0:ℝ) ≤ 1/2)
  · simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      using mul_le_mul_of_nonneg_left hCI (by norm_num : (0:ℝ) ≤ 1/2)

theorem cutCenteredJet_frozen_remainder_eq
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (ho : MassOrdered 0 as) :
    cutCenteredJet n q U b h K T P Q x 0 1 1 =
      cutCenteredJet n q U b h K T P Q x 0 0 1+
      cutFrozenCenteredJet n q U b h K T P Q x 1 0 0+
      cutFrozenCenteredJet n q U b h K T P Q x 1 1 0+
      (1/2:ℝ)*cutFrozenCenteredJet n q U b h K T P Q x 2 0 0+
      cutFrozenRemainder n q U b h K T P Q x := by
  rw [cutCenteredJet_frozen_decomposition n q U b h K T P Q x
    hq0 hq hb hh hK hbm hhm hKm ho]
  unfold cutFrozenRemainder
  ring

end
end OAI.SKFluctuations.Cavity
