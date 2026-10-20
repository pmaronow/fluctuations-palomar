module

public import SKConstants.Completion.Blueprint.Nodes
public import SKConstants.Completion.Blueprint.ExperimentMeasurable

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology unitInterval BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] runMag

theorem sum_sq_signedSpin_sub {n : ℕ} (x y : Spin n) :
    ∑ i, (signedSpin x i - signedSpin y i) ^ 2 = 4 * (hammingDist x y : ℝ) := by
  have h : ∀ i, (signedSpin x i - signedSpin y i) ^ 2 = if x i ≠ y i then 4 else 0 := by
    intro i
    unfold signedSpin
    cases x i <;> cases y i <;> norm_num
  simp only [h, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  rw [hammingDist]
  push_cast
  ring

theorem hammingDist_le_of_gaps {n : ℕ} (x y : Spin n) (m m' : Fin n → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (h1 : pinGap x m ≤ R / 4) (h2 : magGap m m' ≤ R / 4)
    (h3 : pinGap y m' ≤ R / 4) : (hammingDist x y : ℝ) ≤ R := by
  have hpt : ∀ i, (signedSpin x i - signedSpin y i) ^ 2 ≤
      3 * ((signedSpin x i - m i) ^ 2 + (m i - m' i) ^ 2 + (signedSpin y i - m' i) ^ 2) := by
    intro i
    nlinarith [sq_nonneg (signedSpin x i - m i - (m i - m' i)),
      sq_nonneg (signedSpin x i - m i + (signedSpin y i - m' i)),
      sq_nonneg (m i - m' i + (signedSpin y i - m' i))]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [sum_sq_signedSpin_sub, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at hsum
  simp only [pinGap] at h1 h3
  simp only [magGap] at h2
  nlinarith

theorem magGap_self {n : ℕ} (m : Fin n → ℝ) : magGap m m = 0 := by
  simp [magGap]

theorem gridSize_pos (p : Parameters) (n : ℕ) : 0 < gridSize p n := by
  unfold gridSize
  apply Nat.ceil_pos.mpr
  exact mul_pos (by positivity) (Real.exp_pos _)

theorem gridAngle_last (p : Parameters) (n : ℕ) : gridAngle p n (gridSize p n) = Real.pi / 2 := by
  have h := gridSize_pos p n
  unfold gridAngle
  have : (gridSize p n : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  field_simp

theorem pathSpin_zero_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (z : Outer n × Internal p n) :
    pathSpin W β hβ p n z.1 z.2 0 = fineSpin W β hβ p n (angleInput p n 0 0 z).1
      (angleInput p n 0 0 z).2.1 (angleInput p n 0 0 z).2.2 := rfl

theorem pathSpin_coarse_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (z : Outer n × Internal p n) (j : ℕ) (hj : j ≤ gridSize p n) :
    pathSpin W β hβ p n z.1 z.2 (j + 1) =
      coarseSpin W β hβ p n (angleInput p n (gridAngle p n j) (j + 2) z).1
        (angleInput p n (gridAngle p n j) (j + 2) z).2.1
        (angleInput p n (gridAngle p n j) (j + 2) z).2.2 := by
  simp only [pathSpin, hj, ite_true]
  rfl

theorem pathSpin_last_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (z : Outer n × Internal p n) :
    pathSpin W β hβ p n z.1 z.2 (gridSize p n + 2) =
      fineSpin W β hβ p n (angleInput p n (Real.pi / 2) 1 z).1
        (angleInput p n (Real.pi / 2) 1 z).2.1 (angleInput p n (Real.pi / 2) 1 z).2.2 := by
  have h : ¬ (gridSize p n + 1 ≤ gridSize p n) := by omega
  simp only [pathSpin, h, ite_false]
  rfl

theorem measurable_angleInput (p : Parameters) (n : ℕ) (θ : ℝ) (k : ℕ) :
    Measurable (angleInput p n θ k) :=
  (measurable_angleMatrix p n θ).prodMk ((measurable_angleAux p n θ).prodMk
    (measurable_thresholdAt p n k))

theorem measurable_runSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (t : ℝ≥0) :
    Measurable (fun y : RunInput p n => thresholdSpin (runMag W β hβ p n t y.1 y.2.1) y.2.2) :=
  (measurable_spinAt W β hβ p n t).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem measurableSet_pinGap (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (t : ℝ≥0) (R : ℝ) :
    MeasurableSet {y : RunInput p n | R <
      pinGap (thresholdSpin (runMag W β hβ p n t y.1 y.2.1) y.2.2)
        (coarseMag W β hβ p n y.1 y.2.1)} := by
  apply measurableSet_lt measurable_const
  unfold pinGap
  apply Finset.measurable_sum
  intro i _
  have hs : Measurable (fun y : RunInput p n =>
      signedSpin (thresholdSpin (runMag W β hβ p n t y.1 y.2.1) y.2.2) i) :=
    (measurable_of_finite (fun x : Spin n => signedSpin x i)).comp (measurable_runSpin W β hβ p n t)
  have hm : Measurable (fun y : RunInput p n => coarseMag W β hβ p n y.1 y.2.1 i) :=
    ((measurable_runMag W β hβ p n _).comp (measurable_fst.prodMk measurable_snd.fst)).eval
  exact (hs.sub hm).pow_const 2

theorem measurableSet_coarseHitEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : MeasurableSet (coarseHitEvent W β hβ p n) := by
  have h := measurableSet_not_mem_excludedSet β p n
    ((measurable_runSpin W β hβ p n (readoutTime p.a p.b n)).comp measurable_snd)
    (measurable_fst : Measurable (fun x : Prim n × RunInput p n => x.1))
  have he : coarseHitEvent W β hβ p n = {x : Prim n × RunInput p n |
      thresholdSpin (runMag W β hβ p n (readoutTime p.a p.b n) x.2.1 x.2.2.1) x.2.2.2 ∉
        excludedSet β p n x.1}ᶜ := by
    ext x
    simp [coarseHitEvent, coarseSpin]
  rw [he]
  exact h.compl

theorem grid_absorb (g e s κ C : ℝ) (hg : g < e) (hs : s < e) (he : 0 < e) (hκ : 0 < κ)
    (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C * Real.exp ((n : ℝ) ^ g) * Real.exp (-(κ * (n : ℝ) ^ e)) ≤
      Real.exp (-((n : ℝ) ^ s)) / 4 := by
  filter_upwards [constant_rpow_le_small_rpow g e 1 (κ / 3) hg (by norm_num) (by positivity),
    constant_rpow_le_small_rpow s e 1 (κ / 3) hs (by norm_num) (by positivity),
    constant_rpow_le_small_rpow 0 e (|Real.log (4 * (C + 1))|) (κ / 3) he (abs_nonneg _)
      (by positivity), eventually_ge_atTop 1] with n h1 h2 h3 hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_zero, mul_one] at h3
  have hC1 : 0 < 4 * (C + 1) := by positivity
  have hlog : Real.log (4 * (C + 1)) ≤ |Real.log (4 * (C + 1))| := le_abs_self _
  have hkey : (n : ℝ) ^ g - κ * (n : ℝ) ^ e ≤ -((n : ℝ) ^ s) - Real.log (4 * (C + 1)) := by
    linarith
  have hE := Real.exp_le_exp.mpr hkey
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hC1] at hE
  have hCle : C ≤ C + 1 := by linarith
  calc C * Real.exp ((n : ℝ) ^ g) * Real.exp (-(κ * (n : ℝ) ^ e))
      ≤ (C + 1) * (Real.exp ((n : ℝ) ^ g) / Real.exp (κ * (n : ℝ) ^ e)) := by
        rw [Real.exp_neg, mul_assoc, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hCle (by positivity)
    _ ≤ (C + 1) * (Real.exp (-((n : ℝ) ^ s)) / (4 * (C + 1))) :=
        mul_le_mul_of_nonneg_left hE (by linarith)
    _ = Real.exp (-((n : ℝ) ^ s)) / 4 := by field_simp

theorem gridSize_le (p : Parameters) (n : ℕ) :
    ((gridSize p n : ℕ) : ℝ) + 2 ≤ 5 * Real.exp ((n : ℝ) ^ p.grid) := by
  unfold gridSize
  have h := Nat.ceil_lt_add_one (show 0 ≤ (Real.pi / 2) * Real.exp ((n : ℝ) ^ p.grid) by
    positivity)
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
  have he : 1 ≤ Real.exp ((n : ℝ) ^ p.grid) := Real.one_le_exp (by positivity)
  nlinarith

theorem magGap_comm {n : ℕ} (m m' : Fin n → ℝ) : magGap m m' = magGap m' m := by
  unfold magGap
  congr 1
  funext i
  ring

theorem experiment_real_of_run (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) (θ : ℝ) (k : ℕ)
    (hA : (experimentLaw W p n).map (angleInput p n θ k) = runLaw W p n)
    (S : Set (RunInput p n)) (hS : MeasurableSet S) :
    (experimentLaw W p n).real {z | angleInput p n θ k z ∈ S} = (runLaw W p n).real S := by
  rw [measureReal_def, measureReal_def, ← hA, Measure.map_apply (measurable_angleInput p n θ k) hS]
  rfl

theorem experiment_real_of_regression (W : BrownianSystem Ω) (p : Parameters) (n : ℕ)
    (θ : ℝ) (k : ℕ)
    (hA : (experimentLaw W p n).map (fun z => (z.1.1, angleInput p n θ k z)) =
      (angleLaw W p n).map (regressionInput p n))
    (S : Set (Prim n × RunInput p n)) (hS : MeasurableSet S) :
    (experimentLaw W p n).real {z | (z.1.1, angleInput p n θ k z) ∈ S} =
      ((angleLaw W p n).map (regressionInput p n)).real S := by
  rw [measureReal_def, measureReal_def, ← hA,
    Measure.map_apply (measurable_fst.fst.prodMk (measurable_angleInput p n θ k)) hS]
  rfl

theorem gridAngle_zero_eq (p : Parameters) (n : ℕ) : gridAngle p n 0 = 0 := by
  simp [gridAngle]

section Steps

variable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)

def pinCoarseEvent (θ : ℝ) (k : ℕ) (R : ℝ) : Set (Outer n × Internal p n) :=
  {z | R / 4 < pinGap (coarseSpin W β hβ p n (angleInput p n θ k z).1
    (angleInput p n θ k z).2.1 (angleInput p n θ k z).2.2)
    (coarseMag W β hβ p n (angleInput p n θ k z).1 (angleInput p n θ k z).2.1)}

def pinFineEvent (θ : ℝ) (k : ℕ) (R : ℝ) : Set (Outer n × Internal p n) :=
  {z | R / 4 < pinGap (fineSpin W β hβ p n (angleInput p n θ k z).1
    (angleInput p n θ k z).2.1 (angleInput p n θ k z).2.2)
    (coarseMag W β hβ p n (angleInput p n θ k z).1 (angleInput p n θ k z).2.1)}

def contEvent (j : ℕ) (R : ℝ) : Set (Outer n × Internal p n) :=
  {z | R / 4 < magGap (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n (j + 1)) z.1 z.2)
      (angleAux p n (gridAngle p n (j + 1)) z.2))
    (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n j) z.1 z.2)
      (angleAux p n (gridAngle p n j) z.2))}

def stepEvent (i : ℕ) (R : ℕ) : Set (Outer n × Internal p n) :=
  {z | R < hammingDist (pathSpin W β hβ p n z.1 z.2 i) (pathSpin W β hβ p n z.1 z.2 (i + 1))}

def hitEvent (j : ℕ) : Set (Outer n × Internal p n) :=
  {z | pathSpin W β hβ p n z.1 z.2 (j + 1) ∈ excludedSet β p n z.1.1}

theorem stepEvent_zero_subset (R : ℕ) :
    stepEvent W β hβ p n 0 R ⊆ pinFineEvent W β hβ p n 0 0 R ∪ pinCoarseEvent W β hβ p n 0 2 R := by
  intro z hz
  by_contra hcon
  simp only [pinFineEvent, pinCoarseEvent, Set.mem_union, Set.mem_setOf_eq, not_or,
    not_lt] at hcon
  have h1 := pathSpin_coarse_eq W β hβ p n z 0 (Nat.zero_le _)
  rw [gridAngle_zero_eq] at h1
  have hd := hammingDist_le_of_gaps _ _ _ _ (R : ℝ) (Nat.cast_nonneg _) hcon.1
    (le_of_eq_of_le (magGap_self _) (by positivity)) hcon.2
  simp only [stepEvent, Set.mem_setOf_eq] at hz
  rw [pathSpin_zero_eq W β hβ p n z, h1] at hz
  exact absurd hz (not_lt.mpr (Nat.cast_le.mp hd))

theorem stepEvent_mid_subset (R : ℕ) (j : ℕ) (hj : j < gridSize p n) :
    stepEvent W β hβ p n (j + 1) R ⊆
      (pinCoarseEvent W β hβ p n (gridAngle p n j) (j + 2) R ∪ contEvent W β hβ p n j R) ∪
        pinCoarseEvent W β hβ p n (gridAngle p n (j + 1)) (j + 1 + 2) R := by
  intro z hz
  by_contra hcon
  simp only [pinCoarseEvent, contEvent, Set.mem_union, Set.mem_setOf_eq, not_or,
    not_lt] at hcon
  have e1 := pathSpin_coarse_eq W β hβ p n z j (by omega)
  have e2 := pathSpin_coarse_eq W β hβ p n z (j + 1) (by omega)
  have hd := hammingDist_le_of_gaps _ _ _ _ (R : ℝ) (Nat.cast_nonneg _) hcon.1.1
    (by rw [magGap_comm]; exact hcon.1.2) hcon.2
  simp only [stepEvent, Set.mem_setOf_eq] at hz
  rw [e1, e2] at hz
  exact absurd hz (not_lt.mpr (Nat.cast_le.mp hd))

theorem stepEvent_last_subset (R : ℕ) :
    stepEvent W β hβ p n (gridSize p n + 1) R ⊆
      pinCoarseEvent W β hβ p n (Real.pi / 2) (gridSize p n + 2) R ∪
        pinFineEvent W β hβ p n (Real.pi / 2) 1 R := by
  intro z hz
  by_contra hcon
  simp only [pinFineEvent, pinCoarseEvent, Set.mem_union, Set.mem_setOf_eq, not_or,
    not_lt] at hcon
  have e1 := pathSpin_coarse_eq W β hβ p n z (gridSize p n) le_rfl
  rw [gridAngle_last] at e1
  have e2 := pathSpin_last_eq W β hβ p n z
  have hd := hammingDist_le_of_gaps _ _ _ _ (R : ℝ) (Nat.cast_nonneg _) hcon.1
    (le_of_eq_of_le (magGap_self _) (by positivity)) hcon.2
  simp only [stepEvent, Set.mem_setOf_eq] at hz
  rw [e1, e2] at hz
  exact absurd hz (not_lt.mpr (Nat.cast_le.mp hd))

theorem hitEvent_eq (j : ℕ) (hj : j ≤ gridSize p n) :
    hitEvent W β hβ p n j =
      {z | (z.1.1, angleInput p n (gridAngle p n j) (j + 2) z) ∈ coarseHitEvent W β hβ p n} := by
  ext z
  simp only [hitEvent, Set.mem_setOf_eq, coarseHitEvent]
  rw [pathSpin_coarse_eq W β hβ p n z j hj]

theorem notGood_subset :
    {z : Outer n × Internal p n | z.2 ∉ goodEvent W β hβ p n z.1} ⊆
      (⋃ i ∈ Finset.range (gridSize p n + 2), stepEvent W β hβ p n i (hammingRadius p n)) ∪
      ⋃ j ∈ Finset.range (gridSize p n + 1), hitEvent W β hβ p n j := by
  intro z hz
  simp only [Set.mem_setOf_eq, goodEvent, not_and_or, not_forall, not_le] at hz
  rcases hz with ⟨i, hi, hd⟩ | ⟨j, hj, hx⟩
  · exact Or.inl (Set.mem_biUnion (Finset.mem_range.mpr hi) hd)
  · exact Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (by omega)) (not_not.mp hx))

theorem notGood_le (ePin eCont eHit : ℝ)
    (hpinC : ∀ θ k, (experimentLaw W p n).real
      (pinCoarseEvent W β hβ p n θ k (hammingRadius p n)) ≤ ePin)
    (hpinF : ∀ θ k, (experimentLaw W p n).real
      (pinFineEvent W β hβ p n θ k (hammingRadius p n)) ≤ ePin)
    (hcont : ∀ j < gridSize p n, (experimentLaw W p n).real
      (contEvent W β hβ p n j (hammingRadius p n)) ≤ eCont)
    (hhit : ∀ j ≤ gridSize p n, (experimentLaw W p n).real (hitEvent W β hβ p n j) ≤ eHit)
    (hePin : 0 ≤ ePin) (heCont : 0 ≤ eCont) :
    (experimentLaw W p n).real {z | z.2 ∉ goodEvent W β hβ p n z.1} ≤
      ((gridSize p n : ℝ) + 2) * (2 * ePin + eCont) + ((gridSize p n : ℝ) + 1) * eHit := by
  set P := experimentLaw W p n
  set R := hammingRadius p n
  have step : ∀ i < gridSize p n + 2, P.real (stepEvent W β hβ p n i R) ≤ 2 * ePin + eCont := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · calc P.real (stepEvent W β hβ p n 0 R) ≤ ePin + ePin :=
            (measureReal_mono (stepEvent_zero_subset W β hβ p n R)).trans
              ((measureReal_union_le _ _).trans (add_le_add (hpinF _ _) (hpinC _ _)))
        _ ≤ 2 * ePin + eCont := by linarith
    · rcases lt_or_ge i (gridSize p n + 1) with hlt | hge
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hj : j < gridSize p n := by omega
        calc P.real (stepEvent W β hβ p n (j + 1) R) ≤ ePin + eCont + ePin :=
              (measureReal_mono (stepEvent_mid_subset W β hβ p n R j hj)).trans
                ((measureReal_union_le _ _).trans (add_le_add
                  ((measureReal_union_le _ _).trans (add_le_add (hpinC _ _) (hcont j hj)))
                  (hpinC _ _)))
          _ = 2 * ePin + eCont := by ring
      · have him : i = gridSize p n + 1 := by omega
        subst him
        calc P.real (stepEvent W β hβ p n (gridSize p n + 1) R) ≤ ePin + ePin :=
              (measureReal_mono (stepEvent_last_subset W β hβ p n R)).trans
                ((measureReal_union_le _ _).trans (add_le_add (hpinC _ _) (hpinF _ _)))
          _ ≤ 2 * ePin + eCont := by linarith
  refine (measureReal_mono (notGood_subset W β hβ p n)).trans
    ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ i ∈ Finset.range (gridSize p n + 2), P.real (stepEvent W β hβ p n i R)
        ≤ ∑ _i ∈ Finset.range (gridSize p n + 2), (2 * ePin + eCont) :=
          Finset.sum_le_sum (fun i hi => step i (Finset.mem_range.mp hi))
      _ = ((gridSize p n : ℝ) + 2) * (2 * ePin + eCont) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  · refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ j ∈ Finset.range (gridSize p n + 1), P.real (hitEvent W β hβ p n j)
        ≤ ∑ _j ∈ Finset.range (gridSize p n + 1), eHit :=
          Finset.sum_le_sum (fun j hj => hhit j (by have := Finset.mem_range.mp hj; omega))
      _ = ((gridSize p n : ℝ) + 1) * eHit := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

end Steps

theorem absorption_arith (X m E ePin A1 A2 A3 A4 T : ℝ)
    (hsum : X ≤ (m + 2) * (2 * ePin + (A2 + 2 * A3)) + (m + 1) * (A3 + A4))
    (hm0 : 0 ≤ m) (hm : m + 2 ≤ 5 * E) (hP0 : 0 ≤ ePin) (hP : ePin ≤ 2 * A1)
    (h2 : 0 ≤ A2) (h3 : 0 ≤ A3) (h4 : 0 ≤ A4)
    (b1 : 20 * E * A1 ≤ T / 4) (b2 : 5 * E * A2 ≤ T / 4) (b3 : 15 * E * A3 ≤ T / 4)
    (b4 : 5 * E * A4 ≤ T / 4) : X ≤ T := by
  have hA : 0 ≤ 2 * ePin + (A2 + 2 * A3) := by positivity
  have hB : 0 ≤ A3 + A4 := by positivity
  have e1 : (m + 2) * (2 * ePin + (A2 + 2 * A3)) ≤ (5 * E) * (2 * ePin + (A2 + 2 * A3)) :=
    mul_le_mul_of_nonneg_right hm hA
  have e2 : (m + 1) * (A3 + A4) ≤ (5 * E) * (A3 + A4) :=
    mul_le_mul_of_nonneg_right (by linarith) hB
  have hE : 0 ≤ E := by linarith
  have e3 : (5 * E) * (2 * ePin) ≤ 20 * E * A1 := by nlinarith
  nlinarith

theorem sequenceGood_of_nodes (hAngle : PerAngleLawNonnegativeExponentStatement) (hHit : CoarseHitStatement)
    (hCont : CoarseContinuityStatement) (hPin : PinningStatement) : SequenceGoodStatement := by
  intro p sseq hfe hce hbe hse Ω _ W β hβ
  have hse' := hse
  have hbe' := hbe
  have hfe' := hfe
  have hce' := hce
  obtain ⟨hr_sb, hq_sb, ha_g, hg_sb, hsb_s, hr_b, hq_kb, hq_D, hq_zP, hzP0, hzP, hD⟩ := hse'
  obtain ⟨hq0, hqu, hur, hr1, hfield, hqhalf⟩ := hbe'
  obtain ⟨hfa, haf, hkf0, hkfa, hkff, hkf1⟩ := hfe'
  obtain ⟨hb0, hbf, hz0, hγ0, hkb0, hkbz, hkbγ, hkba, hkbb, hzsb, hγsb, hasb⟩ := hce'
  have hr0 : 0 < p.r := by linarith
  set μ₂ := min (min p.kb p.zP) (min p.D p.sb) with hμ₂
  have hqμ : p.q < μ₂ := lt_min (lt_min hq_kb hq_zP) (lt_min hq_D hq_sb)
  set s₂ := (p.q + μ₂) / 2 with hs₂
  have hs₂q : p.q < s₂ := by linarith
  have hs₂μ : s₂ < μ₂ := by linarith
  have hs₂kb : s₂ < p.kb := lt_of_lt_of_le hs₂μ ((min_le_left _ _).trans (min_le_left _ _))
  have hs₂zP : s₂ < p.zP := lt_of_lt_of_le hs₂μ ((min_le_left _ _).trans (min_le_right _ _))
  have hs₂D : s₂ < p.D := lt_of_lt_of_le hs₂μ ((min_le_right _ _).trans (min_le_left _ _))
  have hs₂sb : s₂ < p.sb := lt_of_lt_of_le hs₂μ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c, hc, hC⟩ := hCont p sseq hfe hce hbe hse W β hβ
  have hH := hHit p s₂ hfe hce hbe hs₂q hs₂kb hs₂zP hs₂D W β hβ
  have hP := hPin p hfe hce hr0 hr_b W β hβ
  have hA := hAngle p hD.le W
  have a1 := grid_absorb p.grid (1 - p.r) (1 - sseq) (1 / 64) 20 (by linarith) (by linarith)
    (by linarith) (by norm_num) (by norm_num)
  have a2 := grid_absorb p.grid 1 (1 - sseq) c 5 (by linarith) (by linarith) one_pos hc
    (by norm_num)
  have a3 := grid_absorb p.grid (1 - p.sb) (1 - sseq) 1 15 (by linarith) (by linarith)
    (by linarith) one_pos (by norm_num)
  have a4 := grid_absorb p.grid (1 - s₂) (1 - sseq) 1 5 (by linarith) (by linarith)
    (by linarith) one_pos (by norm_num)
  filter_upwards [hC, hH, hP, hA, a1, a2, a3, a4] with n hCn hHn hPn hAn h1 h2 h3 h4
  set R := hammingRadius p n with hR
  set ePin := 2 * Real.exp (-((R : ℝ) / 64)) with hePin
  set eHit := Real.exp (-((n : ℝ) ^ (1 - p.sb))) + Real.exp (-((n : ℝ) ^ (1 - s₂))) with heHit
  set eCont := Real.exp (-(c * n)) + 2 * Real.exp (-((n : ℝ) ^ (1 - p.sb))) with heCont
  have hpinC : ∀ θ k, (experimentLaw W p n).real (pinCoarseEvent W β hβ p n θ k R) ≤ ePin := by
    intro θ k
    have h := experiment_real_of_run W p n θ k (hAn θ k).2 _
      (measurableSet_pinGap W β hβ p n (readoutTime p.a p.b n) ((R : ℝ) / 4))
    exact (le_of_eq h).trans hPn.1
  have hpinF : ∀ θ k, (experimentLaw W p n).real (pinFineEvent W β hβ p n θ k R) ≤ ePin := by
    intro θ k
    have h := experiment_real_of_run W p n θ k (hAn θ k).2 _
      (measurableSet_pinGap W β hβ p n (readoutTime p.a p.f n) ((R : ℝ) / 4))
    exact (le_of_eq h).trans hPn.2
  have hhit : ∀ j ≤ gridSize p n, (experimentLaw W p n).real (hitEvent W β hβ p n j) ≤ eHit := by
    intro j hj
    rw [hitEvent_eq W β hβ p n j hj, experiment_real_of_regression W p n _ _ (hAn _ _).1 _
      (measurableSet_coarseHitEvent W β hβ p n)]
    exact hHn
  have hcont : ∀ j < gridSize p n, (experimentLaw W p n).real
      (contEvent W β hβ p n j R) ≤ eCont := by
    intro j hj
    unfold contEvent
    exact hCn j hj
  have hsum := notGood_le W β hβ p n ePin eCont eHit hpinC hpinF hcont hhit (by positivity)
    (by positivity)
  have hmE := gridSize_le p n
  have hRn : (n : ℝ) ^ (1 - p.r) ≤ R := Nat.le_ceil _
  have hePinle : ePin ≤ 2 * Real.exp (-((1 / 64) * (n : ℝ) ^ (1 - p.r))) := by
    rw [hePin]
    gcongr
    linarith
  have hcn : Real.exp (-(c * n)) = Real.exp (-(c * (n : ℝ) ^ (1 : ℝ))) := by
    rw [Real.rpow_one]
  rw [one_mul] at h3 h4
  rw [heCont, heHit, hcn] at hsum
  exact absorption_arith _ (gridSize p n : ℝ) (Real.exp ((n : ℝ) ^ p.grid)) ePin _ _ _ _ _ hsum
    (Nat.cast_nonneg _) hmE (by positivity) hePinle (Real.exp_pos _).le (Real.exp_pos _).le
    (Real.exp_pos _).le h1 h2 h3 h4

end SKConstants.Blueprint
