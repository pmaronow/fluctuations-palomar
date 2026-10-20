module

public import SKBarriers2.Corner.FrozenMerge
public import SKBarriers2.Corner.FrozenGaussian

@[expose] public section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

structure QuadraticTerminal where
  constant : ℝ
  linear : Vec3
  hessian : Fin 3 → Fin 3 → ℝ
  symmetric : ∀ i j, hessian i j = hessian j i

namespace QuadraticTerminal

def value (Q : QuadraticTerminal) (x : Vec3) : ℝ :=
  Q.constant + (∑ i, Q.linear i * x i) + (1 / 2 : ℝ) * ∑ i, ∑ j, x i * Q.hessian i j * x j

def hessianDirection (Q : QuadraticTerminal) (v : Vec3) : Vec3 :=
  fun i => ∑ j, Q.hessian i j * v j

def linearDirection (Q : QuadraticTerminal) (v : Vec3) : ℝ := ∑ i, Q.linear i * v i

def curvature (Q : QuadraticTerminal) (v : Vec3) : ℝ :=
  ∑ i, v i * Q.hessianDirection v i

def slope (Q : QuadraticTerminal) (v x : Vec3) : ℝ :=
  Q.linearDirection v + ∑ i, x i * Q.hessianDirection v i

def precision (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) : ℝ := 1 - m * Q.curvature v

def update (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) : QuadraticTerminal where
  constant := Q.constant - Real.log (Q.precision m v) / (2 * m) +
    m * Q.linearDirection v ^ 2 / (2 * Q.precision m v)
  linear := fun i => Q.linear i + m / Q.precision m v * Q.linearDirection v * Q.hessianDirection v i
  hessian := fun i j => Q.hessian i j + m / Q.precision m v * Q.hessianDirection v i * Q.hessianDirection v j
  symmetric := fun i j => by rw [Q.symmetric i j]; ring

theorem value_shift (Q : QuadraticTerminal) (v x : Vec3) (t : ℝ) :
    Q.value (x + t • v) = Q.value x + Q.slope v x * t + Q.curvature v / 2 * t ^ 2 := by
  simp [value, slope, curvature, linearDirection, hessianDirection,
    Fin.sum_univ_succ]
  rw [Q.symmetric 1 0, Q.symmetric 2 0, Q.symmetric 2 1]
  ring

theorem update_value (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) :
    (Q.update m v).value x = Q.value x - Real.log (Q.precision m v) / (2 * m) +
      m * Q.slope v x ^ 2 / (2 * Q.precision m v) := by
  simp only [update, value, slope, linearDirection, Fin.sum_univ_succ]
  ring

theorem vectorStep_value (Q : QuadraticTerminal) (m : ℝ) (v : Vec3)
    (hm : m ≠ 0) (hD : 0 < Q.precision m v) :
    vectorStep m v Q.value = (Q.update m v).value := by
  funext x
  have he : vectorStep m v Q.value x =
      gaussianStep m (fun p : Unit × ℝ => Q.value x + Q.slope v x * p.2 + Q.curvature v / 2 * p.2 ^ 2) () := by
    simp only [vectorStep, gaussianStep, positiveGaussianLogStep, value_shift]
  rw [he, gaussianStep_quadratic hm hD, update_value]
  rfl

theorem vectorStep_perturbation (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (K : Vec3 → ℝ) (ε : ℝ) :
    vectorStep m v (fun y => Q.value y + ε * K y) x =
      quadraticPerturbation m (Q.value x) (Q.slope v x) (Q.curvature v)
        (fun t => K (x + t • v)) ε := by
  simp only [vectorStep, quadraticPerturbation, gaussianStep, positiveGaussianLogStep, value_shift]

theorem vectorStep_perturbation_first (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (K : Vec3 → ℝ) (hm : m ≠ 0) (hD : 0 < Q.precision m v)
    (hK : 0 ∈ interior (integrableExpSet (fun t => K (x + t • v))
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))) :
    HasDerivAt (fun ε => vectorStep m v (fun y => Q.value y + ε * K y) x)
      (∫ t, K (x + t • v) ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) 0 := by
  simpa only [vectorStep_perturbation, precision] using
    quadraticPerturbation_hasDerivAt_zero hm hD (Q.value x) (Q.slope v x) (fun t => K (x + t • v)) hK

theorem vectorStep_perturbation_second (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (K : Vec3 → ℝ) (hm : m ≠ 0) (hD : 0 < Q.precision m v)
    (hK : 0 ∈ interior (integrableExpSet (fun t => K (x + t • v))
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))) :
    iteratedDeriv 2 (fun ε => vectorStep m v (fun y => Q.value y + ε * K y) x) 0 =
      m * ((∫ t, K (x + t • v) ^ 2 ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) -
        (∫ t, K (x + t • v) ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) ^ 2) := by
  simpa only [vectorStep_perturbation, precision] using
    quadraticPerturbation_second_zero hm hD (Q.value x) (Q.slope v x) (fun t => K (x + t • v)) hK

end QuadraticTerminal

def riccatiRecursion : List (ℝ × Vec3) → QuadraticTerminal → QuadraticTerminal
  | [], Q => Q
  | u :: l, Q => (riccatiRecursion l Q).update u.1 u.2

def RiccatiAdmissible : List (ℝ × Vec3) → QuadraticTerminal → Prop
  | [], _ => True
  | u :: l, Q => RiccatiAdmissible l Q ∧ u.1 ≠ 0 ∧ 0 < (riccatiRecursion l Q).precision u.1 u.2

theorem vectorIncrementChain_quadratic (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hQ : RiccatiAdmissible l Q) :
    vectorIncrementChain l Q.value = (riccatiRecursion l Q).value := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    rcases hQ with ⟨hl, hm, hD⟩
    rw [vectorIncrementChain, ih hl]
    exact (riccatiRecursion l Q).vectorStep_value u.1 u.2 hm hD

def separableTaylorQuadratic (c u χ z : ℝ) : QuadraticTerminal where
  constant := 3 * c - 3 * u * z + (3 / 2 : ℝ) * χ * z ^ 2
  linear := fun _ => u - χ * z
  hessian := fun i j => if i = j then χ else 0
  symmetric := fun i j => by by_cases he : i = j <;> simp [he, eq_comm]

theorem separableTaylorQuadratic_value (c u χ z : ℝ) (x : Vec3) :
    (separableTaylorQuadratic c u χ z).value x =
      ∑ i : Fin 3, (c + u * (x i - z) + χ / 2 * (x i - z) ^ 2) := by
  simp [separableTaylorQuadratic, QuadraticTerminal.value, Fin.sum_univ_succ]
  ring

def directionSize (v : Vec3) : ℝ := ∑ i, |v i|

def directionEnergy (v : Vec3) : ℝ := directionSize v ^ 2

theorem directionSize_nonneg (v : Vec3) : 0 ≤ directionSize v := by
  exact Finset.sum_nonneg (fun i _ => abs_nonneg (v i))

theorem directionEnergy_nonneg (v : Vec3) : 0 ≤ directionEnergy v := by
  exact sq_nonneg _

def squaredLength (v : Vec3) : ℝ := ∑ i, v i ^ 2

def chainEnergy (l : List (ℝ × Vec3)) : ℝ := (l.map fun u => squaredLength u.2).sum

theorem squaredLength_nonneg (v : Vec3) : 0 ≤ squaredLength v := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

theorem chainEnergy_eq_trace (l : List (ℝ × Vec3)) :
    chainEnergy l = ∑ i, matrixChainCovariance l i i := by
  induction l with
  | nil => simp [chainEnergy]
  | cons u l ih =>
    simp only [chainEnergy, List.map_cons, List.sum_cons, matrixChainCovariance_cons,
      Pi.add_apply, rankOneMatrix, Finset.sum_add_distrib]
    rw [← ih]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem directionEnergy_le_squaredLength (v : Vec3) :
    directionEnergy v ≤ 3 * squaredLength v := by
  have h₀₁ := sq_nonneg (|v 0| - |v 1|)
  have h₀₂ := sq_nonneg (|v 0| - |v 2|)
  have h₁₂ := sq_nonneg (|v 1| - |v 2|)
  simp only [directionEnergy, directionSize, squaredLength]
  simp [Fin.sum_univ_succ]
  nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]

theorem squaredLength_le_chainEnergy {l : List (ℝ × Vec3)} {u : ℝ × Vec3} (hu : u ∈ l) :
    squaredLength u.2 ≤ chainEnergy l := by
  exact List.single_le_sum (fun t ht => by
    rcases List.mem_map.mp ht with ⟨v, _, rfl⟩
    exact squaredLength_nonneg v.2) _ (List.mem_map.mpr ⟨u, hu, rfl⟩)

namespace QuadraticTerminal

theorem hessianDirection_abs_le {Q : QuadraticTerminal} {B : ℝ} (_hB : 0 ≤ B)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (v : Vec3) (i : Fin 3) :
    |Q.hessianDirection v i| ≤ B * directionSize v := by
  calc
    _ ≤ ∑ j, |Q.hessian i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, B * |v j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hQ i j) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem curvature_abs_le {Q : QuadraticTerminal} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (v : Vec3) :
    |Q.curvature v| ≤ B * directionEnergy v := by
  calc
    _ ≤ ∑ i, |v i * Q.hessianDirection v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| * (B * directionSize v) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hessianDirection_abs_le hB hQ v i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold directionEnergy directionSize; ring

theorem update_small {Q : QuadraticTerminal} {B m : ℝ} (hB : 0 < B)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (hm : m ∈ Icc (0 : ℝ) 1) (v : Vec3)
    (hv : 2 * B * directionEnergy v ≤ 1) :
    1 / 2 ≤ Q.precision m v ∧ ∀ i j, |(Q.update m v).hessian i j| ≤ 2 * B := by
  have hc := curvature_abs_le hB.le hQ v
  have hcurv : m * Q.curvature v ≤ B * directionEnergy v := by
    calc
      _ ≤ m * |Q.curvature v| := mul_le_mul_of_nonneg_left (le_abs_self _) hm.1
      _ ≤ |Q.curvature v| := mul_le_of_le_one_left (abs_nonneg _) hm.2
      _ ≤ _ := hc
  have hprec : 1 / 2 ≤ Q.precision m v := by unfold precision; linarith
  refine ⟨hprec, ?_⟩
  have hD : 0 < Q.precision m v := by linarith
  have hcoef : m / Q.precision m v ∈ Icc (0 : ℝ) 2 := by
    refine ⟨div_nonneg hm.1 hD.le, (div_le_iff₀ hD).mpr ?_⟩
    linarith [hm.2]
  intro i j
  have hprod : |Q.hessianDirection v i * Q.hessianDirection v j| ≤ (B * directionSize v) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hessianDirection_abs_le hB.le hQ v i)
      (hessianDirection_abs_le hB.le hQ v j) (abs_nonneg _) (mul_nonneg hB.le (directionSize_nonneg v))
  have hsmall := mul_le_mul_of_nonneg_left hv hB.le
  calc
    _ ≤ |Q.hessian i j| + |m / Q.precision m v| *
        |Q.hessianDirection v i * Q.hessianDirection v j| := by
      change |Q.hessian i j + m / Q.precision m v * Q.hessianDirection v i * Q.hessianDirection v j| ≤ _
      simpa only [abs_mul, mul_assoc] using abs_add_le (Q.hessian i j)
        (m / Q.precision m v * Q.hessianDirection v i * Q.hessianDirection v j)
    _ ≤ B + 2 * (B * directionSize v) ^ 2 := by
      rw [abs_of_nonneg hcoef.1]
      exact add_le_add (hQ i j) (mul_le_mul hcoef.2 hprod (abs_nonneg _) (by norm_num))
    _ ≤ 2 * B := by unfold directionEnergy at hsmall; nlinarith

end QuadraticTerminal

theorem riccatiAdmissible_of_small_directions (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {B : ℝ} (hB : 0 < B) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (hm : ∀ u ∈ l, 0 < u.1 ∧ u.1 ≤ 1)
    (hv : ∀ u ∈ l, 2 * (2 ^ l.length * B) * directionEnergy u.2 ≤ 1) :
    RiccatiAdmissible l Q ∧ ∀ i j, |(riccatiRecursion l Q).hessian i j| ≤ 2 ^ l.length * B := by
  induction l with
  | nil => simpa only [RiccatiAdmissible, riccatiRecursion, List.length_nil, pow_zero, one_mul] using And.intro True.intro hQ
  | cons u l ih =>
    have hpow : 0 < (2 : ℝ) ^ l.length * B := mul_pos (by positivity) hB
    have he (v : Vec3) : 2 * ((2 : ℝ) ^ l.length * B) * directionEnergy v ≤
        2 * ((2 : ℝ) ^ (u :: l).length * B) * directionEnergy v := by
      simp only [List.length_cons, pow_succ]
      have hE := directionEnergy_nonneg v
      nlinarith
    have ht := ih (fun v hv' => hm v (List.mem_cons_of_mem _ hv'))
      (fun v hv' => (he v.2).trans (hv v (List.mem_cons_of_mem _ hv')))
    have hu := hm u (List.mem_cons_self)
    have hup := QuadraticTerminal.update_small hpow ht.2 ⟨hu.1.le, hu.2⟩ u.2
      ((he u.2).trans (hv u List.mem_cons_self))
    refine ⟨⟨ht.1, ne_of_gt hu.1, lt_of_lt_of_le (by norm_num) hup.1⟩, ?_⟩
    intro i j
    change |((riccatiRecursion l Q).update u.1 u.2).hessian i j| ≤ 2 ^ (l.length + 1) * B
    calc
      _ ≤ 2 * (2 ^ l.length * B) := hup.2 i j
      _ = _ := by rw [pow_succ]; ring

def riccatiPrecisions : List (ℝ × Vec3) → QuadraticTerminal → List ℝ
  | [], _ => []
  | u :: l, Q => (riccatiRecursion l Q).precision u.1 u.2 :: riccatiPrecisions l Q

theorem riccatiPrecisions_ge_half (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {B : ℝ} (hB : 0 < B) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (hm : ∀ u ∈ l, 0 < u.1 ∧ u.1 ≤ 1)
    (hv : ∀ u ∈ l, 2 * (2 ^ l.length * B) * directionEnergy u.2 ≤ 1) :
    ∀ D ∈ riccatiPrecisions l Q, 1 / 2 ≤ D := by
  induction l with
  | nil => simp [riccatiPrecisions]
  | cons u l ih =>
    have hpow : 0 < (2 : ℝ) ^ l.length * B := mul_pos (by positivity) hB
    have he (v : Vec3) : 2 * ((2 : ℝ) ^ l.length * B) * directionEnergy v ≤
        2 * ((2 : ℝ) ^ (u :: l).length * B) * directionEnergy v := by
      simp only [List.length_cons, pow_succ]
      have hE := directionEnergy_nonneg v
      nlinarith
    have hmt := fun v hv' => hm v (List.mem_cons_of_mem _ hv')
    have hvt := fun v hv' => (he v.2).trans (hv v (List.mem_cons_of_mem _ hv'))
    have ht := riccatiAdmissible_of_small_directions l Q hB hQ hmt hvt
    have hu := hm u List.mem_cons_self
    have hp := (QuadraticTerminal.update_small hpow ht.2 ⟨hu.1.le, hu.2⟩ u.2
      ((he u.2).trans (hv u List.mem_cons_self))).1
    intro D hD
    rcases List.mem_cons.mp hD with hD | hD
    · simpa only [← hD] using hp
    · exact ih hmt hvt D hD

theorem frozenSchedule_chainEnergy (β a h k : ℝ) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    chainEnergy (frozenSchedule β a (1 / 2) h k) = 12 * β ^ 2 * h := by
  rw [chainEnergy_eq_trace, frozenSchedule_covariance β a (1 / 2) h k hh (by norm_num)
    (OW.repairLength_mem (by norm_num) hk)]
  simp [Fin.sum_univ_succ]
  ring

theorem frozenSchedule_masses (β a p h k : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1) :
    ∀ u ∈ frozenSchedule β a p h k, 0 < u.1 ∧ u.1 ≤ 1 := by
  have ha₂ : 0 < a / 2 ∧ a / 2 ≤ 1 := ⟨div_pos ha.1 (by norm_num), by linarith [ha.2]⟩
  have ha₃ : 0 < a / 3 ∧ a / 3 ≤ 1 := ⟨div_pos ha.1 (by norm_num), by linarith [ha.2]⟩
  simp [frozenSchedule, frozenCommon, frozenShared, frozenInner, ha.1, ha.2,
    ha₂.1, ha₂.2, ha₃.1, ha₃.2]

theorem frozenSchedule_mass_floor (β a p h k a₀ : ℝ) (ha₀ : 0 ≤ a₀) (ha : a₀ ≤ a) :
    ∀ u ∈ frozenSchedule β a p h k, a₀ / 3 ≤ u.1 := by
  have h₁ : a₀ / 3 ≤ a := by linarith
  have h₂ : a₀ / 3 ≤ a / 2 := by linarith
  have h₃ : a₀ / 3 ≤ a / 3 := by linarith
  simp [frozenSchedule, frozenCommon, frozenShared, frozenInner, h₁, h₂, h₃]

theorem frozenSchedule_small_directions (β a h k : ℝ) {B : ℝ} (hB : 0 < B)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1) :
    ∀ u ∈ frozenSchedule β a (1 / 2) h k,
      2 * (2 ^ (frozenSchedule β a (1 / 2) h k).length * B) * directionEnergy u.2 ≤ 1 := by
  intro u hu
  have hnoise : directionEnergy u.2 ≤ 36 * β ^ 2 * h := by
    calc
      _ ≤ 3 * squaredLength u.2 := directionEnergy_le_squaredLength _
      _ ≤ 3 * chainEnergy (frozenSchedule β a (1 / 2) h k) :=
        mul_le_mul_of_nonneg_left (squaredLength_le_chainEnergy hu) (by norm_num)
      _ = _ := by rw [frozenSchedule_chainEnergy β a h k hh hk]; ring
  rw [frozenSchedule_length]
  calc
    _ ≤ 2 * (2 ^ 12 * B) * (36 * β ^ 2 * h) := mul_le_mul_of_nonneg_left hnoise (by positivity)
    _ = 72 * (2 ^ 12 * B) * β ^ 2 * h := by ring
    _ ≤ 1 := hsmall

theorem frozenSchedule_riccatiAdmissible (β a h k : ℝ) (Q : QuadraticTerminal)
    {B : ℝ} (hB : 0 < B) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (ha : a ∈ Ioc (0 : ℝ) 1) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1) :
    RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q ∧
      ∀ i j, |(riccatiRecursion (frozenSchedule β a (1 / 2) h k) Q).hessian i j| ≤ 2 ^ 12 * B := by
  simpa only [frozenSchedule_length] using riccatiAdmissible_of_small_directions
    (frozenSchedule β a (1 / 2) h k) Q hB hQ (frozenSchedule_masses β a (1 / 2) h k ha)
    (frozenSchedule_small_directions β a h k hB hh hk hsmall)

theorem frozenSchedule_precisions_ge_half (β a h k : ℝ) (Q : QuadraticTerminal)
    {B : ℝ} (hB : 0 < B) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (ha : a ∈ Ioc (0 : ℝ) 1) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1) :
    ∀ D ∈ riccatiPrecisions (frozenSchedule β a (1 / 2) h k) Q, 1 / 2 ≤ D := by
  exact riccatiPrecisions_ge_half _ Q hB hQ (frozenSchedule_masses β a (1 / 2) h k ha)
    (frozenSchedule_small_directions β a h k hB hh hk hsmall)

def frozenTheta (β a p h k : ℝ) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (x : Vec3) (ε : ℝ) : ℝ :=
  vectorIncrementChain (frozenSchedule β a p h k)
    (fun y => Q.value y + ε * (G y - Q.value y)) x

theorem frozenTheta_one (β a p h k : ℝ) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (x : Vec3) :
    frozenTheta β a p h k Q G x 1 = vectorIncrementChain (frozenSchedule β a p h k) G x := by
  simp only [frozenTheta, one_mul, add_sub_cancel]

theorem frozenTheta_zero (β a p h k : ℝ) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (x : Vec3)
    (hQ : RiccatiAdmissible (frozenSchedule β a p h k) Q) :
    frozenTheta β a p h k Q G x 0 = (riccatiRecursion (frozenSchedule β a p h k) Q).value x := by
  simp only [frozenTheta, zero_mul, add_zero]
  rw [vectorIncrementChain_quadratic _ Q hQ]

def terminalTaylorQuadratic (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) : QuadraticTerminal :=
  separableTaylorQuadratic (Phi β α (s + 4 * h) z) (jet β α 1 (s + 4 * h) z)
    (jet β α 2 (s + 4 * h) z) z

theorem terminalTaylorQuadratic_value (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (x : Vec3) :
    (terminalTaylorQuadratic β α s h z).value x =
      ∑ i : Fin 3, (Phi β α (s + 4 * h) z + jet β α 1 (s + 4 * h) z * (x i - z) +
        jet β α 2 (s + 4 * h) z / 2 * (x i - z) ^ 2) := by
  exact separableTaylorQuadratic_value _ _ _ _ x

theorem terminalTaylorQuadratic_hessian_bound (β : ℝ) (α : ℝ → ℝ) (s h z B : ℝ)
    (hB : 0 ≤ B) (hχ : |jet β α 2 (s + 4 * h) z| ≤ B) :
    ∀ i j, |(terminalTaylorQuadratic β α s h z).hessian i j| ≤ B := by
  intro i j
  change |if i = j then jet β α 2 (s + 4 * h) z else 0| ≤ B
  split_ifs
  · exact hχ
  · simpa using hB

theorem terminalTaylorQuadratic_uniform_admissible (β B : ℝ) (hB : 0 < B) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h k z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → |k| ≤ 1 / 2 →
      |jet β α 2 (s + 4 * h) z| ≤ B →
      RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) := by
  let D : ℝ := 72 * (2 ^ 12 * B) * (β ^ 2 + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro α a s h k z ha hh hh₀ hk hχ
  have hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ D * h := by dsimp [D]; nlinarith
      _ ≤ D * D⁻¹ := mul_le_mul_of_nonneg_left hh₀ hD.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hD)
  exact (frozenSchedule_riccatiAdmissible β a h k _ hB
    (terminalTaylorQuadratic_hessian_bound β α s h z B hB.le hχ) ha hh hk hsmall).1

def terminalResidual (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (x : Vec3) : ℝ :=
  frozenTerminal β α s h x - (terminalTaylorQuadratic β α s h z).value x

private theorem scalar_residual_growth {φ : ℝ → ℝ} {B u χ z : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ y, |φ y - φ z| ≤ B * |y - z|) (hu : |u| ≤ B) (hχ : |χ| ≤ B) (y : ℝ) :
    |φ y - (φ z + u * (y - z) + χ / 2 * (y - z) ^ 2)| ≤ 2 * B * (1 + (y - z) ^ 2) := by
  have hu' : |u * (y - z)| ≤ B * |y - z| := by rw [abs_mul]; gcongr
  have hχ' : |χ / 2 * (y - z) ^ 2| ≤ B / 2 * (y - z) ^ 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (y - z))]
    norm_num
    gcongr
  have he : 2 * |y - z| ≤ 1 + (y - z) ^ 2 := by nlinarith [sq_nonneg (|y - z| - 1), sq_abs (y - z)]
  have heB := mul_le_mul_of_nonneg_left he hB
  calc
    _ = |(φ y - φ z) - u * (y - z) - χ / 2 * (y - z) ^ 2| := by congr 1; ring
    _ ≤ |(φ y - φ z) - u * (y - z)| + |χ / 2 * (y - z) ^ 2| := abs_sub _ _
    _ ≤ |φ y - φ z| + |u * (y - z)| + |χ / 2 * (y - z) ^ 2| := by
      gcongr
      exact abs_sub _ _
    _ ≤ B * |y - z| + B * |y - z| + B / 2 * (y - z) ^ 2 := add_le_add (add_le_add (hφ y) hu') hχ'
    _ ≤ _ := by nlinarith [mul_nonneg hB (sq_nonneg (y - z))]

theorem terminalResidual_growth (β : ℝ) (α : ℝ → ℝ) (s h z B : ℝ)
    (hB : 0 ≤ B) (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B) (x v : Vec3) (t : ℝ) :
    |terminalResidual β α s h z (x + t • v)| ≤
      (6 * B + 4 * B * ∑ i, (x i - z) ^ 2) + (4 * B * squaredLength v) * t ^ 2 := by
  have hφ (y : ℝ) : |Phi β α (s + 4 * h) y - Phi β α (s + 4 * h) z| ≤ B * |y - z| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
      (fun y (_ : y ∈ (Set.univ : Set ℝ)) => hΦ.1.differentiable (by norm_num) y)
      (fun y (_ : y ∈ (Set.univ : Set ℝ)) => by
        simpa only [jet, iteratedDeriv_one, Real.norm_eq_abs] using h₁ y)
      convex_univ (Set.mem_univ z) (Set.mem_univ y)
  have hr (y : ℝ) := scalar_residual_growth hB hφ (h₁ z) h₂ y
  have he : terminalResidual β α s h z (x + t • v) =
      ∑ i : Fin 3, (Phi β α (s + 4 * h) ((x + t • v) i) -
        (Phi β α (s + 4 * h) z + jet β α 1 (s + 4 * h) z * ((x + t • v) i - z) +
          jet β α 2 (s + 4 * h) z / 2 * ((x + t • v) i - z) ^ 2)) := by
    rw [terminalResidual, terminalTaylorQuadratic_value, Finset.sum_sub_distrib]
    rfl
  rw [he]
  calc
    _ ≤ ∑ i, |Phi β α (s + 4 * h) ((x + t • v) i) -
        (Phi β α (s + 4 * h) z + jet β α 1 (s + 4 * h) z * ((x + t • v) i - z) +
          jet β α 2 (s + 4 * h) z / 2 * ((x + t • v) i - z) ^ 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, (2 * B + 4 * B * (x i - z) ^ 2 + 4 * B * t ^ 2 * v i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hri := hr ((x + t • v) i)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hri ⊢
      have hs := mul_le_mul_of_nonneg_left (sq_nonneg ((x i - z) - t * v i)) hB
      nlinarith
    _ = _ := by simp [squaredLength, Fin.sum_univ_succ]; ring

theorem terminalResidual_continuous (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) : Continuous (terminalResidual β α s h z) := by
  have hG := (frozenTerminal_regular β α s h hΦ).1.continuous
  have hQ : Continuous (terminalTaylorQuadratic β α s h z).value := by
    unfold QuadraticTerminal.value
    fun_prop
  exact hG.sub hQ

theorem terminalResidual_uniform_moments (β a s h k z B : ℝ) {α : ℝ → ℝ} (hB : 0 < B)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1)
    {u : ℝ × Vec3} (hu : u ∈ frozenSchedule β a (1 / 2) h k)
    (x : Vec3) (D L ε : ℝ) (hD : 1 / 2 ≤ D) (hε : |ε| ≤ 1) :
    Integrable (fun t => Real.exp (ε * terminalResidual β α s h z (x + t • u.2)))
      (quadraticGaussian D L) := by
  have hnoise : squaredLength u.2 ≤ 12 * β ^ 2 * h := by
    calc
      _ ≤ chainEnergy (frozenSchedule β a (1 / 2) h k) := squaredLength_le_chainEnergy hu
      _ = _ := frozenSchedule_chainEnergy β a h k hh hk
  have hC : 0 ≤ 4 * B * squaredLength u.2 :=
    mul_nonneg (by positivity) (squaredLength_nonneg _)
  apply integrable_exp_quadraticGrowth (by linarith : 0 < D) hC L
    (6 * B + 4 * B * ∑ i, (x i - z) ^ 2) ε
    ((terminalResidual_continuous β α s h z hΦ).comp (by fun_prop))
    (terminalResidual_growth β α s h z B hB.le hΦ h₁ h₂ x u.2)
  have hn := mul_le_mul_of_nonneg_left hnoise (by positivity : 0 ≤ 4 * B)
  have he := mul_le_mul_of_nonneg_right hε hC
  norm_num at hsmall
  nlinarith

theorem terminalResidual_moment_interior (β a s h k z B : ℝ) {α : ℝ → ℝ} (hB : 0 < B)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1)
    {u : ℝ × Vec3} (hu : u ∈ frozenSchedule β a (1 / 2) h k)
    (x : Vec3) (D L : ℝ) (hD : 1 / 2 ≤ D) :
    0 ∈ interior (integrableExpSet (fun t => terminalResidual β α s h z (x + t • u.2))
      (quadraticGaussian D L)) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  intro ε hε
  exact terminalResidual_uniform_moments β a s h k z B hB hΦ h₁ h₂ hh hk hsmall hu x D L ε hD
    (le_of_lt (abs_lt.mpr hε))

theorem terminalResidual_memLp (β a s h k z B : ℝ) {α : ℝ → ℝ} (hB : 0 < B)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1)
    {u : ℝ × Vec3} (hu : u ∈ frozenSchedule β a (1 / 2) h k)
    (x : Vec3) (D L : ℝ) (hD : 1 / 2 ≤ D) (p : ℝ≥0) :
    MemLp (fun t => terminalResidual β α s h z (x + t • u.2)) p (quadraticGaussian D L) := by
  exact memLp_of_mem_interior_integrableExpSet
    (terminalResidual_moment_interior β a s h k z B hB hΦ h₁ h₂ hh hk hsmall hu x D L hD) p

theorem frozen_uniform_startup (β B a₀ : ℝ) (hB : 0 < B) (ha₀ : 0 < a₀) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (s h k z : ℝ),
      α s ∈ Icc a₀ 1 → 0 ≤ h → h ≤ h₀ → |k| ≤ 1 / 2 →
      BoundedDerivs (Phi β α (s + 4 * h)) →
      (∀ y, |jet β α 1 (s + 4 * h) y| ≤ B) → |jet β α 2 (s + 4 * h) z| ≤ B →
      RiccatiAdmissible (frozenSchedule β (α s) (1 / 2) h k) (terminalTaylorQuadratic β α s h z) ∧
      (∀ D ∈ riccatiPrecisions (frozenSchedule β (α s) (1 / 2) h k) (terminalTaylorQuadratic β α s h z), 1 / 2 ≤ D) ∧
      ∀ u ∈ frozenSchedule β (α s) (1 / 2) h k, ∀ (x : Vec3) (D L ε : ℝ),
        1 / 2 ≤ D → |ε| ≤ 1 →
        Integrable (fun t => Real.exp (ε * terminalResidual β α s h z (x + t • u.2)))
          (quadraticGaussian D L) := by
  let R : ℝ := 72 * (2 ^ 12 * B) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro α s h k z ha hh hh₀ hk hΦ h₁ h₂
  have hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ R * h := by dsimp [R]; nlinarith
      _ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left hh₀ hR.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  refine ⟨(frozenSchedule_riccatiAdmissible β (α s) h k _ hB
    (terminalTaylorQuadratic_hessian_bound β α s h z B hB.le h₂)
    ⟨lt_of_lt_of_le ha₀ ha.1, ha.2⟩ hh hk hsmall).1, ?_⟩
  refine ⟨frozenSchedule_precisions_ge_half β (α s) h k _ hB
    (terminalTaylorQuadratic_hessian_bound β α s h z B hB.le h₂)
    ⟨lt_of_lt_of_le ha₀ ha.1, ha.2⟩ hh hk hsmall, ?_⟩
  intro u hu x D L ε hD hε
  exact terminalResidual_uniform_moments β (α s) s h k z B hB hΦ h₁ h₂ hh hk hsmall hu x D L ε hD hε

structure FrozenJetHypotheses (β : ℝ) (α : ℝ → ℝ) (J : Set ℝ) (a₀ B : ℝ) : Prop where
  mass_pos : 0 < a₀
  bound_pos : 0 < B
  mass_range : ∀ t ∈ J, α t ∈ Icc a₀ 1
  spatial_smooth : ∀ t ∈ J, ContDiff ℝ 12 (Phi β α t)
  spatial_jets : ∀ j : ℕ, 1 ≤ j → j ≤ 12 → ∀ t ∈ J, ∀ x, |jet β α j t x| ≤ B
  time_deriv : ∀ j : ℕ, j ≤ 6 → ∀ t ∈ J, ∀ x,
    HasDerivAt (fun τ => jet β α j τ x)
      (-(β ^ 2 / 2) * (jet β α (j + 2) t x +
        α t * iteratedDeriv j (fun y => jet β α 1 t y ^ 2) x)) t

namespace FrozenJetHypotheses

theorem terminal_regular {β a₀ B : ℝ} {α : ℝ → ℝ} {J : Set ℝ}
    (H : FrozenJetHypotheses β α J a₀ B) {t : ℝ} (ht : t ∈ J) :
    BoundedDerivs (Phi β α t) := by
  refine ⟨(H.spatial_smooth t ht).of_le (by norm_num), B, B, H.bound_pos.le, H.bound_pos.le, ?_, ?_⟩
  · intro x
    rw [← norm_deriv_eq_norm_fderiv]
    simpa only [jet, iteratedDeriv_one, Real.norm_eq_abs] using H.spatial_jets 1 le_rfl (by norm_num) t ht x
  · intro x
    have hh : ‖iteratedFDeriv ℝ 2 (Phi β α t) x‖ ≤ B := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact H.spatial_jets 2 (by norm_num) (by norm_num) t ht x
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at hh
    exact hh

theorem uniform_startup {β a₀ B : ℝ} {α : ℝ → ℝ} {J : Set ℝ}
    (H : FrozenJetHypotheses β α J a₀ B) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ (s h k z : ℝ), s ∈ J → s + 4 * h ∈ J →
      0 ≤ h → h ≤ h₀ → |k| ≤ 1 / 2 →
      RiccatiAdmissible (frozenSchedule β (α s) (1 / 2) h k) (terminalTaylorQuadratic β α s h z) ∧
      (∀ D ∈ riccatiPrecisions (frozenSchedule β (α s) (1 / 2) h k) (terminalTaylorQuadratic β α s h z), 1 / 2 ≤ D) ∧
      ∀ u ∈ frozenSchedule β (α s) (1 / 2) h k, ∀ (x : Vec3) (D L ε : ℝ),
        1 / 2 ≤ D → |ε| ≤ 1 →
        Integrable (fun t => Real.exp (ε * terminalResidual β α s h z (x + t • u.2)))
          (quadraticGaussian D L) := by
  rcases frozen_uniform_startup β B a₀ H.bound_pos H.mass_pos with ⟨h₀, hh₀, hstart⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro s h k z hs ht hh hhsmall hk
  exact hstart α s h k z (H.mass_range s hs) hh hhsmall hk (H.terminal_regular ht)
    (H.spatial_jets 1 le_rfl (by norm_num) _ ht)
    (H.spatial_jets 2 (by norm_num) (by norm_num) _ ht z)

end FrozenJetHypotheses

def frozenTerminalTheta (β : ℝ) (α : ℝ → ℝ) (a s h k z ε : ℝ) : ℝ :=
  frozenTheta β a (1 / 2) h k (terminalTaylorQuadratic β α s h z)
    (frozenTerminal β α s h) (fun _ => z) ε

theorem frozenTerminalTheta_one (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) :
    frozenTerminalTheta β α a s h k z 1 = frozenBoundary β α a (1 / 2) s h k N z := by
  rw [frozenTerminalTheta, frozenTheta_one, frozenBoundary,
    frozen_window_merge β a (1 / 2) s h k hN hh (by norm_num)
      (OW.repairLength_mem (by norm_num) hk) (frozenTerminal_regular β α s h hΦ)]

theorem frozenTerminalTheta_zero (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)) :
    frozenTerminalTheta β α a s h k z 0 =
      (riccatiRecursion (frozenSchedule β a (1 / 2) h k)
        (terminalTaylorQuadratic β α s h z)).value (fun _ => z) := by
  exact frozenTheta_zero _ _ _ _ _ _ _ _ hQ

theorem frozenTerminalTheta_zero_of_jets {β a₀ B : ℝ} {α : ℝ → ℝ} {J : Set ℝ}
    (H : FrozenJetHypotheses β α J a₀ B) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ (s h k z : ℝ), s ∈ J → s + 4 * h ∈ J →
      0 ≤ h → h ≤ h₀ → |k| ≤ 1 / 2 →
      frozenTerminalTheta β α (α s) s h k z 0 =
        (riccatiRecursion (frozenSchedule β (α s) (1 / 2) h k)
          (terminalTaylorQuadratic β α s h z)).value (fun _ => z) := by
  rcases H.uniform_startup with ⟨h₀, hh₀, hstart⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro s h k z hs ht hh hhsmall hk
  exact frozenTerminalTheta_zero β α (α s) s h k z (hstart s h k z hs ht hh hhsmall hk).1

def quadraticAverage (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) (ψ : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ t, ψ (x + t • v) ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)

def quadraticPartition (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) : ℝ :=
  Real.exp (m * Q.value x) * quadraticNormalizer (Q.precision m v) (m * Q.slope v x)

theorem quadraticPartition_pos (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (hD : 0 < Q.precision m v) : 0 < quadraticPartition Q m v x := by
  exact mul_pos (Real.exp_pos _) (quadraticNormalizer_pos hD _)

theorem quadratic_weighted_moment (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (hD : 0 < Q.precision m v) (ψ : Vec3 → ℝ) :
    (∫ t, Real.exp (m * Q.value (x + t • v)) * ψ (x + t • v) ∂gaussianReal 0 1) =
      quadraticPartition Q m v x * quadraticAverage Q m v ψ x := by
  have he (t : ℝ) : Real.exp (m * Q.value (x + t • v)) = Real.exp (m * Q.value x) *
      Real.exp ((1 - Q.precision m v) * t ^ 2 / 2 + (m * Q.slope v x) * t) := by
    rw [← Real.exp_add, Q.value_shift]
    congr 1
    unfold QuadraticTerminal.precision
    ring
  have heψ (t : ℝ) : Real.exp (m * Q.value (x + t • v)) * ψ (x + t • v) =
      Real.exp (m * Q.value x) * (Real.exp ((1 - Q.precision m v) * t ^ 2 / 2 +
        (m * Q.slope v x) * t) * ψ (x + t • v)) := by rw [he]; ring
  simp_rw [heψ]
  rw [integral_const_mul, integral_quadratic_tilt hD]
  unfold quadraticPartition quadraticAverage
  ring

def epsilonChain (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ) (ε : ℝ) : Vec3 → ℝ :=
  vectorIncrementChain l (fun y => Q.value y + ε * K y)

def quadraticFirst : List (ℝ × Vec3) → QuadraticTerminal → (Vec3 → ℝ) → Vec3 → ℝ
  | [], _, K => K
  | u :: l, Q, K => quadraticAverage (riccatiRecursion l Q) u.1 u.2 (quadraticFirst l Q K)

def quadraticSecond : List (ℝ × Vec3) → QuadraticTerminal → (Vec3 → ℝ) → Vec3 → ℝ
  | [], _, _ => fun _ => 0
  | u :: l, Q, K => fun x =>
      quadraticAverage (riccatiRecursion l Q) u.1 u.2
        (fun y => quadraticSecond l Q K y + u.1 * quadraticFirst l Q K y ^ 2) x -
      u.1 * quadraticFirst (u :: l) Q K x ^ 2

def epsilonWeight (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (u : ℝ × Vec3) (x : Vec3) (ε t : ℝ) : ℝ :=
  Real.exp (u.1 * epsilonChain l Q K ε (x + t • u.2))

def epsilonWeightFirst (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (u : ℝ × Vec3) (x : Vec3) (ε t : ℝ) : ℝ :=
  u.1 * (epsilonWeight l Q K u x ε t *
    deriv (fun e => epsilonChain l Q K e (x + t • u.2)) ε)

def epsilonWeightSecond (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (u : ℝ × Vec3) (x : Vec3) (ε t : ℝ) : ℝ :=
  u.1 * (epsilonWeight l Q K u x ε t *
    (iteratedDeriv 2 (fun e => epsilonChain l Q K e (x + t • u.2)) ε +
      u.1 * deriv (fun e => epsilonChain l Q K e (x + t • u.2)) ε ^ 2))

def EpsilonChainControl : List (ℝ × Vec3) → QuadraticTerminal → (Vec3 → ℝ) → Prop
  | [], _, _ => True
  | u :: l, Q, K => EpsilonChainControl l Q K ∧ ∀ x : Vec3,
      (∀ᶠ ε in 𝓝 (0 : ℝ), IntegralDerivativeControl (gaussianReal 0 1)
        (epsilonWeight l Q K u x) (epsilonWeightFirst l Q K u x) ε) ∧
      IntegralDerivativeControl (gaussianReal 0 1)
        (epsilonWeightFirst l Q K u x) (epsilonWeightSecond l Q K u x) 0

theorem epsilonChain_zero (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (hQ : RiccatiAdmissible l Q) : epsilonChain l Q K 0 = (riccatiRecursion l Q).value := by
  unfold epsilonChain
  simp only [zero_mul, add_zero]
  exact vectorIncrementChain_quadratic l Q hQ

theorem epsilonChain_first_second (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (hQ : RiccatiAdmissible l Q) (hD : EpsilonChainControl l Q K) (x : Vec3) :
    HasDerivAt (fun ε => epsilonChain l Q K ε x) (quadraticFirst l Q K x) 0 ∧
    HasDerivAt (deriv (fun ε => epsilonChain l Q K ε x)) (quadraticSecond l Q K x) 0 := by
  induction l generalizing x with
  | nil =>
    have hd (ε : ℝ) : HasDerivAt (fun e => epsilonChain [] Q K e x) (K x) ε := by
      simpa only [epsilonChain, vectorIncrementChain, one_mul, id_eq] using
        (((hasDerivAt_id ε).mul_const (K x)).const_add (Q.value x))
    refine ⟨hd 0, ?_⟩
    have he : deriv (fun ε => epsilonChain [] Q K ε x) = fun _ => K x := funext (fun ε => (hd ε).deriv)
    rw [he]
    exact hasDerivAt_const 0 (K x)
  | cons u l ih =>
    rcases hQ with ⟨hQ, hm, hp⟩
    rcases hD with ⟨hD, hc⟩
    have hi (y : Vec3) := ih hQ hD y
    let R := riccatiRecursion l Q
    let Z : ℝ → ℝ := fun ε => ∫ t, epsilonWeight l Q K u x ε t ∂gaussianReal 0 1
    let P := quadraticPartition R u.1 u.2 x
    let A := quadraticFirst (u :: l) Q K x
    let B := quadraticAverage R u.1 u.2
      (fun y => quadraticSecond l Q K y + u.1 * quadraticFirst l Q K y ^ 2) x
    have he₀ : Z 0 = P := by
      dsimp only [Z, epsilonWeight]
      rw [epsilonChain_zero l Q K hQ]
      have hw := quadratic_weighted_moment R u.1 u.2 x hp (fun _ => 1)
      simpa [quadraticAverage, quadraticGaussian, P, R] using hw
    have hP : P ≠ 0 := ne_of_gt (quadraticPartition_pos R u.1 u.2 x hp)
    have hc₁ := (hc x).1
    have hz₁ := (hc₁.self_of_nhds).hasDerivAt
    have hz₁val : (∫ t, epsilonWeightFirst l Q K u x 0 t ∂gaussianReal 0 1) = u.1 * (P * A) := by
      unfold epsilonWeightFirst epsilonWeight
      simp_rw [epsilonChain_zero l Q K hQ, (hi _).1.deriv]
      rw [integral_const_mul, quadratic_weighted_moment R u.1 u.2 x hp]
      rfl
    rw [hz₁val] at hz₁
    have hdZ : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ Z ε := by
      filter_upwards [hc₁] with ε hε
      exact hε.hasDerivAt.differentiableAt
    have heZ : deriv Z =ᶠ[𝓝 (0 : ℝ)]
        fun ε => ∫ t, epsilonWeightFirst l Q K u x ε t ∂gaussianReal 0 1 := by
      filter_upwards [hc₁] with ε hε
      exact hε.hasDerivAt.deriv
    have hz₂ := ((hc x).2.hasDerivAt).congr_of_eventuallyEq heZ
    have hz₂val : (∫ t, epsilonWeightSecond l Q K u x 0 t ∂gaussianReal 0 1) = u.1 * (P * B) := by
      unfold epsilonWeightSecond epsilonWeight
      simp_rw [epsilonChain_zero l Q K hQ, (hi _).1.deriv]
      have hi₂ (y : Vec3) : iteratedDeriv 2 (fun e => epsilonChain l Q K e y) 0 = quadraticSecond l Q K y := by
        simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using (hi y).2.deriv
      simp_rw [hi₂]
      rw [integral_const_mul, quadratic_weighted_moment (riccatiRecursion l Q) u.1 u.2 x hp
        (fun y => quadraticSecond l Q K y + u.1 * quadraticFirst l Q K y ^ 2)]
    rw [hz₂val] at hz₂
    have hfun : (fun ε => epsilonChain (u :: l) Q K ε x) = fun ε => Real.log (Z ε) / u.1 := by
      funext ε
      simp only [epsilonChain, vectorIncrementChain, vectorStep, gaussianStep, ite_eq_right hm,
        positiveGaussianLogStep, Z, epsilonWeight]
    rw [hfun]
    have hz₀ : Z 0 ≠ 0 := he₀ ▸ hP
    have H₁ := logPartition_hasDerivAt (Z := Z) (m := u.1) hz₁ hz₀
    have H₂ := logPartition_second (Z := Z) (m := u.1) hz₁ hz₂ hdZ hz₀
    change HasDerivAt (fun ε => Real.log (Z ε) / u.1) (u.1 * (P * A) / Z 0 / u.1) 0 at H₁
    change HasDerivAt (deriv (fun ε => Real.log (Z ε) / u.1))
      ((u.1 * (P * B) * Z 0 - (u.1 * (P * A)) ^ 2) / (Z 0) ^ 2 / u.1) 0 at H₂
    rw [he₀] at H₁ H₂
    refine ⟨?_, ?_⟩
    · convert H₁ using 1
      dsimp only [A]
      field_simp [hm, hP]
    · have hv : (u.1 * (P * B) * P - (u.1 * (P * A)) ^ 2) / P ^ 2 / u.1 = B - u.1 * A ^ 2 := by
        field_simp [hm, hP]
      rw [hv] at H₂
      exact H₂

theorem epsilonChain_eventually_differentiable (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (hQ : RiccatiAdmissible l Q) (hD : EpsilonChainControl l Q K) (x : Vec3) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun e => epsilonChain l Q K e x) ε := by
  cases l with
  | nil =>
    apply Filter.Eventually.of_forall
    intro ε
    simpa only [epsilonChain, vectorIncrementChain, id_eq] using
      ((hasDerivAt_id ε).mul_const (K x)).const_add (Q.value x) |>.differentiableAt
  | cons u l =>
    rcases hQ with ⟨hQ, hm, hp⟩
    have hc := (hD.2 x).1
    let Z : ℝ → ℝ := fun ε => ∫ t, epsilonWeight l Q K u x ε t ∂gaussianReal 0 1
    have hz := hc.self_of_nhds.hasDerivAt
    have hzero : Z 0 = quadraticPartition (riccatiRecursion l Q) u.1 u.2 x := by
      dsimp only [Z, epsilonWeight]
      rw [epsilonChain_zero l Q K hQ]
      have H := quadratic_weighted_moment (riccatiRecursion l Q) u.1 u.2 x hp (fun _ => 1)
      simpa [quadraticAverage, quadraticGaussian] using H
    have hn : Z 0 ≠ 0 := hzero ▸ ne_of_gt (quadraticPartition_pos _ _ _ _ hp)
    have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), Z ε ≠ 0 := hz.continuousAt.eventually_ne hn
    have hfun : (fun ε => epsilonChain (u :: l) Q K ε x) = fun ε => Real.log (Z ε) / u.1 := by
      funext ε
      simp only [epsilonChain, vectorIncrementChain, vectorStep, gaussianStep, ite_eq_right hm,
        positiveGaussianLogStep, Z, epsilonWeight]
    rw [hfun]
    filter_upwards [hc, hnear] with ε hε hnε
    exact ((hε.hasDerivAt.log hnε).div_const u.1).differentiableAt

def quadraticMeanTransition (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) : Vec3 :=
  x + (m * Q.slope v x / Q.precision m v) • v

def gaussianPathMean : List (ℝ × Vec3) → QuadraticTerminal → Vec3 → Vec3
  | [], _, x => x
  | u :: l, Q, x => gaussianPathMean l Q (quadraticMeanTransition (riccatiRecursion l Q) u.1 u.2 x)

def gaussianPathLinear : List (ℝ × Vec3) → QuadraticTerminal → Vec3 → Vec3
  | [], _, w => w
  | u :: l, Q, w => gaussianPathLinear l Q
      (w + (u.1 / (riccatiRecursion l Q).precision u.1 u.2 *
        (∑ i, w i * (riccatiRecursion l Q).hessianDirection u.2 i)) • u.2)

def gaussianPathCovariance : List (ℝ × Vec3) → QuadraticTerminal → Fin 3 → Fin 3 → ℝ
  | [], _, _, _ => 0
  | u :: l, Q, i, j => gaussianPathCovariance l Q i j +
      ((riccatiRecursion l Q).precision u.1 u.2)⁻¹ *
        gaussianPathLinear l Q u.2 i * gaussianPathLinear l Q u.2 j

private theorem quadraticMeanTransition_shift (Q : QuadraticTerminal) (m : ℝ) (v x w : Vec3) (t : ℝ) :
    quadraticMeanTransition Q m v (x + t • w) = quadraticMeanTransition Q m v x +
      t • (w + (m / Q.precision m v * (∑ i, w i * Q.hessianDirection v i)) • v) := by
  have hs : Q.slope v (x + t • w) = Q.slope v x + t * (∑ i, w i * Q.hessianDirection v i) := by
    simp [QuadraticTerminal.slope, Fin.sum_univ_succ]
    ring
  ext i
  simp only [quadraticMeanTransition, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
  ring

theorem gaussianPathMean_shift (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x w : Vec3) (t : ℝ) :
    gaussianPathMean l Q (x + t • w) = gaussianPathMean l Q x + t • gaussianPathLinear l Q w := by
  induction l generalizing x w with
  | nil => rfl
  | cons u l ih =>
    simp only [gaussianPathMean, gaussianPathLinear]
    rw [quadraticMeanTransition_shift, ih]

theorem gaussianPathCovariance_projection (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (u : ℝ × Vec3) (w : Vec3) :
    (∑ i, ∑ j, w i * gaussianPathCovariance (u :: l) Q i j * w j) =
      (∑ i, ∑ j, w i * gaussianPathCovariance l Q i j * w j) +
        ((riccatiRecursion l Q).precision u.1 u.2)⁻¹ * (∑ i, w i * gaussianPathLinear l Q u.2 i) ^ 2 := by
  simp [gaussianPathCovariance, Fin.sum_univ_succ]
  ring

theorem quadraticFirst_exp_linear (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hQ : RiccatiAdmissible l Q) (w x : Vec3) :
    quadraticFirst l Q (fun y => Real.exp (∑ i, w i * y i)) x =
      Real.exp ((∑ i, w i * gaussianPathMean l Q x i) +
        (1 / 2 : ℝ) * ∑ i, ∑ j, w i * gaussianPathCovariance l Q i j * w j) := by
  induction l generalizing x with
  | nil => simp [quadraticFirst, gaussianPathMean, gaussianPathCovariance]
  | cons u l ih =>
    rcases hQ with ⟨hQ, _hm, hp⟩
    change (∫ t, quadraticFirst l Q (fun y => Real.exp (∑ i, w i * y i)) (x + t • u.2)
      ∂quadraticGaussian ((riccatiRecursion l Q).precision u.1 u.2) (u.1 * (riccatiRecursion l Q).slope u.2 x)) = _
    simp_rw [ih hQ]
    let C := (∑ i, w i * gaussianPathMean l Q x i) +
      (1 / 2 : ℝ) * ∑ i, ∑ j, w i * gaussianPathCovariance l Q i j * w j
    let L := ∑ i, w i * gaussianPathLinear l Q u.2 i
    have he (t : ℝ) : (∑ i, w i * gaussianPathMean l Q (x + t • u.2) i) +
        (1 / 2 : ℝ) * ∑ i, ∑ j, w i * gaussianPathCovariance l Q i j * w j = C + L * t := by
      rw [gaussianPathMean_shift]
      simp [C, L, Fin.sum_univ_succ]
      ring
    simp_rw [he]
    rw [integral_exp_linear_quadraticGaussian hp]
    congr 1
    rw [gaussianPathCovariance_projection]
    simp only [gaussianPathMean, quadraticMeanTransition]
    rw [gaussianPathMean_shift]
    simp [C, L, Fin.sum_univ_succ]
    ring

def quadraticVariance (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) (ψ : Vec3 → ℝ) (x : Vec3) : ℝ :=
  quadraticAverage Q m v (fun y => ψ y ^ 2) x - quadraticAverage Q m v ψ x ^ 2

theorem quadraticVariance_eq_variance (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) (ψ : Vec3 → ℝ)
    (hψ : MemLp (fun t => ψ (x + t • v)) 2
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x))) :
    quadraticVariance Q m v ψ x = variance (fun t => ψ (x + t • v))
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
  let : IsProbabilityMeasure (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    unfold quadraticGaussian
    infer_instance
  simpa only [quadraticVariance, quadraticAverage, Pi.pow_apply] using (variance_eq_sub hψ).symm

theorem quadraticSecond_cons (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (u : ℝ × Vec3) (x : Vec3)
    (h₂ : Integrable (fun t => quadraticSecond l Q K (x + t • u.2))
      (quadraticGaussian ((riccatiRecursion l Q).precision u.1 u.2) (u.1 * (riccatiRecursion l Q).slope u.2 x)))
    (h₁ : Integrable (fun t => quadraticFirst l Q K (x + t • u.2) ^ 2)
      (quadraticGaussian ((riccatiRecursion l Q).precision u.1 u.2) (u.1 * (riccatiRecursion l Q).slope u.2 x))) :
    quadraticSecond (u :: l) Q K x =
      quadraticAverage (riccatiRecursion l Q) u.1 u.2 (quadraticSecond l Q K) x +
        u.1 * quadraticVariance (riccatiRecursion l Q) u.1 u.2 (quadraticFirst l Q K) x := by
  let μ := quadraticGaussian ((riccatiRecursion l Q).precision u.1 u.2)
    (u.1 * (riccatiRecursion l Q).slope u.2 x)
  change (∫ t, (quadraticSecond l Q K (x + t • u.2) +
        u.1 * quadraticFirst l Q K (x + t • u.2) ^ 2) ∂μ) -
      u.1 * (∫ t, quadraticFirst l Q K (x + t • u.2) ∂μ) ^ 2 =
    (∫ t, quadraticSecond l Q K (x + t • u.2) ∂μ) +
      u.1 * ((∫ t, quadraticFirst l Q K (x + t • u.2) ^ 2 ∂μ) -
        (∫ t, quadraticFirst l Q K (x + t • u.2) ∂μ) ^ 2)
  have hadd := integral_add h₂ (h₁.const_mul u.1)
  change (∫ t, (quadraticSecond l Q K (x + t • u.2) +
    u.1 * quadraticFirst l Q K (x + t • u.2) ^ 2) ∂μ) = _ at hadd
  rw [hadd, integral_const_mul]
  ring

def frozenFirstMoment (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) : ℝ :=
  quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
    (terminalResidual β α s h z) (fun _ => z)

def frozenSecondMoment (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) : ℝ :=
  quadraticSecond (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
    (terminalResidual β α s h z) (fun _ => z)

theorem frozenTerminalTheta_first_second (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hD : EpsilonChainControl (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)) :
    HasDerivAt (frozenTerminalTheta β α a s h k z) (frozenFirstMoment β α a s h k z) 0 ∧
      HasDerivAt (deriv (frozenTerminalTheta β α a s h k z)) (frozenSecondMoment β α a s h k z) 0 := by
  exact epsilonChain_first_second _ _ _ hQ hD (fun _ => z)

theorem frozenTerminalTheta_eventually_differentiable (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hD : EpsilonChainControl (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ (frozenTerminalTheta β α a s h k z) ε := by
  exact epsilonChain_eventually_differentiable _ _ _ hQ hD (fun _ => z)

end SKBarriers2.Corner
