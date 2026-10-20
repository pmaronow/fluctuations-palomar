module

public import SKConstants.ContinuousHeatBath
public import SKConstants.SpinGeometry
public import SKConstants.IndependentCrossing

public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

@[expose] def heatBathMinimumRate (beta L : ℝ) : ℝ := Real.exp (-|beta| * L) / ((2 : ℕ) : ℝ)

theorem heatBathMinimumRate_pos (beta L : ℝ) : 0 < heatBathMinimumRate beta L := by
  unfold heatBathMinimumRate
  positivity

theorem heatBathFlipRate_eq_logistic {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    heatBathFlipRate beta W x i =
      1 / (1 + Real.exp (beta * (quadraticHamiltonian W x -
        quadraticHamiltonian W (flipSpin x i)))) := by
  unfold heatBathFlipRate
  rw [mul_sub, Real.exp_sub]
  field_simp
  ring

theorem heatBathFlipRate_lower_of_energy_difference {n : ℕ} (beta L : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n)
    (henergy : |quadraticHamiltonian W (flipSpin x i) - quadraticHamiltonian W x| ≤ L) :
    heatBathMinimumRate beta L ≤ heatBathFlipRate beta W x i := by
  have hL : 0 ≤ L := (abs_nonneg _).trans henergy
  have ha : 0 ≤ |beta| * L := mul_nonneg (abs_nonneg beta) hL
  have hdiff : beta * (quadraticHamiltonian W x - quadraticHamiltonian W (flipSpin x i)) ≤
      |beta| * L := by
    have hab : |beta * (quadraticHamiltonian W x - quadraticHamiltonian W (flipSpin x i))| ≤
        |beta| * L := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left henergy (abs_nonneg beta)
    exact (le_abs_self _).trans hab
  have hden : 1 + Real.exp (beta * (quadraticHamiltonian W x -
      quadraticHamiltonian W (flipSpin x i))) ≤ 2 * Real.exp (|beta| * L) := by
    have h1 : 1 ≤ Real.exp (|beta| * L) := by simpa using Real.exp_le_exp.mpr ha
    have h2 := Real.exp_le_exp.mpr hdiff
    linarith
  have h := one_div_le_one_div_of_le (by positivity : 0 < 1 +
    Real.exp (beta * (quadraticHamiltonian W x - quadraticHamiltonian W (flipSpin x i)))) hden
  rw [heatBathFlipRate_eq_logistic]
  exact (show heatBathMinimumRate beta L = 1 / (2 * Real.exp (|beta| * L)) by
    unfold heatBathMinimumRate
    norm_num only [Nat.cast_ofNat]
    rw [neg_mul, Real.exp_neg]
    field_simp).le.trans h

theorem heatBathMinimumRate_eq_exp (beta L : ℝ) :
    heatBathMinimumRate beta L = Real.exp (-(|beta| * L + Real.log 2)) := by
  unfold heatBathMinimumRate
  norm_num only [Nat.cast_ofNat]
  simp only [neg_mul, neg_add, Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv]

@[expose] def spinInnerBoundary {n : ℕ} (S : Finset (Spin n)) : Finset (Spin n) :=
  S.filter (fun x => ∃ i : Fin n, flipSpin x i ∉ S)

@[expose] def spinBoundary {n : ℕ} (S : Finset (Spin n)) : Finset (Spin n) :=
  spinInnerBoundary S ∪ spinInnerBoundary Sᶜ

@[simp] theorem mem_spinInnerBoundary {n : ℕ} (S : Finset (Spin n)) (x : Spin n) :
    x ∈ spinInnerBoundary S ↔ x ∈ S ∧ ∃ i : Fin n, flipSpin x i ∉ S := by
  simp [spinInnerBoundary]

theorem heatBath_inner_boundary_mass_mul_le_flow {n : ℕ} (hn : 0 < n)
    (beta r : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hrate : ∀ x i, r ≤ heatBathFlipRate beta W x i) (S : Finset (Spin n)) :
    r * cutMass (gibbsProbability beta W) (spinInnerBoundary S) ≤
      cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ := by
  rw [continuousHeatBathEdgeFlow_cut_site_sum hn]
  unfold cutMass
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ spinInnerBoundary S, r * gibbsProbability beta W x) ≤
        ∑ x ∈ spinInnerBoundary S, ∑ i : Fin n, if flipSpin x i ∉ S then
          gibbsProbability beta W x * heatBathFlipRate beta W x i else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨_, i, hi⟩ := (mem_spinInnerBoundary S x).mp hx
      have hterm : r * gibbsProbability beta W x ≤
          gibbsProbability beta W x * heatBathFlipRate beta W x i := by
        have h := mul_le_mul_of_nonneg_left (hrate x i) (gibbsProbability_pos beta W x).le
        simpa only [mul_comm] using h
      exact hterm.trans (by
        have h := Finset.single_le_sum
          (s := Finset.univ) (f := fun j : Fin n => if flipSpin x j ∉ S then
            gibbsProbability beta W x * heatBathFlipRate beta W x j else 0)
          (fun j _ => by
            by_cases hj : flipSpin x j ∉ S
            · simp only [ite_eq_left hj]
              exact mul_nonneg (gibbsProbability_pos beta W x).le (heatBathFlipRate_pos beta W x j).le
            · simp only [ite_eq_right hj]
              exact le_rfl) (Finset.mem_univ i)
        simpa only [ite_eq_left hi] using h)
    _ ≤ ∑ x ∈ S, ∑ i : Fin n, if flipSpin x i ∉ S then
          gibbsProbability beta W x * heatBathFlipRate beta W x i else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : flipSpin x i ∉ S
      · simp only [ite_eq_left hi]
        exact mul_nonneg (gibbsProbability_pos beta W x).le (heatBathFlipRate_pos beta W x i).le
      · simp only [ite_eq_right hi]
        exact le_rfl

theorem continuousHeatBath_cutFlow_compl {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n)) :
    cutFlow (continuousHeatBathEdgeFlow beta W) Sᶜ S =
      cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ := by
  unfold cutFlow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact continuousHeatBathJumpRate_detailed_balance beta W y x

theorem heatBath_boundary_mass_mul_le_flow {n : ℕ} (hn : 0 < n)
    (beta r : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hrate : ∀ x i, r ≤ heatBathFlipRate beta W x i) (S : Finset (Spin n)) :
    r * cutMass (gibbsProbability beta W) (spinBoundary S) ≤
      2 * cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ := by
  have hinner := heatBath_inner_boundary_mass_mul_le_flow hn beta r W hrate S
  have houter := heatBath_inner_boundary_mass_mul_le_flow hn beta r W hrate Sᶜ
  rw [compl_compl, continuousHeatBath_cutFlow_compl] at houter
  have hdis : Disjoint (spinInnerBoundary S) (spinInnerBoundary Sᶜ) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_compl.mp ((mem_spinInnerBoundary Sᶜ x).mp hy).1)
      ((mem_spinInnerBoundary S x).mp hx).1
  unfold spinBoundary
  rw [cutMass_union _ hdis]
  linarith

theorem heatBath_boundary_mass_le_of_energy_difference {n : ℕ} (hn : 0 < n)
    (beta L : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (henergy : ∀ x i, |quadraticHamiltonian W (flipSpin x i) - quadraticHamiltonian W x| ≤ L)
    (S : Finset (Spin n)) :
    cutMass (gibbsProbability beta W) (spinBoundary S) ≤
      2 * cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ / heatBathMinimumRate beta L := by
  apply (le_div_iff₀ (heatBathMinimumRate_pos beta L)).mpr
  simpa only [mul_comm] using heatBath_boundary_mass_mul_le_flow hn beta
    (heatBathMinimumRate beta L) W
    (fun x i => heatBathFlipRate_lower_of_energy_difference beta L W x i (henergy x i)) S

theorem heatBath_boundary_mass_le_opNorm {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n)) :
    cutMass (gibbsProbability beta W) (spinBoundary S) ≤
      2 * cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ /
        heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖) :=
  heatBath_boundary_mass_le_of_energy_difference hn beta _ W
    (quadraticHamiltonian_flip_opNorm_bound W) S

theorem heatBath_boundary_mass_le_add_diagonal_opNorm {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (S : Finset (Spin n)) :
    cutMass (gibbsProbability beta (W + Matrix.diagonal d)) (spinBoundary S) ≤
      2 * cutFlow (continuousHeatBathEdgeFlow beta (W + Matrix.diagonal d)) S Sᶜ /
        heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖) :=
  heatBath_boundary_mass_le_of_energy_difference hn beta _ (W + Matrix.diagonal d)
    (quadraticHamiltonian_flip_add_diagonal_opNorm_bound W d) S

theorem cutMass_biUnion_le {V I : Type*} [DecidableEq V]
    (pi : V → ℝ) (hpi : ∀ x, 0 ≤ pi x) (A : Finset I) (sets : I → Finset V) :
    cutMass pi (A.biUnion sets) ≤ ∑ a ∈ A, cutMass pi (sets a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [cutMass]
  | @insert a A ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion : cutMass pi (sets a ∪ A.biUnion sets) ≤
        cutMass pi (sets a) + cutMass pi (A.biUnion sets) := by
      have h := Finset.sum_union_inter (s₁ := sets a) (s₂ := A.biUnion sets) (f := pi)
      have hi := cutMass_nonneg pi (sets a ∩ A.biUnion sets) hpi
      unfold cutMass at *
      linarith
    exact hunion.trans (add_le_add le_rfl ih)

theorem spinHammingBall_gibbs_mass_le {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (r : ℕ) :
    cutMass (gibbsProbability beta W) (spinHammingBall x r) ≤
      (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖)) *
          gibbsProbability beta W x := by
  let E := Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖))
  have hcomp : ∀ y ∈ spinHammingBall x r, gibbsProbability beta W y ≤ E * gibbsProbability beta W x := by
    intro y hy
    have hxy : hammingDist x y ≤ r := (Finset.mem_filter.mp hy).2
    have he := quadraticHamiltonian_hamming_opNorm_bound W x y r hxy
    exact gibbsProbability_spin_comparison beta _ W y x (by simpa only [abs_sub_comm] using he)
  calc
    cutMass (gibbsProbability beta W) (spinHammingBall x r) ≤
        ∑ _y ∈ spinHammingBall x r, E * gibbsProbability beta W x :=
      Finset.sum_le_sum hcomp
    _ = ((spinHammingBall x r).card : ℝ) * (E * gibbsProbability beta W x) := by
      simp
    _ ≤ (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) * (E * gibbsProbability beta W x) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast spinHammingBall_card_le_pow x r)
      exact mul_nonneg (Real.exp_pos _).le (gibbsProbability_pos beta W x).le
    _ = _ := by dsimp only [E]; ring

theorem spinHammingEnlargement_gibbs_mass_le {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (A : Finset (Spin n)) (r : ℕ) :
    cutMass (gibbsProbability beta W) (spinHammingEnlargement A r) ≤
      (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖)) *
          cutMass (gibbsProbability beta W) A := by
  have h := cutMass_biUnion_le (gibbsProbability beta W)
    (fun x => (gibbsProbability_pos beta W x).le) A (fun x => spinHammingBall x r)
  calc
    cutMass (gibbsProbability beta W) (spinHammingEnlargement A r) ≤
        ∑ x ∈ A, cutMass (gibbsProbability beta W) (spinHammingBall x r) := h
    _ ≤ ∑ x ∈ A, (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖)) *
          gibbsProbability beta W x :=
      Finset.sum_le_sum (fun x _ => spinHammingBall_gibbs_mass_le beta W x r)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem heatBath_enlarged_boundary_mass_le_opNorm {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n)) (r : ℕ) :
    cutMass (gibbsProbability beta W) (spinHammingEnlargement (spinBoundary S) r) ≤
      (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖)) *
          (2 * cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ /
            heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖)) :=
  (spinHammingEnlargement_gibbs_mass_le beta W (spinBoundary S) r).trans
    (mul_le_mul_of_nonneg_left (heatBath_boundary_mass_le_opNorm hn beta W S) (by positivity))

theorem spin_crossing_boundary_witness {n : ℕ} (S : Finset (Spin n))
    (x y : Spin n) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ b ∈ spinInnerBoundary S, hammingDist x b ≤ hammingDist x y := by
  generalize hdist : hammingDist x y = m
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    have hxy : x ≠ y := by
      intro heq
      subst y
      exact hy hx
    have hset : (spinDifferenceSet x y).Nonempty :=
      Finset.card_pos.mp (hammingDist_pos.mpr hxy)
    obtain ⟨i, hi⟩ := hset
    have hineq : x i ≠ y i := (Finset.mem_filter.mp hi).2
    have hdec := hammingDist_flipSpin_decreases x y i hineq
    by_cases hflip : flipSpin x i ∈ S
    · have hless : hammingDist (flipSpin x i) y < m := by omega
      obtain ⟨b, hb, hnear⟩ := ih (hammingDist (flipSpin x i) y) hless
        (flipSpin x i) hflip rfl
      refine ⟨b, hb, ?_⟩
      have htriangle := hammingDist_triangle x (flipSpin x i) b
      rw [hammingDist_flipSpin_self] at htriangle
      omega
    · refine ⟨x, (mem_spinInnerBoundary S x).mpr ⟨hx, i, hflip⟩, ?_⟩
      simp

theorem spin_close_crossing_mem_enlargement {n : ℕ} (S : Finset (Spin n))
    (x y : Spin n) (r : ℕ) (hx : x ∈ S) (hy : y ∉ S)
    (hxy : hammingDist x y ≤ r) :
    x ∈ spinHammingEnlargement (spinBoundary S) r ∧
      y ∈ spinHammingEnlargement (spinBoundary S) r := by
  constructor
  · obtain ⟨b, hb, hnear⟩ := spin_crossing_boundary_witness S x y hx hy
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_union_left _ hb, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hammingDist_comm]
    exact hnear.trans hxy
  · obtain ⟨b, hb, hnear⟩ := spin_crossing_boundary_witness Sᶜ y x
      (Finset.mem_compl.mpr hy) (by simpa using hx)
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_union_right _ hb, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hammingDist_comm b y]
    exact hnear.trans (by simpa only [hammingDist_comm] using hxy)

theorem spin_coarse_sampled_path_hits_enlargement {n : ℕ} (S : Finset (Spin n))
    (f : ℕ → Spin n) (coarse : ℕ → Prop) (N r : ℕ)
    (hstart : f 0 ∈ S) (hend : f N ∉ S)
    (hsteps : ∀ i < N, hammingDist (f i) (f (i + 1)) ≤ r)
    (hcoarse : ∀ i < N, coarse i ∨ coarse (i + 1)) :
    ∃ i ≤ N, coarse i ∧ f i ∈ spinHammingEnlargement (spinBoundary S) r := by
  obtain ⟨i, hi, hin, hout⟩ := sampled_cut_crossing (S : Set (Spin n)) f N hstart hend
  obtain ⟨hleft, hright⟩ := spin_close_crossing_mem_enlargement S
    (f i) (f (i + 1)) r hin hout (hsteps i hi)
  rcases hcoarse i hi with hflag | hflag
  · exact ⟨i, Nat.le_of_lt hi, hflag, hleft⟩
  · exact ⟨i + 1, Nat.succ_le_of_lt hi, hflag, hright⟩

theorem probability_spin_coarse_sampled_path_bound {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (S : Finset (Spin n)) (f : Ω → ℕ → Spin n)
    (coarse : Ω → ℕ → Prop) (N r : ℕ)
    {A C : Set Ω} {p : ℝ} (hp : 0 < p)
    (hstart : ∀ ω ∈ A ∩ C, f ω 0 ∈ S)
    (hend : ∀ ω ∈ A ∩ C, f ω N ∉ S)
    (hsteps : ∀ ω ∈ A ∩ C, ∀ i < N, hammingDist (f ω i) (f ω (i + 1)) ≤ r)
    (hcoarse : ∀ ω ∈ A ∩ C, ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (hlower : p * μ.real A ≤ μ.real (A ∩ C)) :
    μ.real A ≤ μ.real {ω | ∃ i ≤ N, coarse ω i ∧
      f ω i ∈ spinHammingEnlargement (spinBoundary S) r} / p := by
  apply probability_le_div_of_inter_subset μ hp _ hlower
  intro ω hω
  exact spin_coarse_sampled_path_hits_enlargement S (f ω) (coarse ω) N r
    (hstart ω hω) (hend ω hω) (hsteps ω hω) (hcoarse ω hω)

theorem probability_spinGibbs_balanced_coarse_avoidance_bad_mass {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (q : Spin n → ℝ) (S : Finset (Spin n))
    (f : Ω → ℕ → Spin n) (coarse : Ω → ℕ → Prop) (good : Set Ω)
    (N r : ℕ) (K alpha : ℝ)
    (hq : ∀ x, 0 < q x) (hqsum : ∑ x, q x = 1)
    (hKL : finiteKL (gibbsProbability beta W) q ≤ K) (halpha : 0 < alpha)
    (hS : alpha ≤ cutMass (gibbsProbability beta W) S)
    (hSc : alpha ≤ cutMass (gibbsProbability beta W) Sᶜ)
    (hX : Measurable (fun ω => f ω 0)) (hY : Measurable (fun ω => f ω N))
    (hind : ProbabilityTheory.IndepFun (fun ω => f ω 0) (fun ω => f ω N) μ)
    (hXmarg : ∀ x, μ.real {ω | f ω 0 = x} = q x)
    (hYmarg : ∀ y, μ.real {ω | f ω N = y} = q y)
    (hgood : MeasurableSet good)
    (hsteps : ∀ ω ∈ good, ∀ i < N, hammingDist (f ω i) (f ω (i + 1)) ≤ r)
    (hcoarse : ∀ ω ∈ good, ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω ∈ good, ∀ i ≤ N, coarse ω i →
      f ω i ∉ spinHammingEnlargement (spinBoundary S) r) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤ μ.real goodᶜ ∧
      μ.real good ≤ 1 - Real.exp (-2 * (K + Real.log 2) / alpha) := by
  have hcross := probability_finiteKL_balanced_endpoint_crossing μ (gibbsProbability beta W) q
    (fun ω => f ω 0) (fun ω => f ω N) S K alpha (gibbsProbability_pos beta W) hq
    (gibbsProbability_sum beta W) hqsum hKL halpha hS hSc hX hY hind hXmarg hYmarg
  have hbad : {ω | f ω 0 ∈ S ∧ f ω N ∉ S} ⊆ goodᶜ := by
    intro ω hω hωgood
    obtain ⟨i, hi, hflag, hhit⟩ := spin_coarse_sampled_path_hits_enlargement S
      (f ω) (coarse ω) N r hω.1 hω.2 (hsteps ω hωgood) (hcoarse ω hωgood)
    exact havoid ω hωgood i hi hflag hhit
  have hmass := hcross.trans (MeasureTheory.measureReal_mono hbad)
  refine ⟨hmass, ?_⟩
  rw [MeasureTheory.measureReal_compl hgood] at hmass
  have huniv : μ.real Set.univ = 1 := by simp [MeasureTheory.Measure.real]
  rw [huniv] at hmass
  linarith

end SKConstants
