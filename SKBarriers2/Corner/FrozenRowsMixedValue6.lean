module

public import SKBarriers2.Corner.FrozenRowsMixedValue5

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

private theorem first_wJets_zero (r p : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    WJets r B p (fun _ : Vec3 => (0 : ℝ)) :=
  (WJets.const r (0 : ℝ)).mono (by simpa only [norm_zero] using hB) (Nat.zero_le p)

private theorem first_degree_zero (r p : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    MomentKJet.FirstDegreeBound r B p (fun _ : Vec3 => MomentKJet.const 0) :=
  ⟨⟨first_wJets_zero r (p+1) hB,(first_wJets_zero r p hB).potential⟩,
    first_wJets_zero r (p+1) hB⟩

private theorem first_budget_mono {r s : ℕ} (hrs : r ≤ s) {T : ℝ} (hT : 0 ≤ T) :
    epsilonSpatialStepBudget r T ≤ epsilonSpatialStepBudget s T := by
  have hpow : (2 : ℝ)^r ≤ 2^s := pow_le_pow_right₀ (by norm_num) hrs
  dsimp only [epsilonSpatialStepBudget]
  gcongr

theorem firstDegreeBound_twelve_steps {d : ℕ} {M₀ δ T : ℝ}
    (hM₀ : 0 ≤ M₀) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (J : ℕ → Fin 3 → Vec3 → MomentKJet)
    (Hterminal : ∀ i : Fin 3, MomentKJet.FirstDegreeBound (d+12)
      ((M₀*δ)^(i.val+1)) (2*(i.val+1)-1) (J 12 i))
    (HS : ∀ q : Fin 12, ∀ r : ℕ, r ≤ d+12 → ∀ V : ℝ, 0 ≤ V →
      (∀ i : Fin 3, MomentKJet.FirstDegreeBound (r+1) (V^(i.val+1))
        (2*(i.val+1)-1) (J (q.val+1) i)) →
      ∀ i : Fin 3, MomentKJet.FirstDegreeBound r
        ((epsilonSpatialStepBudget (r+2) T*V)^(i.val+1))
        (2*(i.val+1)-1) (J q.val i)) :
    let C := epsilonSpatialStepBudget ((d+12)+2) T
    ∀ n : Fin 13, ∀ i : Fin 3, MomentKJet.FirstDegreeBound d
      ((C^12*M₀*δ)^(i.val+1)) (2*(i.val+1)-1) (J n.val i) := by
  dsimp only
  let d₀ := d+12
  let C := epsilonSpatialStepBudget (d₀+2) T
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one (d₀+2) hT
  have hC₀ : 0 ≤ C := by linarith
  have Hbound : ∀ m : ℕ, m ≤ 12 → ∀ i : Fin 3,
      MomentKJet.FirstDegreeBound (d₀-m) ((C^m*M₀*δ)^(i.val+1)) (2*(i.val+1)-1)
        (J (12-m) i) := by
    intro m
    induction m with
    | zero =>
      intro _ i
      simpa only [Nat.sub_zero,pow_zero,one_mul] using Hterminal i
    | succ m ih =>
      intro hm i
      let q : Fin 12 := ⟨12-(m+1),by omega⟩
      let j := d₀-(m+1)
      have hji : j+1 = d₀-m := by dsimp only [j,d₀]; omega
      have hq : q.val+1 = 12-m := by dsimp only [q]; omega
      have Hinput : ∀ i : Fin 3, MomentKJet.FirstDegreeBound (j+1)
          ((C^m*M₀*δ)^(i.val+1)) (2*(i.val+1)-1)
          (J (q.val+1) i) := by
        rw [hji,hq]
        exact ih (by omega)
      have Hnext := HS q j
        (by dsimp only [j]; omega) (C^m*M₀*δ) (by positivity) Hinput i
      have hbudget : epsilonSpatialStepBudget (j+2) T ≤ C :=
        first_budget_mono (by dsimp only [j]; omega) hT
      have hbudget₀ : 0 ≤ epsilonSpatialStepBudget (j+2) T :=
        (by norm_num : (0 : ℝ) ≤ 1).trans (epsilonSpatialStepBudget_ge_one _ hT)
      have Hnext' := Hnext.mono (pow_le_pow_left₀ (by positivity :
        0 ≤ epsilonSpatialStepBudget (j+2) T * (C^m*M₀*δ))
        (mul_le_mul_of_nonneg_right hbudget (by positivity : 0 ≤ C^m*M₀*δ)) (i.val+1)) le_rfl
      have heq : C * (C^m*M₀*δ) = C^(m+1)*M₀*δ := by rw [pow_succ]; ring
      rw [heq] at Hnext'
      exact Hnext'
  intro n i
  have hm : 12-n.val ≤ 12 := by omega
  have H := Hbound (12-n.val) hm i
  have hn : 12-(12-n.val) = n.val := by omega
  rw [hn] at H
  apply (H.of_le (by dsimp only [d₀]; omega)).mono _ le_rfl
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hm) hM₀) hδ

private theorem first_nil_epsilon_first (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (ε : ℝ) (x : Vec3) :
    epsilonSpatialJet (fun e => epsilonChain [] Q K e) 1 ε x = K x := by
  simpa only [epsilonSpatialJet,iteratedDeriv_one,epsilonChain,vectorIncrementChain,id_eq,one_mul]
    using (((hasDerivAt_id ε).mul_const (K x)).const_add (Q.value x)).deriv

private theorem first_nil_epsilon_second (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (ε : ℝ) (x : Vec3) :
    epsilonSpatialJet (fun e => epsilonChain [] Q K e) 2 ε x = 0 := by
  change iteratedDeriv (1+1) (fun e => epsilonChain [] Q K e x) ε = 0
  rw [iteratedDeriv_succ,iteratedDeriv_one]
  have H : deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
    funext e
    simpa only [epsilonSpatialJet,iteratedDeriv_one] using first_nil_epsilon_first Q K e x
  rw [H]
  exact deriv_const ε (K x)

private theorem first_nil_epsilon_third (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (ε : ℝ) (x : Vec3) :
    epsilonSpatialJet (fun e => epsilonChain [] Q K e) 3 ε x = 0 := by
  change iteratedDeriv (2+1) (fun e => epsilonChain [] Q K e x) ε = 0
  rw [iteratedDeriv_succ]
  have H : iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
    funext e
    exact first_nil_epsilon_second Q K e x
  rw [H]
  exact deriv_const ε 0

theorem frozenRowsCoarseRawJet_terminal (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (i : Fin 3) (y : Vec3) (k : ℝ) :
    frozenRowsCoarseRawJet β α a s h z ε 12 i y k =
      MomentKJet.const (epsilonSpatialJet
        (fun e => epsilonChain [] (terminalTaylorQuadratic β α s h z)
          (terminalResidual β α s h z) e) (i.val+1) ε
        ((Real.sqrt h) • y+(fun _ => z))) := by
  have hn (t : ℝ) : (frozenSchedule β a (1/2) h t).drop 12 = [] := by
    apply List.drop_eq_nil_of_le
    simpa only [frozenSchedule_length] using (le_refl 12)
  simp only [frozenRowsCoarseRawJet,originalEpsilonKJet,hn]
  simp [iteratedDeriv_const,MomentKJet.rescale,MomentKJet.const]

theorem scalarData_frozen_coarse_first_scaled_epsilon_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ k ∈ frozenRowsKDomain, ∀ n : Fin 13, ∀ i : Fin 3,
        MomentKJet.FirstDegreeBound d ((M*h)^(i.val+1)) (2*(i.val+1)-1)
          (fun y => frozenRowsCoarseRawJet β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h z ε n.val i y k) := by
  let d₀ := d+12
  obtain ⟨hS,T,hhS,hT,HS⟩ := scalarData_frozen_coarse_first_step D hl hu d₀
  let M₀ := 6*scalarTerminalJetBound D (max 2 d₀)+1
  let C := epsilonSpatialStepBudget (d₀+2) T
  let M := C^12*M₀
  have hM₀ : 1 ≤ M₀ := by
    dsimp only [M₀]
    linarith [scalarTerminalJetBound_nonneg D (max 2 d₀)]
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one (d₀+2) (by linarith)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) hM₀
  let h₀ := min hS (min 1 (min (l/2) ((D.q-u)/6)))
  refine ⟨h₀,M,lt_min hhS (lt_min (by norm_num) (lt_min (by positivity) (by positivity))),hM,?_⟩
  intro r hr h hh hhsmall z ε hε k hk n i
  have hhS' : h ≤ hS := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l/2 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q-u)/6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have htime : (r-h)+4*h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hr.1],by linarith [hr.2,D.q_mem.2]⟩
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r-h)
  let ρ := Real.sqrt h
  let c : Vec3 := fun _ => z
  let Q := terminalTaylorQuadratic β α (r-h) h z
  let K := terminalResidual β α (r-h) h z
  have hρ : ρ ∈ Ioc (0 : ℝ) 1 := ⟨Real.sqrt_pos.mpr hh,Real.sqrt_le_one.mpr hh₁⟩
  have hρh : ρ^2 = h := Real.sq_sqrt hh.le
  have Hterminal : ∀ i : Fin 3, MomentKJet.FirstDegreeBound d₀
      ((M₀*h)^(i.val+1)) (2*(i.val+1)-1)
      (fun y => frozenRowsCoarseRawJet β α a (r-h) h z ε 12 i y k) := by
    intro i
    have Heq := fun y => frozenRowsCoarseRawJet_terminal β α a (r-h) h z ε i y k
    fin_cases i
    · have HK := scalarData_terminalResidual_coarse_degreeJets D htime hρ d₀
        (by dsimp only [d₀]; omega) z
      have HK' : DegreeJets d₀ (M₀*h) 1 (spatialRescale ρ c K) := by
        apply HK.mono _ le_rfl
        rw [hρh]
        dsimp only [M₀]
        nlinarith
      have H : MomentKJet.FirstDegreeBound d₀ (M₀*h) 1
          (fun y => MomentKJet.const (spatialRescale ρ c K y)) :=
        ⟨HK',first_wJets_zero d₀ 2 (by positivity : 0 ≤ M₀*h)⟩
      simpa only [Heq,first_nil_epsilon_first,spatialRescale,Fin.val_zero,zero_add,pow_one] using H
    · have H := first_degree_zero d₀ 3 (by positivity : 0 ≤ (M₀*h)^2)
      simpa only [Heq,Nat.reduceAdd,first_nil_epsilon_second] using H
    · have H := first_degree_zero d₀ 5 (by positivity : 0 ≤ (M₀*h)^3)
      simpa only [Heq,Nat.reduceAdd,first_nil_epsilon_third] using H
  have H := firstDegreeBound_twelve_steps (by linarith : 0 ≤ M₀) hh.le (by linarith : 0 ≤ T)
    (fun n i y => frozenRowsCoarseRawJet β α a (r-h) h z ε n i y k) Hterminal
    (fun q j hj V hV Hinput => HS r hr h hh hhS' z ε hε k hk q j hj V hV Hinput)
  exact H n i

def frozenRowsCoarseNormalizedJet (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (n : ℕ) (i : Fin 3) (y : Vec3) (k : ℝ) : MomentKJet :=
  MomentKJet.rescale (Real.sqrt h)
    (normalizedEpsilonKJet (fun t => (frozenSchedule β a (1/2) h t).drop n)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
      (Real.sqrt h) (fun _ => z) (fun _ => y) (i.val+1) ε k)

theorem scalarData_frozen_coarse_normalized_first_epsilon_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ k ∈ frozenRowsKDomain, ∀ n : Fin 13, ∀ i : Fin 3,
        MomentKJet.FirstDegreeBound d ((M*(Real.sqrt h)⁻¹)^(i.val+1)) (2*(i.val+1)-1)
          (fun y => frozenRowsCoarseNormalizedJet β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h z ε n.val i y k) := by
  obtain ⟨h₀,M,hh₀,hM,H⟩ := scalarData_frozen_coarse_first_scaled_epsilon_jets D hl hu d
  refine ⟨h₀,M,hh₀,hM,?_⟩
  intro r hr h hh hhsmall z ε hε k hk n i
  have HB := H r hr h hh hhsmall z ε hε k hk n i
  let α := cdf (D.μ : Measure ℝ)
  let ρ := Real.sqrt h
  let δ := ρ^3
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hδ : 0 < δ := pow_pos hρ _
  have heq (y : Vec3) : frozenRowsCoarseRawJet β α (α (r-h)) (r-h) h z ε n.val i y k =
      (frozenRowsCoarseNormalizedJet β α (α (r-h)) (r-h) h z ε n.val i y k).scale
        (δ^(i.val+1)) := by
    unfold frozenRowsCoarseRawJet frozenRowsCoarseNormalizedJet
    rw [originalEpsilonKJet_eq_scale hρ.ne',MomentKJet.rescale_scale]
  have hcoef : (M*h)^(i.val+1) = (M*ρ^2)^(i.val+1) := by rw [Real.sq_sqrt hh.le]
  rw [hcoef] at HB
  have Hscaled := HB.scale ((δ^(i.val+1))⁻¹)
  have hinv : (fun y => (frozenRowsCoarseRawJet β α (α (r-h)) (r-h) h z ε n.val i y k).scale
      ((δ^(i.val+1))⁻¹)) =
      fun y => frozenRowsCoarseNormalizedJet β α (α (r-h)) (r-h) h z ε n.val i y k := by
    funext y
    rw [heq,MomentKJet.scale_scale,inv_mul_cancel₀ (pow_ne_zero _ hδ.ne')]
    simp only [MomentKJet.scale,one_mul]
  rw [hinv] at Hscaled
  convert Hscaled using 1
  rw [abs_of_pos (inv_pos.mpr (pow_pos hδ _)),← inv_pow,← mul_pow]
  congr 1
  dsimp only [δ,ρ]
  field_simp [hρ.ne']

end SKBarriers2.Corner
