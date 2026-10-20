module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import SKBarriers2.Dynamics.Coverage
public import OAI.Probability.SKBarriers.Coverage.CoverageSchedule
public import OAI.Probability.SKBarriers.Dynamics.BankNumerics
public import OAI.Probability.SKBarriers.Dynamics.BankAvoidance

@[expose] public section

/-! Banks for the frozen forbidden set, with an arbitrary scale `L`.
No scale exponent is fixed here. The numerical estimates are adapted from
upstream `BankNumerics`, and bank selection reuses `exists_fixed_good_bank`. -/

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI.SK OAI.SK.Analytic

namespace SKBarriers2

/-- The bank sizes at scale `L`. -/
def scheduledBankSize (c : ℕ → ℝ) (B : ℕ) (L : ℝ) {p : ℕ} (j : Fin p) : ℕ :=
  ⌈Real.exp ((c (j.val % B) + 1) * L)⌉₊

theorem scheduledBankSize_pos (c : ℕ → ℝ) (B : ℕ) (L : ℝ) {p : ℕ} (j : Fin p) :
    0 < scheduledBankSize c B L j := Nat.ceil_pos.mpr (Real.exp_pos _)

theorem scheduled_bank_coverage_sum {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j) {L : ℝ}
    (hL : 1≤L)
    (hdom : (bankPrefix c B+5)*L≤Real.exp L) :
    (∑j : Fin p,(Fintype.card (BankTuple (scheduledBankSize c B L) (blockPrior p B) j):ℝ)*
      (Real.exp (-(bankPrefix c (j.val%B)+5)*L)+
        Real.exp (-(Real.exp (-c (j.val%B)*L))*(scheduledBankSize c B L j))))≤
      2*p*Real.exp (-5*L) := by
  have hK (j : Fin p) : (scheduledBankSize c B L j:ℝ)≤Real.exp ((c (j.val%B)+2)*L) := ceil_exp_bound (hc _) hL
  calc
    _ ≤ ∑_j : Fin p,2*Real.exp (-5*L) := by
      apply Finset.sum_le_sum
      intro j _
      have HA := bankTuple_card_bound hB c (scheduledBankSize c B L) L hK j
      have hAj : bankPrefix c (j.val%B)≤bankPrefix c B := bankPrefix_mono c hc (Nat.mod_lt _ hB).le
      have Hmiss : Real.exp (-(Real.exp (-c (j.val%B)*L))*(scheduledBankSize c B L j))≤
          Real.exp (-(bankPrefix c (j.val%B)+5)*L) := by
        refine (bank_miss_exp_bound (c (j.val%B)) L 0).trans ?_
        apply Real.exp_le_exp.mpr
        have HH := mul_le_mul_of_nonneg_right (add_le_add hAj (le_refl (5:ℝ))) (by linarith only [hL])
        linarith only [HH,hdom]
      have H := mul_le_mul HA (add_le_add (le_refl (Real.exp (-(bankPrefix c (j.val%B)+5)*L))) Hmiss) (by positivity) (Real.exp_pos _).le
      refine H.trans_eq ?_
      rw [← two_mul,mul_comm (Real.exp _) (2*_),mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem scheduled_bank_locking_cost {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j) {L : ℝ}
    (hL : 5≤L) (hp : (p:ℝ)≤Real.exp L) {v : ℝ}
    (hv0 : 0≤v) (hv : v≤Real.exp (-(3*bankPrefix c B+20)*L)) :
    (8*(Fintype.card (BankIndex (scheduledBankSize c B L (p:=p))):ℝ)^3+
      48*(Fintype.card (BankIndex (scheduledBankSize c B L (p:=p))):ℝ)^2)*v≤Real.exp (-4*L) := by
  let A := bankPrefix c B
  let N : ℝ := Fintype.card (BankIndex (scheduledBankSize c B L (p:=p)))
  have hA : 0≤A := bankPrefix_nonneg c hc B
  have hL0 : 0≤L := by linarith only [hL]
  have hN0 : 0≤N := Nat.cast_nonneg _
  have hN : N≤Real.exp ((A+1)*L) := by
    refine (bankIndex_card_bound hB c hc (scheduledBankSize c B L) hL0
      (fun j => ceil_exp_bound (hc _) (by linarith only [hL]))).trans ?_
    calc
      _ ≤ Real.exp L*Real.exp (A*L) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he1 : 1≤Real.exp ((A+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have HN3 : N^3≤Real.exp (3*(A+1)*L) := by
    have H := pow_le_pow_left₀ hN0 hN 3
    simpa only [← Real.exp_nat_mul,Nat.cast_ofNat,mul_assoc] using H
  have HN2 : N^2≤Real.exp (3*(A+1)*L) := by
    have H := pow_le_pow_left₀ hN0 hN 2
    have HH : (Real.exp ((A+1)*L))^2≤(Real.exp ((A+1)*L))^3 := pow_le_pow_right₀ he1 (by decide)
    exact (H.trans HH).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have HC : (8*N^3+48*N^2)*v≤56*Real.exp (-17*L) := by
    calc
      _ ≤ (56*Real.exp (3*(A+1)*L))*Real.exp (-(3*A+20)*L) :=
        mul_le_mul (by linarith only [HN3,HN2]) hv hv0 (by positivity)
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have HE56 : (56:ℝ)≤Real.exp (13*L) := by
    have H := Real.add_one_le_exp (13*L)
    linarith only [H,hL]
  refine HC.trans ?_
  calc
    _ ≤ Real.exp (13*L)*Real.exp (-17*L) := mul_le_mul_of_nonneg_right HE56 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem scheduled_bank_total {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j) {L : ℝ}
    (hL : 5≤L) (hp : (p:ℝ)≤Real.exp L)
    (hdom : (bankPrefix c B+5)*L≤Real.exp L)
    {v : ℝ} (hv0 : 0≤v) (hv : v≤Real.exp (-(3*bankPrefix c B+20)*L)) :
    (8*(Fintype.card (BankIndex (scheduledBankSize c B L (p:=p))):ℝ)^3+
      48*(Fintype.card (BankIndex (scheduledBankSize c B L (p:=p))):ℝ)^2)*v+
    (∑j : Fin p,(Fintype.card (BankTuple (scheduledBankSize c B L) (blockPrior p B) j):ℝ)*
      (Real.exp (-(bankPrefix c (j.val%B)+5)*L)+
        Real.exp (-(Real.exp (-c (j.val%B)*L))*(scheduledBankSize c B L j))))≤
      3*Real.exp (-4*L) := by
  have HL := scheduled_bank_locking_cost hB c hc hL hp hv0 hv
  have HC := scheduled_bank_coverage_sum (p:=p) hB c hc (by linarith only [hL]) hdom
  have HP : 2*(p:ℝ)*Real.exp (-5*L)≤2*Real.exp (-4*L) := by
    calc
      _ ≤ 2*Real.exp L*Real.exp (-5*L) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  linarith only [HL,HC,HP]


theorem exists_coverage_schedule (β q : ℝ) (L : ℕ → ℝ)
    (h : ∀D : ℝ,0<D → ∃c : ℝ,0<c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*L n)))<Real.exp (-D*L n)) :
    ∃c : ℕ → ℝ, (∀j,0<c j) ∧ ∃C : ℕ → (n : ℕ) → Set (Disorder n),
      (∀j n,MeasurableSet (C j n)) ∧
      (∀j,Tendsto (fun n => (disorderLaw n).real (C j n)) atTop (𝓝 1)) ∧
      ∀j n J,J∈C j n → ∀E : Config n → Prop,
        (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<Real.exp (-c j*L n))≤
          Real.exp (-(bankPrefix c j+5)*L n) := by
  choose f hf C hC hC1 hcov using (fun D : ℝ => h (max D 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
  let c : ℕ → ℝ := fun j => f (coveragePrefix f j+5)
  refine ⟨c,fun j => hf _,fun j => C (coveragePrefix f j+5),fun j n => hC _ n,fun j => hC1 _,?_⟩
  intro j n J hJ E
  have HD : max (coveragePrefix f j+5) 1=coveragePrefix f j+5 := max_eq_left (by linarith only [coveragePrefix_nonneg f hf j])
  have H := gibbs_coverage_predicate β J q _ _ (hcov (coveragePrefix f j+5) n J hJ) E
  simpa only [HD,c,bankPrefix_coverage] using H

/-- At any scale, a small frozen forbidden mass produces one deterministic bank.
The coverage cutoff is `qs`; the cell threshold `t` is independent of it. -/
theorem exists_fixed_good_bank {n p B : ℕ} (hB : 0 < B)
    (β : ℝ) (J : Disorder n) (I : Set ℝ) (ρ ε η qs b b' t L : ℝ)
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcov : ∀ j < B, ∀ E : Config n → Prop,
      (gibbsFiniteLaw β J).prob (fun x => E x ∧
        (gibbsFiniteLaw β J).prob (fun y => E y ∧ qs ≤ |overlap x y|) <
          Real.exp (-c j * L)) ≤ Real.exp (-(bankPrefix c j + 5) * L))
    (hv : replicaGibbsMass β J (forbiddenSet n I ρ ε η qs b b') ≤
      Real.exp (-(3 * bankPrefix c B + 20) * L))
    (hL : 5 ≤ L) (hp : (p : ℝ) ≤ Real.exp L)
    (hdom : (bankPrefix c B + 5) * L ≤ Real.exp L)
    (hsmall : 3 * Real.exp (-4 * L) < 1) :
    ∃ z : BankIndex (scheduledBankSize c B L (p := p)) → Config n,
      ¬bankTripleBad (fun i : BankIndex (scheduledBankSize c B L (p := p)) => i.1.val)
        (forbiddenSet n I ρ ε η qs b b') z ∧
      (gibbsFiniteLaw β J).prob (fun x =>
        bankCoverageBad (scheduledBankSize c B L) (blockPrior p B) t qs z x ∨
        bankVertexBad (fun i : BankIndex (scheduledBankSize c B L (p := p)) => i.1.val)
          (forbiddenSet n I ρ ε η qs b b') z x) ≤ 3 * Real.exp (-4 * L) := by
  apply OAI.SK.Analytic.exists_fixed_good_bank β J (scheduledBankSize c B L)
    (blockPrior p B) (blockPrior_not_self p B) t qs
    (fun j => Real.exp (-c (j.val % B) * L))
    (fun j => Real.exp (-(bankPrefix c (j.val % B) + 5) * L))
    (fun j => (Real.exp_pos _).le) (forbiddenSet n I ρ ε η qs b b')
  · intro j w
    exact hcov (j.val % B) (Nat.mod_lt _ hB) (fun x => ∀ i, |overlap (w i) x| ≤ 3 * t)
  · exact scheduled_bank_total hB c hc hL hp hdom
      (replicaGibbsMass_nonneg β J _) hv
  · exact hsmall

/-- The same cutoff works for schedules at every admissible scale. -/
theorem exists_uniform_coverage_schedule {β : ℝ} (hβ : 1 < β) :
    ∃ qs : ℝ, 0 < qs ∧ qs < 1 ∧ ∀ L : ℕ → ℝ,
      Tendsto L atTop atTop →
      Tendsto (fun n => L n / (n : ℝ)) atTop (𝓝 0) →
      ∃ c : ℕ → ℝ, (∀ j, 0 < c j) ∧
        ∃ C : ℕ → (n : ℕ) → Set (Disorder n),
          (∀ j n, MeasurableSet (C j n)) ∧
          (∀ j, Tendsto (fun n => (disorderLaw n).real (C j n)) atTop (𝓝 1)) ∧
          ∀ j n J, J ∈ C j n → ∀ E : Config n → Prop,
            (gibbsFiniteLaw β J).prob (fun x => E x ∧
              (gibbsFiniteLaw β J).prob (fun y => E y ∧ qs ≤ |overlap x y|) <
                Real.exp (-c j * L n)) ≤ Real.exp (-(bankPrefix c j + 5) * L n) := by
  obtain ⟨qs, hqs, hqs1, hcov⟩ := uniform_coverage' hβ
  refine ⟨qs, hqs, hqs1, ?_⟩
  intro L hL hsub
  exact exists_coverage_schedule β qs L (hcov L hL hsub)

end SKBarriers2
