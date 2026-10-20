module

public import ComparisonSignedCavityWholeLawNaturalTaylor

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def wholeLawRowComparisonConstant (r : ℕ) : ℝ :=
  2*(7*(r:ℝ)+8*(r:ℝ)^2*(r+1:ℝ))

theorem wholeLawRowComparisonConstant_nonneg (r : ℕ) :
    0 ≤ wholeLawRowComparisonConstant r := by unfold wholeLawRowComparisonConstant;positivity

theorem wholeLawRowComparisonConstant_mono {r R : ℕ} (h : r ≤ R) :
    wholeLawRowComparisonConstant r ≤ wholeLawRowComparisonConstant R := by
  unfold wholeLawRowComparisonConstant
  have H : (r:ℝ) ≤ R := by exact_mod_cast h
  gcongr

theorem native_wholeLaw_scalar_clock_expect_close (n U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K₁ K₂ : ℕ→ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀j i,0 ≤ q j i)
    (hb : Monotone b) (hh : Monotone h) (hK₁ : Monotone K₁) (hK₂ : Monotone K₂)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    (hK₁0 : ∀j,0 ≤ K₁ j) (hK₂0 : ∀j,0 ≤ K₂ j)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (P : T.Assignment→ℝ) (hP : ∀σ,0 ≤ P σ) (x : FullCoordinate n→ℝ) :
    ExpClose (wholeLawRowComparisonConstant T.leaves*(K₁ as.length+K₂ as.length))
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K₁) P x)
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K₂) P x) := by
  have H:=actualRow_disorderExpect_close n T ho
    (cutFullVariance n q U l t b h K₁) (cutFullVariance n q U l t b h K₂)
    (cutFullVariance_monotone n q U hl ht hq hb0 hh0 hK₁0 hb hh hK₁)
    (cutFullVariance_monotone n q U hl ht hq hb0 hh0 hK₂0 hb hh hK₂)
    (cutFullVariance_nonneg n q U hl ht hq0 hb0 hh0 hK₁0 0)
    (cutFullVariance_nonneg n q U hl ht hq0 hb0 hh0 hK₂0 0)
    (B:=0) (H:=0) (K:=K₁ as.length+K₂ as.length) le_rfl le_rfl
    (add_nonneg (hK₁0 _) (hK₂0 _)) (by
      intro i j hj
      rcases i with (i|i)|(i|i)
      · simp only [cutFullVariance,fullVariance,rowChangeBound,Sum.elim_inl,sub_self,abs_zero]
        exact le_rfl
      · have H₁0 : 0 ≤ (1-t)*relocatedClock U l K₁ j:=
          mul_nonneg (sub_nonneg.mpr ht.2) (relocatedClock_nonneg U hl.1 hK₁0 j)
        have H₂0 : 0 ≤ (1-t)*relocatedClock U l K₂ j:=
          mul_nonneg (sub_nonneg.mpr ht.2) (relocatedClock_nonneg U hl.1 hK₂0 j)
        have H₁ : (1-t)*relocatedClock U l K₁ j ≤ K₁ as.length:=
          (mul_le_of_le_one_left (relocatedClock_nonneg U hl.1 hK₁0 j) (by linarith [ht.1])).trans
            ((relocatedClock_le U hl.2 hK₁0 j).trans (hK₁ hj))
        have H₂ : (1-t)*relocatedClock U l K₂ j ≤ K₂ as.length:=
          (mul_le_of_le_one_left (relocatedClock_nonneg U hl.1 hK₂0 j) (by linarith [ht.1])).trans
            ((relocatedClock_le U hl.2 hK₂0 j).trans (hK₂ hj))
        simp only [cutFullVariance,fullVariance,rowChangeBound,Sum.elim_inl,Sum.elim_inr]
        exact abs_le.mpr ⟨by linarith [hK₁0 as.length],by linarith [hK₂0 as.length]⟩
      · simp only [cutFullVariance,fullVariance,rowChangeBound,Sum.elim_inr,Sum.elim_inl,sub_self,abs_zero]
        exact le_rfl
      · simp only [cutFullVariance,fullVariance,rowChangeBound,Sum.elim_inr,sub_self,abs_zero]
        exact le_rfl) P hP x
  simpa only [wholeLawRowComparisonConstant,add_zero] using H

theorem native_wholeLaw_scalar_clock_moment_le (n U rBound : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K₁ K₂ : ℕ→ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀j i,0 ≤ q j i)
    (hb : Monotone b) (hh : Monotone h) (hK₁ : Monotone K₁) (hK₂ : Monotone K₂)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    (hK₁0 : ∀j,0 ≤ K₁ j) (hK₂0 : ∀j,0 ≤ K₂ j)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (P : T.Assignment→ℝ) (p B M : ℝ)
    (hT : T.leaves ≤ rBound) (hClock : K₁ as.length+K₂ as.length ≤ M)
    (hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K₂) (fun σ=>|P σ|^p) 0 ≤ B) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K₁) (fun σ=>|P σ|^p) 0 ≤
      Real.exp (wholeLawRowComparisonConstant rBound*M)*B := by
  have H:=native_wholeLaw_scalar_clock_expect_close n U T ho q b h K₁ K₂
    hq hq0 hb hh hK₁ hK₂ hb0 hh0 hK₁0 hK₂0 hl ht (fun σ=>|P σ|^p)
    (fun _=>Real.rpow_nonneg (abs_nonneg _) _) 0
  have HC : wholeLawRowComparisonConstant T.leaves*(K₁ as.length+K₂ as.length) ≤
      wholeLawRowComparisonConstant rBound*M :=
    mul_le_mul (wholeLawRowComparisonConstant_mono hT) hClock
      (add_nonneg (hK₁0 _) (hK₂0 _)) (wholeLawRowComparisonConstant_nonneg _)
  exact (H.mono HC).le_mul.trans (mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le)

theorem native_wholeLaw_scalar_clock_nat_moment_le (n U rBound order : ℕ) (horder : 0 < order)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K₁ K₂ : ℕ→ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀j i,0 ≤ q j i)
    (hb : Monotone b) (hh : Monotone h) (hK₁ : Monotone K₁) (hK₂ : Monotone K₂)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    (hK₁0 : ∀j,0 ≤ K₁ j) (hK₂0 : ∀j,0 ≤ K₂ j)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (P : T.Assignment→ℝ) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hT : T.leaves ≤ rBound) (hClock : K₁ as.length+K₂ as.length ≤ M)
    (hmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K₂) (fun σ=>|P σ|^order) 0 ≤ B^order) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K₁) (fun σ=>|P σ|^order) 0 ≤
      (Real.exp (wholeLawRowComparisonConstant rBound*M)*B)^order := by
  have H:=native_wholeLaw_scalar_clock_moment_le n U rBound T ho q b h K₁ K₂
    hq hq0 hb hh hK₁ hK₂ hb0 hh0 hK₁0 hK₂0 hl ht P (order:ℝ) (B^order) M hT hClock
    (by simpa only [Real.rpow_natCast] using hmoment)
  simp only [Real.rpow_natCast] at H
  apply H.trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right
    (le_self_pow₀ (Real.one_le_exp (mul_nonneg (wholeLawRowComparisonConstant_nonneg _) hM)) horder.ne')
    (pow_nonneg hB _)

end OAI.SKFluctuations.Cavity
