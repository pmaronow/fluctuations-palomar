module

public import ComparisonSignedCavityFixedLowHighIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

def nativeCenteredFixedLowHigh (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a z : T.Slot) (k : Fin 4) (r : ℕ) (t : ℝ) : ℝ :=
  nativeFixedLowHighProfile n q U b h K T
    (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) k r 1 0 t-
  productJet3 (fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i 0 0)
    (fun i=>nativeFixedLowHighProfile n q U b h K T P i r 1 0 t) k

theorem native_centered_fixed_low_high_eq_frozen (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (k : Fin 4) (r : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 k r t=
      nativeCenteredFixedLowHigh n q U b h K T
        (fun σ=>P (T.cavityAssignment σ).1) a z k r t := by
  unfold cutFrozenCenteredJet nativeCenteredFixedLowHigh
  have Hz : cavityEmbed (0:ActiveCoordinate n→ℝ)=(0:FullCoordinate n→ℝ):=by
    funext i
    cases i <;> rfl
  simp only [Hz]
  simp_rw [native_fixed_low_high_eq_frozen n q U b h K T ho _ hq0 hq hb hh hK hbm hhm hKm _ _ ht]

theorem native_centered_fixed_second_product_bound
    {W Z Cost J : ℝ} (hW : 0≤W) (A B f g : Fin 4→ℝ) (hB : ∀i,0≤B i)
    (hJ : |J|≤A 2*W^2*Z*Cost)
    (hf : ∀i : Fin 4,i.val≤2→|f i|≤A i*W^(i:ℕ)*Z*Cost)
    (hg : ∀i : Fin 4,i.val≤2→|g i|≤B i*W^(i:ℕ)) :
    |J-productJet3 g f 2|≤(A 2+B 0*A 2+2*B 1*A 1+B 2*A 0)*W^2*Z*Cost := by
  have Hterm (i j : Fin 4) (hi : i.val≤2) (hj : j.val≤2) : |g i*f j|≤(B i*W^(i:ℕ))*(A j*W^(j:ℕ)*Z*Cost):=by
    rw [abs_mul]
    exact mul_le_mul (hg i hi) (hf j hj) (abs_nonneg _) (mul_nonneg (hB i) (pow_nonneg hW _))
  have H02:=Hterm 0 2 (by decide) (by decide)
  have H11:=Hterm 1 1 (by decide) (by decide)
  have H20:=Hterm 2 0 (by decide) (by decide)
  norm_num at H02 H11 H20
  simp only [←abs_mul] at H02 H11 H20
  have H11' : |2*g 1*f 1|≤2*((B 1*W)*(A 1*W*Z*Cost)):=by
    calc
      _=2*|g 1*f 1|:=by rw [mul_assoc,abs_mul];norm_num
      _≤_:=mul_le_mul_of_nonneg_left H11 (by norm_num)
  have Hp : |productJet3 g f 2|≤(B 0*A 2+2*B 1*A 1+B 2*A 0)*W^2*Z*Cost:=by
    have HH:=((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add H02 H11')) H20))
    change |g 0*f 2+2*g 1*f 1+g 2*f 0|≤_
    nlinarith only [HH]
  exact (abs_sub _ _).trans (by nlinarith only [hJ,Hp])

theorem native_centered_fixed_first_product_bound
    {W Z Cost J : ℝ} (hW : 0≤W) (A B f g : Fin 4→ℝ) (hB : ∀i,0≤B i)
    (hJ : |J|≤A 1*W*Z*Cost)
    (hf : ∀i : Fin 4,i.val≤1→|f i|≤A i*W^(i:ℕ)*Z*Cost)
    (hg : ∀i : Fin 4,i.val≤1→|g i|≤B i*W^(i:ℕ)) :
    |J-productJet3 g f 1|≤(A 1+B 0*A 1+B 1*A 0)*W*Z*Cost := by
  have Hterm (i j : Fin 4) (hi : i.val≤1) (hj : j.val≤1) : |g i*f j|≤(B i*W^(i:ℕ))*(A j*W^(j:ℕ)*Z*Cost):=by
    rw [abs_mul]
    exact mul_le_mul (hg i hi) (hf j hj) (abs_nonneg _) (mul_nonneg (hB i) (pow_nonneg hW _))
  have H01:=Hterm 0 1 (by decide) (by decide)
  have H10:=Hterm 1 0 (by decide) (by decide)
  norm_num at H01 H10
  simp only [←abs_mul] at H01 H10
  have Hp : |productJet3 g f 1|≤(B 0*A 1+B 1*A 0)*W*Z*Cost:=by
    have HH:=(abs_add_le _ _).trans (add_le_add H01 H10)
    change |g 0*f 1+g 1*f 0|≤_
    nlinarith only [HH]
  exact (abs_sub _ _).trans (by nlinarith only [hJ,Hp])

end OAI.SKFluctuations.Cavity
