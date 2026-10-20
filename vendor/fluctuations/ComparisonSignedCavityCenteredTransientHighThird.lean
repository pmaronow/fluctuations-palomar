module

public import ComparisonSignedCavityCanonicalTransientHighZero
public import ComparisonSignedCavityFrozenAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

def nativeCenteredTransientHighThird (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a z : T.Slot) (l t : ℝ) : ℝ :=
  nativeTransientHighJet n q U b h K T
    (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 3 l t-
    productJet3 (fun i=>cutLowJet n q U b h K T
      (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i l 0)
      (fun i=>nativeTransientHighJet n q U b h K T P 0 i l t) 3

theorem native_centered_third_HIGH_product_bound
    {W Z Cost J : ℝ} (hW : 0≤W) (_hZ : 0≤Z) (_hCost : 0≤Cost)
    (A B f g : Fin 4→ℝ) (_hA : ∀i,0≤A i) (hB : ∀i,0≤B i)
    (hJ : |J|≤A 3*W^3*Z*Cost)
    (hf : ∀i,|f i|≤A i*W^(i:ℕ)*Z*Cost)
    (hg : ∀i,|g i|≤B i*W^(i:ℕ)) :
    |J-productJet3 g f 3|≤
      (A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0)*W^3*Z*Cost := by
  have Hterm (i j : Fin 4) : |g i*f j|≤(B i*W^(i:ℕ))*(A j*W^(j:ℕ)*Z*Cost):=by
    rw [abs_mul]
    exact mul_le_mul (hg i) (hf j) (abs_nonneg _) (mul_nonneg (hB i) (pow_nonneg hW _))
  have H03:=Hterm 0 3
  have H12:=Hterm 1 2
  have H21:=Hterm 2 1
  have H30:=Hterm 3 0
  norm_num at H03 H12 H21 H30
  simp only [←abs_mul] at H03 H12 H21 H30
  have H12' : |3*g 1*f 2|≤3*((B 1*W)*(A 2*W^2*Z*Cost)):=by
    calc
      _=3*|g 1*f 2|:=by rw [mul_assoc,abs_mul];norm_num
      _≤_:=mul_le_mul_of_nonneg_left H12 (by norm_num)
  have H21' : |3*g 2*f 1|≤3*((B 2*W^2)*(A 1*W*Z*Cost)):=by
    calc
      _=3*|g 2*f 1|:=by rw [mul_assoc,abs_mul];norm_num
      _≤_:=mul_le_mul_of_nonneg_left H21 (by norm_num)
  have Hp : |productJet3 g f 3|≤
      (B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0)*W^3*Z*Cost:=by
    have HH:=((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add H03 H12')) H21')) H30))
    change |g 0*f 3+3*g 1*f 2+3*g 2*f 1+g 3*f 0|≤_
    nlinarith only [HH]
  exact (abs_sub _ _).trans (by nlinarith only [hJ,Hp])

end OAI.SKFluctuations.Cavity
