module

public import ComparisonSignedCavityFullSquareRepeatedBudget
public import CavityTwoErrorPairBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

theorem wholeLaw_rpow_square_eq {z : ℝ} (hz : 0 ≤ z) (p : ℝ) :
    (z^p)^2=z^(2*p) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hz]
  congr 1
  push_cast
  ring

omit [Nonempty ι] in
theorem wholeLaw_disorderExpect_nonneg {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (F : T.Assignment→ℝ)
    (hF : ∀σ,0 ≤ F σ) (x : ι→ℝ) : 0 ≤ T.disorderExpect w φ v q F x := by
  unfold disorderExpect
  exact Finset.sum_nonneg fun σ _=>mul_nonneg
    ((T.disorderWeight_probability hw φ ho v q x).1 σ) (hF σ)

omit [Nonempty ι] in
theorem disorderExpect_product_wholeLaw_rpow_le {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (P L : T.Assignment→ℝ) {C R p : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^(2*p)) x ≤ C^(2*p))
    (hL : T.disorderExpect w φ v q (fun σ=>|L σ|^(2*p)) x ≤ R^(2*p)) :
    T.disorderExpect w φ v q (fun σ=>|P σ*L σ|^p) x ≤ (C*R)^p := by
  have HC:=T.disorderExpect_mul_sq_le hw φ ho v q
    (fun σ=>|P σ|^p) (fun σ=>|L σ|^p) x
  have HPow : (fun σ=>(|P σ|^p)^2)=(fun σ=>|P σ|^(2*p)) := by
    funext σ
    exact wholeLaw_rpow_square_eq (abs_nonneg _) _
  have LPow : (fun σ=>(|L σ|^p)^2)=(fun σ=>|L σ|^(2*p)) := by
    funext σ
    exact wholeLaw_rpow_square_eq (abs_nonneg _) _
  have HM : (fun σ=>|P σ|^p*|L σ|^p)=(fun σ=>|P σ*L σ|^p) := by
    funext σ
    rw [abs_mul,Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [HPow,LPow,HM] at HC
  have hLn:=wholeLaw_disorderExpect_nonneg hw φ T ho v q
    (fun σ=>|L σ|^(2*p)) (fun _=>Real.rpow_nonneg (abs_nonneg _) _) x
  have HB : (T.disorderExpect w φ v q (fun σ=>|P σ*L σ|^p) x)^2 ≤ ((C*R)^p)^2 := by
    calc
      _ ≤ _:=HC
      _ ≤ C^(2*p)*T.disorderExpect w φ v q (fun σ=>|L σ|^(2*p)) x:=
        mul_le_mul_of_nonneg_right hP hLn
      _ ≤ C^(2*p)*R^(2*p):=mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hC _)
      _ = _:=by rw [wholeLaw_rpow_square_eq (mul_nonneg hC hR),Real.mul_rpow hC hR]
  exact (sq_le_sq₀ (wholeLaw_disorderExpect_nonneg hw φ T ho v q
    (fun σ=>|P σ*L σ|^p) (fun _=>Real.rpow_nonneg (abs_nonneg _) _) x)
    (Real.rpow_nonneg (mul_nonneg hC hR) _)).mp HB

theorem wholeLaw_double_marked_moment_eq {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (P : T.Assignment→ℝ) (pOrder : ℝ)
    (b : MarkedPlacement T) (hb : b∈T.markedAttach 0)
    (c : MarkedPlacement b.tree) (hc : c∈b.tree.markedAttach 0) :
    c.tree.disorderExpect w φ v q
      (fun σ=>|P (b.restrict (c.restrict σ))|^pOrder) x=
      T.disorderExpect w φ v q (fun σ=>|P σ|^pOrder) x := by
  rw [b.tree.markedAttach_disorderPreserves_actual hw φ ho c hc v q
    (fun σ=>|P (b.restrict σ)|^pOrder) x,
    T.markedAttach_disorderPreserves_actual hw φ ho b hb v q
      (fun σ=>|P σ|^pOrder) x]

theorem wholeLaw_double_marked_nat_moment_eq {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (P : T.Assignment→ℝ) (pOrder : ℕ)
    (b : MarkedPlacement T) (hb : b∈T.markedAttach 0)
    (c : MarkedPlacement b.tree) (hc : c∈b.tree.markedAttach 0) :
    c.tree.disorderExpect w φ v q
      (fun σ=>|P (b.restrict (c.restrict σ))|^pOrder) x=
      T.disorderExpect w φ v q (fun σ=>|P σ|^pOrder) x := by
  simpa only [Real.rpow_natCast] using
    wholeLaw_double_marked_moment_eq hw φ T ho v q x P (pOrder:ℝ) b hb c hc

theorem disorderExpect_oneError_wholeLaw_product_scales {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ) (T : ClockTree S as)
    {k : ℕ} (hk : 0 < k) (P : T.Assignment→ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^4) x ≤ C^4)
    (A : ℕ→S→S→ℝ) (u z : T.Slot) (hne : u≠z)
    (E : Fin k→ℕ→S→S→ℝ) (s t : Fin k→T.Slot) (hst : ∀i,s i≠t i)
    (rho : Fin k→ℝ) (hrho : ∀i,0 < rho i)
    (hsecond : (pairClock as (T.splitIndex u z)).disorderExpect w φ v q
      (fun σ=>(A (T.splitIndex u z) (pairSpin as (T.splitIndex u z) σ).1
        (pairSpin as (T.splitIndex u z) σ).2)^2) x ≤ D^2)
    (hmoment : ∀i,(pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ=>|E i (T.splitIndex (s i) (t i)) (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(4*k)) x ≤ (rho i)^(4*k)) :
    |T.disorderExpect w φ v q (fun σ=>P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
      (∏i,E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))) x| ≤
      C*D*(∏i,rho i) := by
  let L:=fun σ=>∏i,E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i))
  let R:=fun σ=>A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)
  let B:=∏i,rho i
  have hB : 0 ≤ B:=(Finset.prod_pos fun i _=>hrho i).le
  have hFour : (4:ℝ)*(k:ℝ)=((4*k:ℕ):ℝ):=by push_cast;rfl
  have hL : T.disorderExpect w φ v q (fun σ=>|L σ|^4) x ≤ B^4 := by
    have H:=T.disorderExpect_pair_product_rpow_scales hw φ ho v q x hk
      (fun i=>E i (T.splitIndex (s i) (t i))) s t hst rho hrho
      (p:=4) (by norm_num) (fun i=>by
        simpa only [hFour,Real.rpow_natCast] using hmoment i)
    simpa only [Real.rpow_ofNat] using H
  have hPL : T.disorderExpect w φ v q (fun σ=>(P σ*L σ)^2) x ≤ (C*B)^2 := by
    have H:=T.disorderExpect_product_wholeLaw_rpow_le hw φ ho v q x P L hC hB
      (p:=2) (by simpa only [Real.rpow_two,show (2:ℝ)*2=4 by norm_num,Real.rpow_ofNat] using hP)
      (by simpa only [show (2:ℝ)*2=4 by norm_num,Real.rpow_ofNat] using hL)
    simpa only [Real.rpow_two,sq_abs] using H
  have hR : T.disorderExpect w φ v q (fun σ=>(R σ)^2) x ≤ D^2 := by
    dsimp only [R]
    rw [T.disorderExpect_pairAtSlot_actual hw φ ho v q x u z hne
      (fun σ τ=>(A (T.splitIndex u z) σ τ)^2)]
    exact hsecond
  have HC:=T.disorderExpect_mul_sq_le hw φ ho v q (fun σ=>P σ*L σ) R x
  have HRn:=wholeLaw_disorderExpect_nonneg hw φ T ho v q (fun σ=>(R σ)^2) (fun _=>sq_nonneg _) x
  have HH : (T.disorderExpect w φ v q (fun σ=>(P σ*L σ)*R σ) x)^2 ≤ (C*D*B)^2 := by
    calc
      _ ≤ _:=HC
      _ ≤ (C*B)^2*T.disorderExpect w φ v q (fun σ=>(R σ)^2) x:=mul_le_mul_of_nonneg_right hPL HRn
      _ ≤ (C*B)^2*D^2:=mul_le_mul_of_nonneg_left hR (sq_nonneg _)
      _ = _:=by ring
  have HE : (fun σ=>P σ*L σ*R σ)=(fun σ=>P σ*R σ*L σ):=by funext σ;ring
  rw [HE] at HH
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C*D*B)).mp (by simpa only [sq_abs] using HH)

end OAI.SKFluctuations.Hierarchy.ClockTree
