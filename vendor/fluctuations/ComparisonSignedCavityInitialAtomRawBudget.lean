module

public import ComparisonSignedCavitySmallCutAtomicKernels
public import ComparisonSignedCavityWholeLawOneErrorJets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open OAI.SKFluctuations.Cavity Hierarchy
open scoped BigOperators
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
set_option maxHeartbeats 14000000

 theorem native_initial_observed_error_product_abs_le
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (P : T.Assignment→ℝ) {C d : ℝ} (hC : 0≤C) (hd : 0≤d)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^4) x≤C^4)
    (A : ℕ→S→S→ℝ) (u z : T.Slot) (huz : u≠z)
    (hA : (pairClock as (T.splitIndex u z)).disorderExpect w φ v q
      (fun σ=>(A (T.splitIndex u z) (pairSpin as (T.splitIndex u z) σ).1
        (pairSpin as (T.splitIndex u z) σ).2)^2) x≤d^2)
    {aRows : ℕ} (E : Fin aRows→ℕ→S→S→ℝ) (s t : Fin aRows→T.Slot) (hst : ∀e,s e≠t e)
    (rho : Fin aRows→ℝ) (hrho : ∀e,0<rho e)
    (hE : ∀e,(pairClock as (T.splitIndex (s e) (t e))).disorderExpect w φ v q
      (fun σ=>|E e (T.splitIndex (s e) (t e)) (pairSpin as (T.splitIndex (s e) (t e)) σ).1
        (pairSpin as (T.splitIndex (s e) (t e)) σ).2|^(4*(aRows+1))) x≤(rho e)^(4*(aRows+1))) :
    |T.disorderExpect w φ v q (fun σ=>P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
      (∏e,E e (T.splitIndex (s e) (t e)) (T.atSlot σ (s e)) (T.atSlot σ (t e)))) x|≤C*d*(∏e,rho e) := by
  let En : Fin (aRows+1)→ℕ→S→S→ℝ:=Fin.cases (fun _ _ _=>1) E
  let sn : Fin (aRows+1)→T.Slot:=Fin.cases u s
  let tn : Fin (aRows+1)→T.Slot:=Fin.cases z t
  let rn : Fin (aRows+1)→ℝ:=Fin.cases 1 rho
  have Hnn : ∀e,sn e≠tn e:=fun e=>Fin.cases huz hst e
  have Hrn : ∀e,0<rn e:=fun e=>Fin.cases (by dsimp [rn];norm_num) hrho e
  have HE : ∀e,(pairClock as (T.splitIndex (sn e) (tn e))).disorderExpect w φ v q
      (fun σ=>|En e (T.splitIndex (sn e) (tn e)) (pairSpin as (T.splitIndex (sn e) (tn e)) σ).1
        (pairSpin as (T.splitIndex (sn e) (tn e)) σ).2|^(4*(aRows+1))) x≤(rn e)^(4*(aRows+1)):=by
    intro e
    refine Fin.cases ?_ (fun e=>hE e) e
    simp only [En,sn,tn,rn,Fin.cases_zero,abs_one,one_pow]
    exact le_of_eq ((pairClock as (T.splitIndex u z)).disorderExpect_one hw φ ho v q x)
  have H:=T.disorderExpect_oneError_wholeLaw_product_scales hw φ ho v q x
    (by omega : 0<aRows+1) P hC hd hP A u z huz En sn tn Hnn rn Hrn hA HE
  simpa only [En,sn,tn,rn,Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ,one_mul] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
