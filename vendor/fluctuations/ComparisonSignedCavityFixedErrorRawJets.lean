module

public import ComparisonSignedCavityWholeLawProfileBudgets

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

theorem disorderProfileJets_fixedError_finite_wholeLaw_raw_bound
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ] ℝ)
    (F : ι→ℝ) (hF : ∀σ i,(φ σ (Pi.single i 1))^2=F i)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i≤q 0 i)
    (Ds : List (ℕ→ι→ℝ)) (hk : 0<Ds.length)
    {B C rho d : ℝ} (hB : 0≤B) (hC : 0≤C) (hrho : 0<rho) (hd : 0≤d)
    (hDs : ∀D∈Ds,∀j,j≤as.length→∀i,|D j i|≤B)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves≤r)
    (P : T.Assignment→ℝ)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^4) x≤C^4)
    (A : S→S→ℝ) (u z : T.Slot) (huz : u≠z)
    (hsecond : (pairClock as (T.splitIndex u z)).disorderExpect w φ v q
      (fun σ=>(A (pairSpin as (T.splitIndex u z) σ).1
        (pairSpin as (T.splitIndex u z) σ).2)^2) x≤d^2)
    (hmoment : ∀D∈Ds,∀j,j≤as.length→(pairClock as j).disorderExpect w φ v q
      (fun σ=>|ReplicaTree.coordinateProfile φ D j (pairSpin as j σ).1
        (pairSpin as j σ).2|^(4*Ds.length)) x≤rho^(4*Ds.length)) :
    |disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T
      (fun σ=>P σ*A (T.atSlot σ u) (T.atSlot σ z))|≤
      absJetVariation r Ds.length*C*d*rho^Ds.length := by
  classical
  let J:=fun σ=>P σ*A (T.atSlot σ u) (T.atSlot σ z)
  rw [disorderProfileJets_eq_clipDirections w φ v q x Ds T J]
  have hbounds:=clipDirection_bounded as.length Ds hB hDs
  rw [T.disorderProfileJets_eq_allOffDiagonal hw φ F hF ho v q hq hq0
    (Ds.map (clipDirection as.length)) hB hbounds J x]
  let Ks:=(Ds.map (clipDirection as.length)).map
    (fun D=>(ReplicaTree.coordinateProfile φ D,rho))
  let Ac:=fun j σ τ=>if j=T.splitIndex u z then A σ τ else 0
  have hsecondAll : ∀j,(pairClock as j).disorderExpect w φ v q
      (fun σ=>(Ac j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x≤d^2 := by
    intro j
    by_cases hj : j=T.splitIndex u z
    · subst j
      simpa only [Ac,ite_true] using hsecond
    · simp only [Ac,hj,ite_false,zero_pow (by norm_num : (2:ℕ)≠0),
        disorderExpect,mul_zero,Finset.sum_const_zero]
      exact sq_nonneg d
  have hmomentAll : ∀K∈Ks,∀j,(pairClock as j).disorderExpect w φ v q
      (fun σ=>|K.1 j (pairSpin as j σ).1 (pairSpin as j σ).2|^(4*Ds.length)) x≤K.2^(4*Ds.length) := by
    intro K hK j
    obtain ⟨Dc,hDc,rfl⟩:=List.mem_map.mp hK
    obtain ⟨D,hD,rfl⟩:=List.mem_map.mp hDc
    by_cases hj : j≤as.length
    · simpa only [coordinateProfile_clip_below φ as.length D hj] using hmoment D hD j hj
    · simp only [coordinateProfile_clip_above φ as.length D hj,Pi.zero_apply,abs_zero,
        zero_pow (by omega : 4*Ds.length≠0),disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho.le _
  have H:=disorderOffDiagonalJets_oneError_wholeLaw_scaled_pair_bound hw φ ho v q x
    Ks hk hC T hT 0 P hP Ac u z huz (fun _=>hd) hsecondAll
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i=>Fin.elim0 i) Fin.elim0 (fun i=>Fin.elim0 i)
    (by simp only [Ks,List.length_map,zero_add]) (by intro i;exact Fin.elim0 i)
    hmomentAll (by intro K hK;obtain ⟨Dc,hDc,rfl⟩:=List.mem_map.mp hK;exact hrho)
  simpa [Ks,Function.comp_def,Ac,J] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
