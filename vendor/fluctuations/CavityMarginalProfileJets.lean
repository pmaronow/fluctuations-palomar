module

public import CavityDiagonalCancellation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 def strictCumulativeClock (v : ι → ℝ) (q : ℕ → ι → ℝ) (epsilon : ℝ) : Prop :=
    (∀ i, v i+epsilon ≤ q 0 i) ∧ (∀ j i, q j i+epsilon ≤ q (j+1) i)

 theorem strictCumulativeClock.monotone {v : ι → ℝ} {q : ℕ → ι → ℝ} {epsilon : ℝ}
    (h : strictCumulativeClock v q epsilon) (he : 0 ≤ epsilon) (i : ι) :
    Monotone (fun j => q j i) := by
  apply monotone_nat_of_le_succ
  intro j
  exact (le_add_of_nonneg_right he).trans (h.2 j i)

 theorem strictCumulativeClock_perturb {v : ι → ℝ} {q D : ℕ → ι → ℝ}
    {epsilon B s : ℝ} (he : 0 < epsilon) (hB : 0 ≤ B)
    (hq : strictCumulativeClock v q epsilon) (hD : ∀ j i, |D j i| ≤ B)
    (hs : |s| * (2*B+1) ≤ epsilon/2) :
    strictCumulativeClock v (fun j i => q j i+s*D j i) (epsilon/2) := by
  have hprod (j : ℕ) (i : ι) : |s*D j i| ≤ |s| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hD j i) (abs_nonneg _)
  have hsmall : |s| * B ≤ epsilon/2 := by nlinarith [abs_nonneg s]
  have hsmall2 : 2*(|s| * B) ≤ epsilon/2 := by nlinarith [abs_nonneg s]
  constructor
  · intro i
    have H := hq.1 i
    have hp := (neg_le_of_abs_le (hprod 0 i))
    linarith
  · intro j i
    have H := hq.2 j i
    have hp := (le_of_abs_le (hprod j i))
    have hm := (neg_le_of_abs_le (hprod (j+1) i))
    linarith

 theorem strictCumulativeClock_regularize {v : ι → ℝ} {q : ℕ → ι → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    {epsilon : ℝ} (he : 0 ≤ epsilon) :
    strictCumulativeClock v (fun j i => q j i+epsilon*(j+1:ℕ)) epsilon := by
  constructor
  · intro i
    norm_num only [Nat.zero_add,Nat.cast_one,mul_one]
    exact add_le_add (hq0 i) le_rfl
  · intro j i
    have H := hq i (Nat.le_succ j)
    push_cast
    nlinarith

namespace ClockTree

 theorem markedAttach_profileJets_preserves_strict {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (v : ι → ℝ) (Ds : List (ℕ → ι → ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B)
    (P : T.Assignment → ℝ) (x : ι → ℝ)
    (q : ℕ → ι → ℝ) {epsilon : ℝ} (he : 0 < epsilon)
    (hq : strictCumulativeClock v q epsilon) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ => P (p.restrict σ)) =
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P := by
  induction Ds using List.reverseRecOn generalizing q epsilon with
  | nil => exact T.markedAttach_disorderPreserves_actual hw φ ho p hp v q P x
  | append_singleton Ds D ih =>
    have hD : ∀ j i, |D j i| ≤ B := hDs D (by simp)
    have hOld : ∀ E ∈ Ds, ∀ j i, |E j i| ≤ B := fun E hE => hDs E (by simp [hE])
    let radius := epsilon/(2*(2*B+1))
    have hrpos : 0 < radius := by dsimp [radius]; positivity
    have hpert (s : ℝ) (hs : s ∈ Ioo (-radius) radius) :
        strictCumulativeClock v (fun j i => q j i+s*D j i) (epsilon/2) := by
      apply strictCumulativeClock_perturb he hB hq hD
      have hsabs : |s| ≤ radius := (abs_le).2 ⟨hs.1.le,hs.2.le⟩
      have hh := mul_le_mul_of_nonneg_right hsabs (by positivity : 0 ≤ 2*B+1)
      have hrad : radius*(2*B+1)=epsilon/2 := by dsimp [radius]; field_simp
      rwa [hrad] at hh
    have hmono : ∀ s ∈ Ioo (-radius) radius, ∀ i, Monotone (fun j => q j i+s*D j i) := by
      intro s hs i
      exact (hpert s hs).monotone (by positivity) i
    have hroot : ∀ s ∈ Ioo (-radius) radius, ∀ i, v i ≤ q 0 i+s*D 0 i := by
      intro s hs i
      have H := (hpert s hs).1 i
      linarith
    have hzero : (0:ℝ) ∈ Ioo (-radius) radius := by constructor <;> linarith
    have hL := hasDerivAt_finiteProfileJets hw φ ho v q D hmono hroot
      (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree (fun σ => P (p.restrict σ)) x hzero
    have hR := hasDerivAt_finiteProfileJets hw φ ho v q D hmono hroot
      (Ds.map (ReplicaTree.coordinateProfile φ)) T P x hzero
    have hfamily : (fun s => disorderProfileJets w φ v (fun j i => q j i+s*D j i) x
        (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree (fun σ => P (p.restrict σ))) =ᶠ[𝓝 (0:ℝ)]
        (fun s => disorderProfileJets w φ v (fun j i => q j i+s*D j i) x
          (Ds.map (ReplicaTree.coordinateProfile φ)) T P) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact ih hOld _ (by positivity) (hpert s hs)
    have H := hfamily.deriv_eq
    rw [hL.deriv,hR.deriv] at H
    simpa only [List.map_append,List.map_singleton,zero_mul,add_zero] using H

 theorem markedAttach_profileJets_preserves_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (hq : ∀ i, Monotone (fun j => q j i))
    (hq0 : ∀ i, v i ≤ q 0 i) (Ds : List (ℕ → ι → ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ => P (p.restrict σ)) =
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P := by
  let qr := fun e : ℝ => fun j i => q j i+e*(j+1:ℕ)
  have heq : EqOn
      (fun e => disorderProfileJets w φ v (qr e) x (Ds.map (ReplicaTree.coordinateProfile φ))
        p.tree (fun σ => P (p.restrict σ)))
      (fun e => disorderProfileJets w φ v (qr e) x (Ds.map (ReplicaTree.coordinateProfile φ)) T P)
      (Ioi (0:ℝ)) := by
    intro e he
    exact T.markedAttach_profileJets_preserves_strict hw φ ho p hp v Ds hB hDs P x
      (qr e) he (strictCumulativeClock_regularize hq hq0 he.le)
  have hc (j : ℕ) : Continuous (fun e => qr e j) := by dsimp [qr]; fun_prop
  have hL := disorderProfileJets_continuous hw φ ho v qr hc (fun _ => x) continuous_const
    (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree (fun σ => P (p.restrict σ))
  have hR := disorderProfileJets_continuous hw φ ho v qr hc (fun _ => x) continuous_const
    (Ds.map (ReplicaTree.coordinateProfile φ)) T P
  have h0 : (0:ℝ) ∈ closure (Ioi (0:ℝ)) := by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ) ≤ 0)
  have H := heq.closure hL hR h0
  simpa only [qr,zero_mul,add_zero] using H

end ClockTree
end OAI.SKFluctuations.Hierarchy
