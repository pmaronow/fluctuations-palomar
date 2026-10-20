module

public import ComparisonSignedCavitySmallCutRowGraph
public import ComparisonSignedCavityWholeLawOneErrorJets

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_small_cut_nat_moment_le_original_cap (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U V : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (m : ℕ) (hm : 0 < m) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hbound : ∀ j<V,|K j|+|h j|+|b j| ≤ M)
    {l s t : ℝ} (hl : l∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1)
    (ht : t∈Icc (0:ℝ) 1)
    (hsource : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t b h K) (fun σ => |P σ|^m) x ≤ A^m) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (nativeSmallCutRowClock n q U V l s t b h K) (fun σ => |P σ|^m) x ≤
      (Real.exp (ClockTree.jetVariation T.leaves 1*M)*A)^m := by
  let E := Real.exp (ClockTree.jetVariation T.leaves 1*M)
  have hE : 1≤E := Real.one_le_exp (mul_nonneg (ClockTree.jetVariation_nonneg _ _) hM)
  have H := native_small_cut_nonnegative_test_le_original n q U V b h K T ho
    (fun σ => |P σ|^m) (fun σ => pow_nonneg (abs_nonneg _) _) x hq0 hq hb hh hK
    hbm hhm hKm hM hbound hl hs ht
  have hp : E≤E^m := by
    have HH := pow_le_pow_right₀ hE (show 1 ≤ m by omega)
    simpa only [pow_one] using HH
  exact H.trans ((mul_le_mul_of_nonneg_left hsource (Real.exp_nonneg _)).trans (by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hp (pow_nonneg hA _)))

theorem native_single_low_insertion_fixed_error_bound (n : ℕ)
    (q : ℕ → FullCoordinate n → ℝ) (hq : ∀ i,Monotone (fun j => q j i))
    (hq0 : ∀ i,0 ≤ q 0 i) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (A : ℕ → (Spin n×Bool) → (Spin n×Bool) → ℝ)
    (u z : T.Slot) (huz : u ≠ z)
    {a : ℕ} (E : Fin a → ℕ → (Spin n×Bool) → (Spin n×Bool) → ℝ)
    (s t : Fin a → T.Slot) (hst : ∀ i,s i≠t i)
    (D : ℕ → FullCoordinate n → ℝ) (x : FullCoordinate n → ℝ)
    {C d rho : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hrho : 0<rho)
    (r : Fin a → ℝ) (hr : ∀ i,0<r i)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ => |P σ|^4) x ≤ C^4)
    (hA : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ => (A (T.splitIndex u z) (ClockTree.pairSpin as (T.splitIndex u z) σ).1
        (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) x ≤ d^2)
    (hE : ∀ i,(ClockTree.pairClock as (T.splitIndex (s i) (t i))).disorderExpect
      (fullWeight n) (fullFeature n) 0 q
      (fun σ => |E i (T.splitIndex (s i) (t i))
        (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(4*(a+1))) x ≤ (r i)^(4*(a+1)))
    (hD : ∀ j,(ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ => |ReplicaTree.coordinateProfile (fullFeature n) D j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*(a+1))) x ≤ rho^(4*(a+1))) :
    |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 q x
      [ReplicaTree.coordinateProfile (fullFeature n) D] T
      (fun σ => P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
        (∏ i,E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i))))| ≤
      ClockTree.absJetVariation T.leaves 1*C*d*(∏ i,r i)*rho := by
  let J := fun σ => P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
    (∏ i,E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))
  let A0 := fun j σ τ => if j=T.splitIndex u z then A j σ τ else 0
  let E0 := fun i j σ τ => if j=T.splitIndex (s i) (t i) then E i j σ τ else 0
  have hA0 (j : ℕ) : (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ => (A0 j (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) x ≤ d^2 := by
    by_cases hj : j=T.splitIndex u z
    · subst j
      simpa only [A0,ite_eq_left] using hA
    · simp only [A0,hj,↓reduceIte,zero_pow (by norm_num : (2:ℕ)≠0),
        ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact sq_nonneg d
  have hE0 (i : Fin a) (j : ℕ) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 q
      (fun σ => |E0 i j (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*(a+1))) x ≤
        (r i)^(4*(a+1)) := by
    by_cases hj : j=T.splitIndex (s i) (t i)
    · subst j
      simpa only [E0,ite_eq_left] using hE i
    · simp only [E0,hj,↓reduceIte,abs_zero,zero_pow (show 4*(a+1)≠0 by omega),
        ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg (hr i).le _
  have Hdiag := T.disorderProfileJets_errorFirst_eq_offDiagonal (fullWeight_pos n)
    (fullFeature n) ho 0 q hq hq0 [] (B:=0) (by norm_num) (by simp)
    J (fun σ => fullFeature_coordinateProfile_self n D as.length σ) x
  simp only [List.map_nil,ClockTree.disorderOffDiagonalProfileJets,
    ClockTree.disorderOffDiagonalJets,ClockTree.disorderProfileJets] at Hdiag
  have H := T.disorderOffDiagonalJets_oneError_wholeLaw_scaled_pair_bound
    (fullWeight_pos n) (fullFeature n) ho 0 q x
    [(ReplicaTree.coordinateProfile (fullFeature n) D,rho)]
    (k:=a+1) (by omega) hC (le_refl _) a P hP A0 u z huz
    (D:=fun _ => d) (fun _ => hd) hA0 E0 s t hst r hr (by simp)
    hE0 (by
      intro K hK j
      have HK := List.mem_singleton.mp hK
      subst K
      exact hD j)
    (by
      intro K hK
      have HK := List.mem_singleton.mp hK
      subst K
      exact hrho)
  have Heq : ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0 q x
      [ReplicaTree.coordinateProfile (fullFeature n) D] T J =
    ClockTree.disorderOffDiagonalJets (fullWeight n) (fullFeature n) 0 q x
      [ReplicaTree.coordinateProfile (fullFeature n) D] T J := by
    simpa only [ClockTree.disorderProfileJets,ClockTree.disorderOffDiagonalJets] using Hdiag
  rw [Heq]
  simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,List.length_cons,
    List.length_nil,zero_add,A0,E0,ite_eq_left] using H

theorem native_old_initial_row_product_abs_le_original_moments (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U V : ℕ) (hV0 : 0<V) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hV : V≤as.length) (P : T.cavityLeft.Assignment → ℝ)
    (A : ℕ → Spin n → Spin n → ℝ) (u z : T.Slot) (huz : T.splitIndex u z<V)
    {a : ℕ} (E : Fin a → ℕ → Spin n → Spin n → ℝ) (s t : Fin a → T.Slot)
    (hst : ∀ i,V ≤ T.splitIndex (s i) (t i)) (hne : ∀ i,s i≠t i)
    (x : FullCoordinate n → ℝ) (hs : ∀ i,x (.inl (.inr i))=0) (hr : ∀ i,x (.inr i)=0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {M C d rho : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hd : 0 ≤ d) (hrho : 0<rho)
    (hbound : ∀ j<V,|K j|+|h j|+|b j| ≤ M)
    (r : Fin a → ℝ) (hrpos : ∀ i,0<r i)
    {l t' : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t'∈Icc (0:ℝ) 1)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t' b h K)
      (fun σ => |P (T.cavityAssignment σ).1|^4) x ≤ C^4)
    (hA : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect (fullWeight n)
      (fullFeature n) 0 (cutFullVariance n q U l t' b h K)
      (fun σ => (nativeRestRowKernel n A (T.splitIndex u z)
        (ClockTree.pairSpin as (T.splitIndex u z) σ).1 (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) x ≤ d^2)
    (hE : ∀ i,(ClockTree.pairClock as (T.splitIndex (s i) (t i))).disorderExpect (fullWeight n)
      (fullFeature n) 0 (cutFullVariance n q U l t' b h K)
      (fun σ => |nativeRestRowKernel n (E i) (T.splitIndex (s i) (t i))
        (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(4*(a+1))) x ≤ (r i)^(4*(a+1)))
    (hnew : ∀ j,(ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l t' b h K)
      (fun σ => |ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n V t' (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*(a+1))) x ≤ rho^(4*(a+1))) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t' b h K)
      (nativeOldInitialRowProduct n T P A u z E s t) x| ≤
      ClockTree.absJetVariation T.leaves 1*
        (Real.exp (ClockTree.jetVariation T.leaves 1*M)*C)*
        (Real.exp (ClockTree.jetVariation 2 1*M)*d)*
        (∏ i,Real.exp (ClockTree.jetVariation 2 1*M)*r i)*
        (Real.exp (ClockTree.jetVariation 2 1*M)*rho) := by
  let ep := Real.exp (ClockTree.jetVariation 2 1*M)
  let et := Real.exp (ClockTree.jetVariation T.leaves 1*M)
  let J := nativeOldInitialRowProduct n T P A u z E s t
  let D := cutLSlope n V t' (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K)
  let B := ClockTree.absJetVariation T.leaves 1*(et*C)*(ep*d)*(∏ i,ep*r i)*(ep*rho)
  have hep : 0<ep := Real.exp_pos _
  have het : 0<et := Real.exp_pos _
  have hB : 0 ≤ B := by
    have hv := ClockTree.absJetVariation_nonneg T.leaves 1
    have hprod : 0 ≤ ∏ i,ep*r i := Finset.prod_nonneg (fun i _ => (mul_pos hep (hrpos i)).le)
    dsimp only [B]
    positivity
  have hb' := relocatedClock_nonneg U hl.1 hb
  have hh' := relocatedClock_nonneg U hl.1 hh
  have hK' := relocatedClock_nonneg U hl.1 hK
  have hbm' := relocatedClock_monotone U hl hbm hb
  have hhm' := relocatedClock_monotone U hl hhm hh
  have hKm' := relocatedClock_monotone U hl hKm hK
  have hboundJet (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      |cutLowJet n q V (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K)
        T J x 1 v t'| ≤ B := by
    rw [cutLowJet_eq_profileJets n q V _ _ _ T ho J x hq0 hq hb' hh' hK'
      hbm' hhm' hKm' 1 hv ht]
    simp only [List.replicate_one]
    apply native_single_low_insertion_fixed_error_bound n
      (nativeSmallCutRowClock n q U V l v t' b h K)
      (nativeSmallCutRowClock_monotone n q U V hl hv ht b h K hq hb hh hK hbm hhm hKm)
      (nativeSmallCutRowClock_nonneg n q U V hl hv ht b h K hq0 hb hh hK 0)
      T ho (fun σ => P (T.cavityAssignment σ).1) (nativeRestRowKernel n A) u z
      (by intro H; subst z; rw [T.splitIndex_self] at huz; omega)
      (fun i => nativeRestRowKernel n (E i)) s t hne D x
      (mul_nonneg het.le hC) (mul_nonneg hep.le hd) (mul_pos hep hrho)
      (fun i => ep*r i) (fun i => mul_pos hep (hrpos i))
    · exact native_small_cut_nat_moment_le_original_cap n q U V b h K T ho
        (fun σ => P (T.cavityAssignment σ).1) 4 (by norm_num) x hq0 hq hb hh hK hbm hhm hKm
        hM hC hbound hl hv ht hP
    · have H := native_small_cut_nat_moment_le_original_cap n q U V b h K
        (ClockTree.pairClock as (T.splitIndex u z)) ho
        (fun σ => nativeRestRowKernel n A (T.splitIndex u z)
          (ClockTree.pairSpin as (T.splitIndex u z) σ).1 (ClockTree.pairSpin as (T.splitIndex u z) σ).2)
        2 (by norm_num) x hq0 hq hb hh hK hbm hhm hKm hM hd hbound hl hv ht
        (by simpa only [sq_abs] using hA)
      simpa only [sq_abs,ClockTree.pairClock_leaves,ep] using H
    · intro i
      have H := native_small_cut_nat_moment_le_original_cap n q U V b h K
        (ClockTree.pairClock as (T.splitIndex (s i) (t i))) ho
        (fun σ => nativeRestRowKernel n (E i) (T.splitIndex (s i) (t i))
          (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).1
          (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).2)
        (4*(a+1)) (by omega) x hq0 hq hb hh hK hbm hhm hKm hM (hrpos i).le hbound
        hl hv ht (hE i)
      simpa only [ClockTree.pairClock_leaves,ep] using H
    · intro j
      have H := native_small_cut_nat_moment_le_original_cap n q U V b h K
        (ClockTree.pairClock as j) ho
        (fun σ => ReplicaTree.coordinateProfile (fullFeature n) D j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)
        (4*(a+1)) (by omega) x hq0 hq hb hh hK hbm hhm hKm hM hrho.le hbound hl hv ht (hnew j)
      simpa only [ClockTree.pairClock_leaves,ep] using H
  have Hrestore := native_old_initial_row_product_restore n q U V hV0 b h K T ho hV
    P A u z huz E s t hst x hs hr hq0 hq hb hh hK hbm hhm hKm hl ht
  rw [Hrestore]
  have H := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume)
    (f:=fun v => cutLowJet n q V (relocatedClock U l b) (relocatedClock U l h)
      (relocatedClock U l K) T J x 1 v t') (a:=0) (b:=1) (g:=fun _ => B)
    (by norm_num : (0:ℝ)≤1)
    (Filter.Eventually.of_forall (fun v (hv : v∈Ioc (0:ℝ) 1) => by
      rw [Real.norm_eq_abs]
      exact hboundJet v ⟨hv.1.le,hv.2⟩))
    (intervalIntegrable_const)
  simpa only [Real.norm_eq_abs,intervalIntegral.integral_const,smul_eq_mul,
    sub_zero,one_mul,B,ep,et] using H

end OAI.SKFluctuations.Cavity
