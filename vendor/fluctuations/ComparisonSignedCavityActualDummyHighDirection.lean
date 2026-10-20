module

public import ComparisonSignedCavityActualDummyScalarModel
public import ComparisonSignedCavityActualGhostProfileRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 10000000

def nativeOriginalHighKernel (n U : ℕ) (b C : ℕ→ℝ) (j : ℕ)
    (s t : Spin n×Bool) : ℝ :=
  if U ≤ j then b j*(deletedOverlap n (joinSpin s) (joinSpin t)-C j) else 0

def nativeDummyHighDirection (n U : ℕ) (b C : ℕ→ℝ) (j : ℕ) :
    NativeDummyCoordinate n→ℝ :=
  if U ≤ j then Sum.elim (Sum.elim (fun _=>0) (fun _=>-b j*C j)) (fun _=>b j)
  else 0

def nativeDummyScalarRootDirection (n : ℕ) : NativeDummyCoordinate n→ℝ :=
  Sum.elim (Sum.elim (fun _=>0) (fun _=>1)) (fun _=>0)

theorem nativeDummyFeature_scalarRootDirection (n : ℕ) (s : (Spin n×Bool)×Bool) :
    nativeDummyFeature n s (nativeDummyScalarRootDirection n)=spinValue s.2 := by
  rw [nativeDummyFeature_apply]
  simp [nativeDummyScalarRootDirection]

theorem nativeDummyHighDirection_coordinateProfile (n U : ℕ) (b C : ℕ→ℝ)
    (j : ℕ) (s t : (Spin n×Bool)×Bool) :
    ReplicaTree.coordinateProfile (nativeDummyFeature n) (nativeDummyHighDirection n U b C) j s t=
      spinValue s.2*spinValue t.2*nativeOriginalHighKernel n U b C j s.1 t.1 := by
  classical
  by_cases hj : U ≤ j
  · unfold ReplicaTree.coordinateProfile
    simp only [Fintype.sum_sum_type,nativeDummyHighDirection,hj,ite_true,Sum.elim_inl,
      Sum.elim_inr,zero_mul,Finset.sum_const_zero,zero_add,
      nativeDummyFeature_single_scalar,nativeDummyFeature_single_cross]
    simp only [Fin.sum_univ_one,nativeOriginalHighKernel,hj,ite_true,
      deletedOverlap,joinSpin,Fin.lastCases_castSucc]
    have hden : (Real.sqrt (n+1:ℕ))^2=(n+1:ℕ) := Real.sq_sqrt (by positivity)
    have hpos : Real.sqrt (n+1:ℕ)≠0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have he (i : Fin n) :
        b j*(spinValue (s.1.1 i)*spinValue s.2/Real.sqrt (n+1:ℕ))*
            (spinValue (t.1.1 i)*spinValue t.2/Real.sqrt (n+1:ℕ))=
          spinValue s.2*spinValue t.2*b j/(n+1:ℕ)*
            (spinValue (s.1.1 i)*spinValue (t.1.1 i)) := by
      calc
        _ = (spinValue s.2*spinValue t.2*b j*
          (spinValue (s.1.1 i)*spinValue (t.1.1 i)))/(Real.sqrt (n+1:ℕ))^2 := by ring
        _ = _ := by rw [hden];ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    ring
  · simp [ReplicaTree.coordinateProfile,nativeDummyHighDirection,nativeOriginalHighKernel,hj]

theorem nativeDummyClock_monotone {n : ℕ} (q : ℕ→FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    ∀i,Monotone (fun j=>nativeDummyClock q U K j i) := by
  intro i
  rcases i with (i|i)|i
  · exact hq i
  · exact relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK
  · exact monotone_const

theorem nativeDummyRoot_le_clock_zero {n : ℕ} (v : FullCoordinate n→ℝ)
    (q : ℕ→FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    (hq0 : ∀i,v i ≤ q 0 i) (hK : ∀j,0 ≤ K j) :
    ∀i,nativeDummyRoot v i ≤ nativeDummyClock q U K 0 i := by
  intro i
  rcases i with (i|i)|i
  · exact hq0 i
  · exact relocatedClock_nonneg U (by norm_num : (0:ℝ) ≤ 0) hK 0
  · exact le_rfl

theorem native_original_high_G_atom_eq_kernel {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K b C : ℕ→ℝ) (a c e f : T.Slot) (hU : U ≤ as.length)
    (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e f σ=
      (1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*
        nativeOriginalHighKernel n U b C (T.splitIndex e f) (T.atSlot σ e) (T.atSlot σ f) := by
  rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b
    (fun j=>K j-b j*C j) K C (by intro j;ring) a c e f hU]
  unfold restHighKernel nativeOriginalHighKernel
  by_cases hj : U ≤ T.splitIndex e f
  · simp only [not_lt.mpr hj,hj,ite_false,ite_true,deletedOverlap,joinSpin,
      Fin.lastCases_castSucc]
    ring
  · simp only [lt_of_not_ge hj,hj,ite_true,ite_false,mul_zero]

end OAI.SKFluctuations.Cavity
