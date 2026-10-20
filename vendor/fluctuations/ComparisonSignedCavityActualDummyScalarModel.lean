module

public import ComparisonSignedCavityActualOriginalGPairingTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 8000000

abbrev NativeDummyCoordinate (n : ℕ) := (FullCoordinate n ⊕ Fin 1) ⊕ Fin n

def nativeDummyWeight (n : ℕ) (s : (Spin n×Bool)×Bool) : ℝ :=
  fullWeight n s.1*(1/2:ℝ)

theorem nativeDummyWeight_pos (n : ℕ) (s : (Spin n×Bool)×Bool) :
    0 < nativeDummyWeight n s := mul_pos (fullWeight_pos n s.1) (by norm_num)

def nativeDummyCrossFeature (n : ℕ) (s : (Spin n×Bool)×Bool) : (Fin n→ℝ)→L[ℝ]ℝ :=
  ∑i, (spinValue (s.1.1 i)*spinValue s.2/Real.sqrt (n+1:ℕ)) • ContinuousLinearMap.proj i

def nativeDummyFeature (n : ℕ) (s : (Spin n×Bool)×Bool) : (NativeDummyCoordinate n→ℝ)→L[ℝ]ℝ :=
  (productFeature (fullFeature n) scalarFeature s).comp sumLeft+
    (nativeDummyCrossFeature n s).comp sumRight

def nativeDummyRoot {n : ℕ} (v : FullCoordinate n→ℝ) : NativeDummyCoordinate n→ℝ :=
  Sum.elim (Sum.elim v (fun _=>0)) (fun _=>0)

def nativeDummyClock {n : ℕ} (q : ℕ→FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ) :
    ℕ→NativeDummyCoordinate n→ℝ :=
  fun j=>Sum.elim (Sum.elim (q j) (fun _=>relocatedClock U 0 K j)) (fun _=>0)

def nativeDummyField {n : ℕ} (x : FullCoordinate n→ℝ) : NativeDummyCoordinate n→ℝ :=
  cavityEmbed (Sum.elim x (fun _=>0))

theorem nativeDummyFeature_apply (n : ℕ) (s : (Spin n×Bool)×Bool)
    (x : NativeDummyCoordinate n→ℝ) :
    nativeDummyFeature n s x =
      fullFeature n s.1 (fun i=>x (.inl (.inl i)))+
      spinValue s.2*x (.inl (.inr 0))+
      ∑i, (spinValue (s.1.1 i)*spinValue s.2/Real.sqrt (n+1:ℕ))*x (.inr i) := by
  simp [nativeDummyFeature,nativeDummyCrossFeature,productFeature,scalarFeature,
    sumLeft,sumRight,spinValue]
  split <;> simp_all

theorem nativeDummyFeature_restrict (n : ℕ) (s : (Spin n×Bool)×Bool) :
    (nativeDummyFeature n s).comp cavityEmbed=productFeature (fullFeature n) scalarFeature s := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,nativeDummyFeature_apply,cavityEmbed_inl,cavityEmbed_inr,
    mul_zero,Finset.sum_const_zero,add_zero]
  rfl

theorem nativeDummyFeature_single_cross (n : ℕ) [DecidableEq (NativeDummyCoordinate n)]
    (s : (Spin n×Bool)×Bool) (i : Fin n) :
    nativeDummyFeature n s (Pi.single (.inr i) 1)=
      spinValue (s.1.1 i)*spinValue s.2/Real.sqrt (n+1:ℕ) := by
  classical
  rw [nativeDummyFeature_apply]
  have hz : (fun k : FullCoordinate n=>(Pi.single (Sum.inr i) (1:ℝ) : NativeDummyCoordinate n→ℝ) (Sum.inl (Sum.inl k)))=0 := by
    funext k;simp
  rw [hz,map_zero]
  simp [Pi.single_apply]

theorem nativeDummyFeature_single_scalar (n : ℕ) [DecidableEq (NativeDummyCoordinate n)]
    (s : (Spin n×Bool)×Bool) (i : Fin 1) :
    nativeDummyFeature n s (Pi.single (.inl (.inr i)) 1)=spinValue s.2 := by
  classical
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rw [nativeDummyFeature_apply]
  have hz : (fun k : FullCoordinate n=>(Pi.single (Sum.inl (Sum.inr (0:Fin 1))) (1:ℝ) : NativeDummyCoordinate n→ℝ) (Sum.inl (Sum.inl k)))=0 := by
    funext k;simp
  rw [hz,map_zero]
  simp

theorem nativeDummyFeature_single_physical (n : ℕ) [DecidableEq (NativeDummyCoordinate n)]
    (s : (Spin n×Bool)×Bool) (i : FullCoordinate n) :
    nativeDummyFeature n s (Pi.single (.inl (.inl i)) 1)=fullFeature n s.1 (Pi.single i 1) := by
  classical
  rw [nativeDummyFeature_apply]
  have he : (fun k : FullCoordinate n=>(Pi.single (Sum.inl (Sum.inl i)) (1:ℝ) : NativeDummyCoordinate n→ℝ) (Sum.inl (Sum.inl k)))=
      Pi.single i 1 := by
    funext k;simp [Pi.single_apply]
  rw [he]
  simp

end OAI.SKFluctuations.Cavity
