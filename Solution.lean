module

public import Chapter10ArcPenalty
public import Chapter10SequenceFixed

@[expose] public section

/-! Exact aliases of accepted literal formulation/penalty/fixed-domain results.
No source hypothesis, quantifier, constant or conclusion is changed. -/
noncomputable section
open scoped BigOperators

namespace Chapter10

/-- Exact source interface: incidence companion; its original full signature is retained. -/
theorem palomar_source_route_penalty_proposition {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ) (x : Bits n) :
    (energyMin A c ρ x ∧ ∃ y, feasible A y) ↔ routeMin A c x := by
  exact Chapter10.source_route_penalty_proposition A c ρ hρ x

end Chapter10

namespace Chapter10.Algebra

/-- Exact source interface: unit-gap support; its original full signature is retained. -/
theorem palomar_integer_penalty_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x) :
    integerPenalty A b x = 0 ↔ integerFeasible A b x := by
  exact Chapter10.Algebra.integer_penalty_zero_iff A b x hx

end Chapter10.Algebra

namespace Chapter10.Algebra

/-- Exact source interface: unit-gap support; its original full signature is retained. -/
theorem palomar_integer_penalty_gap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x)
    (hf : ¬ integerFeasible A b x) : 1 ≤ integerPenalty A b x := by
  exact Chapter10.Algebra.integer_penalty_gap A b x hx hf

end Chapter10.Algebra

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc matrix bridge; its original full signature is retained. -/
theorem palomar_matrix_iff_literal {n k} (D : Data n) (T : Grid k) (x : Assignment n k) :
    MatrixFeasible D T x ↔ Literal D T x := by
  exact Chapter10.Routing.Arc.matrix_iff_literal D T x

end Chapter10.Routing.Arc

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc penalty; its original full signature is retained. -/
theorem palomar_arc_penalty_zero_iff (D : Data n) (T : Grid k) (x : Assignment n k) :
    arcPenalty D T x = 0 ↔ Feasible D T x := by
  exact Chapter10.Routing.Arc.arc_penalty_zero_iff D T x

end Chapter10.Routing.Arc

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc minimizers; its original full signature is retained. -/
theorem palomar_arc_minimizers_exact (D : Data n) (T : Grid k) (domain : Set (Assignment n k))
    (ρ : ℝ) (hρ : (∑ e : Edge n k, |coordinateCost D e|) < ρ) (x : Assignment n k) :
    (IsMinOn domain (arcEnergy D T ρ) x ∧ ∃ y ∈ domain, Feasible D T y) ↔
      IsMinOn {y | y ∈ domain ∧ Feasible D T y} (objective D) x := by
  exact Chapter10.Routing.Arc.arc_minimizers_exact D T domain ρ hρ x

end Chapter10.Routing.Arc

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc matrix energy; its original full signature is retained. -/
theorem palomar_actual_arc_qubo_identity (D : Data n) (T : Grid k) (ρ : ℝ) (x : Assignment n k) :
    arcEnergy D T ρ x = quadratic (arcQUBO D T ρ) (fun e => Chapter10.bit (x e)) + ρ * (n : ℝ) := by
  exact Chapter10.Routing.Arc.actual_arc_qubo_identity D T ρ x

end Chapter10.Routing.Arc

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence penalty sums; its original full signature is retained. -/
theorem palomar_source_penalty_sums {n v k} (D : Data n) (x : Sequence.Array n v k) :
    penalty D x =
      (∑ i : Fin n, ((∑ a, ∑ p, x a p (some i)) - 1)^2) +
      (∑ a, ∑ p, ((∑ i, x a p i) - 1)^2) +
      (∑ a, ∑ p : Fin (k+1), ∑ i, ∑ j, if D.allowed i j then 0 else
        x a (Sequence.left p) i * x a (Sequence.right p) j) +
      (∑ a, ∑ p : Fin (k+1), ∑ j : Fin n, if 0 < p.val then
        x a (Sequence.left p) none * x a (Sequence.right p) (some j) else 0) := by
  exact Chapter10.SequencePenalty.source_penalty_sums D x

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence penalty; its original full signature is retained. -/
theorem palomar_penalty_zero_iff {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    penalty D x = 0 ↔ Rows D x := by
  exact Chapter10.SequencePenalty.penalty_zero_iff D x hx

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: tight repeated-cost bound; its original full signature is retained. -/
theorem palomar_objective_range {n v k} (D : Data n) (x y : Sequence.Array n v k)
    (hx : Sequence.Binary x) (hy : Sequence.Binary y) :
    Sequence.objective D x - Sequence.objective D y ≤ (k+1 : ℕ) * (v : ℝ) * arcAbsCost D := by
  exact Chapter10.SequencePenalty.objective_range D x y hx hy

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: printed repeated-cost bound; its original full signature is retained. -/
theorem palomar_objective_range_printed {n v k} (D : Data n) (x y : Sequence.Array n v k)
    (hx : Sequence.Binary x) (hy : Sequence.Binary y) :
    Sequence.objective D x - Sequence.objective D y ≤ printedBound D v k := by
  exact Chapter10.SequencePenalty.objective_range_printed D x y hx hy

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence minimizers; its original full signature is retained. -/
theorem palomar_minimizers_exact {n v k} (D : Data n) (ρ : ℝ)
    (hρ : printedBound D v k < ρ) (x : Sequence.Array n v k) :
    (IsMinOn (domain D) (energy D ρ) x ∧ ∃ y : Sequence.Array n v k, Sequence.Literal D y) ↔
      IsMinOn {y | Sequence.Literal D y} (Sequence.objective D) x := by
  exact Chapter10.SequencePenalty.minimizers_exact D ρ hρ x

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence matrix energy; its original full signature is retained. -/
theorem palomar_source_energy_matrix_identity {n v k} (D : Data n) (x : Sequence.Array n v k)
    (ρ : ℝ) (hx : Sequence.Binary x) :
    energy D ρ x = quadratic (matrix D ρ) (flatten x) +
      ρ * ((n : ℝ) + (v : ℝ) * (k+2 : ℕ)) := by
  exact Chapter10.SequencePenalty.source_energy_matrix_identity D x ρ hx

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source fixed partition; its original full signature is retained. -/
theorem palomar_domain_iff_split_fixed {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (x : Sequence.Array n v k) : x ∈ domain D ↔ splitArray D x ∈ fixedDomain (fixedValues D) := by
  exact Chapter10.SequencePenalty.domain_iff_split_fixed D hdd x

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source reduced energy; its original full signature is retained. -/
theorem palomar_source_fixed_energy_identity {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (z : Free n v k D → ℝ) (hz : Algebra.Binary z) :
    energy D ρ (sourceExtend D z) = reducedEnergy D ρ z := by
  exact Chapter10.SequencePenalty.source_fixed_energy_identity D hdd ρ z hz

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source minimum transport; its original full signature is retained. -/
theorem palomar_source_fixed_min_transport {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (z : Free n v k D → ℝ) :
    IsMinOn (domain D) (energy D ρ) (sourceExtend D z) ↔
      IsMinOn {z | Algebra.Binary z} (reducedEnergy D ρ) z := by
  exact Chapter10.SequencePenalty.source_fixed_min_transport D hdd ρ z

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source reduced exactness; its original full signature is retained. -/
theorem palomar_reduced_minimizers_exact {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (hρ : printedBound D v k < ρ) (z : Free n v k D → ℝ) :
    (IsMinOn {z | Algebra.Binary z} (reducedEnergy D ρ) z ∧
      ∃ w : Free n v k D → ℝ, Algebra.Binary w ∧ Sequence.Literal D (sourceExtend D w)) ↔
      IsMinOn {x | Sequence.Literal D x} (Sequence.objective D) (sourceExtend D z) := by
  exact Chapter10.SequencePenalty.reduced_minimizers_exact D hdd ρ hρ z

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual finite source attainment; its original full signature is retained. -/
theorem palomar_source_energy_attainment {n v k : ℕ} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) : ∃ x : Sequence.Array n v k, IsMinOn (domain D) (energy D ρ) x := by
  exact Chapter10.SequencePenalty.source_energy_attainment D hdd ρ

end Chapter10.SequencePenalty


namespace Chapter10.Algebra

theorem palomar_full_qubo_identity {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c x : ι → ℝ) (ρ : ℝ) (hx : Binary x) :
    linearCost c x + ρ * squaredResidual A b x =
      quadratic (quboMatrix A b c ρ) x + ρ * ∑ r, (b r)^2 := by
  exact Chapter10.Algebra.full_qubo_identity A b c x ρ hx

theorem palomar_integer_penalty_minimizers_exact {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (c : ι → ℝ) (D : Set (ι → ℝ))
    (hD : ∀ x ∈ D, Binary x) (ρ : ℝ) (hρ : (∑ i, |c i|) < ρ) (x : ι → ℝ) :
    (IsMinOn D (penalized (linearCost c) (integerPenalty A b) ρ) x ∧
      ∃ y ∈ D, integerFeasible A b y) ↔
      IsMinOn {y | y ∈ D ∧ integerFeasible A b y} (linearCost c) x := by
  exact Chapter10.Algebra.integer_penalty_minimizers_exact A b c D hD ρ hρ x

theorem palomar_fixed_qubo_identity {U F : Type*} [Fintype U] [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (z : U → ℝ) (κ : ℝ) (hz : Binary z) :
    quadratic M (extend a z) + κ = quadratic (fixedMatrix M a) z + fixedOffset M a κ := by
  exact Chapter10.Algebra.fixed_qubo_identity M a z κ hz

theorem palomar_fixed_qubo_min_transport {U F : Type*} [Fintype U] [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (ha : Binary a) (z : U → ℝ) (κ : ℝ) :
    IsMinOn (fixedDomain a) (fun x => quadratic M x + κ) (extend a z) ↔
      IsMinOn {z | Binary z} (fun z => quadratic (fixedMatrix M a) z + fixedOffset M a κ) z := by
  exact Chapter10.Algebra.fixed_qubo_min_transport M a ha z κ

end Chapter10.Algebra
