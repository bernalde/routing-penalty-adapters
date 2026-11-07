module

public import Mathlib

@[expose] public section

/-! Literal finite routing penalties and actual fixed-coordinate transport.
All computational definitions and finite-index/partition proof bodies below
are copied from their source definitions. Only advertised theorem obligations
are deliberately unproved; Solution never imports this module. -/
noncomputable section
open scoped BigOperators

namespace Chapter10

/-- Finite Boolean incidence decisions. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The real value zero or one of a Boolean decision. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The actual number of chosen incidence columns covering one row. -/
def coverCount {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) (i : Fin m) : ℕ :=
  ∑ r, if A i r && x r then 1 else 0

/-- Every incidence row has exactly one chosen covering column. -/
def feasible {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) : Prop :=
  ∀ i, coverCount A x i = 1

/-- The complete finite linear incidence objective. -/
def cost {n : ℕ} (c : Fin n → ℝ) (x : Bits n) : ℝ := ∑ r, c r * bit (x r)

/-- The sum of squared deviations of incidence counts from one. -/
def penalty {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) : ℝ :=
  ∑ i, ((coverCount A x i : ℝ) - 1)^2

/-- The actual incidence objective plus its weighted squared penalty. -/
def energy {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ)
    (ρ : ℝ) (x : Bits n) : ℝ := cost c x + ρ * penalty A x

/-- A feasible incidence decision no more costly than any other feasible decision. -/
def routeMin {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ) (x : Bits n) : Prop :=
  feasible A x ∧ ∀ y, feasible A y → cost c x ≤ cost c y

/-- A global minimum of the actual penalized incidence energy. -/
def energyMin {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ)
    (ρ : ℝ) (x : Bits n) : Prop := ∀ y, energy A c ρ x ≤ energy A c ρ y

end Chapter10

namespace Chapter10.Algebra

/-- Every real coordinate is exactly zero or one. -/
def Binary {ι : Type*} (x : ι → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

/-- The complete finite linear objective. -/
def linearCost {ι : Type*} [Fintype ι] (c x : ι → ℝ) : ℝ := ∑ i, c i * x i

/-- The full ordered matrix sum, with both orientations retained. -/
def quadratic {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * x i * x j

/-- A diagonal matrix with the supplied entries and zero off the diagonal. -/
def diagonal {ι : Type*} [DecidableEq ι] (d : ι → ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then d i else 0

/-- The actual sum of squared real equality residuals. -/
def squaredResidual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ r, ((∑ i, A r i * x i) - b r)^2

/-- The full matrix ρ AᵀA + diag(c − 2ρ Aᵀb). -/
def quboMatrix {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c : ι → ℝ) (ρ : ℝ) : ι → ι → ℝ :=
  fun i j => ρ * (∑ r, A r i * A r j) +
    diagonal (fun i => c i - 2 * ρ * (∑ r, A r i * b r)) i j

/-- Domain membership and objective no larger than every other domain point. -/
def IsMinOn {α : Type*} (D : Set α) (f : α → ℝ) (x : α) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, f x ≤ f y

/-- The original objective plus the supplied weighted penalty. -/
def penalized {α : Type*} (f w : α → ℝ) (ρ : ℝ) (x : α) : ℝ := f x + ρ * w x

/-- Every signed-integer equality holds after casting to real coordinates. -/
def integerFeasible {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) : Prop :=
  ∀ r, (∑ i, (A r i : ℝ) * x i) = (b r : ℝ)

/-- The actual squared residuals of the supplied signed-integer rows. -/
def integerPenalty {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) : ℝ :=
  squaredResidual (fun r i => (A r i : ℝ)) (fun r => (b r : ℝ)) x

/-- Combine free coordinates with the fixed assignment on a disjoint-sum domain. -/
def extend {U F : Type*} (a : F → ℝ) (z : U → ℝ) : U ⊕ F → ℝ := Sum.elim z a

/-- Binary full assignments agreeing with the supplied fixed coordinates. -/
def fixedDomain {U F : Type*} (a : F → ℝ) : Set (U ⊕ F → ℝ) :=
  {x | Binary x ∧ ∀ f, x (Sum.inr f) = a f}

/-- The free-variable linear term from both ordered free/fixed cross blocks. -/
def fixedLinear {U F : Type*} [Fintype F] (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) : U → ℝ :=
  fun u => ∑ f, (M (Sum.inl u) (Sum.inr f) + M (Sum.inr f) (Sum.inl u)) * a f

/-- The free/free block with the cross-block term on its diagonal. -/
def fixedMatrix {U F : Type*} [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) : U → U → ℝ :=
  fun u v => M (Sum.inl u) (Sum.inl v) + diagonal (fixedLinear M a) u v

/-- Original offset plus the full fixed/fixed quadratic contribution. -/
def fixedOffset {U F : Type*} [Fintype F]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (κ : ℝ) : ℝ :=
  κ + quadratic (fun f g => M (Sum.inr f) (Sum.inr g)) a

/-- Accumulate all ordered monomial coefficients, including repeated coordinates. -/
def productMatrix {ι τ : Type*} [DecidableEq ι] [Fintype τ]
    (c : τ → ℝ) (left right : τ → ι) : ι → ι → ℝ :=
  fun i j => ∑ t, if i = left t then if j = right t then c t else 0 else 0

end Chapter10.Algebra

namespace Chapter10.Routing

/-- A depot (none) or one of the finite customer labels. -/
abbrev Node (n : ℕ) := Option (Fin n)

/-- Literal routing data: allowed arcs, travel/cost, windows and separate load/capacity fields. No physical feasibility is assumed by the structure. -/
structure Data (n : ℕ) where
  allowed : Node n → Node n → Bool
  travel : Node n → Node n → ℝ
  cost : Node n → Node n → ℝ
  opening : Fin n → ℝ
  closing : Fin n → ℝ
  demand : Fin n → ℝ
  initialLoad : ℝ
  capacity : ℝ

/-- Nonnegative depot time, or the stated customer opening/closing interval. -/
def inWindow {n : ℕ} (D : Data n) (i : Node n) (s : ℝ) : Prop :=
  match i with
  | none => 0 ≤ s
  | some j => D.opening j ≤ s ∧ s ≤ D.closing j

end Chapter10.Routing

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- A finite node/time-grid event. -/
abbrev Event (n k : ℕ) := Node n × Fin k

/-- An ordered pair of finite node/time-grid events. -/
abbrev Edge (n k : ℕ) := Event n k × Event n k

/-- A Boolean decision for every time-indexed edge. -/
abbrev Assignment (n k : ℕ) := Edge n k → Bool

/-- A finite injective nonnegative real time grid, exactly as in the source type. -/
structure Grid (k : ℕ) where
  time : Fin k → ℝ
  distinct : Function.Injective time
  nonnegative : ∀ s, 0 ≤ time s

/-- The finite set of edge coordinates whose decisions are true. -/
def chosen {n k} (x : Assignment n k) : Finset (Edge n k) :=
  Finset.univ.filter fun e => x e = true

/-- Chosen edges entering a given customer at any grid event. -/
def arrivals {n k} (x : Assignment n k) (i : Fin n) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.2.1 = some i

/-- Chosen edges entering the specified customer/time event. -/
def incoming {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.2 = (some i, s)

/-- Chosen edges leaving the specified customer/time event. -/
def outgoing {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.1 = (some i, s)

/-- Each customer has exactly one chosen incoming edge. -/
def Visit {n k} (x : Assignment n k) : Prop := ∀ i, (arrivals x i).card = 1

/-- At every customer/time event the incoming and outgoing chosen-edge counts agree. -/
def Flow {n k} (x : Assignment n k) : Prop :=
  ∀ i s, (incoming x i s).card = (outgoing x i s).card

/-- Every chosen edge arrives in its endpoint window. -/
def ArrivalWindows {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → inWindow D e.2.1 (T.time e.2.2)

/-- Every chosen edge departs in its starting-node window. -/
def DepartureWindows {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → inWindow D e.1.1 (T.time e.1.2)

/-- Every chosen edge follows an allowed node pair. -/
def Permitted {n k} (D : Data n) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → D.allowed e.1.1 e.2.1 = true

/-- Every chosen edge satisfies the source travel-time inequality. -/
def Travel {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → T.time e.1.2 + D.travel e.1.1 e.2.1 ≤ T.time e.2.2

/-- The exact visit, flow, window, permitted-edge and travel rows; capacity and global path completeness are not included. -/
def Feasible {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  Visit x ∧ Flow x ∧ ArrivalWindows D T x ∧ DepartureWindows D T x ∧
    Permitted D x ∧ Travel D T x

/-- The real sum of chosen Boolean coordinates satisfying the supplied index predicate. -/
def displayedSum {n k} (x : Assignment n k) (p : Edge n k → Prop) [DecidablePred p] : ℝ :=
  ∑ e, if p e then Chapter10.bit (x e) else 0

/-- The literal real visit/flow equalities and fixed-zero rows of the printed time-indexed formulation. -/
def Literal {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  (∀ i, displayedSum x (fun e => e.2.1 = some i) = 1) ∧
  (∀ i s, displayedSum x (fun e => e.2 = (some i,s)) =
    displayedSum x (fun e => e.1 = (some i,s))) ∧
  (∀ e, ¬ inWindow D e.2.1 (T.time e.2.2) → Chapter10.bit (x e) = 0) ∧
  (∀ e, ¬ inWindow D e.1.1 (T.time e.1.2) → Chapter10.bit (x e) = 0) ∧
  (∀ e, D.allowed e.1.1 e.2.1 ≠ true → Chapter10.bit (x e) = 0) ∧
  (∀ e, T.time e.2.2 < T.time e.1.2 + D.travel e.1.1 e.2.1 → Chapter10.bit (x e) = 0)

/-- The complete edge objective, counting every time-indexed copy of node-pair cost. -/
def objective {n k} (D : Data n) (x : Assignment n k) : ℝ :=
  ∑ e, D.cost e.1.1 e.2.1 * Chapter10.bit (x e)

/-- Actual signed-integer visit, flow and per-edge fixed-zero row indices. -/
abbrev Row (n k : ℕ) := Sum (Fin n) (Sum (Fin n × Fin k) (Edge n k))

/-- The conjunction of both source windows, allowed-edge and travel-time conditions. -/
def edgeValid {n k} (D : Data n) (T : Grid k) (e : Edge n k) : Prop :=
  inWindow D e.2.1 (T.time e.2.2) ∧ inWindow D e.1.1 (T.time e.1.2) ∧
    D.allowed e.1.1 e.2.1 = true ∧ T.time e.1.2 + D.travel e.1.1 e.2.1 ≤ T.time e.2.2

/-- The same classical decision procedure for the literal validity proposition as the proof source. -/
noncomputable def edgeValidDecision {n k} (D : Data n) (T : Grid k) (e : Edge n k) : Decidable (edgeValid D T e) :=
  Classical.propDecidable _

attribute [local instance] edgeValidDecision

/-- The literal integer row matrix, including signed flow cancellation and actual fixed-zero rows. -/
def rowMatrix {n k} (D : Data n) (T : Grid k) : Row n k → Edge n k → ℤ := by
  classical
  exact fun r e => match r with
  | .inl i => if e.2.1 = some i then 1 else 0
  | .inr (.inl q) => (if e.2 = (some q.1,q.2) then 1 else 0) -
      (if e.1 = (some q.1,q.2) then 1 else 0)
  | .inr (.inr f) => if edgeValid D T f then 0 else if e = f then 1 else 0

/-- One on visit rows and zero on flow/fixed rows. -/
def rowRhs {n k} : Row n k → ℤ
  | .inl _ => 1
  | .inr _ => 0

/-- The actual matrix-row dot product with real Boolean edge values. -/
def rowValue {n k} (D : Data n) (T : Grid k) (x : Assignment n k) (r : Row n k) : ℝ :=
  ∑ e, (rowMatrix D T r e : ℝ) * Chapter10.bit (x e)

/-- Every actual integer row equality holds. -/
def MatrixFeasible {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ r, rowValue D T x r = (rowRhs r : ℝ)

/-- The source cost at each complete time-indexed edge coordinate. -/
def coordinateCost {n k} (D : Data n) (e : Edge n k) : ℝ := D.cost e.1.1 e.2.1

/-- The signed-integer squared-residual penalty of the actual arc row matrix. -/
def arcPenalty (D : Data n) (T : Grid k) (x : Assignment n k) : ℝ :=
  integerPenalty (rowMatrix D T) rowRhs (fun e => Chapter10.bit (x e))

/-- The actual arc objective plus weighted actual row penalty. -/
def arcEnergy (D : Data n) (T : Grid k) (ρ : ℝ) (x : Assignment n k) : ℝ :=
  objective D x + ρ * arcPenalty D T x

/-- The full ordered QUBO matrix from the actual arc rows and repeated edge costs. -/
def arcQUBO (D : Data n) (T : Grid k) (ρ : ℝ) : Edge n k → Edge n k → ℝ :=
  quboMatrix (fun r e => (rowMatrix D T r e : ℝ)) (fun r => (rowRhs r : ℝ)) (coordinateCost D) ρ

end Chapter10.Routing.Arc

namespace Chapter10.Sequence
open Chapter10.Routing

/-- A real coordinate for each vehicle, one of k+2 positions and node. -/
abbrev Array (n v k : ℕ) := Fin v → Fin (k+2) → Node n → ℝ

/-- The actual initial position in Fin(k+2). -/
abbrev first (k : ℕ) : Fin (k+2) := 0

/-- The actual terminal position in Fin(k+2). -/
abbrev last (k : ℕ) : Fin (k+2) := Fin.last (k+1)

/-- Explicit finite-index proof interface; support only. -/
theorem second._proof_2 (k : ℕ) : 1 < k+2 := by omega

/-- The actual second position, with the source finite-index proof. -/
abbrev second (k : ℕ) : Fin (k+2) := ⟨1, second._proof_2 k⟩

/-- Explicit finite-index proof interface; support only. -/
theorem penultimate._proof_2 (k : ℕ) : k < k+2 := by omega

/-- The actual penultimate position, with the source finite-index proof. -/
abbrev penultimate (k : ℕ) : Fin (k+2) := ⟨k, penultimate._proof_2 k⟩

/-- The source left endpoint of one of k+1 transitions. -/
abbrev left {k : ℕ} (p : Fin (k+1)) : Fin (k+2) := p.castSucc

/-- The source right endpoint of one of k+1 transitions. -/
abbrev right {k : ℕ} (p : Fin (k+1)) : Fin (k+2) := p.succ

/-- Every source vehicle/position/node coordinate is zero or one. -/
def Binary {n v k} (x : Array n v k) : Prop :=
  ∀ a p i, x a p i = 0 ∨ x a p i = 1

/-- Every customer is used once over all vehicles and positions. -/
def CustomerOnce {n v k} (x : Array n v k) : Prop :=
  ∀ i : Fin n, ∑ a, ∑ p, x a p (some i) = 1

/-- Every vehicle position has total node mass one. -/
def PositionOnce {n v k} (x : Array n v k) : Prop :=
  ∀ a p, ∑ i, x a p i = 1

/-- Every disallowed node-pair transition product is zero. -/
def AllowedProducts {n v k} (D : Data n) (x : Array n v k) : Prop :=
  ∀ a p i j, D.allowed i j = false → x a (left p) i * x a (right p) j = 0

/-- After positive-index depot return no subsequent customer transition is permitted. -/
def AbsorbingProducts {n v k} (x : Array n v k) : Prop :=
  ∀ a (p : Fin (k+1)) (j : Fin n), 0 < p.val →
    x a (left p) none * x a (right p) (some j) = 0

/-- All six literal start/end and impossible departure/return fixed-row groups. -/
structure FixedRows {n v k} (D : Data n) (x : Array n v k) : Prop where
  start_depot : ∀ a, x a (first k) none = 1
  end_depot : ∀ a, x a (last k) none = 1
  start_customer : ∀ a i, x a (first k) (some i) = 0
  end_customer : ∀ a i, x a (last k) (some i) = 0
  impossible_departure : ∀ a j, D.allowed none j = false → x a (second k) j = 0
  impossible_return : ∀ a j, D.allowed j none = false → x a (penultimate k) j = 0

/-- All actual binary, coverage, one-hot, allowed, absorbing and fixed rows of the source sequence formulation. -/
structure Literal {n v k} (D : Data n) (x : Array n v k) : Prop where
  binary : Binary x
  customer_once : CustomerOnce x
  position_once : PositionOnce x
  allowed : AllowedProducts D x
  absorbing : AbsorbingProducts x
  fixed : FixedRows D x

/-- The actual repeated bilinear cost sum over vehicles and k+1 allowed transitions. -/
def objective {n v k} (D : Data n) (x : Array n v k) : ℝ :=
  ∑ a, ∑ p : Fin (k+1), ∑ i, ∑ j,
    if D.allowed i j then D.cost i j * x a (left p) i * x a (right p) j else 0

end Chapter10.Sequence

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Flattened actual vehicle/position/node source coordinates. -/
abbrev Coord (n v k : ℕ) := Fin v × Fin (k+2) × Node n

/-- Every actual vehicle/transition/ordered-node-pair index. -/
abbrev Transition (n v k : ℕ) := Fin v × Fin (k+1) × Node n × Node n

/-- Every actual vehicle/transition/customer absorption-row index. -/
abbrev Absorption (n v k : ℕ) := Fin v × Fin (k+1) × Fin n

/-- Flatten the actual source array without deleting coordinates. -/
def flatten {n v k} (x : Sequence.Array n v k) : Coord n v k → ℝ := fun r => x r.1 r.2.1 r.2.2

/-- Inflate every flattened coordinate to the actual source array. -/
def inflate {n v k} (z : Coord n v k → ℝ) : Sequence.Array n v k := fun a p i => z (a,p,i)

/-- Squared deviations from actual customer-once sums. -/
def customerPenalty {n v k} (x : Sequence.Array n v k) : ℝ :=
  ∑ i : Fin n, ((∑ a, ∑ p, x a p (some i)) - 1)^2

/-- Squared deviation from one actual vehicle/position node sum. -/
def positionTerm {n v k} (x : Sequence.Array n v k) (r : Fin v × Fin (k+2)) : ℝ :=
  ((∑ i, x r.1 r.2 i) - 1)^2

/-- Sum of all actual position one-hot penalties. -/
def positionPenalty {n v k} (x : Sequence.Array n v k) : ℝ := ∑ r, positionTerm x r

/-- The actual disallowed node-pair transition product, or zero for an allowed pair. -/
def forbiddenTerm {n v k} (D : Data n) (x : Sequence.Array n v k) (r : Transition n v k) : ℝ :=
  if D.allowed r.2.2.1 r.2.2.2 then 0 else
    x r.1 (Sequence.left r.2.1) r.2.2.1 * x r.1 (Sequence.right r.2.1) r.2.2.2

/-- Sum of every forbidden-transition penalty term. -/
def forbiddenPenalty {n v k} (D : Data n) (x : Sequence.Array n v k) : ℝ := ∑ r, forbiddenTerm D x r

/-- The actual positive-index depot-to-customer product, or zero at the initial transition. -/
def absorbingTerm {n v k} (x : Sequence.Array n v k) (r : Absorption n v k) : ℝ :=
  if 0 < r.2.1.val then x r.1 (Sequence.left r.2.1) none * x r.1 (Sequence.right r.2.1) (some r.2.2) else 0

/-- Sum of every actual absorbing-row product penalty. -/
def absorbingPenalty {n v k} (x : Sequence.Array n v k) : ℝ := ∑ r, absorbingTerm x r

/-- The complete customer, position, forbidden and absorbing penalty sum. -/
def penalty {n v k} (D : Data n) (x : Sequence.Array n v k) : ℝ :=
  customerPenalty x + positionPenalty x + forbiddenPenalty D x + absorbingPenalty x

/-- The non-fixed customer, position, allowed and absorbing rows. -/
def Rows {n v k} (D : Data n) (x : Sequence.Array n v k) : Prop :=
  Sequence.CustomerOnce x ∧ Sequence.PositionOnce x ∧ Sequence.AllowedProducts D x ∧ Sequence.AbsorbingProducts x

/-- The binary source arrays retaining all source fixed rows. -/
def domain {n v k} (D : Data n) : Set (Sequence.Array n v k) :=
  {x | Sequence.Binary x ∧ Sequence.FixedRows D x}

/-- The actual source sequence cost plus the complete weighted penalty. -/
def energy {n v k} (D : Data n) (ρ : ℝ) (x : Sequence.Array n v k) : ℝ :=
  Sequence.objective D x + ρ * penalty D x

/-- The actual allowed source cost for every repeated transition coordinate. -/
def coefficient {n v k} (D : Data n) (r : Transition n v k) : ℝ :=
  if D.allowed r.2.2.1 r.2.2.2 then D.cost r.2.2.1 r.2.2.2 else 0

/-- The sum of absolute costs of all allowed ordered node pairs. -/
def arcAbsCost {n} (D : Data n) : ℝ :=
  ∑ i, ∑ j, if D.allowed i j then |D.cost i j| else 0

/-- The larger printed P*v times absolute allowed-pair cost bound, with P=k+2. -/
def printedBound {n} (D : Data n) (v k : ℕ) : ℝ := (k+2 : ℕ) * (v : ℝ) * arcAbsCost D

/-- Actual customer and vehicle/position one-hot row indices. -/
abbrev OneHotRow (n v k : ℕ) := Fin n ⊕ (Fin v × Fin (k+2))

/-- The literal real matrix for customer-once and position-once sums. -/
def rowMatrix {n v k} : OneHotRow n v k → Coord n v k → ℝ
  | .inl c, r => if r.2.2 = some c then 1 else 0
  | .inr ap, r => if r.1 = ap.1 then if r.2.1 = ap.2 then 1 else 0 else 0

/-- The actual left source coordinate of a transition monomial. -/
def transitionLeft {n v k} (r : Transition n v k) : Coord n v k := (r.1, Sequence.left r.2.1, r.2.2.1)

/-- The actual right source coordinate of a transition monomial. -/
def transitionRight {n v k} (r : Transition n v k) : Coord n v k := (r.1, Sequence.right r.2.1, r.2.2.2)

/-- The actual depot left coordinate of an absorption monomial. -/
def absorptionLeft {n v k} (r : Absorption n v k) : Coord n v k := (r.1, Sequence.left r.2.1, none)

/-- The actual customer right coordinate of an absorption monomial. -/
def absorptionRight {n v k} (r : Absorption n v k) : Coord n v k := (r.1, Sequence.right r.2.1, some r.2.2)

/-- All actual ordered objective monomials accumulated with repeated coefficients. -/
def objectiveMatrix {n v k} (D : Data n) : Coord n v k → Coord n v k → ℝ :=
  productMatrix (coefficient D) transitionLeft transitionRight

/-- All actual ordered forbidden-transition monomials. -/
def forbiddenMatrix {n v k} (D : Data n) : Coord n v k → Coord n v k → ℝ :=
  productMatrix (fun r : Transition n v k => if D.allowed r.2.2.1 r.2.2.2 then 0 else 1) transitionLeft transitionRight

/-- All actual ordered positive-index absorption monomials. -/
def absorbingMatrix (n v k : ℕ) : Coord n v k → Coord n v k → ℝ :=
  productMatrix (fun r : Absorption n v k => if 0 < r.2.1.val then 1 else 0) absorptionLeft absorptionRight

/-- The full actual one-hot QUBO matrix plus objective, forbidden and absorbing matrices. -/
def matrix {n v k} (D : Data n) (ρ : ℝ) : Coord n v k → Coord n v k → ℝ :=
  fun i j => quboMatrix rowMatrix (fun _ : OneHotRow n v k => 1) (fun _ => 0) ρ i j +
    objectiveMatrix D i j + ρ * forbiddenMatrix D i j + ρ * absorbingMatrix n v k i j

/-- Exactly the initial/terminal depot-one source coordinates. -/
def fixedOne {n v k} (r : Coord n v k) : Prop :=
  (r.2.1 = Sequence.first k ∨ r.2.1 = Sequence.last k) ∧ r.2.2 = none

/-- Exactly the customer endpoint and impossible departure/return zero prescriptions. -/
def fixedZero {n v k} (D : Data n) (r : Coord n v k) : Prop :=
  ((r.2.1 = Sequence.first k ∨ r.2.1 = Sequence.last k) ∧ r.2.2 ≠ none) ∨
  (r.2.1 = Sequence.second k ∧ D.allowed none r.2.2 = false) ∨
  (r.2.1 = Sequence.penultimate k ∧ D.allowed r.2.2 none = false)

/-- The actual union of source fixed-one and fixed-zero prescriptions. -/
def fixedCondition {n v k} (D : Data n) (r : Coord n v k) : Prop := fixedOne r ∨ fixedZero D r

/-- Actual source coordinates outside the fixed prescriptions. -/
abbrev Free (n v k : ℕ) (D : Data n) := {r : Coord n v k // ¬ fixedCondition D r}

/-- Actual source coordinates covered by the fixed prescriptions. -/
abbrev Fixed (n v k : ℕ) (D : Data n) := {r : Coord n v k // fixedCondition D r}

/-- The source finite-type instance on actual free coordinates. -/
noncomputable def freeFintype {n v k} (D : Data n) : Fintype (Free n v k D) := Fintype.ofFinite _

/-- The source finite-type instance on actual fixed coordinates. -/
noncomputable def fixedFintype {n v k} (D : Data n) : Fintype (Fixed n v k D) := Fintype.ofFinite _

attribute [instance] freeFintype fixedFintype

/-- The complete source equivalence between the free/fixed disjoint sum and actual coordinates; both inverse proofs are retained. -/
def splitCoordinates {n v k} (D : Data n) : Free n v k D ⊕ Fixed n v k D ≃ Coord n v k := by
  classical
  exact {
    toFun := Sum.elim Subtype.val Subtype.val
    invFun := fun r => if h : fixedCondition D r then .inr ⟨r,h⟩ else .inl ⟨r,h⟩
    left_inv := by
      intro r
      cases r with
      | inl u => simp [u.property]
      | inr f => simp [f.property]
    right_inv := by intro r; dsimp; split_ifs <;> rfl }

/-- The source assignment one at fixed-one coordinates, zero otherwise. -/
def fixedValues {n v k} (D : Data n) (f : Fixed n v k D) : ℝ := by
  classical
  exact if fixedOne f.val then 1 else 0

/-- The actual flattened source array transported by its actual partition equivalence. -/
def splitArray {n v k} (D : Data n) (x : Sequence.Array n v k) : Free n v k D ⊕ Fixed n v k D → ℝ :=
  fun r => flatten x (splitCoordinates D r)

/-- The actual source extension of free values using source fixed values and the inverse partition map. -/
def sourceExtend {n v k} (D : Data n) (z : Free n v k D → ℝ) : Sequence.Array n v k :=
  inflate (fun r => extend (fixedValues D) z ((splitCoordinates D).symm r))

/-- The actual source energy matrix reindexed by the free/fixed coordinate equivalence. -/
def splitMatrix {n v k} (D : Data n) (ρ : ℝ) :
    (Free n v k D ⊕ Fixed n v k D) → (Free n v k D ⊕ Fixed n v k D) → ℝ :=
  fun i j => matrix D ρ (splitCoordinates D i) (splitCoordinates D j)

/-- The actual reindexed free matrix after consistent fixed-coordinate substitution. -/
def reducedMatrix {n v k : ℕ} (D : Data n) (ρ : ℝ) : Free n v k D → Free n v k D → ℝ :=
  fixedMatrix (splitMatrix (v := v) (k := k) D ρ) (fixedValues D)

/-- The complete reindexed fixed-coordinate offset, including the original one-hot constant. -/
def reducedOffset {n v k : ℕ} (D : Data n) (ρ : ℝ) : ℝ :=
  fixedOffset (splitMatrix (v := v) (k := k) D ρ) (fixedValues D)
    (ρ * ((n : ℝ) + (v : ℝ) * (k+2 : ℕ)))

/-- The actual reduced quadratic energy with its complete fixed offset. -/
def reducedEnergy {n v k} (D : Data n) (ρ : ℝ) (z : Free n v k D → ℝ) : ℝ :=
  quadratic (reducedMatrix D ρ) z + reducedOffset (v := v) (k := k) D ρ

end Chapter10.SequencePenalty

namespace Chapter10

/-- Exact source interface: incidence companion; its original full signature is retained. -/
theorem palomar_source_route_penalty_proposition {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ) (x : Bits n) :
    (energyMin A c ρ x ∧ ∃ y, feasible A y) ↔ routeMin A c x := by
  sorry

end Chapter10

namespace Chapter10.Algebra

/-- Exact source interface: unit-gap support; its original full signature is retained. -/
theorem palomar_integer_penalty_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x) :
    integerPenalty A b x = 0 ↔ integerFeasible A b x := by
  sorry

end Chapter10.Algebra

namespace Chapter10.Algebra

/-- Exact source interface: unit-gap support; its original full signature is retained. -/
theorem palomar_integer_penalty_gap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x)
    (hf : ¬ integerFeasible A b x) : 1 ≤ integerPenalty A b x := by
  sorry

end Chapter10.Algebra

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc matrix bridge; its original full signature is retained. -/
theorem palomar_matrix_iff_literal {n k} (D : Data n) (T : Grid k) (x : Assignment n k) :
    MatrixFeasible D T x ↔ Literal D T x := by
  sorry

end Chapter10.Routing.Arc

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc penalty; its original full signature is retained. -/
theorem palomar_arc_penalty_zero_iff (D : Data n) (T : Grid k) (x : Assignment n k) :
    arcPenalty D T x = 0 ↔ Feasible D T x := by
  sorry

end Chapter10.Routing.Arc

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc minimizers; its original full signature is retained. -/
theorem palomar_arc_minimizers_exact (D : Data n) (T : Grid k) (domain : Set (Assignment n k))
    (ρ : ℝ) (hρ : (∑ e : Edge n k, |coordinateCost D e|) < ρ) (x : Assignment n k) :
    (IsMinOn domain (arcEnergy D T ρ) x ∧ ∃ y ∈ domain, Feasible D T y) ↔
      IsMinOn {y | y ∈ domain ∧ Feasible D T y} (objective D) x := by
  sorry

end Chapter10.Routing.Arc

namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

/-- Exact source interface: literal arc matrix energy; its original full signature is retained. -/
theorem palomar_actual_arc_qubo_identity (D : Data n) (T : Grid k) (ρ : ℝ) (x : Assignment n k) :
    arcEnergy D T ρ x = quadratic (arcQUBO D T ρ) (fun e => Chapter10.bit (x e)) + ρ * (n : ℝ) := by
  sorry

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
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence penalty; its original full signature is retained. -/
theorem palomar_penalty_zero_iff {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    penalty D x = 0 ↔ Rows D x := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: tight repeated-cost bound; its original full signature is retained. -/
theorem palomar_objective_range {n v k} (D : Data n) (x y : Sequence.Array n v k)
    (hx : Sequence.Binary x) (hy : Sequence.Binary y) :
    Sequence.objective D x - Sequence.objective D y ≤ (k+1 : ℕ) * (v : ℝ) * arcAbsCost D := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: printed repeated-cost bound; its original full signature is retained. -/
theorem palomar_objective_range_printed {n v k} (D : Data n) (x y : Sequence.Array n v k)
    (hx : Sequence.Binary x) (hy : Sequence.Binary y) :
    Sequence.objective D x - Sequence.objective D y ≤ printedBound D v k := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence minimizers; its original full signature is retained. -/
theorem palomar_minimizers_exact {n v k} (D : Data n) (ρ : ℝ)
    (hρ : printedBound D v k < ρ) (x : Sequence.Array n v k) :
    (IsMinOn (domain D) (energy D ρ) x ∧ ∃ y : Sequence.Array n v k, Sequence.Literal D y) ↔
      IsMinOn {y | Sequence.Literal D y} (Sequence.objective D) x := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: literal sequence matrix energy; its original full signature is retained. -/
theorem palomar_source_energy_matrix_identity {n v k} (D : Data n) (x : Sequence.Array n v k)
    (ρ : ℝ) (hx : Sequence.Binary x) :
    energy D ρ x = quadratic (matrix D ρ) (flatten x) +
      ρ * ((n : ℝ) + (v : ℝ) * (k+2 : ℕ)) := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source fixed partition; its original full signature is retained. -/
theorem palomar_domain_iff_split_fixed {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (x : Sequence.Array n v k) : x ∈ domain D ↔ splitArray D x ∈ fixedDomain (fixedValues D) := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source reduced energy; its original full signature is retained. -/
theorem palomar_source_fixed_energy_identity {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (z : Free n v k D → ℝ) (hz : Algebra.Binary z) :
    energy D ρ (sourceExtend D z) = reducedEnergy D ρ z := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source minimum transport; its original full signature is retained. -/
theorem palomar_source_fixed_min_transport {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (z : Free n v k D → ℝ) :
    IsMinOn (domain D) (energy D ρ) (sourceExtend D z) ↔
      IsMinOn {z | Algebra.Binary z} (reducedEnergy D ρ) z := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual source reduced exactness; its original full signature is retained. -/
theorem palomar_reduced_minimizers_exact {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (hρ : printedBound D v k < ρ) (z : Free n v k D → ℝ) :
    (IsMinOn {z | Algebra.Binary z} (reducedEnergy D ρ) z ∧
      ∃ w : Free n v k D → ℝ, Algebra.Binary w ∧ Sequence.Literal D (sourceExtend D w)) ↔
      IsMinOn {x | Sequence.Literal D x} (Sequence.objective D) (sourceExtend D z) := by
  sorry

end Chapter10.SequencePenalty

namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

/-- Exact source interface: actual finite source attainment; its original full signature is retained. -/
theorem palomar_source_energy_attainment {n v k : ℕ} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) : ∃ x : Sequence.Array n v k, IsMinOn (domain D) (energy D ρ) x := by
  sorry

end Chapter10.SequencePenalty


namespace Chapter10.Algebra

theorem palomar_full_qubo_identity {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c x : ι → ℝ) (ρ : ℝ) (hx : Binary x) :
    linearCost c x + ρ * squaredResidual A b x =
      quadratic (quboMatrix A b c ρ) x + ρ * ∑ r, (b r)^2 := by
  sorry

theorem palomar_integer_penalty_minimizers_exact {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (c : ι → ℝ) (D : Set (ι → ℝ))
    (hD : ∀ x ∈ D, Binary x) (ρ : ℝ) (hρ : (∑ i, |c i|) < ρ) (x : ι → ℝ) :
    (IsMinOn D (penalized (linearCost c) (integerPenalty A b) ρ) x ∧
      ∃ y ∈ D, integerFeasible A b y) ↔
      IsMinOn {y | y ∈ D ∧ integerFeasible A b y} (linearCost c) x := by
  sorry

theorem palomar_fixed_qubo_identity {U F : Type*} [Fintype U] [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (z : U → ℝ) (κ : ℝ) (hz : Binary z) :
    quadratic M (extend a z) + κ = quadratic (fixedMatrix M a) z + fixedOffset M a κ := by
  sorry

theorem palomar_fixed_qubo_min_transport {U F : Type*} [Fintype U] [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (ha : Binary a) (z : U → ℝ) (κ : ℝ) :
    IsMinOn (fixedDomain a) (fun x => quadratic M x + κ) (extend a z) ↔
      IsMinOn {z | Binary z} (fun z => quadratic (fixedMatrix M a) z + fixedOffset M a κ) z := by
  sorry

end Chapter10.Algebra
