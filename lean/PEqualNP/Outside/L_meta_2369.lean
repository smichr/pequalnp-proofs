import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.NestedCoverCircuit

-- L-meta-2369: a nine-gate lower bound
--
-- The target is the monotone Boolean function given by the edges
-- (0,7), (1,7), (2,5), (2,6), (2,7), (3,4), (3,6), (3,7).
-- It is computed as the OR of the ANDs of the two endpoint inputs.
-- We prove that any read-back AND/OR circuit of fan-in at most two
-- computing this function has at least nine gates.
--
-- Proof strategy:
-- 1. Work only with the ancestors of the output (the active circuit).
--    Every essential input is active. Count operand occurrences,
--    including multiple reads of the same wire by one gate. If A is
--    the number of active gates, n the number of inputs
--    (here all inputs are essential), and S the sum of excess active
--    fanouts, then n + S <= A + 1.
-- 2. A hypothetical circuit with at most eight gates has S <= 1.
--    If there is a shared vertex q, it is unique. Every dependency
--    from an ancestor of q to the active circuit outside that ancestry
--    must leave through q itself. Thus the input ancestors D of q
--    induce at most two distinct cofactors of the target function.
-- 3. A finite, kernel-checked certificate excludes all D except the
--    empty set, singletons, {0,1}, and the full input set. Independently,
--    three induced four-vertex paths provide sensitivity witnesses.
-- 4. A read-once monotone formula cannot be sensitive to the same two
--    distinct variables at two assignments with different outputs.
--    Unfolding an active wire into a formula preserves its value and
--    controls variable occurrences using fanout among strict ancestors.
-- 5. With no shared vertex the output has a read-once formula. With a
--    proper group D, fixing D to zero leaves a read-once formula and
--    at least one surviving sensitivity witness. With all inputs in D,
--    the formula for q is read-once and every distinction made by the
--    circuit output must already be made by q. All cases contradict 4.
--
-- The general structural and formula lemmas are separated by section
-- comments from the graph-specific certificates and final assembly.
-- The certificate tables are data, checked with `decide`; no trust in
-- an external certificate generator or enumeration of circuits is needed.
-- The final declaration uses the project's original conjecture statement.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2369

-- 1. Circuit ancestry and evaluation
--
-- Wire numbers below n denote inputs; subsequent numbers denote gate
-- outputs. Ancestry is reflexive. The read-back condition gives a strict
-- decrease in wire number when following an operand backwards.

-- The immediate predecessors of a wire.
def predecessors (n : Nat) (C : Circuit) (w : Nat) : List Nat :=
  if w < n then []
  else
    match C.gates[w - n]? with
    | none => []
    | some g => g.inputs

theorem input_predecessors (n : Nat) (C : Circuit)
    (w : Nat) (h : w < n) :
    predecessors n C w = [] := by
  simp [predecessors, h]

def readsBack (n : Nat) (C : Circuit) : Prop :=
  ∀ w i, i ∈ predecessors n C w → i < w

-- A wire is an ancestor of itself or of a wire
-- that depends on it.
inductive Ancestor (n : Nat) (C : Circuit) :
    Nat → Nat → Prop where
  | self (w : Nat) : Ancestor n C w w
  | step {a i w : Nat}
      (ha : Ancestor n C a i)
      (hi : i ∈ predecessors n C w) :
      Ancestor n C a w

theorem ancestor_le (n : Nat) (C : Circuit)
    (h : readsBack n C)
    {a w : Nat} (ha : Ancestor n C a w) :
    a ≤ w := by
  induction ha with
  | self => exact Nat.le_refl _
  | step ha hi ih =>
    have hp := h _ _ hi
    omega

theorem ancestor_trans (n : Nat) (C : Circuit)
    {a b c : Nat}
    (hab : Ancestor n C a b)
    (hbc : Ancestor n C b c) :
    Ancestor n C a c := by
  induction hbc with
  | self => exact hab
  | step ha hi ih =>
    exact Ancestor.step ih hi

theorem predecessor_ancestor (n : Nat) (C : Circuit)
    {i w : Nat}
    (hi : i ∈ predecessors n C w) :
    Ancestor n C i w :=
  Ancestor.step (Ancestor.self i) hi

-- Two assignments agree on the input ancestors of w.
def AncestorAgree (n : Nat) (C : Circuit)
    (w : Nat) (x y : Fin n → Bool) : Prop :=
  ∀ i : Fin n, Ancestor n C i.val w → x i = y i

-- Agreement propagates backward through the circuit.
theorem agree_predecessor (n : Nat) (C : Circuit)
    {i w : Nat} {x y : Fin n → Bool}
    (h : AncestorAgree n C w x y)
    (hi : i ∈ predecessors n C w) :
    AncestorAgree n C i x y := by
  intro a ha
  exact h a (Ancestor.step ha hi)

-- Agreement at an input implies equality of its value.
theorem agree_input (n : Nat) (C : Circuit)
    (i : Fin n) {x y : Fin n → Bool}
    (h : AncestorAgree n C i.val x y) :
    x i = y i :=
  h i (Ancestor.self i.val)

-- The following list lemmas connect the project's sequential evaluation
-- of gates to local wire equations. The read-back condition ensures that
-- later gates cannot change the values used by an earlier gate.

-- Evaluate a single gate and append its output.
def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem appendGate_length (w : List Bool) (g : Gate) :
    (appendGate w g).length = w.length + 1 := by
  simp [appendGate]

theorem foldGates_length (w : List Bool) (gs : List Gate) :
    (gs.foldl appendGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, appendGate_length]
    omega

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact foldGates_length x C.gates

theorem append_getD_preserves (a b : List Bool)
    (i : Nat) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  induction a generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [List.cons_append, List.getD_cons_succ]
      apply ih
      omega

theorem appendGate_preserves (w : List Bool) (g : Gate)
    (i : Nat) (hi : i < w.length) :
    (appendGate w g).getD i false = w.getD i false := by
  unfold appendGate
  exact append_getD_preserves _ _ i hi

theorem foldGates_preserves (w : List Bool)
    (gs : List Gate) (i : Nat) (hi : i < w.length) :
    (gs.foldl appendGate w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    · exact appendGate_preserves w g i hi
    · rw [appendGate_length]
      omega

theorem append_getD_new (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    exact ih

theorem appendGate_new (w : List Bool) (g : Gate) :
    (appendGate w g).getD w.length false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold appendGate
  exact append_getD_new _ _

theorem wires_input (C : Circuit) (x : List Bool)
    (i : Nat) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldGates_preserves x C.gates i hi

theorem foldGates_append (w : List Bool)
    (as bs : List Gate) :
    ((as ++ bs).foldl appendGate w) =
      bs.foldl appendGate (as.foldl appendGate w) := by
  exact List.foldl_append

theorem foldGates_gate (w : List Bool)
    (as bs : List Gate) (g : Gate) :
    ((as ++ g :: bs).foldl appendGate w).getD
        (w.length + as.length) false =
      g.op.eval (g.inputs.map fun i =>
        (as.foldl appendGate w).getD i false) := by
  rw [foldGates_append]
  simp only [List.foldl_cons]
  have hl := foldGates_length w as
  rw [← hl]
  rw [foldGates_preserves]
  · exact appendGate_new _ _
  · rw [appendGate_length]
    omega

theorem foldGates_gate_final (w : List Bool)
    (as bs : List Gate) (g : Gate)
    (h : ∀ i ∈ g.inputs, i < w.length + as.length) :
    ((as ++ g :: bs).foldl appendGate w).getD
        (w.length + as.length) false =
      g.op.eval (g.inputs.map fun i =>
        ((as ++ g :: bs).foldl appendGate w).getD i false) := by
  rw [foldGates_gate]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [foldGates_append]
  symm
  apply foldGates_preserves
  rw [foldGates_length]
  exact h i hi

theorem gate_list_split (gs : List Gate)
    (j : Nat) (g : Gate)
    (h : gs[j]? = some g) :
    ∃ pre post : List Gate,
      gs = pre ++ g :: post ∧ pre.length = j := by
  induction gs generalizing j with
  | nil => simp at h
  | cons a as ih =>
    cases j with
    | zero =>
      simp at h
      subst g
      exact ⟨[], as, rfl, rfl⟩
    | succ j =>
      have hj : as[j]? = some g := by
        simpa using h
      obtain ⟨pre, post, hp, hl⟩ := ih j hj
      exact ⟨a :: pre, post,
        by rw [hp]; rfl,
        by simp [hl]⟩

theorem wires_gate (C : Circuit) (x : List Bool)
    (j : Nat) (g : Gate)
    (hg : C.gates[j]? = some g)
    (hb : ∀ i ∈ g.inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        (C.wires x).getD i false) := by
  obtain ⟨pre, post, hp, hl⟩ :=
    gate_list_split C.gates j g hg
  unfold Circuit.wires
  rw [hp, ← hl]
  exact foldGates_gate_final x pre post g (by
    simpa [hl] using hb)

def wireValue (n : Nat) (C : Circuit)
    (x : Fin n → Bool) (w : Nat) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem wireValue_input (n : Nat) (C : Circuit)
    (x : Fin n → Bool) (i : Fin n) :
    wireValue n C x i.val = x i := by
  unfold wireValue
  rw [wires_input]
  · simp
  · simp

theorem wireValue_gate (n : Nat) (C : Circuit)
    (x : Fin n → Bool) (j : Nat) (g : Gate)
    (hg : C.gates[j]? = some g)
    (hb : readsBack n C) :
    wireValue n C x (n + j) =
      g.op.eval (g.inputs.map (wireValue n C x)) := by
  have hp : predecessors n C (n + j) = g.inputs := by
    unfold predecessors
    have hn : ¬ n + j < n := by omega
    simp [hn, hg]
  have hlt : ∀ i ∈ g.inputs, i < n + j := by
    intro i hi
    apply hb (n + j) i
    rw [hp]
    exact hi
  unfold wireValue
  have he := wires_gate C (List.ofFn x) j g hg (by
    simpa using hlt)
  simpa using he

theorem wireValue_agree (n : Nat) (C : Circuit)
    (hb : readsBack n C)
    (x y : Fin n → Bool)
    (w : Nat)
    (h : AncestorAgree n C w x y) :
    wireValue n C x w = wireValue n C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let i : Fin n := ⟨w, hw⟩
      change wireValue n C x i.val =
        wireValue n C y i.val
      rw [wireValue_input, wireValue_input]
      exact agree_input n C i h
    · have he : w = n + (w - n) := by omega
      cases hg : C.gates[w - n]? with
      | none =>
        have hl : C.gates.length ≤ w - n := by
          simpa using hg
        have hx : (C.wires (List.ofFn x)).length ≤ w := by
          rw [wires_length]
          simp [Circuit.size]
          omega
        have hy : (C.wires (List.ofFn y)).length ≤ w := by
          rw [wires_length]
          simp [Circuit.size]
          omega
        unfold wireValue
        simp [List.getD, List.getElem?_eq_none hx,
          List.getElem?_eq_none hy]
      | some g =>
        have hp : predecessors n C w = g.inputs := by
          simp [predecessors, hw, hg]
        have ev (z : Fin n → Bool) :
            wireValue n C z w =
              g.op.eval (g.inputs.map (wireValue n C z)) := by
          conv_lhs => rw [he]
          exact wireValue_gate n C z (w - n) g hg hb
        rw [ev x, ev y]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hip : i ∈ predecessors n C w := by
          rw [hp]
          exact hi
        exact ih i (hb w i hip)
          (agree_predecessor n C h hip)

-- An input is essential if changing only that input can change the output.

def Essential (n : Nat) (C : Circuit) (i : Fin n) : Prop :=
  ∃ x y : Fin n → Bool,
    (∀ j : Fin n, j ≠ i → x j = y j) ∧
    C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)

theorem essential_ancestor (n : Nat) (C : Circuit)
    (hb : readsBack n C) (i : Fin n)
    (he : Essential n C i) :
    Ancestor n C i.val C.output := by
  classical
  by_contra hn
  obtain ⟨x, y, hagree, hne⟩ := he
  apply hne
  change wireValue n C x C.output =
    wireValue n C y C.output
  apply wireValue_agree n C hb x y C.output
  intro j hj
  apply hagree j
  intro hji
  subst j
  exact hn hj

-- 2. Active circuit and sharing budget
--
-- Ignore gates not contributing to the output. Active fanout counts operand
-- positions, not merely distinct successor gates. This matters when a gate
-- reads the same wire twice.

def Active (n : Nat) (C : Circuit) (w : Nat) : Prop :=
  Ancestor n C w C.output

theorem ancestor_successor (n : Nat) (C : Circuit)
    {a w : Nat}
    (ha : Ancestor n C a w)
    (hne : a ≠ w) :
    ∃ v, a ∈ predecessors n C v ∧
      Ancestor n C v w := by
  induction ha with
  | self => exact False.elim (hne rfl)
  | @step i w ha hi ih =>
    by_cases he : a = i
    · subst i
      exact ⟨w, hi, Ancestor.self w⟩
    · obtain ⟨v, hv, hv'⟩ := ih he
      exact ⟨v, hv, Ancestor.step hv' hi⟩

theorem active_successor (n : Nat) (C : Circuit)
    (w : Nat)
    (ha : Active n C w)
    (hne : w ≠ C.output) :
    ∃ v, Active n C v ∧
      w ∈ predecessors n C v := by
  obtain ⟨v, hv, hv'⟩ :=
    ancestor_successor n C ha hne
  exact ⟨v, hv', hv⟩

-- All vertices contributing to the circuit output.
noncomputable def activeVertices (n : Nat) (C : Circuit) :
    Finset Nat := by
  classical
  exact (Finset.range (C.output + 1)).filter (Active n C)

theorem mem_activeVertices (n : Nat) (C : Circuit)
    (hb : readsBack n C) (w : Nat) :
    w ∈ activeVertices n C ↔ Active n C w := by
  classical
  simp only [activeVertices, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hl := ancestor_le n C hb h
    exact ⟨by omega, h⟩

-- Count operand occurrences among active vertices.
noncomputable def activeFanout (n : Nat) (C : Circuit)
    (w : Nat) : Nat :=
  (activeVertices n C).sum
    (fun v => (predecessors n C v).count w)

theorem output_active (n : Nat) (C : Circuit)
    (hb : readsBack n C) :
    C.output ∈ activeVertices n C := by
  apply (mem_activeVertices n C hb C.output).mpr
  exact Ancestor.self _

theorem activeFanout_pos (n : Nat) (C : Circuit)
    (hb : readsBack n C) (w : Nat)
    (ha : Active n C w)
    (hne : w ≠ C.output) :
    1 ≤ activeFanout n C w := by
  classical
  obtain ⟨v, hv, hw⟩ := active_successor n C w ha hne
  have hm := (mem_activeVertices n C hb v).mpr hv
  have hc : 0 < (predecessors n C v).count w :=
    List.count_pos_iff.mpr hw
  have hs :
      (predecessors n C v).count w ≤
        activeFanout n C w := by
    unfold activeFanout
    exact Finset.single_le_sum (f := fun v => (predecessors n C v).count w)
      (fun i _ => Nat.zero_le _) hm
  omega

theorem activeFanout_output (n : Nat) (C : Circuit)
    (hb : readsBack n C) :
    activeFanout n C C.output = 0 := by
  classical
  unfold activeFanout
  apply Finset.sum_eq_zero
  intro v hv
  have ha := (mem_activeVertices n C hb v).mp hv
  have hl := ancestor_le n C hb ha
  apply List.count_eq_zero.mpr
  intro hm
  have hp := hb v C.output hm
  omega

theorem active_predecessor (n : Nat) (C : Circuit)
    {i v : Nat}
    (hv : Active n C v)
    (hi : i ∈ predecessors n C v) :
    Active n C i :=
  ancestor_trans n C
    (predecessor_ancestor n C hi) hv

noncomputable def activeWireCount (n : Nat)
    (C : Circuit) : Nat :=
  (activeVertices n C).sum
    (fun v => (predecessors n C v).length)

theorem activeFanout_sum_swap (n : Nat) (C : Circuit) :
    (activeVertices n C).sum (activeFanout n C) =
    (activeVertices n C).sum
      (fun v => (activeVertices n C).sum
        (fun w => (predecessors n C v).count w)) := by
  unfold activeFanout
  rw [Finset.sum_comm]

theorem sum_counts_eq_length (S : Finset Nat)
    (xs : List Nat)
    (h : ∀ x ∈ xs, x ∈ S) :
    S.sum (fun x => xs.count x) = xs.length := by
  classical
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha : a ∈ S := h a List.mem_cons_self
    have hs := ih (fun x hx =>
      h x (List.mem_cons_of_mem a hx))
    have he : ∀ x : Nat,
        (a :: as).count x =
          as.count x + (if x = a then 1 else 0) := by
      intro x
      by_cases hx : x = a
      · subst x
        simp
      · simp [hx, Ne.symm hx]
    simp only [he, Finset.sum_add_distrib,
      List.length_cons]
    rw [hs]
    simp [ha]

theorem activeFanout_sum (n : Nat) (C : Circuit)
    (hb : readsBack n C) :
    (activeVertices n C).sum (activeFanout n C) =
      activeWireCount n C := by
  classical
  rw [activeFanout_sum_swap]
  unfold activeWireCount
  apply Finset.sum_congr rfl
  intro v hv
  apply sum_counts_eq_length
  intro w hw
  apply (mem_activeVertices n C hb w).mpr
  exact active_predecessor n C
    ((mem_activeVertices n C hb v).mp hv) hw

-- Each active non-output vertex needs at least one outgoing operand use.
-- Fanout above one is the excess; the output contributes zero excess.

noncomputable def excessFanout (n : Nat) (C : Circuit)
    (w : Nat) : Nat :=
  activeFanout n C w - 1

noncomputable def sharingBudget (n : Nat)
    (C : Circuit) : Nat :=
  (activeVertices n C).sum (excessFanout n C)

theorem fanout_decompose (n : Nat) (C : Circuit)
    (hb : readsBack n C)
    (w : Nat) (hw : w ∈ activeVertices n C) :
    activeFanout n C w =
      excessFanout n C w +
        (if w = C.output then 0 else 1) := by
  unfold excessFanout
  by_cases he : w = C.output
  · subst w
    simp [activeFanout_output n C hb]
  · have hp := activeFanout_pos n C hb w
      ((mem_activeVertices n C hb w).mp hw) he
    simp only [he, ite_false]
    omega

--  The number of active operand occurrences plus one equals the number
-- of active vertices plus the total excess fanout. This is an exact
-- counting identity, independent of the gate operations.

theorem sharingBudget_exact (n : Nat) (C : Circuit)
    (hb : readsBack n C) :
    activeWireCount n C + 1 =
      (activeVertices n C).card + sharingBudget n C := by
  classical
  have he := activeFanout_sum n C hb
  have hs :
      (activeVertices n C).sum (activeFanout n C) =
      (activeVertices n C).sum
        (fun w => excessFanout n C w +
          (if w = C.output then 0 else 1)) := by
    apply Finset.sum_congr rfl
    intro w hw
    exact fanout_decompose n C hb w hw
  rw [Finset.sum_add_distrib] at hs
  have ho := output_active n C hb
  have hc :
      (activeVertices n C).sum
        (fun w => if w = C.output then 0 else 1) + 1 =
      (activeVertices n C).card := by
    rw [← Finset.sum_erase_add _ _ ho]
    have hh :
        (∑ x ∈ (activeVertices n C).erase C.output,
          if x = C.output then 0 else 1) =
        ((activeVertices n C).erase C.output).card := by
      calc
        _ = ∑ x ∈ (activeVertices n C).erase C.output, (1 : Nat) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [(Finset.mem_erase.mp hx).1]
        _ = _ := by simp
    simp only [ite_true, Nat.add_zero]
    rw [hh, Finset.card_erase_of_mem ho]
    have hp := Finset.card_pos.mpr ⟨C.output, ho⟩
    omega
  have hs' : activeWireCount n C =
      sharingBudget n C +
        (activeVertices n C).sum
          (fun w => if w = C.output then 0 else 1) := by
    rw [← he]
    exact hs
  omega

theorem predecessors_length_le (n : Nat)
    (C : Circuit)
    (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (w : Nat) :
    (predecessors n C w).length ≤
      (if w < n then 0 else 2) := by
  unfold predecessors
  split
  · simp
  · rename_i hn
    cases hg : C.gates[w - n]? with
    | none => simp
    | some g =>
      exact h g (List.mem_of_getElem? hg)

noncomputable def activeGates (n : Nat)
    (C : Circuit) : Finset Nat :=
  (activeVertices n C).filter (fun w => n ≤ w)

theorem activeWireCount_le (n : Nat)
    (C : Circuit)
    (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    activeWireCount n C ≤ 2 * (activeGates n C).card := by
  classical
  unfold activeWireCount activeGates
  calc
    _ ≤ (activeVertices n C).sum
        (fun w => if w < n then 0 else 2) := by
      apply Finset.sum_le_sum
      intro w hw
      exact predecessors_length_le n C h w
    _ = _ := by
      have he (w : Nat) :
          (if w < n then 0 else 2 : Nat) =
          (if n ≤ w then 2 else 0) := by
        by_cases hlt : w < n
        · have hge : ¬ n ≤ w := by omega
          simp [hlt, hge]
        · have hge : n ≤ w := by omega
          simp [hlt, hge]
      simp only [he]
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]

theorem activeVertices_card (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (he : ∀ i : Fin n, Essential n C i) :
    (activeVertices n C).card =
      n + (activeGates n C).card := by
  classical
  have hd : Disjoint (Finset.range n)
      (activeGates n C) := by
    apply Finset.disjoint_left.mpr
    intro w hi hg
    have hl := Finset.mem_range.mp hi
    have hge := (Finset.mem_filter.mp hg).2
    omega
  have hu : activeVertices n C =
      Finset.range n ∪ activeGates n C := by
    ext w
    simp only [Finset.mem_union, Finset.mem_range,
      activeGates, Finset.mem_filter]
    constructor
    · intro hw
      by_cases hl : w < n
      · exact Or.inl hl
      · exact Or.inr ⟨hw, by omega⟩
    · intro hw
      rcases hw with hl | hg
      · apply (mem_activeVertices n C hb w).mpr
        exact essential_ancestor n C hb
          ⟨w, hl⟩ (he ⟨w, hl⟩)
      · exact hg.1
  rw [hu, Finset.card_union_of_disjoint hd,
    Finset.card_range]

theorem sharingBudget_active_bound (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (he : ∀ i : Fin n, Essential n C i)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    n + sharingBudget n C ≤
      (activeGates n C).card + 1 := by
  have h1 := sharingBudget_exact n C hb
  have h2 := activeVertices_card n C hb he
  have h3 := activeWireCount_le n C hf
  omega

theorem activeGates_card_le (n : Nat)
    (C : Circuit)
    (hout : C.output < n + C.size) :
    (activeGates n C).card ≤ C.size := by
  classical
  have hs : activeGates n C ⊆
      Finset.Ico n (n + C.size) := by
    intro w hw
    have hf := Finset.mem_filter.mp hw
    have hl := (Finset.mem_filter.mp hf.1).1
    have hr := Finset.mem_range.mp hl
    apply Finset.mem_Ico.mpr
    exact ⟨hf.2, by omega⟩
  calc
    _ ≤ (Finset.Ico n (n + C.size)).card :=
      Finset.card_le_card hs
    _ = C.size := by simp

--  With all inputs essential and fan-in at most two, each unit of
-- sharing requires one gate beyond the baseline of n - 1 gates (in the
-- sense of the natural-number inequality below).

theorem sharingBudget_bound (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (he : ∀ i : Fin n, Essential n C i)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hout : C.output < n + C.size) :
    n + sharingBudget n C ≤ C.size + 1 := by
  have h1 := sharingBudget_active_bound n C hb he hf
  have h2 := activeGates_card_le n C hout
  omega

theorem excessFanout_le_budget (n : Nat)
    (C : Circuit) (w : Nat)
    (hw : w ∈ activeVertices n C) :
    excessFanout n C w ≤ sharingBudget n C := by
  classical
  unfold sharingBudget
  exact Finset.single_le_sum
    (f := excessFanout n C)
    (fun i _ => Nat.zero_le _) hw

theorem fanout_le_two (n : Nat)
    (C : Circuit)
    (hs : sharingBudget n C ≤ 1)
    (w : Nat) (hw : w ∈ activeVertices n C) :
    activeFanout n C w ≤ 2 := by
  have h := excessFanout_le_budget n C w hw
  unfold excessFanout at h
  omega

-- 3. The unique shared vertex and its bottleneck

theorem shared_unique (n : Nat)
    (C : Circuit)
    (hs : sharingBudget n C ≤ 1)
    (u v : Nat)
    (hu : u ∈ activeVertices n C)
    (hv : v ∈ activeVertices n C)
    (hfu : 2 ≤ activeFanout n C u)
    (hfv : 2 ≤ activeFanout n C v) :
    u = v := by
  classical
  by_contra hne
  have hsub : ({u, v} : Finset Nat) ⊆
      activeVertices n C := by
    intro w hw
    simp at hw
    rcases hw with h | h
    · simpa [h] using hu
    · simpa [h] using hv
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := excessFanout n C) hsub
    (fun i _ _ => Nat.zero_le _)
  simp [hne] at hsum
  change excessFanout n C u +
    excessFanout n C v ≤ sharingBudget n C at hsum
  unfold excessFanout at hsum
  omega

theorem two_successors_fanout (n : Nat)
    (C : Circuit) (w u v : Nat)
    (hu : u ∈ activeVertices n C)
    (hv : v ∈ activeVertices n C)
    (hne : u ≠ v)
    (hwu : w ∈ predecessors n C u)
    (hwv : w ∈ predecessors n C v) :
    2 ≤ activeFanout n C w := by
  classical
  have hsub : ({u, v} : Finset Nat) ⊆
      activeVertices n C := by
    intro a ha
    simp at ha
    rcases ha with h | h
    · simpa [h] using hu
    · simpa [h] using hv
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun a => (predecessors n C a).count w)
    hsub (fun i _ _ => Nat.zero_le _)
  simp [hne] at hs
  change (predecessors n C u).count w +
    (predecessors n C v).count w ≤
      activeFanout n C w at hs
  have h1 := List.count_pos_iff.mpr hwu
  have h2 := List.count_pos_iff.mpr hwv
  omega

theorem unshared_successor_unique (n : Nat)
    (C : Circuit) (w u v : Nat)
    (hf : activeFanout n C w ≤ 1)
    (hu : u ∈ activeVertices n C)
    (hv : v ∈ activeVertices n C)
    (hwu : w ∈ predecessors n C u)
    (hwv : w ∈ predecessors n C v) :
    u = v := by
  by_contra hne
  have h := two_successors_fanout n C w u v
    hu hv hne hwu hwv
  omega

--  If q is the unique shared active vertex, no strict ancestor of q
-- can feed an active successor outside the ancestry of q.

theorem shared_boundary (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (a v : Nat)
    (ha : Ancestor n C a q)
    (hv : Active n C v)
    (hav : a ∈ predecessors n C v)
    (hout : ¬ Ancestor n C v q) :
    a = q := by
  classical
  by_contra hne
  obtain ⟨u, hau, huq⟩ :=
    ancestor_successor n C ha hne
  have hu : Active n C u :=
    ancestor_trans n C huq hq
  have haa : Active n C a :=
    ancestor_trans n C ha hq
  have ham := (mem_activeVertices n C hb a).mpr haa
  have hqm := (mem_activeVertices n C hb q).mpr hq
  have hum := (mem_activeVertices n C hb u).mpr hu
  have hvm := (mem_activeVertices n C hb v).mpr hv
  have hf : activeFanout n C a ≤ 1 := by
    by_contra hn
    have hf' : 2 ≤ activeFanout n C a := by omega
    exact hne (shared_unique n C hs a q ham hqm hf' hfq)
  have huv := unshared_successor_unique n C
    a u v hf hum hvm hau hav
  exact hout (huv ▸ huq)

--  Outside the ancestry of q, active wire values are determined by
-- the inputs outside that ancestry together with the single bit at q.

theorem shared_value_agree (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n,
      ¬ Ancestor n C i.val q → x i = y i)
    (heq : wireValue n C x q = wireValue n C y q)
    (w : Nat)
    (hw : Active n C w)
    (hout : ¬ Ancestor n C w q) :
    wireValue n C x w = wireValue n C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let i : Fin n := ⟨w, hn⟩
      change wireValue n C x i.val =
        wireValue n C y i.val
      rw [wireValue_input, wireValue_input]
      exact hxy i hout
    · have he : w = n + (w - n) := by omega
      cases hg : C.gates[w - n]? with
      | none =>
        have hl : C.gates.length ≤ w - n := by
          simpa using hg
        have hx : (C.wires (List.ofFn x)).length ≤ w := by
          rw [wires_length]
          simp [Circuit.size]
          omega
        have hy : (C.wires (List.ofFn y)).length ≤ w := by
          rw [wires_length]
          simp [Circuit.size]
          omega
        unfold wireValue
        simp [List.getD, List.getElem?_eq_none hx,
          List.getElem?_eq_none hy]
      | some g =>
        have hp : predecessors n C w = g.inputs := by
          simp [predecessors, hn, hg]
        have ev (z : Fin n → Bool) :
            wireValue n C z w =
              g.op.eval (g.inputs.map (wireValue n C z)) := by
          conv_lhs => rw [he]
          exact wireValue_gate n C z (w - n) g hg hb
        rw [ev x, ev y]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hip : i ∈ predecessors n C w := by
          rw [hp]
          exact hi
        by_cases ha : Ancestor n C i q
        · have hiq := shared_boundary n C hb hs
            q hq hfq i w ha hw hip hout
          subst i
          exact heq
        · exact ih i (hb w i hip)
            (active_predecessor n C hw hip) ha

-- Take values from x inside D and from y outside D.
def spliceInputs (n : Nat) (D : Finset (Fin n))
    (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ D then x i else y i

theorem bool_three (a b c : Bool) :
    a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> decide

theorem output_not_ancestor_shared (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q) :
    ¬ Ancestor n C C.output q := by
  intro h
  have h1 := ancestor_le n C hb h
  have h2 := ancestor_le n C hb hq
  have he : q = C.output := by omega
  subst q
  have hz := activeFanout_output n C hb
  omega

theorem shared_cofactor_eq (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (D : Finset (Fin n))
    (hD : ∀ i : Fin n,
      i ∈ D ↔ Ancestor n C i.val q)
    (a b : Fin n → Bool)
    (he : wireValue n C a q = wireValue n C b q) :
    ∀ y : Fin n → Bool,
      C.eval (List.ofFn (spliceInputs n D a y)) =
      C.eval (List.ofFn (spliceInputs n D b y)) := by
  intro y
  have hval (x : Fin n → Bool) :
      wireValue n C (spliceInputs n D x y) q =
        wireValue n C x q := by
    apply wireValue_agree n C hb
    intro i hi
    simp [spliceInputs, (hD i).mpr hi]
  change wireValue n C (spliceInputs n D a y) C.output =
    wireValue n C (spliceInputs n D b y) C.output
  apply shared_value_agree n C hb hs q hq hfq
  · intro i hi
    have hn : i ∉ D := fun hm => hi ((hD i).mp hm)
    simp [spliceInputs, hn]
  · rw [hval a, hval b]
    exact he
  · exact Ancestor.self _
  · exact output_not_ancestor_shared n C hb q hq hfq

-- Two assignments induce distinct cofactors on D.
def CofactorDistinct (n : Nat) (C : Circuit)
    (D : Finset (Fin n))
    (a b : Fin n → Bool) : Prop :=
  ∃ y : Fin n → Bool,
    C.eval (List.ofFn (spliceInputs n D a y)) ≠
    C.eval (List.ofFn (spliceInputs n D b y))

--  Fixing the input ancestors of q cannot produce three pairwise
-- distinct cofactors: among three assignments, two must agree at q.

theorem shared_no_three_cofactors (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (D : Finset (Fin n))
    (hD : ∀ i : Fin n,
      i ∈ D ↔ Ancestor n C i.val q)
    (a b c : Fin n → Bool)
    (hab : CofactorDistinct n C D a b)
    (hac : CofactorDistinct n C D a c)
    (hbc : CofactorDistinct n C D b c) :
    False := by
  have distinguish (u v : Fin n → Bool)
      (hd : CofactorDistinct n C D u v) :
      wireValue n C u q ≠ wireValue n C v q := by
    intro he
    obtain ⟨y, hy⟩ := hd
    exact hy (shared_cofactor_eq n C hb hs
      q hq hfq D hD u v he y)
  rcases bool_three
      (wireValue n C a q)
      (wireValue n C b q)
      (wireValue n C c q) with h | h | h
  · exact distinguish a b hab h
  · exact distinguish a c hac h
  · exact distinguish b c hbc h

-- 4. Target function and cofactor certificates
--
-- A mask d encodes the subset of inputs assigned by a, b or c; bit i
-- corresponds to input i (least significant bit is input zero).
-- The remaining inputs are assigned by u, v or w.

def target2369 (z : Fin 8 → Bool) : Bool :=
  (z 0 && z 7) || (z 1 && z 7) ||
  (z 2 && z 5) || (z 2 && z 6) ||
  (z 2 && z 7) || (z 3 && z 4) ||
  (z 3 && z 6) || (z 3 && z 7)

def bits8 (a : Fin 256) : Fin 8 → Bool :=
  fun i => a.val.testBit i.val

def splice8 (d a b : Fin 256) : Fin 8 → Bool :=
  fun i => if bits8 d i then bits8 a i else bits8 b i

-- Three assignments and three distinguishing witnesses.
def cofactorCertificate (d a b c u v w : Fin 256) : Bool :=
  (target2369 (splice8 d a u) !=
    target2369 (splice8 d b u)) &&
  (target2369 (splice8 d a v) !=
    target2369 (splice8 d c v)) &&
  (target2369 (splice8 d b w) !=
    target2369 (splice8 d c w))

-- The masks not excluded by the certificate table: empty, each of the
-- eight singletons, {0,1}, and the full set. This is a necessary
-- condition for shared ancestry, not an assertion of realizability.

-- The only permitted input groups.
def allowedGroup (d : Fin 256) : Bool :=
  d.val ∈ ([0, 1, 2, 3, 4, 8, 16, 32, 64, 128, 255] : List Nat)

-- Each row is [d, a, b, c, u, v, w]. It witnesses three pairwise distinct
-- cofactors for mask d: u distinguishes a from b, v distinguishes a from
-- c, and w distinguishes b from c. There are 245 excluded masks.
-- The completeness theorem below checks coverage of all 256 masks by
-- an allowed mask or a successfully checked certificate.

def certificates2369 : List (List Nat) := [
  [5, 0, 1, 4, 128, 32, 32],
  [6, 0, 2, 4, 128, 32, 32],
  [7, 0, 1, 4, 128, 32, 32],
  [9, 0, 1, 8, 128, 16, 16],
  [10, 0, 2, 8, 128, 16, 16],
  [11, 0, 1, 8, 128, 16, 16],
  [12, 0, 4, 8, 32, 16, 16],
  [13, 0, 1, 4, 128, 32, 32],
  [14, 0, 2, 4, 128, 32, 32],
  [15, 0, 1, 4, 128, 32, 32],
  [17, 0, 1, 16, 128, 8, 8],
  [18, 0, 2, 16, 128, 8, 8],
  [19, 0, 1, 16, 128, 8, 8],
  [20, 0, 4, 16, 32, 8, 8],
  [21, 0, 1, 4, 128, 32, 32],
  [22, 0, 2, 4, 128, 32, 32],
  [23, 0, 1, 4, 128, 32, 32],
  [24, 0, 8, 24, 64, 0, 0],
  [25, 0, 1, 8, 128, 64, 64],
  [26, 0, 2, 8, 128, 64, 64],
  [27, 0, 1, 8, 128, 64, 64],
  [28, 0, 4, 8, 32, 64, 32],
  [29, 0, 1, 4, 128, 32, 32],
  [30, 0, 2, 4, 128, 32, 32],
  [31, 0, 1, 4, 128, 32, 32],
  [33, 0, 1, 32, 128, 4, 4],
  [34, 0, 2, 32, 128, 4, 4],
  [35, 0, 1, 32, 128, 4, 4],
  [36, 0, 4, 36, 64, 0, 0],
  [37, 0, 1, 4, 128, 64, 64],
  [38, 0, 2, 4, 128, 64, 64],
  [39, 0, 1, 4, 128, 64, 64],
  [40, 0, 8, 32, 16, 4, 4],
  [41, 0, 1, 8, 128, 16, 16],
  [42, 0, 2, 8, 128, 16, 16],
  [43, 0, 1, 8, 128, 16, 16],
  [44, 0, 4, 8, 64, 16, 16],
  [45, 0, 1, 4, 128, 64, 64],
  [46, 0, 2, 4, 128, 64, 64],
  [47, 0, 1, 4, 128, 64, 64],
  [48, 0, 16, 32, 8, 4, 4],
  [49, 0, 1, 16, 128, 8, 8],
  [50, 0, 2, 16, 128, 8, 8],
  [51, 0, 1, 16, 128, 8, 8],
  [52, 0, 4, 16, 64, 8, 8],
  [53, 0, 1, 4, 128, 64, 64],
  [54, 0, 2, 4, 128, 64, 64],
  [55, 0, 1, 4, 128, 64, 64],
  [56, 0, 8, 24, 64, 0, 0],
  [57, 0, 1, 8, 128, 64, 64],
  [58, 0, 2, 8, 128, 64, 64],
  [59, 0, 1, 8, 128, 64, 64],
  [60, 0, 4, 24, 64, 0, 0],
  [61, 0, 1, 4, 128, 64, 64],
  [62, 0, 2, 4, 128, 64, 64],
  [63, 0, 1, 4, 128, 64, 64],
  [65, 0, 1, 64, 128, 4, 4],
  [66, 0, 2, 64, 128, 4, 4],
  [67, 0, 1, 64, 128, 4, 4],
  [68, 0, 4, 64, 32, 8, 8],
  [69, 0, 1, 4, 128, 32, 32],
  [70, 0, 2, 4, 128, 32, 32],
  [71, 0, 1, 4, 128, 32, 32],
  [72, 0, 8, 64, 16, 4, 4],
  [73, 0, 1, 8, 128, 16, 16],
  [74, 0, 2, 8, 128, 16, 16],
  [75, 0, 1, 8, 128, 16, 16],
  [76, 0, 4, 8, 32, 16, 16],
  [77, 0, 1, 4, 128, 32, 32],
  [78, 0, 2, 4, 128, 32, 32],
  [79, 0, 1, 4, 128, 32, 32],
  [80, 0, 16, 64, 8, 4, 4],
  [81, 0, 1, 16, 128, 8, 8],
  [82, 0, 2, 16, 128, 8, 8],
  [83, 0, 1, 16, 128, 8, 8],
  [84, 0, 4, 16, 32, 8, 8],
  [85, 0, 1, 4, 128, 32, 32],
  [86, 0, 2, 4, 128, 32, 32],
  [87, 0, 1, 4, 128, 32, 32],
  [88, 0, 8, 24, 128, 0, 0],
  [89, 0, 1, 24, 128, 0, 0],
  [90, 0, 2, 24, 128, 0, 0],
  [91, 0, 1, 24, 128, 0, 0],
  [92, 0, 4, 8, 32, 128, 32],
  [93, 0, 1, 4, 128, 32, 32],
  [94, 0, 2, 4, 128, 32, 32],
  [95, 0, 1, 4, 128, 32, 32],
  [96, 0, 32, 64, 4, 4, 8],
  [97, 0, 1, 32, 128, 4, 4],
  [98, 0, 2, 32, 128, 4, 4],
  [99, 0, 1, 32, 128, 4, 4],
  [100, 0, 4, 36, 128, 0, 0],
  [101, 0, 1, 36, 128, 0, 0],
  [102, 0, 2, 36, 128, 0, 0],
  [103, 0, 1, 36, 128, 0, 0],
  [104, 0, 8, 32, 16, 4, 4],
  [105, 0, 1, 8, 128, 16, 16],
  [106, 0, 2, 8, 128, 16, 16],
  [107, 0, 1, 8, 128, 16, 16],
  [108, 0, 4, 8, 128, 16, 16],
  [109, 0, 1, 8, 128, 16, 16],
  [110, 0, 2, 8, 128, 16, 16],
  [111, 0, 1, 8, 128, 16, 16],
  [112, 0, 16, 32, 8, 4, 4],
  [113, 0, 1, 16, 128, 8, 8],
  [114, 0, 2, 16, 128, 8, 8],
  [115, 0, 1, 16, 128, 8, 8],
  [116, 0, 4, 16, 128, 8, 8],
  [117, 0, 1, 16, 128, 8, 8],
  [118, 0, 2, 16, 128, 8, 8],
  [119, 0, 1, 16, 128, 8, 8],
  [120, 0, 8, 24, 128, 0, 0],
  [121, 0, 1, 24, 128, 0, 0],
  [122, 0, 2, 24, 128, 0, 0],
  [123, 0, 1, 24, 128, 0, 0],
  [124, 0, 4, 24, 128, 0, 0],
  [125, 0, 1, 24, 128, 0, 0],
  [126, 0, 2, 24, 128, 0, 0],
  [127, 0, 1, 24, 128, 0, 0],
  [129, 0, 128, 129, 2, 0, 0],
  [130, 0, 128, 130, 1, 0, 0],
  [131, 0, 128, 129, 4, 0, 0],
  [132, 0, 4, 128, 32, 1, 1],
  [133, 0, 4, 128, 32, 2, 2],
  [134, 0, 4, 128, 32, 1, 1],
  [135, 0, 4, 128, 32, 8, 8],
  [136, 0, 8, 128, 16, 1, 1],
  [137, 0, 8, 128, 16, 2, 2],
  [138, 0, 8, 128, 16, 1, 1],
  [139, 0, 8, 128, 16, 4, 4],
  [140, 0, 4, 8, 32, 16, 16],
  [141, 0, 4, 8, 32, 16, 16],
  [142, 0, 4, 8, 32, 16, 16],
  [143, 0, 4, 8, 32, 16, 16],
  [144, 0, 16, 128, 8, 1, 1],
  [145, 0, 16, 128, 8, 2, 2],
  [146, 0, 16, 128, 8, 1, 1],
  [147, 0, 16, 128, 8, 4, 4],
  [148, 0, 4, 16, 32, 8, 8],
  [149, 0, 4, 16, 32, 8, 8],
  [150, 0, 4, 16, 32, 8, 8],
  [151, 0, 4, 16, 32, 8, 8],
  [152, 0, 8, 24, 64, 0, 0],
  [153, 0, 8, 24, 64, 0, 0],
  [154, 0, 8, 24, 64, 0, 0],
  [155, 0, 8, 24, 64, 0, 0],
  [156, 0, 4, 8, 32, 64, 32],
  [157, 0, 4, 8, 32, 64, 32],
  [158, 0, 4, 8, 32, 64, 32],
  [159, 0, 4, 8, 32, 64, 32],
  [160, 0, 32, 128, 4, 1, 1],
  [161, 0, 32, 128, 4, 2, 2],
  [162, 0, 32, 128, 4, 1, 1],
  [163, 0, 32, 128, 4, 4, 8],
  [164, 0, 4, 36, 64, 0, 0],
  [165, 0, 4, 36, 64, 0, 0],
  [166, 0, 4, 36, 64, 0, 0],
  [167, 0, 4, 36, 64, 0, 0],
  [168, 0, 8, 32, 16, 4, 4],
  [169, 0, 8, 32, 16, 4, 4],
  [170, 0, 8, 32, 16, 4, 4],
  [171, 0, 8, 32, 16, 4, 4],
  [172, 0, 4, 8, 64, 16, 16],
  [173, 0, 4, 8, 64, 16, 16],
  [174, 0, 4, 8, 64, 16, 16],
  [175, 0, 4, 8, 64, 16, 16],
  [176, 0, 16, 32, 8, 4, 4],
  [177, 0, 16, 32, 8, 4, 4],
  [178, 0, 16, 32, 8, 4, 4],
  [179, 0, 16, 32, 8, 4, 4],
  [180, 0, 4, 16, 64, 8, 8],
  [181, 0, 4, 16, 64, 8, 8],
  [182, 0, 4, 16, 64, 8, 8],
  [183, 0, 4, 16, 64, 8, 8],
  [184, 0, 8, 24, 64, 0, 0],
  [185, 0, 8, 24, 64, 0, 0],
  [186, 0, 8, 24, 64, 0, 0],
  [187, 0, 8, 24, 64, 0, 0],
  [188, 0, 4, 24, 64, 0, 0],
  [189, 0, 4, 24, 64, 0, 0],
  [190, 0, 4, 24, 64, 0, 0],
  [191, 0, 4, 24, 64, 0, 0],
  [192, 0, 64, 128, 4, 1, 1],
  [193, 0, 64, 128, 4, 2, 2],
  [194, 0, 64, 128, 4, 1, 1],
  [195, 0, 64, 129, 4, 0, 0],
  [196, 0, 4, 64, 32, 8, 8],
  [197, 0, 4, 64, 32, 8, 8],
  [198, 0, 4, 64, 32, 8, 8],
  [199, 0, 4, 64, 32, 8, 8],
  [200, 0, 8, 64, 16, 4, 4],
  [201, 0, 8, 64, 16, 4, 4],
  [202, 0, 8, 64, 16, 4, 4],
  [203, 0, 8, 64, 16, 4, 4],
  [204, 0, 4, 8, 32, 16, 16],
  [205, 0, 4, 8, 32, 16, 16],
  [206, 0, 4, 8, 32, 16, 16],
  [207, 0, 4, 8, 32, 16, 16],
  [208, 0, 16, 64, 8, 4, 4],
  [209, 0, 16, 64, 8, 4, 4],
  [210, 0, 16, 64, 8, 4, 4],
  [211, 0, 16, 64, 8, 4, 4],
  [212, 0, 4, 16, 32, 8, 8],
  [213, 0, 4, 16, 32, 8, 8],
  [214, 0, 4, 16, 32, 8, 8],
  [215, 0, 4, 16, 32, 8, 8],
  [216, 0, 24, 64, 0, 4, 0],
  [217, 0, 24, 64, 0, 4, 0],
  [218, 0, 24, 64, 0, 4, 0],
  [219, 0, 24, 64, 0, 4, 0],
  [220, 0, 4, 24, 32, 0, 0],
  [221, 0, 4, 24, 32, 0, 0],
  [222, 0, 4, 24, 32, 0, 0],
  [223, 0, 4, 24, 32, 0, 0],
  [224, 0, 32, 64, 4, 4, 8],
  [225, 0, 32, 64, 4, 4, 8],
  [226, 0, 32, 64, 4, 4, 8],
  [227, 0, 32, 64, 4, 4, 8],
  [228, 0, 36, 64, 0, 8, 0],
  [229, 0, 36, 64, 0, 8, 0],
  [230, 0, 36, 64, 0, 8, 0],
  [231, 0, 36, 64, 0, 8, 0],
  [232, 0, 8, 32, 16, 4, 4],
  [233, 0, 8, 32, 16, 4, 4],
  [234, 0, 8, 32, 16, 4, 4],
  [235, 0, 8, 32, 16, 4, 4],
  [236, 0, 8, 36, 16, 0, 0],
  [237, 0, 8, 36, 16, 0, 0],
  [238, 0, 8, 36, 16, 0, 0],
  [239, 0, 8, 36, 16, 0, 0],
  [240, 0, 16, 32, 8, 4, 4],
  [241, 0, 16, 32, 8, 4, 4],
  [242, 0, 16, 32, 8, 4, 4],
  [243, 0, 16, 32, 8, 4, 4],
  [244, 0, 16, 36, 8, 0, 0],
  [245, 0, 16, 36, 8, 0, 0],
  [246, 0, 16, 36, 8, 0, 0],
  [247, 0, 16, 36, 8, 0, 0],
  [248, 0, 24, 32, 0, 4, 0],
  [249, 0, 24, 32, 0, 4, 0],
  [250, 0, 24, 32, 0, 4, 0],
  [251, 0, 24, 32, 0, 4, 0],
  [252, 0, 24, 128, 0, 1, 0],
  [253, 0, 24, 128, 0, 2, 0],
  [254, 0, 24, 128, 0, 1, 0]
]

def checkCertificate2369 (row : List Nat) : Bool :=
  match row with
  | [d, a, b, c, u, v, w] =>
    cofactorCertificate
      (Fin.ofNat 256 d)
      (Fin.ofNat 256 a)
      (Fin.ofNat 256 b)
      (Fin.ofNat 256 c)
      (Fin.ofNat 256 u)
      (Fin.ofNat 256 v)
      (Fin.ofNat 256 w)
  | _ => false

def certifiedGroup2369 (d : Fin 256) : Bool :=
  certificates2369.any (fun row =>
    row.headD 256 == d.val &&
    checkCertificate2369 row)

set_option maxRecDepth 4096 in
theorem certificates2369_valid :
    certificates2369.all checkCertificate2369 = true := by
  decide

set_option maxRecDepth 4096 in
theorem certificates2369_complete :
    (List.finRange 256).all
      (fun d => allowedGroup d ||
        certifiedGroup2369 d) = true := by
  decide

theorem forbiddenGroup_certified (d : Fin 256)
    (hd : allowedGroup d = false) :
    certifiedGroup2369 d = true := by
  have hm : d ∈ List.finRange 256 := by simp
  have h := List.all_eq_true.mp
    certificates2369_complete d hm
  simpa [hd] using h

theorem forbiddenGroup_witnesses (d : Fin 256)
    (hd : allowedGroup d = false) :
    ∃ a b c u v w : Fin 256,
      cofactorCertificate d a b c u v w = true := by
  have h := forbiddenGroup_certified d hd
  unfold certifiedGroup2369 at h
  obtain ⟨row, hr, hh⟩ := List.any_eq_true.mp h
  have hp : (row.headD 256 == d.val) = true ∧
      checkCertificate2369 row = true := by
    simpa using hh
  have he : row.headD 256 = d.val := by
    simpa using hp.1
  have hc := hp.2
  rcases row with _ | ⟨r, row⟩ <;>
    simp [checkCertificate2369] at hc
  rcases row with _ | ⟨a, row⟩ <;>
    try simp at hc
  rcases row with _ | ⟨b, row⟩ <;>
    try simp at hc
  rcases row with _ | ⟨c, row⟩ <;>
    try simp at hc
  rcases row with _ | ⟨u, row⟩ <;>
    try simp at hc
  rcases row with _ | ⟨v, row⟩ <;>
    try simp at hc
  rcases row with _ | ⟨w, row⟩ <;>
    try simp at hc
  cases row with
  | nil =>
    have hd' : Fin.ofNat 256 r = d := by
      apply Fin.ext
      change r % 256 = d.val
      have hr' : r = d.val := he
      rw [hr', Nat.mod_eq_of_lt d.isLt]
    refine ⟨Fin.ofNat 256 a, Fin.ofNat 256 b,
      Fin.ofNat 256 c, Fin.ofNat 256 u,
      Fin.ofNat 256 v, Fin.ofNat 256 w, ?_⟩
    rw [← hd']
    exact hc
  | cons z zs =>
    simp at hc

theorem shared_group_allowed (C : Circuit)
    (hb : readsBack 8 C)
    (hs : sharingBudget 8 C ≤ 1)
    (q : Nat)
    (hq : Active 8 C q)
    (hfq : 2 ≤ activeFanout 8 C q)
    (D : Finset (Fin 8))
    (hD : ∀ i : Fin 8,
      i ∈ D ↔ Ancestor 8 C i.val q)
    (d : Fin 256)
    (hd : ∀ i : Fin 8,
      bits8 d i = true ↔ i ∈ D)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x) :
    allowedGroup d = true := by
  cases he : allowedGroup d with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨a, b, c, u, v, w, hc⟩ :=
      forbiddenGroup_witnesses d he
    have hsplice (p r : Fin 256) :
        spliceInputs 8 D (bits8 p) (bits8 r) =
          splice8 d p r := by
      funext i
      by_cases hi : i ∈ D
      · have hb' := (hd i).mpr hi
        simp [spliceInputs, splice8, hi, hb']
      · have hb' : bits8 d i = false := by
          cases hv : bits8 d i with
          | false => rfl
          | true => exact False.elim (hi ((hd i).mp hv))
        simp [spliceInputs, splice8, hi, hb']
    have hcert :
        target2369 (splice8 d a u) ≠
          target2369 (splice8 d b u) ∧
        target2369 (splice8 d a v) ≠
          target2369 (splice8 d c v) ∧
        target2369 (splice8 d b w) ≠
          target2369 (splice8 d c w) := by
      simpa [cofactorCertificate, and_assoc] using hc
    apply shared_no_three_cofactors 8 C hb hs
      q hq hfq D hD (bits8 a) (bits8 b) (bits8 c)
    · refine ⟨bits8 u, ?_⟩
      rw [ht, ht, hsplice, hsplice]
      exact hcert.1
    · refine ⟨bits8 v, ?_⟩
      rw [ht, ht, hsplice, hsplice]
      exact hcert.2.1
    · refine ⟨bits8 w, ?_⟩
      rw [ht, ht, hsplice, hsplice]
      exact hcert.2.2

def groupMask (D : Finset (Fin 8)) : Fin 256 :=
  Fin.ofNat 256 (
    (if (0 : Fin 8) ∈ D then 1 else 0) +
    (if (1 : Fin 8) ∈ D then 2 else 0) +
    (if (2 : Fin 8) ∈ D then 4 else 0) +
    (if (3 : Fin 8) ∈ D then 8 else 0) +
    (if (4 : Fin 8) ∈ D then 16 else 0) +
    (if (5 : Fin 8) ∈ D then 32 else 0) +
    (if (6 : Fin 8) ∈ D then 64 else 0) +
    (if (7 : Fin 8) ∈ D then 128 else 0))

set_option maxRecDepth 4096 in
theorem groupMask_spec (D : Finset (Fin 8)) :
    ∀ i : Fin 8,
      bits8 (groupMask D) i = true ↔ i ∈ D := by
  revert D
  decide

-- 5. Read-once monotone formulas and sensitivity
--
-- A formula is a tree of Boolean constants, variables, conjunctions and
-- disjunctions. Read-once means at most one occurrence of each variable;
-- it does not require every variable to occur. A variable is sensitive at
-- an assignment if flipping just that variable changes the formula value.

inductive MonoFormula (n : Nat) where
  | const : Bool → MonoFormula n
  | var : Fin n → MonoFormula n
  | conj : MonoFormula n → MonoFormula n → MonoFormula n
  | disj : MonoFormula n → MonoFormula n → MonoFormula n

def MonoFormula.eval {n : Nat}
    (x : Fin n → Bool) : MonoFormula n → Bool
  | .const b => b
  | .var i => x i
  | .conj a b => a.eval x && b.eval x
  | .disj a b => a.eval x || b.eval x

def MonoFormula.occurrences {n : Nat}
    (i : Fin n) : MonoFormula n → Nat
  | .const _ => 0
  | .var j => if i = j then 1 else 0
  | .conj a b => a.occurrences i + b.occurrences i
  | .disj a b => a.occurrences i + b.occurrences i

def MonoFormula.ReadOnce {n : Nat}
    (f : MonoFormula n) : Prop :=
  ∀ i : Fin n, f.occurrences i ≤ 1

theorem MonoFormula.eval_agree {n : Nat}
    (f : MonoFormula n) (x y : Fin n → Bool)
    (h : ∀ i, 0 < f.occurrences i → x i = y i) :
    f.eval x = f.eval y := by
  induction f with
  | const b => rfl
  | var j =>
    apply h j
    simp [MonoFormula.occurrences]
  | conj a b ia ib =>
    have ha := ia (by
      intro i hi
      apply h i
      simp only [MonoFormula.occurrences]
      omega)
    have hb := ib (by
      intro i hi
      apply h i
      simp only [MonoFormula.occurrences]
      omega)
    simp only [MonoFormula.eval, ha, hb]
  | disj a b ia ib =>
    have ha := ia (by
      intro i hi
      apply h i
      simp only [MonoFormula.occurrences]
      omega)
    have hb := ib (by
      intro i hi
      apply h i
      simp only [MonoFormula.occurrences]
      omega)
    simp only [MonoFormula.eval, ha, hb]

def flipInput {n : Nat} (x : Fin n → Bool)
    (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !(x j) else x j

theorem MonoFormula.sensitive_occurs {n : Nat}
    (f : MonoFormula n) (x : Fin n → Bool)
    (i : Fin n)
    (h : f.eval x ≠ f.eval (flipInput x i)) :
    0 < f.occurrences i := by
  by_contra hn
  apply h
  apply MonoFormula.eval_agree
  intro j hj
  have hne : j ≠ i := by
    intro he
    subst j
    exact hn hj
  simp [flipInput, hne]

theorem MonoFormula.flip_absent {n : Nat}
    (f : MonoFormula n) (x : Fin n → Bool)
    (i : Fin n) (h : f.occurrences i = 0) :
    f.eval x = f.eval (flipInput x i) := by
  apply MonoFormula.eval_agree
  intro j hj
  have hne : j ≠ i := by
    intro he
    subst j
    omega
  simp [flipInput, hne]

def monoGate (g a b : Bool) : Bool :=
  if g then a && b else a || b

theorem monoGate_sensitive_left (g a b c : Bool)
    (h : monoGate g a b ≠ monoGate g c b) :
    a ≠ c ∧
    monoGate g a b = a ∧ b = g := by
  cases g <;> cases a <;> cases b <;> cases c <;>
    simp_all [monoGate]

theorem monoGate_sensitive_right (g a b c : Bool)
    (h : monoGate g a b ≠ monoGate g a c) :
    b ≠ c ∧
    monoGate g a b = b ∧ a = g := by
  cases g <;> cases a <;> cases b <;> cases c <;>
    simp_all [monoGate]

def MonoFormula.join {n : Nat} (g : Bool)
    (a b : MonoFormula n) : MonoFormula n :=
  if g then .conj a b else .disj a b

theorem MonoFormula.join_eval {n : Nat}
    (g : Bool) (a b : MonoFormula n)
    (x : Fin n → Bool) :
    (MonoFormula.join g a b).eval x =
      monoGate g (a.eval x) (b.eval x) := by
  cases g <;> rfl

theorem MonoFormula.join_occurrences {n : Nat}
    (g : Bool) (a b : MonoFormula n)
    (i : Fin n) :
    (MonoFormula.join g a b).occurrences i =
      a.occurrences i + b.occurrences i := by
  cases g <;> rfl

def MonoFormula.Sensitive {n : Nat}
    (f : MonoFormula n) (x : Fin n → Bool)
    (i : Fin n) : Prop :=
  f.eval x ≠ f.eval (flipInput x i)

theorem MonoFormula.sensitive_branch {n : Nat}
    (g : Bool) (a b : MonoFormula n)
    (hr : (MonoFormula.join g a b).ReadOnce)
    (x : Fin n → Bool) (i : Fin n)
    (hs : (MonoFormula.join g a b).Sensitive x i) :
    (a.Sensitive x i ∧
      b.occurrences i = 0 ∧
      (MonoFormula.join g a b).eval x = a.eval x ∧
      b.eval x = g) ∨
    (b.Sensitive x i ∧
      a.occurrences i = 0 ∧
      (MonoFormula.join g a b).eval x = b.eval x ∧
      a.eval x = g) := by
  have hc := hr i
  rw [MonoFormula.join_occurrences] at hc
  unfold MonoFormula.Sensitive at hs
  rw [MonoFormula.join_eval, MonoFormula.join_eval] at hs
  by_cases ha : a.occurrences i = 0
  · have he := a.flip_absent x i ha
    rw [← he] at hs
    have hh := monoGate_sensitive_right g
      (a.eval x) (b.eval x)
      (b.eval (flipInput x i)) hs
    exact Or.inr ⟨hh.1, ha,
      (MonoFormula.join_eval g a b x).trans hh.2.1,
      hh.2.2⟩
  · have hb : b.occurrences i = 0 := by omega
    have he := b.flip_absent x i hb
    rw [← he] at hs
    have hh := monoGate_sensitive_left g
      (a.eval x) (b.eval x)
      (a.eval (flipInput x i)) hs
    exact Or.inl ⟨hh.1, hb,
      (MonoFormula.join_eval g a b x).trans hh.2.1,
      hh.2.2⟩

theorem MonoFormula.readOnce_join_parts {n : Nat}
    (g : Bool) (a b : MonoFormula n)
    (hr : (MonoFormula.join g a b).ReadOnce) :
    a.ReadOnce ∧ b.ReadOnce := by
  constructor
  · intro i
    have h := hr i
    rw [MonoFormula.join_occurrences] at h
    omega
  · intro i
    have h := hr i
    rw [MonoFormula.join_occurrences] at h
    omega

theorem MonoFormula.sensitive_join_pair {n : Nat}
    (g : Bool) (a b : MonoFormula n)
    (hr : (MonoFormula.join g a b).ReadOnce)
    (x y : Fin n → Bool) (i j : Fin n)
    (hxi : (MonoFormula.join g a b).Sensitive x i)
    (hxj : (MonoFormula.join g a b).Sensitive x j)
    (hyi : (MonoFormula.join g a b).Sensitive y i)
    (hyj : (MonoFormula.join g a b).Sensitive y j)
    (ha : a.Sensitive x i → a.Sensitive x j →
      a.Sensitive y i → a.Sensitive y j →
      a.eval x = a.eval y)
    (hb : b.Sensitive x i → b.Sensitive x j →
      b.Sensitive y i → b.Sensitive y j →
      b.eval x = b.eval y) :
    (MonoFormula.join g a b).eval x =
      (MonoFormula.join g a b).eval y := by
  rcases MonoFormula.sensitive_branch g a b hr x i hxi
    with xi | xi <;>
  rcases MonoFormula.sensitive_branch g a b hr x j hxj
    with xj | xj <;>
  rcases MonoFormula.sensitive_branch g a b hr y i hyi
    with yi | yi <;>
  rcases MonoFormula.sensitive_branch g a b hr y j hyj
    with yj | yj <;>
  first
  | exact xi.2.2.1.trans
      ((ha xi.1 xj.1 yi.1 yj.1).trans yi.2.2.1.symm)
  | exact xi.2.2.1.trans
      ((hb xi.1 xj.1 yi.1 yj.1).trans yi.2.2.1.symm)
  | exfalso
    exact xi.1 (a.flip_absent x i yi.2.1)
  | exfalso
    exact xi.1 (b.flip_absent x i yi.2.1)
  | exfalso
    exact xj.1 (a.flip_absent x j yj.2.1)
  | exfalso
    exact xj.1 (b.flip_absent x j yj.2.1)
  | rw [xi.2.2.1, xj.2.2.2,
        yi.2.2.1, yj.2.2.2]

--  A fixed pair of distinct variables cannot both be sensitive at two
-- assignments with different formula outputs in a read-once monotone
-- formula. In the inductive step, either both variables lie in the same
-- operand, or they lie in different operands. In the latter case the
-- neutral values required for sensitivity determine the output.

theorem MonoFormula.readOnce_sensitive_pair {n : Nat}
    (f : MonoFormula n)
    (hr : f.ReadOnce)
    (x y : Fin n → Bool)
    (i j : Fin n)
    (hne : i ≠ j)
    (hxi : f.Sensitive x i)
    (hxj : f.Sensitive x j)
    (hyi : f.Sensitive y i)
    (hyj : f.Sensitive y j) :
    f.eval x = f.eval y := by
  induction f with
  | const b =>
    rfl
  | var k =>
    have hi := MonoFormula.sensitive_occurs
      (.var k) x i hxi
    have hj := MonoFormula.sensitive_occurs
      (.var k) x j hxj
    have hik : i = k := by
      by_contra h
      simp [MonoFormula.occurrences, h] at hi
    have hjk : j = k := by
      by_contra h
      simp [MonoFormula.occurrences, h] at hj
    exact False.elim (hne (hik.trans hjk.symm))
  | conj a b ia ib =>
    change (MonoFormula.join true a b).ReadOnce at hr
    have hp := MonoFormula.readOnce_join_parts true a b hr
    exact MonoFormula.sensitive_join_pair true a b hr
      x y i j hxi hxj hyi hyj
      (ia hp.1) (ib hp.2)
  | disj a b ia ib =>
    change (MonoFormula.join false a b).ReadOnce at hr
    have hp := MonoFormula.readOnce_join_parts false a b hr
    exact MonoFormula.sensitive_join_pair false a b hr
      x y i j hxi hxj hyi hyj
      (ia hp.1) (ib hp.2)

-- 6. From active circuit wires to formulas
--
-- We unfold gates into formulas, maintaining evaluation, ancestry and a
-- localized occurrence bound. The bound deliberately excludes the wire
-- whose formula is being constructed: sharing its output cannot duplicate
-- variables within the formula computing that output.

theorem unshared_of_not_ancestor (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q a : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (ha : Active n C a)
    (hne : ¬ Ancestor n C a q) :
    activeFanout n C a ≤ 1 := by
  by_contra hn
  have hf : 2 ≤ activeFanout n C a := by omega
  have he := shared_unique n C hs a q
    ((mem_activeVertices n C hb a).mpr ha)
    ((mem_activeVertices n C hb q).mpr hq)
    hf hfq
  subst a
  exact hne (Ancestor.self q)

theorem ancestor_not_shared_forward (n : Nat)
    (C : Circuit)
    {a b q : Nat}
    (ha : ¬ Ancestor n C a q)
    (hab : Ancestor n C a b) :
    ¬ Ancestor n C b q := by
  intro hb
  exact ha (ancestor_trans n C hab hb)

theorem predecessor_count_le_fanout (n : Nat)
    (C : Circuit) (w v : Nat)
    (hv : v ∈ activeVertices n C) :
    (predecessors n C v).count w ≤
      activeFanout n C w := by
  classical
  unfold activeFanout
  exact Finset.single_le_sum
    (f := fun a => (predecessors n C a).count w)
    (fun i _ => Nat.zero_le _) hv

theorem unshared_no_duplicate (n : Nat)
    (C : Circuit) (w v : Nat)
    (hv : v ∈ activeVertices n C)
    (hf : activeFanout n C w ≤ 1) :
    (predecessors n C v).count w ≤ 1 := by
  have h := predecessor_count_le_fanout n C w v hv
  omega

def formulaGate {n : Nat} (op : GateOp)
    (fs : List (MonoFormula n)) : MonoFormula n :=
  match op with
  | .and => fs.foldr MonoFormula.conj (.const true)
  | .or => fs.foldr MonoFormula.disj (.const false)
  | _ => .const false

theorem formulaGate_eval {n : Nat} (op : GateOp)
    (fs : List (MonoFormula n))
    (x : Fin n → Bool)
    (hm : op = GateOp.and ∨ op = GateOp.or) :
    (formulaGate op fs).eval x =
      op.eval (fs.map fun f => f.eval x) := by
  rcases hm with h | h
  · subst op
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      simp [formulaGate, MonoFormula.eval,
        GateOp.eval] at *; rw [ih]
  · subst op
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      simp [formulaGate, MonoFormula.eval,
        GateOp.eval] at *; rw [ih]

theorem formulaGate_occurrences {n : Nat}
    (op : GateOp) (fs : List (MonoFormula n))
    (i : Fin n)
    (hm : op = GateOp.and ∨ op = GateOp.or) :
    (formulaGate op fs).occurrences i =
      (fs.map fun f => f.occurrences i).sum := by
  rcases hm with h | h
  · subst op
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      simp [formulaGate, MonoFormula.occurrences] at *; rw [ih]
  · subst op
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      simp [formulaGate, MonoFormula.occurrences] at *; rw [ih]

theorem list_sum_zero (xs : List Nat)
    (h : ∀ x ∈ xs, x = 0) :
    xs.sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have hs := ih (fun x hx =>
      h x (List.mem_cons_of_mem a hx))
    simp [ha, hs]

--  All active vertices along a dependency from input i to wire w,
-- except w itself, have active fanout at most one.

def UnsharedBelow (n : Nat) (C : Circuit)
    (i : Fin n) (w : Nat) : Prop :=
  ∀ v, Active n C v →
    Ancestor n C i.val v →
    Ancestor n C v w →
    v ≠ w →
    activeFanout n C v ≤ 1

theorem unsharedBelow_predecessor (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (i : Fin n) (u w : Nat)
    (hu : u ∈ predecessors n C w)
    (h : UnsharedBelow n C i w) :
    UnsharedBelow n C i u := by
  intro v hv hiv hvu _
  have hvw : Ancestor n C v w :=
    Ancestor.step hvu hu
  have hle := ancestor_le n C hb hvu
  have hlt := hb w u hu
  exact h v hv hiv hvw (by omega)

theorem shared_unsharedBelow (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (i : Fin n) :
    UnsharedBelow n C i q := by
  intro v hv _ _ hne
  by_contra hn
  have hfv : 2 ≤ activeFanout n C v := by omega
  exact hne (shared_unique n C hs v q
    ((mem_activeVertices n C hb v).mpr hv)
    ((mem_activeVertices n C hb q).mpr hq)
    hfv hfq)

theorem ancestor_comparable_below (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (i : Fin n)
    (u v w : Nat)
    (hau : Ancestor n C i.val u)
    (hav : Ancestor n C i.val v)
    (hw : Active n C w)
    (huw : Ancestor n C u w)
    (hvw : Ancestor n C v w)
    (hun : u ≠ w)
    (hvn : v ≠ w)
    (hf : UnsharedBelow n C i w) :
    Ancestor n C u v ∨ Ancestor n C v u := by
  induction hau with
  | self =>
    exact Or.inl hav
  | @step t u hat htu ih =>
    have htw := ancestor_trans n C
      (predecessor_ancestor n C htu) huw
    have htn : t ≠ w := by
      have h1 := hb u t htu
      have h2 := ancestor_le n C hb huw
      omega
    have hta := ancestor_trans n C htw hw
    rcases ih htw htn with htv | hvt
    · by_cases he : t = v
      · subst v
        exact Or.inr (predecessor_ancestor n C htu)
      · obtain ⟨r, htr, hrv⟩ :=
          ancestor_successor n C htv he
        have hra := ancestor_trans n C
          (ancestor_trans n C hrv hvw) hw
        have hua := ancestor_trans n C huw hw
        have hur := unshared_successor_unique n C
          t u r (hf t hta hat htw htn)
          ((mem_activeVertices n C hb u).mpr hua)
          ((mem_activeVertices n C hb r).mpr hra)
          htu htr
        exact Or.inl (hur.symm ▸ hrv)
    · exact Or.inr (Ancestor.step hvt htu)

-- Two distinct operands cannot have a common ancestor input satisfying
-- the localized unshared condition at their parent gate.

theorem unshared_operands_disjoint_below (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (i : Fin n)
    (u v w : Nat)
    (hw : Active n C w)
    (hu : u ∈ predecessors n C w)
    (hv : v ∈ predecessors n C w)
    (hne : u ≠ v)
    (hau : Ancestor n C i.val u)
    (hav : Ancestor n C i.val v)
    (hf : UnsharedBelow n C i w) :
    False := by
  have huw := predecessor_ancestor n C hu
  have hvw := predecessor_ancestor n C hv
  have hul := hb w u hu
  have hvl := hb w v hv
  have hun : u ≠ w := by omega
  have hvn : v ≠ w := by omega
  have hua := active_predecessor n C hw hu
  have hva := active_predecessor n C hw hv
  rcases ancestor_comparable_below n C hb
    i u v w hau hav hw huw hvw hun hvn hf
    with huv | hvu
  · obtain ⟨r, hur, hrv⟩ :=
      ancestor_successor n C huv hne
    have hra := ancestor_trans n C hrv hva
    have he := unshared_successor_unique n C
      u r w (hf u hua hau huw hun)
      ((mem_activeVertices n C hb r).mpr hra)
      ((mem_activeVertices n C hb w).mpr hw)
      hur hu
    subst r
    have hle := ancestor_le n C hb hrv
    omega
  · obtain ⟨r, hvr, hru⟩ :=
      ancestor_successor n C hvu (Ne.symm hne)
    have hra := ancestor_trans n C hru hua
    have he := unshared_successor_unique n C
      v r w (hf v hva hav hvw hvn)
      ((mem_activeVertices n C hb r).mpr hra)
      ((mem_activeVertices n C hb w).mpr hw)
      hvr hv
    subst r
    have hle := ancestor_le n C hb hru
    omega

theorem operand_occurrences_le_one_below (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (i : Fin n)
    (w u v : Nat)
    (hf : UnsharedBelow n C i w)
    (hw : Active n C w)
    (hp : predecessors n C w = [u, v])
    (a b : MonoFormula n)
    (ha : a.occurrences i ≤ 1)
    (hb' : b.occurrences i ≤ 1)
    (hpa : 0 < a.occurrences i →
      Ancestor n C i.val u)
    (hpb : 0 < b.occurrences i →
      Ancestor n C i.val v) :
    a.occurrences i + b.occurrences i ≤ 1 := by
  by_contra hn
  have h1 : 0 < a.occurrences i := by omega
  have h2 : 0 < b.occurrences i := by omega
  have hu : u ∈ predecessors n C w := by
    simp [hp]
  have hv : v ∈ predecessors n C w := by
    simp [hp]
  by_cases he : u = v
  · subst v
    have hua := active_predecessor n C hw hu
    have huw := predecessor_ancestor n C hu
    have hul := hb w u hu
    have hun : u ≠ w := by omega
    have hc := unshared_no_duplicate n C u w
      ((mem_activeVertices n C hb w).mpr hw)
      (hf u hua (hpa h1) huw hun)
    rw [hp] at hc
    simp at hc
  · exact unshared_operands_disjoint_below n C hb
      i u v w hw hu hv he
      (hpa h1) (hpb h2) hf

theorem operand_list_occurrences_le_one_below
    (n : Nat) (C : Circuit)
    (hb : readsBack n C)
    (i : Fin n)
    (w : Nat)
    (hf : UnsharedBelow n C i w)
    (hw : Active n C w)
    (ps : List Nat)
    (hp : predecessors n C w = ps)
    (hl : ps.length ≤ 2)
    (F : Nat → MonoFormula n)
    (ho : ∀ v ∈ ps, (F v).occurrences i ≤ 1)
    (ha : ∀ v ∈ ps, 0 < (F v).occurrences i →
      Ancestor n C i.val v) :
    (ps.map fun v => (F v).occurrences i).sum ≤ 1 := by
  cases ps with
  | nil => simp
  | cons u us =>
    cases us with
    | nil =>
      simpa using ho u (by simp)
    | cons v vs =>
      have hz : vs.length = 0 := by
        simp only [List.length_cons] at hl
        omega
      have he : vs = [] :=
        List.length_eq_zero_iff.mp hz
      subst vs
      simp only [List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      exact operand_occurrences_le_one_below
        n C hb i w u v hf hw hp (F u) (F v)
        (ho u (by simp))
        (ho v (by simp))
        (ha u (by simp))
        (ha v (by simp))

--  A formula represents a wire if it agrees with its evaluation,
-- uses only ancestor inputs, and uses each locally unshared input at
-- most once.

def RepresentsWireBelow (n : Nat) (C : Circuit)
    (w : Nat) (f : MonoFormula n) : Prop :=
  (∀ x : Fin n → Bool,
    f.eval x = wireValue n C x w) ∧
  (∀ i : Fin n,
    0 < f.occurrences i →
      Ancestor n C i.val w) ∧
  (∀ i : Fin n,
    UnsharedBelow n C i w →
      f.occurrences i ≤ 1)

theorem represents_input_below (n : Nat) (C : Circuit)
    (i : Fin n) :
    RepresentsWireBelow n C i.val (.var i) := by
  constructor
  · intro x
    exact (wireValue_input n C x i).symm
  constructor
  · intro j hj
    have he : j = i := by
      by_contra hn
      simp [MonoFormula.occurrences, hn] at hj
    subst j
    exact Ancestor.self _
  · intro j _
    by_cases he : j = i <;>
      simp [MonoFormula.occurrences, he]

theorem represents_gate_below (n : Nat) (C : Circuit)
    (hb : readsBack n C)
    (j : Nat) (g : Gate)
    (hg : C.gates[j]? = some g)
    (hw : Active n C (n + j))
    (hm : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length ≤ 2)
    (F : Nat → MonoFormula n)
    (hF : ∀ v ∈ g.inputs,
      RepresentsWireBelow n C v (F v)) :
    RepresentsWireBelow n C (n + j)
      (formulaGate g.op (g.inputs.map F)) := by
  have hp : predecessors n C (n + j) = g.inputs := by
    unfold predecessors
    have hn : ¬ n + j < n := by omega
    simp [hn, hg]
  constructor
  · intro x
    rw [formulaGate_eval _ _ _ hm,
      wireValue_gate n C x j g hg hb,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro v hv
    exact (hF v hv).1 x
  constructor
  · intro i hi
    rw [formulaGate_occurrences _ _ _ hm,
      List.map_map] at hi
    by_contra hn
    have hz :
        (g.inputs.map fun v =>
          (F v).occurrences i).sum = 0 := by
      apply list_sum_zero
      intro a ha
      obtain ⟨v, hv, he⟩ := List.mem_map.mp ha
      have hvz : (F v).occurrences i = 0 := by
        by_contra hne
        have hpos : 0 < (F v).occurrences i := by omega
        have han := (hF v hv).2.1 i hpos
        apply hn
        apply Ancestor.step han
        rw [hp]
        exact hv
      omega
    exact (Nat.ne_of_gt hi) (by simpa [Function.comp_def] using hz)
  · intro i hi
    rw [formulaGate_occurrences _ _ _ hm,
      List.map_map]
    exact operand_list_occurrences_le_one_below
      n C hb i (n + j) hi hw g.inputs hp hl F
      (fun v hv => (hF v hv).2.2 i
        (unsharedBelow_predecessor n C hb i v (n + j)
          (by rw [hp]; exact hv) hi))
      (fun v hv => (hF v hv).2.1 i)

--  Every active wire in a valid read-back monotone binary circuit
-- admits a formula with the three representation invariants.

theorem active_representation_below (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hm : ∀ g ∈ C.gates,
      g.op = GateOp.and ∨ g.op = GateOp.or)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hout : C.output < n + C.size)
    (w : Nat)
    (hw : Active n C w) :
    ∃ f : MonoFormula n,
      RepresentsWireBelow n C w f := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · exact ⟨.var ⟨w, hn⟩,
        represents_input_below n C ⟨w, hn⟩⟩
    · have hle := ancestor_le n C hb hw
      have hj : w - n < C.gates.length := by
        unfold Circuit.size at hout
        omega
      let g := C.gates[w - n]
      have hg : C.gates[w - n]? = some g := by
        simp [g, hj]
      have hp : predecessors n C w = g.inputs := by
        simp [predecessors, hn, hg]
      have hex : ∀ v ∈ g.inputs,
          ∃ f : MonoFormula n,
            RepresentsWireBelow n C v f := by
        intro v hv
        have hv' : v ∈ predecessors n C w := by
          rw [hp]
          exact hv
        exact ih v (hb w v hv')
          (active_predecessor n C hw hv')
      let F (v : Nat) : MonoFormula n :=
        if hv : v ∈ g.inputs then
          Classical.choose (hex v hv)
        else .const false
      have hF : ∀ v ∈ g.inputs,
          RepresentsWireBelow n C v (F v) := by
        intro v hv
        simp only [F, dite_eq_left hv]
        exact Classical.choose_spec (hex v hv)
      have hmem := List.mem_of_getElem? hg
      have he : n + (w - n) = w := by omega
      refine ⟨formulaGate g.op (g.inputs.map F), ?_⟩
      have hr := represents_gate_below n C hb
        (w - n) g hg (by rw [he]; exact hw)
        (hm g hmem) (hf g hmem) F hF
      rw [he] at hr
      exact hr

-- 7. Restrictions and read-once representations
--
-- Substituting constants for selected inputs eliminates their occurrences
-- without changing the occurrence count of any other input.

def MonoFormula.restrict {n : Nat}
    (D : Finset (Fin n))
    (z : Fin n → Bool) :
    MonoFormula n → MonoFormula n
  | .const b => .const b
  | .var i => if i ∈ D then .const (z i) else .var i
  | .conj a b => .conj (a.restrict D z) (b.restrict D z)
  | .disj a b => .disj (a.restrict D z) (b.restrict D z)

theorem MonoFormula.restrict_eval {n : Nat}
    (f : MonoFormula n)
    (D : Finset (Fin n))
    (z x : Fin n → Bool) :
    (f.restrict D z).eval x =
      f.eval (spliceInputs n D z x) := by
  induction f with
  | const b => rfl
  | var i =>
    by_cases h : i ∈ D <;>
      simp [MonoFormula.restrict, MonoFormula.eval,
        spliceInputs, h]
  | conj a b ia ib =>
    simp [MonoFormula.restrict, MonoFormula.eval, ia, ib]
  | disj a b ia ib =>
    simp [MonoFormula.restrict, MonoFormula.eval, ia, ib]

theorem MonoFormula.restrict_occurrences {n : Nat}
    (f : MonoFormula n)
    (D : Finset (Fin n))
    (z : Fin n → Bool)
    (i : Fin n) :
    (f.restrict D z).occurrences i =
      if i ∈ D then 0 else f.occurrences i := by
  induction f with
  | const b =>
    simp [MonoFormula.restrict, MonoFormula.occurrences]
  | var j =>
    by_cases he : i = j
    · subst j
      by_cases h : i ∈ D <;>
        simp [MonoFormula.restrict, MonoFormula.occurrences, h]
    · by_cases h : j ∈ D <;>
        simp [MonoFormula.restrict, MonoFormula.occurrences, h, he]
  | conj a b ia ib =>
    by_cases h : i ∈ D <;>
      simp [MonoFormula.restrict, MonoFormula.occurrences,
        ia, ib, h]
  | disj a b ia ib =>
    by_cases h : i ∈ D <;>
      simp [MonoFormula.restrict, MonoFormula.occurrences,
        ia, ib, h]

theorem restricted_readOnce (n : Nat)
    (C : Circuit)
    (w : Nat)
    (f : MonoFormula n)
    (hr : RepresentsWireBelow n C w f)
    (D : Finset (Fin n))
    (z : Fin n → Bool)
    (hD : ∀ i : Fin n, i ∉ D →
      UnsharedBelow n C i w) :
    (f.restrict D z).ReadOnce := by
  intro i
  rw [MonoFormula.restrict_occurrences]
  by_cases hi : i ∈ D
  · simp [hi]
  · simp only [ite_eq_right hi]
    exact hr.2.2 i (hD i hi)

theorem shared_restricted_readOnce (n : Nat)
    (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q w : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (f : MonoFormula n)
    (hr : RepresentsWireBelow n C w f)
    (D : Finset (Fin n))
    (hD : ∀ i : Fin n,
      i ∈ D ↔ Ancestor n C i.val q)
    (z : Fin n → Bool) :
    (f.restrict D z).ReadOnce := by
  apply restricted_readOnce n C w f hr D z
  intro i hi
  have hn : ¬ Ancestor n C i.val q := by
    intro ha
    exact hi ((hD i).mpr ha)
  intro v hv hav _ _
  exact unshared_of_not_ancestor n C hb hs
    q v hq hfq hv
    (ancestor_not_shared_forward n C hn hav)

-- 8. Three induced-path sensitivity witnesses
--
-- The paths (in order of k = 0,1,2) are
--   0 -- 7 -- 2 -- 5
--   2 -- 6 -- 3 -- 4
--   1 -- 7 -- 3 -- 4
-- X sets the two middle inputs to true; Y sets the endpoints to true.
-- All other inputs are false. The outputs are true and false,
-- respectively, and each middle input is sensitive at both assignments.
-- The paths have no common vertex, and the second avoids {0,1}, so
-- one survives every allowed proper group when its inputs are set to zero.
-- The claims are checked directly in the finite witness theorems.

def witnessX (k : Fin 3) : Fin 256 :=
  if k = 0 then 132 else
  if k = 1 then 72 else 136

def witnessY (k : Fin 3) : Fin 256 :=
  if k = 0 then 33 else
  if k = 1 then 20 else 18

def witnessI (k : Fin 3) : Fin 8 :=
  if k = 0 then 7 else
  if k = 1 then 6 else 7

def witnessJ (k : Fin 3) : Fin 8 :=
  if k = 0 then 2 else 3

theorem witness_sensitive :
    ∀ k : Fin 3,
      witnessI k ≠ witnessJ k ∧
      target2369 (bits8 (witnessX k)) ≠
        target2369 (bits8 (witnessY k)) ∧
      target2369 (bits8 (witnessX k)) ≠
        target2369 (flipInput (bits8 (witnessX k)) (witnessI k)) ∧
      target2369 (bits8 (witnessX k)) ≠
        target2369 (flipInput (bits8 (witnessX k)) (witnessJ k)) ∧
      target2369 (bits8 (witnessY k)) ≠
        target2369 (flipInput (bits8 (witnessY k)) (witnessI k)) ∧
      target2369 (bits8 (witnessY k)) ≠
        target2369 (flipInput (bits8 (witnessY k)) (witnessJ k)) := by
  decide

def outside8 (d : Fin 256)
    (x : Fin 8 → Bool) : Prop :=
  ∀ i : Fin 8, bits8 d i = true → x i = false

def witnessSurvives (d : Fin 256)
    (k : Fin 3) : Prop :=
  outside8 d (bits8 (witnessX k)) ∧
  outside8 d (bits8 (witnessY k)) ∧
  bits8 d (witnessI k) = false ∧
  bits8 d (witnessJ k) = false

instance (d : Fin 256) (x : Fin 8 → Bool) :
    Decidable (outside8 d x) := by
  unfold outside8
  infer_instance

instance (d : Fin 256) (k : Fin 3) :
    Decidable (witnessSurvives d k) := by
  unfold witnessSurvives
  infer_instance

set_option maxRecDepth 4096 in
theorem witness_survives :
    ∀ d : Fin 256,
      allowedGroup d = true →
      d.val ≠ 255 →
      ∃ k : Fin 3, witnessSurvives d k := by
  decide

theorem outside8_flip (d : Fin 256)
    (x : Fin 8 → Bool) (i : Fin 8)
    (hx : outside8 d x)
    (hi : bits8 d i = false) :
    outside8 d (flipInput x i) := by
  intro j hj
  have hne : j ≠ i := by
    intro he
    subst j
    rw [hi] at hj
    contradiction
  simpa [flipInput, hne] using hx j hj

theorem witness_not_readOnce
    (f : MonoFormula 8)
    (k : Fin 3)
    (hx : f.eval (bits8 (witnessX k)) =
      target2369 (bits8 (witnessX k)))
    (hy : f.eval (bits8 (witnessY k)) =
      target2369 (bits8 (witnessY k)))
    (hxi : f.eval (flipInput (bits8 (witnessX k)) (witnessI k)) =
      target2369 (flipInput (bits8 (witnessX k)) (witnessI k)))
    (hxj : f.eval (flipInput (bits8 (witnessX k)) (witnessJ k)) =
      target2369 (flipInput (bits8 (witnessX k)) (witnessJ k)))
    (hyi : f.eval (flipInput (bits8 (witnessY k)) (witnessI k)) =
      target2369 (flipInput (bits8 (witnessY k)) (witnessI k)))
    (hyj : f.eval (flipInput (bits8 (witnessY k)) (witnessJ k)) =
      target2369 (flipInput (bits8 (witnessY k)) (witnessJ k))) :
    ¬ f.ReadOnce := by
  intro hr
  obtain ⟨hne, hxy, sxi, sxj, syi, syj⟩ :=
    witness_sensitive k
  have a : f.Sensitive (bits8 (witnessX k)) (witnessI k) := by
    unfold MonoFormula.Sensitive
    rw [hx, hxi]
    exact sxi
  have b : f.Sensitive (bits8 (witnessX k)) (witnessJ k) := by
    unfold MonoFormula.Sensitive
    rw [hx, hxj]
    exact sxj
  have c : f.Sensitive (bits8 (witnessY k)) (witnessI k) := by
    unfold MonoFormula.Sensitive
    rw [hy, hyi]
    exact syi
  have d : f.Sensitive (bits8 (witnessY k)) (witnessJ k) := by
    unfold MonoFormula.Sensitive
    rw [hy, hyj]
    exact syj
  have he := MonoFormula.readOnce_sensitive_pair
    f hr (bits8 (witnessX k)) (bits8 (witnessY k))
    (witnessI k) (witnessJ k) hne a b c d
  rw [hx, hy] at he
  exact hxy he

theorem proper_restriction_not_readOnce
    (f : MonoFormula 8)
    (d : Fin 256)
    (hd : allowedGroup d = true)
    (hne : d.val ≠ 255)
    (he : ∀ x : Fin 8 → Bool,
      outside8 d x → f.eval x = target2369 x) :
    ¬ f.ReadOnce := by
  obtain ⟨k, hk⟩ := witness_survives d hd hne
  obtain ⟨hx, hy, hi, hj⟩ := hk
  exact witness_not_readOnce f k
    (he _ hx)
    (he _ hy)
    (he _ (outside8_flip d _ _ hx hi))
    (he _ (outside8_flip d _ _ hx hj))
    (he _ (outside8_flip d _ _ hy hi))
    (he _ (outside8_flip d _ _ hy hj))

theorem splice_zero_of_outside
    (D : Finset (Fin 8))
    (d : Fin 256)
    (hd : ∀ i : Fin 8,
      bits8 d i = true ↔ i ∈ D)
    (x : Fin 8 → Bool)
    (hx : outside8 d x) :
    spliceInputs 8 D (fun _ => false) x = x := by
  funext i
  by_cases hi : i ∈ D
  · have hz := hx i ((hd i).mpr hi)
    simp [spliceInputs, hi, hz]
  · simp [spliceInputs, hi]

-- 9. Eliminate the three structural possibilities

-- Case 1: the unique shared vertex has a proper group of input ancestors.

theorem shared_proper_impossible
    (C : Circuit)
    (hb : readsBack 8 C)
    (hs : sharingBudget 8 C ≤ 1)
    (q : Nat)
    (hq : Active 8 C q)
    (hfq : 2 ≤ activeFanout 8 C q)
    (D : Finset (Fin 8))
    (hD : ∀ i : Fin 8,
      i ∈ D ↔ Ancestor 8 C i.val q)
    (f : MonoFormula 8)
    (hr : RepresentsWireBelow 8 C C.output f)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x)
    (hne : (groupMask D).val ≠ 255) :
    False := by
  have hd := groupMask_spec D
  have ha := shared_group_allowed C hb hs
    q hq hfq D hD (groupMask D) hd ht
  have hro := shared_restricted_readOnce 8 C
    hb hs q C.output hq hfq f hr D hD
    (fun _ => false)
  apply proper_restriction_not_readOnce
    (f.restrict D (fun _ => false))
    (groupMask D) ha hne _ hro
  intro x hx
  rw [MonoFormula.restrict_eval,
    splice_zero_of_outside D (groupMask D) hd x hx,
    hr.1 x]
  exact ht x

-- Case 2: all active vertices have fanout at most one.

theorem no_sharing_impossible
    (C : Circuit)
    (f : MonoFormula 8)
    (hr : RepresentsWireBelow 8 C C.output f)
    (hf : ∀ w, Active 8 C w →
      activeFanout 8 C w ≤ 1)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x) :
    False := by
  have hro : f.ReadOnce := by
    intro i
    apply hr.2.2 i
    intro w hw _ _ _
    exact hf w hw
  have he : ∀ x : Fin 8 → Bool,
      f.eval x = target2369 x := by
    intro x
    rw [hr.1 x]
    exact ht x
  exact witness_not_readOnce f 0
    (he _) (he _) (he _) (he _) (he _) (he _) hro

-- Case 3: the shared vertex is a bottleneck for all inputs. Its own
-- formula is read-once, even though its output may be used twice.

theorem shared_vertex_readOnce
    (n : Nat) (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (f : MonoFormula n)
    (hr : RepresentsWireBelow n C q f) :
    f.ReadOnce := by
  intro i
  exact hr.2.2 i
    (shared_unsharedBelow n C hb hs q hq hfq i)

theorem shared_all_inputs_bottleneck
    (n : Nat) (C : Circuit)
    (hb : readsBack n C)
    (hs : sharingBudget n C ≤ 1)
    (q : Nat)
    (hq : Active n C q)
    (hfq : 2 ≤ activeFanout n C q)
    (ha : ∀ i : Fin n, Ancestor n C i.val q)
    (x y : Fin n → Bool)
    (he : wireValue n C x q = wireValue n C y q) :
    C.eval (List.ofFn x) =
      C.eval (List.ofFn y) := by
  have hxy : ∀ i : Fin n,
      ¬ Ancestor n C i.val q → x i = y i := by
    intro i hi
    exact False.elim (hi (ha i))
  exact shared_value_agree n C hb hs
    q hq hfq x y hxy he C.output
    (Ancestor.self _)
    (output_not_ancestor_shared n C hb q hq hfq)

theorem shared_all_inputs_impossible
    (C : Circuit)
    (hb : readsBack 8 C)
    (hs : sharingBudget 8 C ≤ 1)
    (q : Nat)
    (hq : Active 8 C q)
    (hfq : 2 ≤ activeFanout 8 C q)
    (ha : ∀ i : Fin 8, Ancestor 8 C i.val q)
    (f : MonoFormula 8)
    (hr : RepresentsWireBelow 8 C q f)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x) :
    False := by
  have hro := shared_vertex_readOnce 8 C
    hb hs q hq hfq f hr
  have distinguish :
      ∀ x y : Fin 8 → Bool,
        target2369 x ≠ target2369 y →
        f.eval x ≠ f.eval y := by
    intro x y hne he
    rw [hr.1 x, hr.1 y] at he
    have he' := shared_all_inputs_bottleneck
      8 C hb hs q hq hfq ha x y he
    rw [ht x, ht y] at he'
    exact hne he'
  obtain ⟨hne, hxy, hxi, hxj, hyi, hyj⟩ :=
    witness_sensitive 0
  have he := MonoFormula.readOnce_sensitive_pair
    f hro
    (bits8 (witnessX 0))
    (bits8 (witnessY 0))
    (witnessI 0)
    (witnessJ 0)
    hne
    (distinguish _ _ hxi)
    (distinguish _ _ hxj)
    (distinguish _ _ hyi)
    (distinguish _ _ hyj)
  exact (distinguish _ _ hxy) he

-- 10. Essential inputs, valid output and lower-bound assembly

set_option maxRecDepth 4096 in
theorem target2369_essential :
    ∀ i : Fin 8, ∃ a : Fin 256,
      target2369 (bits8 a) ≠
        target2369 (flipInput (bits8 a) i) := by
  decide

theorem circuit2369_essential
    (C : Circuit)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x) :
    ∀ i : Fin 8, Essential 8 C i := by
  intro i
  obtain ⟨a, ha⟩ := target2369_essential i
  refine ⟨bits8 a, flipInput (bits8 a) i, ?_, ?_⟩
  · intro j hj
    simp [flipInput, hj]
  · rw [ht, ht]
    exact ha

theorem circuit2369_output_valid
    (C : Circuit)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x) :
    C.output < 8 + C.size := by
  by_contra hn
  let x : Fin 8 → Bool := fun _ => true
  have hl : (C.wires (List.ofFn x)).length =
      8 + C.size := by
    rw [wires_length]
    simp
  have hle : (C.wires (List.ofFn x)).length ≤
      C.output := by omega
  have hz : wireValue 8 C x C.output = false := by
    unfold wireValue
    unfold List.getD
    rw [List.getElem?_eq_none hle]
    rfl
  have ht' : wireValue 8 C x C.output =
      target2369 x := ht x
  rw [hz] at ht'
  have he : target2369 x = true := by
    rfl
  rw [he] at ht'
  contradiction

theorem mask255_all :
    ∀ i : Fin 8, bits8 (255 : Fin 256) i = true := by
  decide

theorem lower_bound_2369
    (C : Circuit)
    (hb : readsBack 8 C)
    (hm : ∀ g ∈ C.gates,
      g.op = GateOp.and ∨ g.op = GateOp.or)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (ht : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = target2369 x) :
    9 ≤ C.size := by
  classical
  by_contra hn
  have he := circuit2369_essential C ht
  have hout := circuit2369_output_valid C ht
  have hbudget := sharingBudget_bound 8 C hb he hf hout
  have hs : sharingBudget 8 C ≤ 1 := by omega
  obtain ⟨f, hr⟩ := active_representation_below 8 C hb
    hm hf hout C.output (Ancestor.self _)
  by_cases hshared :
      ∃ q, Active 8 C q ∧ 2 ≤ activeFanout 8 C q
  · obtain ⟨q, hq, hfq⟩ := hshared
    let D : Finset (Fin 8) :=
      Finset.univ.filter
        (fun i => Ancestor 8 C i.val q)
    have hD : ∀ i : Fin 8,
        i ∈ D ↔ Ancestor 8 C i.val q := by
      intro i
      simp [D]
    by_cases hall : (groupMask D).val = 255
    · have hmask : groupMask D = (255 : Fin 256) :=
        Fin.ext hall
      have ha : ∀ i : Fin 8,
          Ancestor 8 C i.val q := by
        intro i
        apply (hD i).mp
        apply (groupMask_spec D i).mp
        rw [hmask]
        exact mask255_all i
      obtain ⟨fq, hrq⟩ :=
        active_representation_below 8 C hb
          hm hf hout q hq
      exact shared_all_inputs_impossible C hb
        hs q hq hfq ha fq hrq ht
    · exact shared_proper_impossible C hb
        hs q hq hfq D hD f hr ht hall
  · apply no_sharing_impossible C f hr _ ht
    intro w hw
    by_contra h
    exact hshared ⟨w, hw, by omega⟩

-- 11. Bridge to project definitions and exact conjecture

theorem monotone2_bridge (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    (∀ g ∈ C.gates,
      g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) := by
  constructor
  · intro g hg
    simpa using (hm g hg).1
  · intro g hg
    exact (hm g hg).2

theorem readsBack_bridge (n : Nat) (C : Circuit)
    (hb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    readsBack n C := by
  intro w i hi
  by_cases hn : w < n
  · rw [input_predecessors n C w hn] at hi
    simp at hi
  · cases hg : C.gates[w - n]? with
    | none =>
      simp [predecessors, hn, hg] at hi
    | some g =>
      have hj : w - n < C.gates.length := by
        by_contra h
        have hz : C.gates[w - n]? = none :=
          List.getElem?_eq_none (by omega)
        rw [hz] at hg
        contradiction
      have hgate :
          PEqualNP.MetaComplexity.NestedCover.gateAt
            C (w - n) = g := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt,
          List.getD, hg]
      have hmem : i ∈ g.inputs := by
        simpa [predecessors, hn, hg] using hi
      have hlt := hb (w - n) hj i (by
        rw [hgate]
        exact hmem)
      omega

end PEqualNP.Outside.L_meta_2369

theorem PEqualNP.Outside.L_meta_2369 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C →
      (∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          (fun z : Fin 8 → Bool =>
            (z 0 && z 7) ||
            (z 1 && z 7) ||
            (z 2 && z 5) ||
            (z 2 && z 6) ||
            (z 2 && z 7) ||
            (z 3 && z 4) ||
            (z 3 && z 6) ||
            (z 3 && z 7)) x) →
      9 ≤ C.size := by
  intro C hm hb ht
  obtain ⟨hm', hf⟩ := PEqualNP.Outside.L_meta_2369.monotone2_bridge C hm
  exact PEqualNP.Outside.L_meta_2369.lower_bound_2369 C
    (PEqualNP.Outside.L_meta_2369.readsBack_bridge 8 C hb)
    hm' hf ht
