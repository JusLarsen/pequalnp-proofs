import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.SyntacticMultilinear

-- The value of wire `w` of `C` on the input `x` (`false` past the last wire).
def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

-- The fold lemmas below (`wire_run_append` to `wire_run_at`) are taken from the checked file
-- L_meta_2006.lean (`wiresFrom` and its lemmas), restated for any forward pass over the gates.

-- A forward pass over the gates: each gate appends one entry, computed by `f` from the entries
-- so far. `Circuit.wires` and `supports` are both of this form.
def wire_run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem wire_run_append {α : Type} (f : List α → Gate → α) (gs gs' : List Gate) (w : List α) :
    wire_run f (gs ++ gs') w = wire_run f gs' (wire_run f gs w) := by
  simp [wire_run, List.foldl_append]

theorem wire_run_start {α : Type} (f : List α → Gate → α) (gs : List Gate) : ∀ w : List α,
    ∃ t : List α, wire_run f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wire_run], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    have : wire_run f (g :: gs) w = wire_run f gs (w ++ [f w g]) := rfl
    rw [this, ht]; simp

theorem wire_run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (wire_run f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wire_run_start f gs w
  rw [ht]; simp [hl]

theorem wire_run_getD_lt {α : Type} (f : List α → Gate → α) (d : α) (gs : List Gate)
    (w : List α) (i : ℕ) (h : i < w.length) :
    (wire_run f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := wire_run_start f gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem wire_getD_snoc {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem wire_run_at {α : Type} (f : List α → Gate → α) (d : α) (n : ℕ) (pre post : List Gate)
    (g : Gate) (X : List α) (hX : X.length = n) :
    (wire_run f (pre ++ g :: post) X).getD (n + pre.length) d = f (wire_run f pre X) g := by
  have h1 : wire_run f (pre ++ g :: post) X
      = wire_run f post (wire_run f pre X ++ [f (wire_run f pre X) g]) := by
    rw [wire_run_append]; rfl
  have hl : (wire_run f pre X).length = n + pre.length := by
    rw [wire_run_length]; omega
  rw [h1, wire_run_getD_lt _ _ _ _ _ (by simp [hl]), wire_getD_snoc _ _ _ _ hl]

-- Entry `n + k` of a forward pass is what gate `k` computes from the pass over the first `k`
-- gates.
theorem wire_run_gate {α : Type} (f : List α → Gate → α) (d : α) (n : ℕ) (gs : List Gate)
    (X : List α) (hX : X.length = n) (k : ℕ) (hk : k < gs.length) :
    (wire_run f gs X).getD (n + k) d = f (wire_run f (gs.take k) X) gs[k] := by
  have h := wire_run_at f d n (gs.take k) (gs.drop (k + 1)) gs[k] X hX
  have e : gs.take k ++ gs[k] :: gs.drop (k + 1) = gs := by simp
  have l : (gs.take k).length = k := by rw [List.length_take]; omega
  rw [e, l] at h
  exact h

-- The pass over the first `k` gates agrees with the whole pass below entry `n + k`.
theorem wire_run_take_lt {α : Type} (f : List α → Gate → α) (d : α) (n : ℕ) (gs : List Gate)
    (X : List α) (hX : X.length = n) (k : ℕ) (hk : k ≤ gs.length) (i : ℕ) (hi : i < n + k) :
    (wire_run f (gs.take k) X).getD i d = (wire_run f gs X).getD i d := by
  have h : wire_run f gs X = wire_run f (gs.drop k) (wire_run f (gs.take k) X) := by
    rw [← wire_run_append, List.take_append_drop]
  rw [h]
  exact (wire_run_getD_lt f d (gs.drop k) (wire_run f (gs.take k) X) i
    (by rw [wire_run_length, List.length_take]; omega)).symm

-- The pass over the first `k` gates has no entry `n + k` or later.
theorem wire_run_take_ge {α : Type} (f : List α → Gate → α) (d : α) (n : ℕ) (gs : List Gate)
    (X : List α) (hX : X.length = n) (k : ℕ) (i : ℕ) (hi : n + k ≤ i) :
    (wire_run f (gs.take k) X).getD i d = d := by
  apply List.getD_eq_default
  rw [wire_run_length, List.length_take]; omega

theorem wire_gateAt (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt; exact List.getD_eq_getElem _ _ hk

-- The value a gate appends to the wire values so far.
def wire_evalStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wire_wires (C : Circuit) (x : List Bool) :
    C.wires x = wire_run wire_evalStep C.gates x := rfl

theorem wire_val_out (C : Circuit) (x : List Bool) (w : ℕ) (h : x.length + C.gates.length ≤ w) :
    val C x w = false := by
  unfold val
  rw [wire_wires]
  exact List.getD_eq_default _ _ (by rw [wire_run_length]; exact h)

-- What the first `k` gates leave on wire `i` is what gate `k` reads from it.
theorem wire_val_take (C : Circuit) (x : List Bool) (k : ℕ) (hk : k ≤ C.gates.length) (i : ℕ) :
    (wire_run wire_evalStep (C.gates.take k) x).getD i false =
      if i < x.length + k then val C x i else false := by
  by_cases h : i < x.length + k
  · simp only [h, ite_true]
    rw [wire_run_take_lt _ _ _ _ _ rfl _ hk _ h]; rfl
  · simp only [h, ite_false]
    exact wire_run_take_ge _ _ _ _ _ rfl _ _ (by omega)

-- The support a gate appends to the supports so far.
def wire_suppStep {N : ℕ} (s : List (Finset (Fin N))) (g : Gate) : Finset (Fin N) :=
  g.inputs.foldr (fun w acc => s.getD w ∅ ∪ acc) ∅

-- The supports of the input wires.
def wire_init (N : ℕ) : List (Finset (Fin N)) := List.ofFn fun i : Fin N => ({i} : Finset (Fin N))

theorem wire_init_length (N : ℕ) : (wire_init N).length = N := by simp [wire_init]

theorem wire_supports (N : ℕ) (C : Circuit) :
    supports N C = wire_run wire_suppStep C.gates (wire_init N) := rfl

theorem wire_mem_foldr {N : ℕ} (s : List (Finset (Fin N))) (a : Fin N) (l : List ℕ) :
    a ∈ l.foldr (fun w acc => s.getD w ∅ ∪ acc) ∅ ↔ ∃ w ∈ l, a ∈ s.getD w ∅ := by
  induction l with
  | nil => simp
  | cons b l ih =>
    show a ∈ s.getD b ∅ ∪ l.foldr (fun w acc => s.getD w ∅ ∪ acc) ∅ ↔ _
    rw [Finset.mem_union, ih]
    constructor
    · rintro (h | ⟨w, hw, h⟩)
      · exact ⟨b, List.mem_cons.2 (Or.inl rfl), h⟩
      · exact ⟨w, List.mem_cons.2 (Or.inr hw), h⟩
    · rintro ⟨w, hw, h⟩
      rcases List.mem_cons.1 hw with rfl | hw
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, h⟩

-- What the first `k` gates leave as the support of wire `i` is its support as read by gate
-- `k`.
theorem wire_support_take (N : ℕ) (C : Circuit) (k : ℕ) (hk : k ≤ C.gates.length) (i : ℕ) :
    (wire_run wire_suppStep (C.gates.take k) (wire_init N)).getD i ∅ = operandSupport N C k i := by
  unfold operandSupport
  by_cases h : i < N + k
  · simp only [h, ite_true]
    rw [wire_run_take_lt _ _ N _ _ (wire_init_length N) _ hk _ h]; rfl
  · simp only [h, ite_false]
    exact wire_run_take_ge _ _ N _ _ (wire_init_length N) _ _ (by omega)

-- The support of a gate is exactly the union of the supports of its reads.
theorem wire_support_gate_iff (N : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (a : Fin N) :
    a ∈ support N C (N + k) ↔ ∃ i ∈ (gateAt C k).inputs, a ∈ operandSupport N C k i := by
  have h : support N C (N + k)
      = wire_suppStep (wire_run wire_suppStep (C.gates.take k) (wire_init N)) C.gates[k] :=
    wire_run_gate wire_suppStep ∅ N C.gates (wire_init N) (wire_init_length N) k hk
  rw [h, wire_gateAt C k hk]
  show a ∈ C.gates[k].inputs.foldr
    (fun w acc => (wire_run wire_suppStep (C.gates.take k) (wire_init N)).getD w ∅ ∪ acc) ∅ ↔ _
  rw [wire_mem_foldr]
  simp only [wire_support_take N C k (Nat.le_of_lt hk)]

-- The support of an input wire is that input alone.
theorem wire_support_input (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N) :
    support N C w = {⟨w, hw⟩} := by
  have h : support N C w = (wire_init N).getD w ∅ :=
    wire_run_getD_lt wire_suppStep ∅ C.gates (wire_init N) w
      (by rw [wire_init_length]; exact hw)
  rw [h]
  simp [wire_init, hw]

-- An input wire carries its input bit.
theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false := by
  unfold val
  rw [wire_wires]
  exact wire_run_getD_lt _ _ _ _ _ hi

-- Gate number `k` is wire `x.length + k`; it applies its operation to the wires it reads, and a
-- read of a wire that is not strictly earlier gives `false`.
theorem val_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    val C x (x.length + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < x.length + k then val C x i else false) := by
  have h : val C x (x.length + k)
      = wire_evalStep (wire_run wire_evalStep (C.gates.take k) x) C.gates[k] :=
    wire_run_gate wire_evalStep false x.length C.gates x rfl k hk
  rw [h, wire_gateAt C k hk]
  show C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
    (wire_run wire_evalStep (C.gates.take k) x).getD i false) = _
  congr 1
  apply List.map_congr_left
  intro i _
  exact wire_val_take C x k (Nat.le_of_lt hk) i

-- The support of a gate contains the support of every wire it reads (as read).
theorem support_gate (N : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (i : ℕ)
    (hi : i ∈ (gateAt C k).inputs) :
    operandSupport N C k i ⊆ support N C (N + k) := by
  intro a ha
  exact (wire_support_gate_iff N C k hk a).2 ⟨i, hi, ha⟩

-- A wire's value depends only on the inputs in its support.
theorem val_congr (N : ℕ) (C : Circuit) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w : ℕ) (h : ∀ i : Fin N, i ∈ support N C w → x.getD i.val false = y.getD i.val false) :
    val C x w = val C y w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w N with hw | hw
    · rw [val_input C x w (by omega), val_input C y w (by omega)]
      exact h ⟨w, hw⟩ (by rw [wire_support_input N C w hw]; exact Finset.mem_singleton_self _)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hw
      rcases Nat.lt_or_ge k C.gates.length with hk | hk
      · have e1 := val_gate C x k hk
        have e2 := val_gate C y k hk
        rw [hx] at e1
        rw [hy] at e2
        rw [e1, e2]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < N + k
        · simp only [hlt, ite_true]
          exact ih i hlt (fun j hj => h j ((wire_support_gate_iff N C k hk j).2
            ⟨i, hi, by unfold operandSupport; simp only [hlt, ite_true]; exact hj⟩))
        · simp only [hlt, ite_false]
      · rw [wire_val_out C x (N + k) (by omega), wire_val_out C y (N + k) (by omega)]

-- What gate number `k` reads from wire `i` on the input `x`: the wire's value if the wire is
-- strictly earlier than the gate, `false` otherwise.
def rd (C : Circuit) (x : List Bool) (k i : ℕ) : Bool :=
  if i < x.length + k then val C x i else false

-- The members `c` of the family of inputs `E` on which gate number `k` reads `true` from wire
-- `i`.
def trueOn {n : ℕ} (C : Circuit) (E : Fin n → List Bool) (k i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c => rd C (E c) k i = true

-- The conclusion of `pairing`, as one proposition in the gate number `k` and the member `a`.
def pair_Out {n : ℕ} (N : ℕ) (C : Circuit) (P : Finset (Fin N) → Prop) (x0 : List Bool)
    (E : Fin n → List Bool) (pick : Finset (Fin n) → Fin n) (k : ℕ) (a : Fin n) : Prop :=
  ∃ g, g ≤ k ∧ (gateAt C g).op = GateOp.or ∧ P (support N C (N + g)) ∧
      val C x0 (N + g) = false ∧
      pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)) ≠
        pick (trueOn C E g ((gateAt C g).inputs.getD 1 0)) ∧
      (a = pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)) ∨
        a = pick (trueOn C E g ((gateAt C g).inputs.getD 1 0))) ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)))) (N + k) = true ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 1 0)))) (N + k) = true ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)))) (N + g) = true ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 1 0)))) (N + g) = true

theorem pair_bool_false (b : Bool) (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

-- A read of a strictly earlier wire is the wire's value.
theorem pair_rd_lt (C : Circuit) (x : List Bool) (k i : ℕ) (h : i < x.length + k) :
    rd C x k i = val C x i := by
  unfold rd
  simp only [h, ↓reduceIte]

-- A read of a wire that is not strictly earlier is `false`.
theorem pair_rd_ge (C : Circuit) (x : List Bool) (k i : ℕ) (h : ¬ i < x.length + k) :
    rd C x k i = false := by
  unfold rd
  simp only [h, ↓reduceIte]

-- A read that is `true` comes from a strictly earlier wire that is `true`.
theorem pair_rd_true (C : Circuit) (x : List Bool) (k i : ℕ) (h : rd C x k i = true) :
    i < x.length + k ∧ val C x i = true := by
  by_cases hi : i < x.length + k
  · rw [pair_rd_lt C x k i hi] at h
    exact ⟨hi, h⟩
  · rw [pair_rd_ge C x k i hi] at h
    exact absurd h Bool.false_ne_true

-- The support of a strictly earlier wire, as read, is its support.
theorem pair_opSupp_lt (N : ℕ) (C : Circuit) (k i : ℕ) (h : i < N + k) :
    operandSupport N C k i = support N C i := by
  unfold operandSupport
  simp only [h, ↓reduceIte]

-- A read with empty support has the same value on all inputs of length `N`.
theorem pair_rd_const (N : ℕ) (C : Circuit) (k i : ℕ) (hs : operandSupport N C k i = ∅)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) : rd C x k i = rd C y k i := by
  by_cases hi : i < N + k
  · rw [pair_rd_lt C x k i (by rw [hx]; exact hi), pair_rd_lt C y k i (by rw [hy]; exact hi)]
    rw [pair_opSupp_lt N C k i hi] at hs
    apply val_congr N C x y hx hy i
    intro j hj
    rw [hs] at hj
    simp at hj
  · rw [pair_rd_ge C x k i (by rw [hx]; exact hi), pair_rd_ge C y k i (by rw [hy]; exact hi)]

theorem pair_mem_trueOn {n : ℕ} (C : Circuit) (E : Fin n → List Bool) (k i : ℕ) (c : Fin n) :
    c ∈ trueOn C E k i ↔ rd C (E c) k i = true := by
  unfold trueOn
  simp

theorem pair_gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

-- `val_gate` on an input of length `N`, the reads written with `rd`.
theorem pair_val_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) :
    val C x (N + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => rd C x k i) := by
  subst hx
  exact val_gate C x k hk

-- An OR gate is true exactly when one of its reads is.
theorem pair_or_iff (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) :
    val C x (N + k) = true ↔ ∃ i ∈ (gateAt C k).inputs, rd C x k i = true := by
  rw [pair_val_gate N C x hx k hk, hop]
  simp [GateOp.eval]

-- An AND gate is true exactly when all of its reads are.
theorem pair_and_iff (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
    val C x (N + k) = true ↔ ∀ i ∈ (gateAt C k).inputs, rd C x k i = true := by
  rw [pair_val_gate N C x hx k hk, hop]
  simp [GateOp.eval]

-- The conclusion passes from an earlier gate to a gate that is true wherever the earlier one
-- is.
theorem pair_Out_mono {n : ℕ} (N : ℕ) (C : Circuit) (P : Finset (Fin N) → Prop) (x0 : List Bool)
    (E : Fin n → List Bool) (pick : Finset (Fin n) → Fin n) (k0 k : ℕ) (a : Fin n)
    (hle : k0 ≤ k)
    (hmono : ∀ c, val C (E c) (N + k0) = true → val C (E c) (N + k) = true)
    (h : pair_Out N C P x0 E pick k0 a) : pair_Out N C P x0 E pick k a := by
  unfold pair_Out at h ⊢
  obtain ⟨g, hg, hop, hPg, h0g, hne, hor, h1, h2, h3, h4⟩ := h
  exact ⟨g, le_trans hg hle, hop, hPg, h0g, hne, hor, hmono _ h1, hmono _ h2, h3, h4⟩

-- An OR gate with two reads whose picked members differ is its own witness.
theorem pair_self {n : ℕ} (N : ℕ) (C : Circuit) (P : Finset (Fin N) → Prop) (x0 : List Bool)
    (E : Fin n → List Bool) (pick : Finset (Fin n) → Fin n) (k : ℕ) (a : Fin n) (i0 i1 : ℕ)
    (hop : (gateAt C k).op = GateOp.or) (hinp : (gateAt C k).inputs = [i0, i1])
    (hPk : P (support N C (N + k))) (h0 : val C x0 (N + k) = false)
    (hne : pick (trueOn C E k i0) ≠ pick (trueOn C E k i1))
    (hor : a = pick (trueOn C E k i0) ∨ a = pick (trueOn C E k i1))
    (h1 : val C (E (pick (trueOn C E k i0))) (N + k) = true)
    (h2 : val C (E (pick (trueOn C E k i1))) (N + k) = true) :
    pair_Out N C P x0 E pick k a := by
  have e0 : (gateAt C k).inputs.getD 0 0 = i0 := by rw [hinp]; rfl
  have e1 : (gateAt C k).inputs.getD 1 0 = i1 := by rw [hinp]; rfl
  unfold pair_Out
  refine ⟨k, le_refl k, hop, hPk, h0, ?_⟩
  rw [e0, e1]
  exact ⟨hne, hor, h1, h2, h1, h2⟩

-- Descent to a read: a read of gate `k` that is false on `x0`, true on two different members,
-- and below the gate on every member, is an earlier gate, and the induction hypothesis applies to
-- it.
theorem pair_descend {n : ℕ} (N : ℕ) (C : Circuit)
    (P : Finset (Fin N) → Prop) (hP : ∀ s t : Finset (Fin N), t ⊆ s → P s → P t)
    (x0 : List Bool) (E : Fin n → List Bool) (hx0 : x0.length = N) (hE : ∀ a, (E a).length = N)
    (hin : ∀ i, i < N → ∀ a b : Fin n,
      (E a).getD i false = true → (E b).getD i false = true → a = b)
    (pick : Finset (Fin n) → Fin n)
    (k : ℕ) (hk : k < C.gates.length) (hPk : P (support N C (N + k)))
    (ih : ∀ m, m < k → m < C.gates.length → P (support N C (N + m)) →
      val C x0 (N + m) = false → ∀ a b : Fin n, a ≠ b →
      val C (E a) (N + m) = true → val C (E b) (N + m) = true → pair_Out N C P x0 E pick m a)
    (i : ℕ) (hi : i ∈ (gateAt C k).inputs) (h0 : rd C x0 k i = false)
    (hup : ∀ c, rd C (E c) k i = true → val C (E c) (N + k) = true)
    (a b : Fin n) (hab : a ≠ b) (ha : rd C (E a) k i = true) (hb : rd C (E b) k i = true) :
    pair_Out N C P x0 E pick k a := by
  obtain ⟨hia, hva⟩ := pair_rd_true C (E a) k i ha
  obtain ⟨_, hvb⟩ := pair_rd_true C (E b) k i hb
  rw [hE a] at hia
  by_cases hiN : i < N
  · exfalso
    apply hab
    apply hin i hiN a b
    · exact (val_input C (E a) i (by rw [hE a]; exact hiN)).symm.trans hva
    · exact (val_input C (E b) i (by rw [hE b]; exact hiN)).symm.trans hvb
  · obtain ⟨m, rfl⟩ : ∃ m, i = N + m := ⟨i - N, by omega⟩
    have hmk : m < k := by omega
    have hPm : P (support N C (N + m)) := by
      have h1 := hP _ _ (support_gate N C k hk (N + m) hi) hPk
      rwa [pair_opSupp_lt N C k (N + m) hia] at h1
    have h0m : val C x0 (N + m) = false :=
      (pair_rd_lt C x0 k (N + m) (by rw [hx0]; exact hia)).symm.trans h0
    refine pair_Out_mono N C P x0 E pick m k a (le_of_lt hmk) ?_
      (ih m hmk (lt_trans hmk hk) hPm h0m a b hab hva hvb)
    intro c hc
    apply hup
    rw [pair_rd_lt C (E c) k (N + m) (by rw [hE c]; exact hia)]
    exact hc

-- `pairing`, with its conclusion written as `pair_Out`.
theorem pair_main {n : ℕ} (N : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (P : Finset (Fin N) → Prop) (hP : ∀ s t : Finset (Fin N), t ⊆ s → P s → P t)
    (x0 : List Bool) (E : Fin n → List Bool) (hx0 : x0.length = N) (hE : ∀ a, (E a).length = N)
    (hin : ∀ i, i < N → ∀ a b : Fin n,
      (E a).getD i false = true → (E b).getD i false = true → a = b)
    (hand : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and → ∀ i0 i1 : ℕ,
      (gateAt C k).inputs = [i0, i1] → P (operandSupport N C k i0) →
      P (operandSupport N C k i1) →
      operandSupport N C k i0 = ∅ ∨ operandSupport N C k i1 = ∅)
    (pick : Finset (Fin n) → Fin n) (hpick : ∀ s : Finset (Fin n), s.Nonempty → pick s ∈ s)
    (k : ℕ) (hk : k < C.gates.length) (hPk : P (support N C (N + k)))
    (h0 : val C x0 (N + k) = false) (a b : Fin n) (hab : a ≠ b)
    (ha : val C (E a) (N + k) = true) (hb : val C (E b) (N + k) = true) :
    pair_Out N C P x0 E pick k a := by
  revert hk hPk h0 a b
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hPk h0 a b hab ha hb
    have desc := pair_descend N C P hP x0 E hx0 hE hin pick k hk hPk ih
    have hf0 : ¬ val C x0 (N + k) = true := by
      rw [h0]
      exact Bool.false_ne_true
    obtain ⟨hop, hlen⟩ := hC _ (pair_gateAt_mem C k hk)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop
    -- an AND gate
    · have ha' := (pair_and_iff N C (E a) (hE a) k hk hop).mp ha
      have hb' := (pair_and_iff N C (E b) (hE b) k hk hop).mp hb
      rcases hinp : (gateAt C k).inputs with _ | ⟨i0, _ | ⟨i1, _ | ⟨i2, tl⟩⟩⟩
      -- no read: the gate is true on `x0`
      · exfalso
        apply hf0
        rw [pair_and_iff N C x0 hx0 k hk hop, hinp]
        intro i hi
        cases hi
      -- one read: a copy
      · have hm : i0 ∈ (gateAt C k).inputs := by rw [hinp]; simp
        have hall : ∀ x : List Bool, x.length = N → rd C x k i0 = true →
            val C x (N + k) = true := by
          intro x hx h
          rw [pair_and_iff N C x hx k hk hop, hinp]
          intro i hi
          rw [List.mem_singleton] at hi
          rw [hi]
          exact h
        exact desc i0 hm (pair_bool_false _ fun h => hf0 (hall x0 hx0 h))
          (fun c hc => hall (E c) (hE c) hc) a b hab (ha' i0 hm) (hb' i0 hm)
      -- two reads: one of them is constant
      · have hm0 : i0 ∈ (gateAt C k).inputs := by rw [hinp]; simp
        have hm1 : i1 ∈ (gateAt C k).inputs := by rw [hinp]; simp
        have hall : ∀ x : List Bool, x.length = N → rd C x k i0 = true →
            rd C x k i1 = true → val C x (N + k) = true := by
          intro x hx h h'
          rw [pair_and_iff N C x hx k hk hop, hinp]
          intro i hi
          rw [List.mem_cons, List.mem_singleton] at hi
          rcases hi with hi | hi
          · rw [hi]
            exact h
          · rw [hi]
            exact h'
        have hP0 : P (operandSupport N C k i0) := hP _ _ (support_gate N C k hk i0 hm0) hPk
        have hP1 : P (operandSupport N C k i1) := hP _ _ (support_gate N C k hk i1 hm1) hPk
        rcases hand k hk hop i0 i1 hinp hP0 hP1 with hs | hs
        · have hc : ∀ x : List Bool, x.length = N → rd C x k i0 = true := by
            intro x hx
            rw [pair_rd_const N C k i0 hs x (E a) hx (hE a)]
            exact ha' i0 hm0
          exact desc i1 hm1 (pair_bool_false _ fun h => hf0 (hall x0 hx0 (hc x0 hx0) h))
            (fun c h => hall (E c) (hE c) (hc _ (hE c)) h) a b hab (ha' i1 hm1) (hb' i1 hm1)
        · have hc : ∀ x : List Bool, x.length = N → rd C x k i1 = true := by
            intro x hx
            rw [pair_rd_const N C k i1 hs x (E a) hx (hE a)]
            exact ha' i1 hm1
          exact desc i0 hm0 (pair_bool_false _ fun h => hf0 (hall x0 hx0 h (hc x0 hx0)))
            (fun c h => hall (E c) (hE c) h (hc _ (hE c))) a b hab (ha' i0 hm0) (hb' i0 hm0)
      -- three or more reads: excluded
      · exfalso
        rw [hinp] at hlen
        simp only [List.length_cons] at hlen
        omega
    -- an OR gate
    · have hup : ∀ i, i ∈ (gateAt C k).inputs → ∀ x : List Bool, x.length = N →
          rd C x k i = true → val C x (N + k) = true :=
        fun i hi x hx h => (pair_or_iff N C x hx k hk hop).mpr ⟨i, hi, h⟩
      have desc' : ∀ i, i ∈ (gateAt C k).inputs → ∀ a' : Fin n, a ≠ a' →
          rd C (E a) k i = true → rd C (E a') k i = true → pair_Out N C P x0 E pick k a :=
        fun i hi a' hne h h' =>
          desc i hi (pair_bool_false _ fun h => hf0 (hup i hi x0 hx0 h))
            (fun c hc => hup i hi (E c) (hE c) hc) a a' hne h h'
      obtain ⟨ia, hia, hra⟩ := (pair_or_iff N C (E a) (hE a) k hk hop).mp ha
      obtain ⟨ib, hib, hrb⟩ := (pair_or_iff N C (E b) (hE b) k hk hop).mp hb
      rcases hinp : (gateAt C k).inputs with _ | ⟨i0, _ | ⟨i1, _ | ⟨i2, tl⟩⟩⟩
      -- no read: the gate is false
      · rw [hinp] at hia
        cases hia
      -- one read: a copy
      · rw [hinp, List.mem_singleton] at hia hib
        rw [hia] at hra
        rw [hib] at hrb
        exact desc' i0 (by rw [hinp]; simp) b hab hra hrb
      -- two reads
      · have hm0 : i0 ∈ (gateAt C k).inputs := by rw [hinp]; simp
        have hm1 : i1 ∈ (gateAt C k).inputs := by rw [hinp]; simp
        rw [hinp, List.mem_cons, List.mem_singleton] at hia hib
        have hA : rd C (E a) k i0 = true ∨ rd C (E a) k i1 = true := by
          rcases hia with h | h
          · left
            rw [← h]
            exact hra
          · right
            rw [← h]
            exact hra
        have hB : rd C (E b) k i0 = true ∨ rd C (E b) k i1 = true := by
          rcases hib with h | h
          · left
            rw [← h]
            exact hrb
          · right
            rw [← h]
            exact hrb
        by_cases hex0 : ∃ a' : Fin n, a ≠ a' ∧ rd C (E a) k i0 = true ∧ rd C (E a') k i0 = true
        · obtain ⟨a', hne, h, h'⟩ := hex0
          exact desc' i0 hm0 a' hne h h'
        by_cases hex1 : ∃ a' : Fin n, a ≠ a' ∧ rd C (E a) k i1 = true ∧ rd C (E a') k i1 = true
        · obtain ⟨a', hne, h, h'⟩ := hex1
          exact desc' i1 hm1 a' hne h h'
        have u0 : ∀ c : Fin n, rd C (E a) k i0 = true → rd C (E c) k i0 = true → c = a := by
          intro c h h'
          by_contra hne
          exact hex0 ⟨c, fun e => hne e.symm, h, h'⟩
        have u1 : ∀ c : Fin n, rd C (E a) k i1 = true → rd C (E c) k i1 = true → c = a := by
          intro c h h'
          by_contra hne
          exact hex1 ⟨c, fun e => hne e.symm, h, h'⟩
        have hval : ∀ i, i ∈ (gateAt C k).inputs → ∀ c : Fin n, c ∈ trueOn C E k i →
            val C (E c) (N + k) = true :=
          fun i hi c hc => hup i hi (E c) (hE c) ((pair_mem_trueOn C E k i c).mp hc)
        by_cases ha0 : rd C (E a) k i0 = true
        · by_cases ha1 : rd C (E a) k i1 = true
          · exfalso
            rcases hB with h | h
            · exact hab (u0 b ha0 h).symm
            · exact hab (u1 b ha1 h).symm
          · have hb1 : rd C (E b) k i1 = true := by
              rcases hB with h | h
              · exact absurd (u0 b ha0 h).symm hab
              · exact h
            have hp0 : pick (trueOn C E k i0) ∈ trueOn C E k i0 :=
              hpick _ ⟨a, (pair_mem_trueOn C E k i0 a).mpr ha0⟩
            have hp1 : pick (trueOn C E k i1) ∈ trueOn C E k i1 :=
              hpick _ ⟨b, (pair_mem_trueOn C E k i1 b).mpr hb1⟩
            have e0 : pick (trueOn C E k i0) = a :=
              u0 _ ha0 ((pair_mem_trueOn C E k i0 _).mp hp0)
            refine pair_self N C P x0 E pick k a i0 i1 hop hinp hPk h0 ?_ (Or.inl e0.symm)
              (hval i0 hm0 _ hp0) (hval i1 hm1 _ hp1)
            intro e
            apply ha1
            have h := (pair_mem_trueOn C E k i1 _).mp hp1
            rw [← e, e0] at h
            exact h
        · have ha1 : rd C (E a) k i1 = true := by
            rcases hA with h | h
            · exact absurd h ha0
            · exact h
          have hb0 : rd C (E b) k i0 = true := by
            rcases hB with h | h
            · exact h
            · exact absurd (u1 b ha1 h).symm hab
          have hp0 : pick (trueOn C E k i0) ∈ trueOn C E k i0 :=
            hpick _ ⟨b, (pair_mem_trueOn C E k i0 b).mpr hb0⟩
          have hp1 : pick (trueOn C E k i1) ∈ trueOn C E k i1 :=
            hpick _ ⟨a, (pair_mem_trueOn C E k i1 a).mpr ha1⟩
          have e1 : pick (trueOn C E k i1) = a :=
            u1 _ ha1 ((pair_mem_trueOn C E k i1 _).mp hp1)
          refine pair_self N C P x0 E pick k a i0 i1 hop hinp hPk h0 ?_ (Or.inr e1.symm)
            (hval i0 hm0 _ hp0) (hval i1 hm1 _ hp1)
          intro e
          apply ha0
          have h := (pair_mem_trueOn C E k i0 _).mp hp0
          rw [e, e1] at h
          exact h
      -- three or more reads: excluded
      · exfalso
        rw [hinp] at hlen
        simp only [List.length_cons] at hlen
        omega

-- PAIRING. `E` is a family of inputs on which every input wire is true at most once, `x0` an
-- input, `P` a property of supports that passes to subsets, and no AND gate reads two wires with
-- property `P` unless one of them has empty support. If gate `k` has a support with property `P`,
-- is false on `x0` and true on `E a` and on `E b` with `a ≠ b`, then some OR gate `g ≤ k` with a
-- support with property `P`, false on `x0`, has two different picked members, one from each of its
-- two reads, one of them is `a`, and gate `k` is true on both.
theorem pairing {n : ℕ} (N : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (P : Finset (Fin N) → Prop) (hP : ∀ s t : Finset (Fin N), t ⊆ s → P s → P t)
    (x0 : List Bool) (E : Fin n → List Bool) (hx0 : x0.length = N) (hE : ∀ a, (E a).length = N)
    (hin : ∀ i, i < N → ∀ a b : Fin n,
      (E a).getD i false = true → (E b).getD i false = true → a = b)
    (hand : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and → ∀ i0 i1 : ℕ,
      (gateAt C k).inputs = [i0, i1] → P (operandSupport N C k i0) →
      P (operandSupport N C k i1) →
      operandSupport N C k i0 = ∅ ∨ operandSupport N C k i1 = ∅)
    (pick : Finset (Fin n) → Fin n) (hpick : ∀ s : Finset (Fin n), s.Nonempty → pick s ∈ s)
    (k : ℕ) (hk : k < C.gates.length) (hPk : P (support N C (N + k)))
    (h0 : val C x0 (N + k) = false) (a b : Fin n) (hab : a ≠ b)
    (ha : val C (E a) (N + k) = true) (hb : val C (E b) (N + k) = true) :
    ∃ g, g ≤ k ∧ (gateAt C g).op = GateOp.or ∧ P (support N C (N + g)) ∧
      val C x0 (N + g) = false ∧
      pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)) ≠
        pick (trueOn C E g ((gateAt C g).inputs.getD 1 0)) ∧
      (a = pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)) ∨
        a = pick (trueOn C E g ((gateAt C g).inputs.getD 1 0))) ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)))) (N + k) = true ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 1 0)))) (N + k) = true ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 0 0)))) (N + g) = true ∧
      val C (E (pick (trueOn C E g ((gateAt C g).inputs.getD 1 0)))) (N + g) = true :=
  pair_main N C hC P hP x0 E hx0 hE hin hand pick hpick k hk hPk h0 a b hab ha hb

open PEqualNP.GenericRejection PEqualNP.CrossAnd

-- The inputs of the argument: no point and no line on, one point on, one line on, one point
-- and one line on.

-- The input with nothing on.
def e0 (n : ℕ) : List Bool := incidenceInput (∅ : Finset (Fin n)) (∅ : Finset (Fin n))

-- The input with only the point `a` on.
def ept (n : ℕ) (a : Fin n) : List Bool :=
  incidenceInput ({a} : Finset (Fin n)) (∅ : Finset (Fin n))

-- The input with only the line `b` on.
def eln (n : ℕ) (b : Fin n) : List Bool :=
  incidenceInput (∅ : Finset (Fin n)) ({b} : Finset (Fin n))

-- The input with only the point `a` and the line `b` on.
def epl {n : ℕ} (a b : Fin n) : List Bool :=
  incidenceInput ({a} : Finset (Fin n)) ({b} : Finset (Fin n))

theorem inc_length {n : ℕ} (X Y : Finset (Fin n)) : (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

-- A point bit of an incidence input.
theorem inc_getD_pt {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide ((⟨i, hi⟩ : Fin n) ∈ X) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

-- A line bit of an incidence input.
theorem inc_getD_ln {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (h1 : n ≤ i) (h2 : i < n + n) :
    (incidenceInput X Y).getD i false = decide ((⟨i - n, by omega⟩ : Fin n) ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
  have hl : i - n < n := by omega
  simp [List.getD_eq_getElem?_getD, hl]

theorem e0_length (n : ℕ) : (e0 n).length = n + n := inc_length _ _

theorem ept_length {n : ℕ} (a : Fin n) : (ept n a).length = n + n := inc_length _ _

theorem eln_length {n : ℕ} (b : Fin n) : (eln n b).length = n + n := inc_length _ _

theorem epl_length {n : ℕ} (a b : Fin n) : (epl a b).length = n + n := inc_length _ _

-- The marked side is the set of the line inputs.
theorem mem_lines {n : ℕ} (i : Fin (n + n)) :
    i ∈ Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n)) ↔ n ≤ i.val := by
  constructor
  · intro h
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp h
    show n ≤ n + a.val
    omega
  · intro h
    refine Finset.mem_map.mpr ⟨⟨i.val - n, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    show n + (i.val - n) = i.val
    omega

-- An input wire is true on at most one one-point input.
theorem ept_inj {n : ℕ} (i : ℕ) (hi : i < n + n) (a b : Fin n)
    (ha : (ept n a).getD i false = true) (hb : (ept n b).getD i false = true) : a = b := by
  unfold ept at ha hb
  by_cases h : i < n
  · rw [inc_getD_pt _ _ i h] at ha hb
    have ha' : (⟨i, h⟩ : Fin n) = a := by simpa using ha
    have hb' : (⟨i, h⟩ : Fin n) = b := by simpa using hb
    rw [← ha', ← hb']
  · rw [inc_getD_ln _ _ i (by omega) hi] at ha
    simp at ha

-- An input wire is true on at most one one-line input.
theorem eln_inj {n : ℕ} (i : ℕ) (hi : i < n + n) (a b : Fin n)
    (ha : (eln n a).getD i false = true) (hb : (eln n b).getD i false = true) : a = b := by
  unfold eln at ha hb
  by_cases h : i < n
  · rw [inc_getD_pt _ _ i h] at ha
    simp at ha
  · rw [inc_getD_ln _ _ i (by omega) hi] at ha hb
    have ha' : (⟨i - n, by omega⟩ : Fin n) = a := by simpa using ha
    have hb' : (⟨i - n, by omega⟩ : Fin n) = b := by simpa using hb
    rw [← ha', ← hb']

-- Reads.

theorem rd_true (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k i : ℕ)
    (h : rd C x k i = true) : i < N + k := by
  subst hx
  exact (pair_rd_true C x k i h).1

theorem rd_of_lt (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k i : ℕ)
    (hi : i < N + k) : rd C x k i = val C x i := by
  subst hx
  exact pair_rd_lt C x k i hi

-- A read depends only on the inputs in its support.
theorem rd_congr (N : ℕ) (C : Circuit) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (k i : ℕ)
    (h : ∀ j : Fin N, j ∈ operandSupport N C k i → x.getD j.val false = y.getD j.val false) :
    rd C x k i = rd C y k i := by
  by_cases hi : i < N + k
  · rw [rd_of_lt N C x hx k i hi, rd_of_lt N C y hy k i hi]
    refine val_congr N C x y hx hy i fun j hj => h j ?_
    rw [pair_opSupp_lt N C k i hi]
    exact hj
  · subst hx
    unfold rd
    rw [ite_eq_right hi, hy, ite_eq_right hi]

-- A wire with empty support is constant.
theorem val_const (N : ℕ) (C : Circuit) (w : ℕ) (h : support N C w = ∅)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) : val C x w = val C y w := by
  refine val_congr N C x y hx hy w fun j hj => ?_
  rw [h] at hj
  exact absurd hj (by simp)

-- A read whose support does not meet the line inputs depends only on the point bits.
theorem rd_pt {n : ℕ} (M : Finset (Fin (n + n))) (hM : ∀ i : Fin (n + n), i ∈ M ↔ n ≤ i.val)
    (C : Circuit) (k i : ℕ) (h : operandSupport (n + n) C k i ∩ M = ∅)
    (X Y Y' : Finset (Fin n)) :
    rd C (incidenceInput X Y) k i = rd C (incidenceInput X Y') k i := by
  refine rd_congr (n + n) C _ _ (inc_length X Y) (inc_length X Y') k i fun j hj => ?_
  have hjM : j ∉ M := fun hm => by
    have hmem : j ∈ operandSupport (n + n) C k i ∩ M := Finset.mem_inter.mpr ⟨hj, hm⟩
    rw [h] at hmem
    exact absurd hmem (by simp)
  have hlt : j.val < n := by
    by_contra hc
    exact hjM ((hM j).mpr (by omega))
  rw [inc_getD_pt X Y j.val hlt, inc_getD_pt X Y' j.val hlt]

-- A read whose support lies inside the line inputs depends only on the line bits.
theorem rd_ln {n : ℕ} (M : Finset (Fin (n + n))) (hM : ∀ i : Fin (n + n), i ∈ M ↔ n ≤ i.val)
    (C : Circuit) (k i : ℕ) (h : operandSupport (n + n) C k i \ M = ∅)
    (X X' Y : Finset (Fin n)) :
    rd C (incidenceInput X Y) k i = rd C (incidenceInput X' Y) k i := by
  refine rd_congr (n + n) C _ _ (inc_length X Y) (inc_length X' Y) k i fun j hj => ?_
  have hjM : j ∈ M := by
    by_contra hm
    have hmem : j ∈ operandSupport (n + n) C k i \ M := Finset.mem_sdiff.mpr ⟨hj, hm⟩
    rw [h] at hmem
    exact absurd hmem (by simp)
  have hge : n ≤ j.val := (hM j).mp hjM
  rw [inc_getD_ln X Y j.val hge j.isLt, inc_getD_ln X' Y j.val hge j.isLt]

theorem rd_pt' {n : ℕ} (M : Finset (Fin (n + n))) (hM : ∀ i : Fin (n + n), i ∈ M ↔ n ≤ i.val)
    (C : Circuit) (k i : ℕ) (h : operandSupport (n + n) C k i ∩ M = ∅) (a b : Fin n) :
    rd C (epl a b) k i = rd C (ept n a) k i ∧ rd C (eln n b) k i = rd C (e0 n) k i :=
  ⟨rd_pt M hM C k i h {a} {b} ∅, rd_pt M hM C k i h ∅ {b} ∅⟩

theorem rd_ln' {n : ℕ} (M : Finset (Fin (n + n))) (hM : ∀ i : Fin (n + n), i ∈ M ↔ n ≤ i.val)
    (C : Circuit) (k i : ℕ) (h : operandSupport (n + n) C k i \ M = ∅) (a b : Fin n) :
    rd C (epl a b) k i = rd C (eln n b) k i ∧ rd C (ept n a) k i = rd C (e0 n) k i :=
  ⟨rd_ln M hM C k i h {a} ∅ {b}, rd_ln M hM C k i h {a} ∅ ∅⟩

-- Sets of inputs.

theorem empty_of_pure {α : Type} [DecidableEq α] (s M : Finset α) (h1 : s ∩ M = ∅)
    (h2 : s \ M = ∅) : s = ∅ := by
  have h := Finset.sdiff_union_inter s M
  rw [h1, h2] at h
  simpa using h.symm

theorem inter_empty_mono {α : Type} [DecidableEq α] (M s t : Finset α) (hts : t ⊆ s)
    (hs : s ∩ M = ∅) : t ∩ M = ∅ := by
  apply Finset.subset_empty.mp
  rw [← hs]
  exact Finset.inter_subset_inter hts (Finset.Subset.refl M)

theorem sdiff_empty_mono {α : Type} [DecidableEq α] (M s t : Finset α) (hts : t ⊆ s)
    (hs : s \ M = ∅) : t \ M = ∅ := by
  apply Finset.subset_empty.mp
  rw [← hs]
  exact Finset.sdiff_subset_sdiff hts (Finset.Subset.refl M)

-- Gates.

theorem val_inc_input {n : ℕ} (C : Circuit) (X Y : Finset (Fin n)) (w : ℕ) (hw : w < n + n) :
    val C (incidenceInput X Y) w = (incidenceInput X Y).getD w false :=
  val_input C _ w (by rw [inc_length]; exact hw)

theorem gate_shape (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (k : ℕ)
    (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have h := hC _ (pair_gateAt_mem C k hk)
  exact ⟨by simpa using h.1, h.2⟩

theorem gate_and0 (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = []) : val C x (N + k) = true := by
  rw [pair_val_gate N C x hx k hk, hop, hin]
  simp [GateOp.eval]

theorem gate_and1 (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (u : ℕ)
    (hin : (gateAt C k).inputs = [u]) : val C x (N + k) = rd C x k u := by
  rw [pair_val_gate N C x hx k hk, hop, hin]
  simp [GateOp.eval]

theorem gate_and2 (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (u v : ℕ)
    (hin : (gateAt C k).inputs = [u, v]) :
    val C x (N + k) = (rd C x k u && rd C x k v) := by
  rw [pair_val_gate N C x hx k hk, hop, hin]
  simp [GateOp.eval]

-- An AND gate reading two wires that is not a cross AND: one of its reads misses the marked
-- side, and one of its reads lies inside it.
theorem not_cross (N : ℕ) (M : Finset (Fin N)) (C : Circuit)
    (hcross : ∀ k, k < C.gates.length → ¬ IsCrossAnd N M C k) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (u v : ℕ)
    (hin : (gateAt C k).inputs = [u, v]) :
    (operandSupport N C k u ∩ M = ∅ ∨ operandSupport N C k v ∩ M = ∅) ∧
      (operandSupport N C k u \ M = ∅ ∨ operandSupport N C k v \ M = ∅) := by
  have h0 : (gateAt C k).inputs.getD 0 0 = u := by rw [hin]; rfl
  have h1 : (gateAt C k).inputs.getD 1 0 = v := by rw [hin]; rfl
  have hl : (gateAt C k).inputs.length = 2 := by rw [hin]; rfl
  constructor
  · by_contra hc
    rw [not_or] at hc
    refine hcross k hk ⟨hop, hl, Or.inl ⟨?_, ?_⟩⟩
    · rw [h0]; exact Finset.nonempty_iff_ne_empty.mpr hc.1
    · rw [h1]; exact Finset.nonempty_iff_ne_empty.mpr hc.2
  · by_contra hc
    rw [not_or] at hc
    refine hcross k hk ⟨hop, hl, Or.inr ⟨?_, ?_⟩⟩
    · rw [h0]; exact Finset.nonempty_iff_ne_empty.mpr hc.1
    · rw [h1]; exact Finset.nonempty_iff_ne_empty.mpr hc.2

theorem no_cross (N : ℕ) (M : Finset (Fin N)) (C : Circuit) (h : crossCount N M C = 0) (k : ℕ)
    (hk : k < C.gates.length) : ¬ IsCrossAnd N M C k := by
  unfold crossCount at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  exact h (Finset.mem_range.mpr hk)

-- Step 1: a witness gate for each incidence.

-- The wire `w` is GOOD for the incidence `(p, l)`: true on the input `{p}, {l}`, false on the
-- inputs `{p}` and `{l}`, and true on an input `{a}, {b}` only if `a` is on `b`.
def Good {n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit) (p l : Fin n) (w : ℕ) : Prop :=
  val C (epl p l) w = true ∧ val C (ept n p) w = false ∧ val C (eln n l) w = false ∧
    ∀ a b : Fin n, val C (epl a b) w = true → a ∈ S b

-- A WITNESS for the incidence `(p, l)`: a good AND gate with exactly two reads, one missing the
-- marked side and the other inside it.
def HasWitness {n : ℕ} (M : Finset (Fin (n + n))) (S : Fin n → Finset (Fin n)) (C : Circuit)
    (p l : Fin n) : Prop :=
  ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ ∃ u v : ℕ,
    ((gateAt C j).inputs = [u, v] ∨ (gateAt C j).inputs = [v, u]) ∧
    operandSupport (n + n) C j u ∩ M = ∅ ∧ operandSupport (n + n) C j v \ M = ∅ ∧
    Good S C p l (n + n + j)

theorem good_output {n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hC : ComputesIncidence S C) (p l : Fin n) (hpl : p ∈ S l) : Good S C p l C.output := by
  have hv : ∀ X Y : Finset (Fin n),
      val C (incidenceInput X Y) C.output = incidenceFun S X Y := fun X Y => hC X Y
  refine ⟨?_, ?_, ?_, fun a b h => ?_⟩
  · unfold epl
    rw [hv]
    simp [incidenceFun, hpl]
  · unfold ept
    rw [hv]
    simp [incidenceFun]
  · unfold eln
    rw [hv]
    simp [incidenceFun]
  · unfold epl at h
    rw [hv] at h
    simpa [incidenceFun] using h

theorem good_not_input {n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit) (p l : Fin n) (w : ℕ)
    (hw : w < n + n) : ¬ Good S C p l w := by
  rintro ⟨h1, h2, h3, -⟩
  unfold epl at h1
  unfold ept at h2
  unfold eln at h3
  rw [val_inc_input C _ _ w hw] at h1 h2 h3
  by_cases h : w < n
  · rw [inc_getD_pt _ _ w h] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by simp)
  · rw [inc_getD_ln _ _ w (by omega) hw] at h1 h3
    rw [h1] at h3
    exact absurd h3 (by simp)

-- A read of a good gate that is true on `{p}, {l}` and below the gate on every input is a
-- good, strictly earlier wire.
theorem good_read {n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit) (p l : Fin n) (k i : ℕ)
    (hle : ∀ x : List Bool, x.length = n + n → rd C x k i = true → val C x (n + n + k) = true)
    (htrue : rd C (epl p l) k i = true) (hg : Good S C p l (n + n + k)) :
    i < n + n + k ∧ Good S C p l i := by
  have hi : i < n + n + k := rd_true (n + n) C _ (epl_length p l) k i htrue
  have hv : ∀ x : List Bool, x.length = n + n → val C x i = true →
      val C x (n + n + k) = true := fun x hx h =>
    hle x hx (by rw [rd_of_lt (n + n) C x hx k i hi]; exact h)
  obtain ⟨-, g2, g3, g4⟩ := hg
  refine ⟨hi, ?_, ?_, ?_, fun a b h => g4 a b (hv _ (epl_length a b) h)⟩
  · rw [← rd_of_lt (n + n) C _ (epl_length p l) k i hi]
    exact htrue
  · by_contra h
    rw [Bool.not_eq_false] at h
    rw [hv _ (ept_length p) h] at g2
    exact absurd g2 (by simp)
  · by_contra h
    rw [Bool.not_eq_false] at h
    rw [hv _ (eln_length l) h] at g3
    exact absurd g3 (by simp)

-- Step 1. Every good wire yields a witness.
theorem witness {n : ℕ} (M : Finset (Fin (n + n))) (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hC2 : PEqualNP.MetaComplexity.Monotone2 C)
    (hcross : ∀ k, k < C.gates.length → ¬ IsCrossAnd (n + n) M C k) (p l : Fin n) (w : ℕ)
    (hg : Good S C p l w) : HasWitness M S C p l := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n + n
    · exact absurd hg (good_not_input S C p l w hw)
    obtain ⟨k, rfl⟩ : ∃ k, w = n + n + k := ⟨w - (n + n), by omega⟩
    have g1 : val C (epl p l) (n + n + k) = true := hg.1
    have g2 : val C (ept n p) (n + n + k) = false := hg.2.1
    by_cases hk : k < C.gates.length
    swap
    · rw [wire_val_out C (epl p l) (n + n + k) (by rw [epl_length]; omega)] at g1
      exact absurd g1 (by simp)
    have hred : ∀ i : ℕ,
        (∀ x : List Bool, x.length = n + n → rd C x k i = true →
          val C x (n + n + k) = true) →
        rd C (epl p l) k i = true → HasWitness M S C p l := by
      intro i hle htrue
      obtain ⟨hi, hgi⟩ := good_read S C p l k i hle htrue hg
      exact ih i hi hgi
    obtain ⟨hop, hlen⟩ := gate_shape C hC2 k hk
    rcases hop with hop | hop
    · rcases hin : (gateAt C k).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨t, rest⟩⟩⟩
      · rw [gate_and0 (n + n) C _ (ept_length p) k hk hop hin] at g2
        exact absurd g2 (by simp)
      · have hgv : ∀ x : List Bool, x.length = n + n → val C x (n + n + k) = rd C x k u :=
          fun x hx => gate_and1 (n + n) C x hx k hk hop u hin
        refine hred u (fun x hx h => by rw [hgv x hx]; exact h) ?_
        rw [← hgv _ (epl_length p l)]
        exact g1
      · have hgv : ∀ x : List Bool, x.length = n + n →
            val C x (n + n + k) = (rd C x k u && rd C x k v) :=
          fun x hx => gate_and2 (n + n) C x hx k hk hop u v hin
        have hpl := g1
        rw [hgv _ (epl_length p l), Bool.and_eq_true] at hpl
        obtain ⟨hu, hv⟩ := hpl
        obtain ⟨hA, hB⟩ := not_cross (n + n) M C hcross k hk hop u v hin
        have hcu : operandSupport (n + n) C k u = ∅ → HasWitness M S C p l := by
          intro he
          have hall : ∀ x : List Bool, x.length = n + n → rd C x k u = true := fun x hx => by
            rw [pair_rd_const (n + n) C k u he x (epl p l) hx (epl_length p l)]
            exact hu
          exact hred v (fun x hx h => by simp [hgv x hx, hall x hx, h]) hv
        have hcv : operandSupport (n + n) C k v = ∅ → HasWitness M S C p l := by
          intro he
          have hall : ∀ x : List Bool, x.length = n + n → rd C x k v = true := fun x hx => by
            rw [pair_rd_const (n + n) C k v he x (epl p l) hx (epl_length p l)]
            exact hv
          exact hred u (fun x hx h => by simp [hgv x hx, hall x hx, h]) hu
        rcases hA with hA | hA <;> rcases hB with hB | hB
        · exact hcu (empty_of_pure _ _ hA hB)
        · exact ⟨k, hk, hop, u, v, Or.inl hin, hA, hB, hg⟩
        · exact ⟨k, hk, hop, v, u, Or.inr hin, hA, hB, hg⟩
        · exact hcv (empty_of_pure _ _ hA hB)
      · simp only [hin, List.length_cons] at hlen
        omega
    · have hor : ∀ x : List Bool, x.length = n + n →
          (val C x (n + n + k) = true ↔ ∃ i ∈ (gateAt C k).inputs, rd C x k i = true) :=
        fun x hx => pair_or_iff (n + n) C x hx k hk hop
      obtain ⟨i, hi, hti⟩ := (hor _ (epl_length p l)).mp g1
      exact hred i (fun x hx h => (hor x hx).mpr ⟨i, hi, h⟩) hti

-- Step 2: the labels.

-- A chosen member of a nonempty set of indices (index `0` for the empty set).
noncomputable def pick {n : ℕ} (h : 0 < n) (s : Finset (Fin n)) : Fin n :=
  if hs : s.Nonempty then Classical.choose hs else ⟨0, h⟩

theorem pick_mem {n : ℕ} (h : 0 < n) (s : Finset (Fin n)) (hs : s.Nonempty) : pick h s ∈ s := by
  unfold pick
  rw [dite_eq_left hs]
  exact Classical.choose_spec hs

open Classical in
-- The tag of gate `g`: `0` for an AND gate, `1` for another gate whose support misses the
-- marked side, `2` otherwise.
noncomputable def lab_tag {n : ℕ} (M : Finset (Fin (n + n))) (C : Circuit) (g : ℕ) : Fin 3 :=
  if (gateAt C g).op = GateOp.and then 0
  else if support (n + n) C (n + n + g) ∩ M = ∅ then 1 else 2

open Classical in
-- The first label of gate `g`.
noncomputable def lab8 {n : ℕ} (hn : 0 < n) (M : Finset (Fin (n + n))) (C : Circuit) (g : ℕ) :
    Fin n :=
  if (gateAt C g).op = GateOp.and then
    pick hn (trueOn C (ept n) g ((gateAt C g).inputs.getD 0 0) ∪
      trueOn C (ept n) g ((gateAt C g).inputs.getD 1 0))
  else if support (n + n) C (n + n + g) ∩ M = ∅ then
    pick hn (trueOn C (ept n) g ((gateAt C g).inputs.getD 0 0))
  else pick hn (trueOn C (eln n) g ((gateAt C g).inputs.getD 0 0))

open Classical in
-- The second label of gate `g`.
noncomputable def lab9 {n : ℕ} (hn : 0 < n) (M : Finset (Fin (n + n))) (C : Circuit) (g : ℕ) :
    Fin n :=
  if (gateAt C g).op = GateOp.and then
    pick hn (trueOn C (eln n) g ((gateAt C g).inputs.getD 0 0) ∪
      trueOn C (eln n) g ((gateAt C g).inputs.getD 1 0))
  else if support (n + n) C (n + n + g) ∩ M = ∅ then
    pick hn (trueOn C (ept n) g ((gateAt C g).inputs.getD 1 0))
  else pick hn (trueOn C (eln n) g ((gateAt C g).inputs.getD 1 0))

theorem lab_and {n : ℕ} (hn : 0 < n) (M : Finset (Fin (n + n))) (C : Circuit) (g : ℕ)
    (hop : (gateAt C g).op = GateOp.and) :
    lab_tag M C g = 0 ∧
      lab8 hn M C g = pick hn (trueOn C (ept n) g ((gateAt C g).inputs.getD 0 0) ∪
        trueOn C (ept n) g ((gateAt C g).inputs.getD 1 0)) ∧
      lab9 hn M C g = pick hn (trueOn C (eln n) g ((gateAt C g).inputs.getD 0 0) ∪
        trueOn C (eln n) g ((gateAt C g).inputs.getD 1 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold lab_tag
    rw [ite_eq_left hop]
  · unfold lab8
    rw [ite_eq_left hop]
  · unfold lab9
    rw [ite_eq_left hop]

theorem lab_pt {n : ℕ} (hn : 0 < n) (M : Finset (Fin (n + n))) (C : Circuit) (g : ℕ)
    (hop : (gateAt C g).op = GateOp.or) (h : support (n + n) C (n + n + g) ∩ M = ∅) :
    lab_tag M C g = 1 ∧
      lab8 hn M C g = pick hn (trueOn C (ept n) g ((gateAt C g).inputs.getD 0 0)) ∧
      lab9 hn M C g = pick hn (trueOn C (ept n) g ((gateAt C g).inputs.getD 1 0)) := by
  have hna : ¬ (gateAt C g).op = GateOp.and := by
    intro h'
    rw [hop] at h'
    cases h'
  refine ⟨?_, ?_, ?_⟩
  · unfold lab_tag
    rw [ite_eq_right hna, ite_eq_left h]
  · unfold lab8
    rw [ite_eq_right hna, ite_eq_left h]
  · unfold lab9
    rw [ite_eq_right hna, ite_eq_left h]

theorem lab_ln {n : ℕ} (hn : 0 < n) (M : Finset (Fin (n + n))) (C : Circuit) (g : ℕ)
    (hop : (gateAt C g).op = GateOp.or) (h : ¬ support (n + n) C (n + n + g) ∩ M = ∅) :
    lab_tag M C g = 2 ∧
      lab8 hn M C g = pick hn (trueOn C (eln n) g ((gateAt C g).inputs.getD 0 0)) ∧
      lab9 hn M C g = pick hn (trueOn C (eln n) g ((gateAt C g).inputs.getD 1 0)) := by
  have hna : ¬ (gateAt C g).op = GateOp.and := by
    intro h'
    rw [hop] at h'
    cases h'
  refine ⟨?_, ?_, ?_⟩
  · unfold lab_tag
    rw [ite_eq_right hna, ite_eq_right h]
  · unfold lab8
    rw [ite_eq_right hna, ite_eq_right h]
  · unfold lab9
    rw [ite_eq_right hna, ite_eq_right h]

-- Step 3: every incidence is covered.

-- Step 3. An incidence with a witness gate is covered by some gate, with its labels.
theorem cover {n : ℕ} (hn : 0 < n) (M : Finset (Fin (n + n)))
    (hM : ∀ i : Fin (n + n), i ∈ M ↔ n ≤ i.val) (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hC2 : PEqualNP.MetaComplexity.Monotone2 C)
    (hcross : ∀ k, k < C.gates.length → ¬ IsCrossAnd (n + n) M C k) (p l : Fin n)
    (hw : HasWitness M S C p l) :
    ∃ g, g < C.gates.length ∧
      (lab_tag M C g = 0 ∧ p = lab8 hn M C g ∧ l = lab9 hn M C g ∨
        lab_tag M C g = 1 ∧ lab8 hn M C g ≠ lab9 hn M C g ∧
          (p = lab8 hn M C g ∨ p = lab9 hn M C g) ∧
          lab8 hn M C g ∈ S l ∧ lab9 hn M C g ∈ S l ∨
        lab_tag M C g = 2 ∧ lab8 hn M C g ≠ lab9 hn M C g ∧
          (l = lab8 hn M C g ∨ l = lab9 hn M C g) ∧
          p ∈ S (lab8 hn M C g) ∧ p ∈ S (lab9 hn M C g)) := by
  obtain ⟨j, hj, hop, u, v, hin, hu, hv, hg⟩ := hw
  have hgate : ∀ x : List Bool, x.length = n + n →
      val C x (n + n + j) = (rd C x j u && rd C x j v) := by
    intro x hx
    rcases hin with hin | hin
    · exact gate_and2 (n + n) C x hx j hj hop u v hin
    · rw [gate_and2 (n + n) C x hx j hj hop v u hin, Bool.and_comm]
  obtain ⟨g1, g2, g3, g4⟩ := hg
  have hpu := rd_pt' M hM C j u hu
  have hlv := rd_ln' M hM C j v hv
  rw [hgate _ (epl_length p l), Bool.and_eq_true, (hpu p l).1, (hlv p l).1] at g1
  obtain ⟨F1, F2⟩ := g1
  rw [hgate _ (ept_length p), F1, Bool.true_and, (hlv p l).2] at g2
  rw [hgate _ (eln_length l), F2, Bool.and_true, (hpu p l).2] at g3
  have rect : ∀ a b : Fin n, rd C (ept n a) j u = true → rd C (eln n b) j v = true →
      a ∈ S b := by
    intro a b ha hb
    apply g4 a b
    rw [hgate _ (epl_length a b), (hpu a b).1, (hlv a b).1, ha, hb]
    simp
  have hul : u < n + n + j := rd_true (n + n) C _ (ept_length p) j u F1
  have hvl : v < n + n + j := rd_true (n + n) C _ (eln_length l) j v F2
  by_cases h1 : ∃ c : Fin n, c ≠ p ∧ rd C (ept n c) j u = true
  -- the point-pure read is true on two points: a pair of points on the line `l`
  · obtain ⟨c, hcp, hc⟩ := h1
    have hun : n + n ≤ u := by
      by_contra hlt
      rw [not_le] at hlt
      have e1 : (ept n p).getD u false = true := by
        rw [← val_input C (ept n p) u (by rw [ept_length]; exact hlt),
          ← rd_of_lt (n + n) C _ (ept_length p) j u hul]
        exact F1
      have e2 : (ept n c).getD u false = true := by
        rw [← val_input C (ept n c) u (by rw [ept_length]; exact hlt),
          ← rd_of_lt (n + n) C _ (ept_length c) j u hul]
        exact hc
      exact hcp (ept_inj u hlt c p e2 e1)
    obtain ⟨k, rfl⟩ : ∃ k, u = n + n + k := ⟨u - (n + n), by omega⟩
    have hPk : support (n + n) C (n + n + k) ∩ M = ∅ := by
      rw [← pair_opSupp_lt (n + n) C j (n + n + k) hul]
      exact hu
    have h0 : val C (e0 n) (n + n + k) = false := by
      rw [← rd_of_lt (n + n) C _ (e0_length n) j (n + n + k) hul]
      exact g3
    have ha : val C (ept n p) (n + n + k) = true := by
      rw [← rd_of_lt (n + n) C _ (ept_length p) j (n + n + k) hul]
      exact F1
    have hb : val C (ept n c) (n + n + k) = true := by
      rw [← rd_of_lt (n + n) C _ (ept_length c) j (n + n + k) hul]
      exact hc
    obtain ⟨g, hgk, hgor, hgP, -, hne, hor, hk1, hk2, -, -⟩ :=
      pairing (n + n) C hC2 (fun s => s ∩ M = ∅)
        (fun s t hts hs => inter_empty_mono M s t hts hs) (e0 n) (ept n) (e0_length n)
        (fun a => ept_length a) (fun i hi a b => ept_inj i hi a b)
        (fun k' hk' hop' i0 i1 hin' h0' h1' => by
          rcases (not_cross (n + n) M C hcross k' hk' hop' i0 i1 hin').2 with h | h
          · exact Or.inl (empty_of_pure _ _ h0' h)
          · exact Or.inr (empty_of_pure _ _ h1' h))
        (pick hn) (pick_mem hn) k (by omega) hPk h0 p c (Ne.symm hcp) ha hb
    have hgP' : support (n + n) C (n + n + g) ∩ M = ∅ := hgP
    obtain ⟨t1, t8, t9⟩ := lab_pt hn M C g hgor hgP'
    refine ⟨g, by omega, Or.inr (Or.inl ⟨t1, ?_, ?_, ?_, ?_⟩)⟩
    · rw [t8, t9]
      exact hne
    · rw [t8, t9]
      exact hor
    · rw [t8]
      exact rect _ l
        (by rw [rd_of_lt (n + n) C _ (ept_length _) j (n + n + k) hul]; exact hk1) F2
    · rw [t9]
      exact rect _ l
        (by rw [rd_of_lt (n + n) C _ (ept_length _) j (n + n + k) hul]; exact hk2) F2
  by_cases h2 : ∃ d : Fin n, d ≠ l ∧ rd C (eln n d) j v = true
  -- the line-pure read is true on two lines: a pair of lines through the point `p`
  · obtain ⟨d, hdl, hd⟩ := h2
    have hvn : n + n ≤ v := by
      by_contra hlt
      rw [not_le] at hlt
      have e1 : (eln n l).getD v false = true := by
        rw [← val_input C (eln n l) v (by rw [eln_length]; exact hlt),
          ← rd_of_lt (n + n) C _ (eln_length l) j v hvl]
        exact F2
      have e2 : (eln n d).getD v false = true := by
        rw [← val_input C (eln n d) v (by rw [eln_length]; exact hlt),
          ← rd_of_lt (n + n) C _ (eln_length d) j v hvl]
        exact hd
      exact hdl (eln_inj v hlt d l e2 e1)
    obtain ⟨k, rfl⟩ : ∃ k, v = n + n + k := ⟨v - (n + n), by omega⟩
    have hPk : support (n + n) C (n + n + k) \ M = ∅ := by
      rw [← pair_opSupp_lt (n + n) C j (n + n + k) hvl]
      exact hv
    have h0 : val C (e0 n) (n + n + k) = false := by
      rw [← rd_of_lt (n + n) C _ (e0_length n) j (n + n + k) hvl]
      exact g2
    have ha : val C (eln n l) (n + n + k) = true := by
      rw [← rd_of_lt (n + n) C _ (eln_length l) j (n + n + k) hvl]
      exact F2
    have hb : val C (eln n d) (n + n + k) = true := by
      rw [← rd_of_lt (n + n) C _ (eln_length d) j (n + n + k) hvl]
      exact hd
    obtain ⟨g, hgk, hgor, hgP, hg0, hne, hor, hk1, hk2, hg1, -⟩ :=
      pairing (n + n) C hC2 (fun s => s \ M = ∅)
        (fun s t hts hs => sdiff_empty_mono M s t hts hs) (e0 n) (eln n) (e0_length n)
        (fun b => eln_length b) (fun i hi a b => eln_inj i hi a b)
        (fun k' hk' hop' i0 i1 hin' h0' h1' => by
          rcases (not_cross (n + n) M C hcross k' hk' hop' i0 i1 hin').1 with h | h
          · exact Or.inl (empty_of_pure _ _ h h0')
          · exact Or.inr (empty_of_pure _ _ h h1'))
        (pick hn) (pick_mem hn) k (by omega) hPk h0 l d (Ne.symm hdl) ha hb
    have hgP' : support (n + n) C (n + n + g) \ M = ∅ := hgP
    have hnI : ¬ support (n + n) C (n + n + g) ∩ M = ∅ := by
      intro hI
      have he := empty_of_pure _ _ hI hgP'
      rw [val_const (n + n) C (n + n + g) he _ (e0 n) (eln_length _) (e0_length n), hg0] at hg1
      exact absurd hg1 (by simp)
    obtain ⟨t2, t8, t9⟩ := lab_ln hn M C g hgor hnI
    refine ⟨g, by omega, Or.inr (Or.inr ⟨t2, ?_, ?_, ?_, ?_⟩)⟩
    · rw [t8, t9]
      exact hne
    · rw [t8, t9]
      exact hor
    · rw [t8]
      exact rect p _ F1
        (by rw [rd_of_lt (n + n) C _ (eln_length _) j (n + n + k) hvl]; exact hk1)
    · rw [t9]
      exact rect p _ F1
        (by rw [rd_of_lt (n + n) C _ (eln_length _) j (n + n + k) hvl]; exact hk2)
  -- each read is true on one member only: the witness gate itself carries the pair `(p, l)`
  have hPu : trueOn C (ept n) j u = {p} := by
    ext c
    rw [pair_mem_trueOn, Finset.mem_singleton]
    constructor
    · intro hc
      by_contra hne
      exact h1 ⟨c, hne, hc⟩
    · intro hc
      rw [hc]
      exact F1
  have hPv : trueOn C (ept n) j v = ∅ := by
    ext c
    rw [pair_mem_trueOn, (hlv c l).2, g2]
    simp
  have hLv : trueOn C (eln n) j v = {l} := by
    ext d
    rw [pair_mem_trueOn, Finset.mem_singleton]
    constructor
    · intro hd
      by_contra hne
      exact h2 ⟨d, hne, hd⟩
    · intro hd
      rw [hd]
      exact F2
  have hLu : trueOn C (eln n) j u = ∅ := by
    ext d
    rw [pair_mem_trueOn, (hpu p d).2, g3]
    simp
  have hr : ((gateAt C j).inputs.getD 0 0 = u ∧ (gateAt C j).inputs.getD 1 0 = v) ∨
      ((gateAt C j).inputs.getD 0 0 = v ∧ (gateAt C j).inputs.getD 1 0 = u) := by
    rcases hin with hin | hin
    · left
      rw [hin]
      exact ⟨rfl, rfl⟩
    · right
      rw [hin]
      exact ⟨rfl, rfl⟩
  obtain ⟨t0, t8, t9⟩ := lab_and hn M C j hop
  have h8 : lab8 hn M C j = p := by
    have hU : trueOn C (ept n) j ((gateAt C j).inputs.getD 0 0) ∪
        trueOn C (ept n) j ((gateAt C j).inputs.getD 1 0) = {p} := by
      rcases hr with ⟨q0, q1⟩ | ⟨q0, q1⟩
      · rw [q0, q1, hPu, hPv, Finset.union_empty]
      · rw [q0, q1, hPu, hPv, Finset.empty_union]
    rw [t8, hU]
    exact Finset.mem_singleton.mp (pick_mem hn {p} (Finset.singleton_nonempty p))
  have h9 : lab9 hn M C j = l := by
    have hU : trueOn C (eln n) j ((gateAt C j).inputs.getD 0 0) ∪
        trueOn C (eln n) j ((gateAt C j).inputs.getD 1 0) = {l} := by
      rcases hr with ⟨q0, q1⟩ | ⟨q0, q1⟩
      · rw [q0, q1, hLu, hLv, Finset.empty_union]
      · rw [q0, q1, hLu, hLv, Finset.union_empty]
    rw [t9, hU]
    exact Finset.mem_singleton.mp (pick_mem hn {l} (Finset.singleton_nonempty l))
  exact ⟨j, hj, Or.inl ⟨t0, h8.symm, h9.symm⟩⟩

-- The statement, with the labels of Step 2.
theorem main {n : ℕ} (S : Fin n → Finset (Fin n)) (C : Circuit) (hn : 0 < n)
    (hC2 : PEqualNP.MetaComplexity.Monotone2 C) (hCI : ComputesIncidence S C)
    (hcc : crossCount (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C = 0) :
    ∃ (x8 : Fin C.size → Fin n) (x9 : Fin C.size → Fin n) (x10 : Fin C.size → Fin 3),
      ∀ p l : Fin n, p ∈ S l → ∃ g : Fin C.size,
        x10 g = 0 ∧ p = x8 g ∧ l = x9 g ∨
        x10 g = 1 ∧ x8 g ≠ x9 g ∧ (p = x8 g ∨ p = x9 g) ∧ x8 g ∈ S l ∧ x9 g ∈ S l ∨
        x10 g = 2 ∧ x8 g ≠ x9 g ∧ (l = x8 g ∨ l = x9 g) ∧ p ∈ S (x8 g) ∧ p ∈ S (x9 g) := by
  have hM : ∀ i : Fin (n + n),
      i ∈ Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n)) ↔ n ≤ i.val := mem_lines
  generalize Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n)) = M at hM hcc
  have hcross := no_cross (n + n) M C hcc
  refine ⟨fun g => lab8 hn M C g.val, fun g => lab9 hn M C g.val, fun g => lab_tag M C g.val,
    fun p l hpl => ?_⟩
  obtain ⟨g, hg, h⟩ := cover hn M hM S C hC2 hcross p l
    (witness M S C hC2 hcross p l C.output (good_output S C hCI p l hpl))
  exact ⟨⟨g, hg⟩, h⟩

end PEqualNP.Outside.L_meta_4592

theorem PEqualNP.Outside.L_meta_4592 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.GenericRejection.ComputesIncidence x2 x3 → PEqualNP.CrossAnd.crossCount (x1 + x1) (Finset.map (Fin.natAddEmb x1) Finset.univ) x3 = (0 : ℕ) → ∃ (x8 : Fin x3.size → Fin x1) (x9 : Fin x3.size → Fin x1) (x10 : Fin x3.size → Fin (3 : ℕ)), ∀ (x11 x12 : Fin x1), x11 ∈ x2 x12 → ∃ (x14 : Fin x3.size), x10 x14 = (0 : Fin (3 : ℕ)) ∧ x11 = x8 x14 ∧ x12 = x9 x14 ∨ x10 x14 = (1 : Fin (3 : ℕ)) ∧ x8 x14 ≠ x9 x14 ∧ (x11 = x8 x14 ∨ x11 = x9 x14) ∧ x8 x14 ∈ x2 x12 ∧ x9 x14 ∈ x2 x12 ∨ x10 x14 = (2 : Fin (3 : ℕ)) ∧ x8 x14 ≠ x9 x14 ∧ (x12 = x8 x14 ∨ x12 = x9 x14) ∧ x11 ∈ x2 (x8 x14) ∧ x11 ∈ x2 (x9 x14) := by
  intro x1 x2 x3 h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_4592.main x2 x3 h1 h2 h3 h4
