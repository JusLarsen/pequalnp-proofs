import Mathlib
import PEqualNP.Defs
-- Rows are the 64 assignments of the 6 inputs; a wire is the number whose binary digit r is the
-- value of the wire on row r (tab is the table of the function itself, ALL the constant true).
-- A set of tables is Good when every true row of tab differs from every false row on some
-- member, that is, when the function is determined by the set. The set of the 6 input tables
-- is the only Good set of non-constant input tables (nec).
-- If a Good set holds the table c of a gate, replacing c by the one or two tables the gate
-- reads gives a Good set again. So every Good set G of non-constant tables that exist after
-- j gates has 6 ≤ |G| + j, and the family fam lists, with a level, every set that can occur
-- with |G| + j = 6 + level for a level below 3 (Jn). The family is closed under one gate
-- (Clos): the table of an AND or OR gate that takes the place of both, of one, or of none of
-- the two tables it reads keeps the level, raises it by one, or raises it by two; the table
-- of a NOT gate that takes or does not take the place of the table it reads raises it by one
-- or by two. The output of a circuit with j gates is a Good set of one table, so
-- 6 + 3 ≤ 1 + j unless fam holds a one-element set, and it holds none (OkEntry).
-- The kernel checks the closure on sorted lists (ok0, ok1, ...); the family itself was
-- found by a search program and is only checked here.
-- The shape of the link from circuits to tables (Inv, getD_snoc, gate_vec, inv_step, inv0)
-- and of the induction over the gate list in main follows L_meta_5471.lean (PR 11305,
-- willakone).

namespace PEqualNP.Outside.L_meta_7285
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev ALL : ℕ := 18446744073709551615

theorem all_bit : ∀ p : Fin 64, ALL.testBit p = true := by decide +kernel

def nc (pool : List ℕ) : List ℕ := pool.filter (fun a => decide (a ≠ 0) && decide (a ≠ ALL))

theorem mem_nc (pool : List ℕ) (a : ℕ) : a ∈ nc pool ↔ a ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL := by
  simp [nc, List.mem_filter]

def cand (pool : List ℕ) : List ℕ :=
  pool ++ ((nc pool).map (fun a => ALL ^^^ a) ++
    (nc pool).flatMap (fun a => (nc pool).flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 64 → List Bool) : Prop :=
  0 ∈ pool ∧ ALL ∈ pool ∧ ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 64, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem cand_not (pool : List ℕ) (h0 : 0 ∈ pool) (hA : ALL ∈ pool) (m : ℕ) (hm : m ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = !m.testBit p := by
  by_cases e0 : m = 0
  · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [e0, all_bit p]; simp⟩
  · by_cases eA : m = ALL
    · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [eA, all_bit p]; simp⟩
    · refine ⟨ALL ^^^ m, List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨m, (mem_nc pool m).mpr ⟨hm, e0, eA⟩, rfl⟩)), fun p => ?_⟩
      rw [Nat.testBit_xor, all_bit p]
      simp

theorem cand_and (pool : List ℕ) (h0 : 0 ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = (ma.testBit p && mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma &&& mb, ?_, fun p => Nat.testBit_and ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem cand_or (pool : List ℕ) (hA : ALL ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = (ma.testBit p || mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma ||| mb, ?_, fun p => Nat.testBit_or ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem gate_vec (pool : List ℕ) (ws : Fin 64 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ cand pool, ∀ p : Fin 64,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨h0, hA, hw⟩ := h
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
    · exact ⟨0, List.mem_append_left _ h0, fun p => by simp [GateOp.eval]⟩
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    rcases hop with rfl | rfl | rfl
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    obtain ⟨mb, hmb, hb⟩ := hw b
    rcases hop with rfl | rfl | rfl
    · obtain ⟨c, hc, hcv⟩ := cand_and pool h0 ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_or pool hA ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 64 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 64 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 64, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  obtain ⟨h0, hA, hw⟩ := hI
  refine ⟨hsub 0 h0, hsub ALL hA, fun i => ?_⟩
  obtain ⟨m, hm, hmb⟩ := hw i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

def pool0 : List ℕ := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 0, ALL]

def X (p : Fin 64) : List Bool := List.ofFn (fun i : Fin 6 => p.val.testBit i.val)

theorem X_len (p : Fin 64) : (X p).length = 6 := by simp [X]

theorem inv0 : Inv pool0 X := by
  refine ⟨by decide, by decide, fun i => ?_⟩
  by_cases hi : i < 6
  · have key : ∀ j : Fin 6, ∀ p : Fin 64,
        (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide +kernel
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by decide, fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

abbrev Good (T : ℕ) (G : Finset ℕ) : Prop :=
  ∀ p q : Fin 64, T.testBit p = true → T.testBit q = false →
    ∃ w ∈ G, w.testBit p ≠ w.testBit q

theorem good_mono (T : ℕ) (G H : Finset ℕ) (h : G ⊆ H) (hG : Good T G) : Good T H := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  exact ⟨w, h hw, h1⟩

theorem good_split (T : ℕ) (G : Finset ℕ) (a b c : ℕ) (hG : Good T G)
    (hc : ∀ p q : Fin 64, c.testBit p ≠ c.testBit q →
      a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q) :
    Good T (insert a (insert b (G.erase c))) := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  by_cases hwc : w = c
  · rw [hwc] at h1
    rcases hc p q h1 with h2 | h2
    · exact ⟨a, Finset.mem_insert_self _ _, h2⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h2⟩
  · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hwc, hw⟩)), h1⟩

def sel (q w : ℕ) : ℕ := if w.testBit q = true then w else ALL ^^^ w

abbrev GoodL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop :=
  ∀ q ∈ zs, L.foldl (fun acc w => acc &&& sel q w) T = 0

theorem fold_bits (q i : ℕ) : ∀ (L : List ℕ) (acc : ℕ),
    (L.foldl (fun acc w => acc &&& sel q w) acc).testBit i = true →
    acc.testBit i = true ∧ ∀ w ∈ L, (sel q w).testBit i = true
  | [], acc, h => ⟨h, by simp⟩
  | w :: L, acc, h => by
    have h' : (L.foldl (fun acc w => acc &&& sel q w) (acc &&& sel q w)).testBit i = true := h
    obtain ⟨h1, h2⟩ := fold_bits q i L _ h'
    rw [Nat.testBit_and, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun w' hw' => ?_⟩
    rcases List.mem_cons.mp hw' with e | e
    · rw [e]
      exact h1.2
    · exact h2 w' e

theorem goodL_of_good (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (hg : Good T L.toFinset) :
    GoodL T zs L := by
  intro q hq
  obtain ⟨hq1, hq2⟩ := hzs q hq
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨hTi, hall⟩ := fold_bits q i L T hi
  have hiR : i < 64 := by
    by_contra hge
    have hf : T.testBit i = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hf] at hTi
    exact absurd hTi (by simp)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i, hiR⟩ ⟨q, hq1⟩ hTi hq2
  have hwi : (sel q w).testBit i = true := hall w (List.mem_toFinset.mp hw)
  have hAi : ALL.testBit i = true := all_bit ⟨i, hiR⟩
  apply hsep
  show w.testBit i = w.testBit q
  unfold sel at hwi
  by_cases hwq : w.testBit q = true
  · rw [if_pos hwq] at hwi
    rw [hwi, hwq]
  · rw [if_neg hwq, Nat.testBit_xor, hAi] at hwi
    have hwq' : w.testBit q = false := by simpa using hwq
    rw [hwq']
    simpa using hwi

def InF (fam : List (ℕ × List ℕ)) (δ : ℕ) (S : Finset ℕ) : Prop :=
  ∃ e ∈ fam, e.1 ≤ δ ∧ e.2.toFinset = S

theorem inF_mono (fam : List (ℕ × List ℕ)) (δ δ' : ℕ) (h : δ ≤ δ') (S : Finset ℕ)
    (hS : InF fam δ S) : InF fam δ' S := by
  obtain ⟨e, he, h1, h2⟩ := hS
  exact ⟨e, he, le_trans h1 h, h2⟩

def Clos (T D : ℕ) (fam : List (ℕ × List ℕ)) : Prop :=
  ∀ δ : ℕ, ∀ S : Finset ℕ, InF fam δ S → ∀ a ∈ S, ∀ b ∈ S, ∀ c : ℕ,
    ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) →
    c ∉ S → c ≠ 0 → c ≠ ALL →
    ∀ E : Finset ℕ, E ⊆ S → S ⊆ insert a (insert b E) → Good T (insert c E) →
    ∀ δ' : ℕ, δ' < D → δ' + S.card = δ + E.card + 2 → InF fam δ' (insert c E)

def Jn (T N D : ℕ) (fam : List (ℕ × List ℕ)) (pool : List ℕ) (j : ℕ) : Prop :=
  ∀ G : Finset ℕ, G ⊆ pool.toFinset → 0 ∉ G → ALL ∉ G → Good T G →
    N ≤ G.card + j ∧ ∀ δ : ℕ, δ < D → G.card + j = N + δ → InF fam δ G

theorem jn_weak (T N D : ℕ) (fam : List (ℕ × List ℕ)) (pool : List ℕ) (j : ℕ)
    (h : Jn T N D fam pool j) : Jn T N D fam pool (j + 1) := by
  intro G hG hG0 hGA hg
  obtain ⟨h1, h2⟩ := h G hG hG0 hGA hg
  exact ⟨by omega, fun δ hδ hcd =>
    inF_mono fam (δ - 1) δ (by omega) G (h2 (δ - 1) (by omega) (by omega))⟩

theorem jn_step (T N D : ℕ) (fam : List (ℕ × List ℕ)) (hcl : Clos T D fam)
    (pool : List ℕ) (j c : ℕ) (h : Jn T N D fam pool j) (hc : c ∈ cand pool) (hcn : c ∉ pool) :
    Jn T N D fam (pool ++ [c]) (j + 1) := by
  intro G hG hG0 hGA hg
  have hmem : ∀ x ∈ G, x ≠ c → x ∈ pool.toFinset := by
    intro x hx hxc
    have h1 := hG hx
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exact absurd h1 hxc
  by_cases hcG : c ∈ G
  · have hsubE : G.erase c ⊆ pool.toFinset := by
      intro x hx
      obtain ⟨hxc, hxG⟩ := Finset.mem_erase.mp hx
      exact hmem x hxG hxc
    have hcard : (G.erase c).card + 1 = G.card := Finset.card_erase_add_one hcG
    have hIns : insert c (G.erase c) = G := Finset.insert_erase hcG
    have hc0 : c ≠ 0 := fun e => hG0 (e ▸ hcG)
    have hcA : c ≠ ALL := fun e => hGA (e ▸ hcG)
    have key : ∃ a b : ℕ, a ∈ pool ∧ b ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL ∧ b ≠ 0 ∧ b ≠ ALL ∧
        ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) ∧
        ∀ p q : Fin 64, c.testBit p ≠ c.testBit q →
          a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q := by
      simp only [cand, List.mem_append, List.mem_map, List.mem_flatMap] at hc
      rcases hc with hc | ⟨a, ha, hc⟩ | ⟨a, ha, b, hb, hc⟩
      · exact absurd hc hcn
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        refine ⟨a, a, ha1, ha1, ha2, ha3, ha2, ha3, Or.inr ⟨rfl, hc.symm⟩,
          fun p q hpq => Or.inl ?_⟩
        intro e
        apply hpq
        rw [← hc, Nat.testBit_xor, Nat.testBit_xor, all_bit p, all_bit q, e]
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        obtain ⟨hb1, hb2, hb3⟩ := (mem_nc pool b).mp hb
        have hc' : c = a &&& b ∨ c = a ||| b := by simpa using hc
        have hab : a ≠ b := by
          intro e
          apply hcn
          rcases hc' with e2 | e2
          · rw [e2, e, Nat.and_self]
            exact hb1
          · rw [e2, e, Nat.or_self]
            exact hb1
        refine ⟨a, b, ha1, hb1, ha2, ha3, hb2, hb3, Or.inl ⟨hab, hc'⟩, fun p q hpq => ?_⟩
        by_contra hno
        rw [not_or, not_not, not_not] at hno
        apply hpq
        rcases hc' with e2 | e2
        · rw [e2, Nat.testBit_and, Nat.testBit_and, hno.1, hno.2]
        · rw [e2, Nat.testBit_or, Nat.testBit_or, hno.1, hno.2]
    obtain ⟨a, b, ha, hb, ha0, haA, hb0, hbA, hcand, hsep⟩ := key
    have hgA : Good T (insert a (insert b (G.erase c))) := good_split T G a b c hg hsep
    have hsubA : insert a (insert b (G.erase c)) ⊆ pool.toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · rw [hx]
        exact List.mem_toFinset.mpr ha
      · rcases Finset.mem_insert.mp hx with hx | hx
        · rw [hx]
          exact List.mem_toFinset.mpr hb
        · exact hsubE hx
    have h0A : 0 ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact ha0 e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hb0 e.symm
        · exact hG0 (Finset.mem_of_mem_erase e)
    have hAA : ALL ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact haA e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hbA e.symm
        · exact hGA (Finset.mem_of_mem_erase e)
    obtain ⟨h1, h2⟩ := h _ hsubA h0A hAA hgA
    have hcA' : c ∉ insert a (insert b (G.erase c)) :=
      fun e => hcn (List.mem_toFinset.mp (hsubA e))
    have hEA : G.erase c ⊆ insert a (insert b (G.erase c)) :=
      fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have h3 := Finset.card_insert_le a (insert b (G.erase c))
    have h4 := Finset.card_insert_le b (G.erase c)
    refine ⟨by omega, fun δ hδ hcd => ?_⟩
    have hfin := hcl ((insert a (insert b (G.erase c))).card + j - N) _
      (h2 _ (by omega) (by omega)) a (Finset.mem_insert_self _ _) b
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) c hcand hcA' hc0 hcA
      (G.erase c) hEA (Finset.Subset.refl _) (by rw [hIns]; exact hg) δ hδ (by omega)
    rw [hIns] at hfin
    exact hfin
  · have hsubG : G ⊆ pool.toFinset := fun x hx => hmem x hx (fun e => hcG (e ▸ hx))
    exact jn_weak T N D fam pool j h G hsubG hG0 hGA hg

theorem filter_ne (L : List ℕ) (a : ℕ) :
    (L.filter (fun x => decide (x ≠ a))).toFinset = L.toFinset.erase a := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq]
  tauto

theorem filter_ne2 (L : List ℕ) (a b : ℕ) :
    (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))).toFinset =
      (L.toFinset.erase a).erase b := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq,
    Bool.and_eq_true]
  tauto

theorem sub_cases (S E : Finset ℕ) (a b : ℕ) (h1 : E ⊆ S) (h2 : S ⊆ insert a (insert b E)) :
    E = S ∨ E = S.erase a ∨ E = S.erase b ∨ E = (S.erase a).erase b := by
  have hx : ∀ x ∈ S, x = a ∨ x = b ∨ x ∈ E := by
    intro x hx
    rcases Finset.mem_insert.mp (h2 hx) with e | e
    · exact Or.inl e
    · exact Or.inr (Finset.mem_insert.mp e)
  by_cases ha : a ∈ E
  · by_cases hb : b ∈ E
    · left
      refine Finset.Subset.antisymm h1 (fun x hxS => ?_)
      rcases hx x hxS with e | e | e
      · rw [e]
        exact ha
      · rw [e]
        exact hb
      · exact e
    · right; right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · rw [e]
        exact ha
      · exact absurd e hxS.1
      · exact e
  · by_cases hb : b ∈ E
    · right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · exact absurd e hxS.1
      · rw [e]
        exact hb
      · exact e
    · right; right; right
      ext x
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE),
        fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2.2 with e | e | e
      · exact absurd e hxS.2.1
      · exact absurd e hxS.1
      · exact e

def opts (L : List ℕ) (a b : ℕ) : List (List ℕ) :=
  [L, L.filter (fun x => decide (x ≠ a)), L.filter (fun x => decide (x ≠ b)),
    L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))]

abbrev OkOne (T : ℕ) (zs : List ℕ) (D : ℕ) (fam : List (ℕ × List ℕ)) (i : ℕ) (L : List ℕ)
    (a b c : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ ∀ E ∈ opts L a b,
    D + L.length ≤ i + E.length + 2 ∨ ¬ GoodL T zs (c :: E) ∨
      ∃ e ∈ fam, e.1 + L.length ≤ i + E.length + 2 ∧
        e.2 = E.orderedInsert (fun x y => x ≤ y) c

abbrev OkEntry (T : ℕ) (zs : List ℕ) (D : ℕ) (fam : List (ℕ × List ℕ)) (e : ℕ × List ℕ) :
    Prop :=
  e.2.Nodup ∧ e.2.length ≠ 1 ∧ ∀ a ∈ e.2, ∀ b ∈ e.2,
    (a < b → ∀ c ∈ [a &&& b, a ||| b], OkOne T zs D fam e.1 e.2 a b c) ∧
    (a = b → OkOne T zs D fam e.1 e.2 a b (ALL ^^^ a))

theorem clos_of_ok (T D : ℕ) (zs : List ℕ) (fam : List (ℕ × List ℕ)) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hok : ∀ e ∈ fam, OkEntry T zs D fam e) : Clos T D fam := by
  intro δ S hS a ha b hb c hcand hcS hc0 hcA E hES hSE hg δ' hδ' hlev
  obtain ⟨e, he, hlv, heS⟩ := hS
  obtain ⟨hnd, _, hall⟩ := hok e he
  have haL : a ∈ e.2 := List.mem_toFinset.mp (by rw [heS]; exact ha)
  have hbL : b ∈ e.2 := List.mem_toFinset.mp (by rw [heS]; exact hb)
  have hcL : c ∉ e.2 := fun h => hcS (by rw [← heS]; exact List.mem_toFinset.mpr h)
  have hSc : S.card = e.2.length := by
    rw [← heS]
    exact List.toFinset_card_of_nodup hnd
  have hone : ∃ a' b' : ℕ, OkOne T zs D fam e.1 e.2 a' b' c ∧ S ⊆ insert a' (insert b' E) := by
    rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · refine ⟨a, b, (hall a haL b hbL).1 hlt c ?_, hSE⟩
        rcases hc with e2 | e2
        · exact List.mem_cons.mpr (Or.inl e2)
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr e2)
      · refine ⟨b, a, (hall b hbL a haL).1 hgt c ?_, ?_⟩
        · rcases hc with e2 | e2
          · exact List.mem_cons.mpr (Or.inl (e2.trans (Nat.and_comm a b)))
          · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr (e2.trans (Nat.or_comm a b)))
        · rw [Finset.insert_comm]
          exact hSE
    · subst hab
      subst hc
      exact ⟨a, a, (hall a haL a haL).2 rfl, hSE⟩
  obtain ⟨a', b', hone, hSE'⟩ := hone
  rcases hone with h | h | h | h
  · exact absurd h hcL
  · exact absurd h hc0
  · exact absurd h hcA
  · have hopt : ∃ El ∈ opts e.2 a' b', El.toFinset = E ∧ El.Nodup := by
      have hsc := sub_cases S E a' b' hES hSE'
      rw [← heS] at hsc
      rcases hsc with h1 | h1 | h1 | h1
      · exact ⟨e.2, by simp [opts], h1.symm, hnd⟩
      · exact ⟨e.2.filter (fun x => decide (x ≠ a')), by simp [opts],
          by rw [filter_ne, h1], hnd.filter _⟩
      · exact ⟨e.2.filter (fun x => decide (x ≠ b')), by simp [opts],
          by rw [filter_ne, h1], hnd.filter _⟩
      · exact ⟨e.2.filter (fun x => decide (x ≠ a') && decide (x ≠ b')), by simp [opts],
          by rw [filter_ne2, h1], hnd.filter _⟩
    obtain ⟨El, hEl, hElE, hElnd⟩ := hopt
    have hElc : El.length = E.card := by
      rw [← hElE]
      exact (List.toFinset_card_of_nodup hElnd).symm
    have hcons : (c :: El).toFinset = insert c E := by rw [List.toFinset_cons, hElE]
    rcases h El hEl with h3 | h3 | ⟨e', he', hlv', heq⟩
    · omega
    · exact absurd (goodL_of_good T zs hT hzs (c :: El) (by rw [hcons]; exact hg)) h3
    · refine ⟨e', he', by omega, ?_⟩
      rw [heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _), hcons]

theorem jn_base (T N D : ℕ) (fam : List (ℕ × List ℕ)) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (base : List ℕ)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : (0, base) ∈ fam) (hcard : base.length = N) (hnd : base.Nodup) :
    Jn T N D fam pool0 0 := by
  intro G hG hG0 hGA hg
  have hGb : G ⊆ base.toFinset := by
    intro x hx
    have h1 := List.mem_toFinset.mp (hG hx)
    rw [hpool] at h1
    rcases List.mem_append.mp h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exfalso
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact hG0 (by rw [← h1]; exact hx)
      · exact hGA (by rw [← List.mem_singleton.mp h1]; exact hx)
  have hbG : base.toFinset ⊆ G := by
    intro a ha
    by_contra hna
    apply hnec a (List.mem_toFinset.mp ha)
    apply goodL_of_good T zs hT hzs
    rw [filter_ne]
    exact good_mono T G _ (fun x hx => Finset.mem_erase.mpr
      ⟨fun e => hna (by rw [← e]; exact hx), hGb hx⟩) hg
  have hEq : G = base.toFinset := Finset.Subset.antisymm hGb hbG
  have hc : G.card = N := by rw [hEq, List.toFinset_card_of_nodup hnd, hcard]
  exact ⟨by omega, fun δ _ _ => ⟨(0, base), hbase, Nat.zero_le _, hEq.symm⟩⟩

theorem main (T N D : ℕ) (fam : List (ℕ × List ℕ)) (hcl : Clos T D fam)
    (hT1 : ∃ p : Fin 64, T.testBit p = true) (hT0 : ∃ q : Fin 64, T.testBit q = false) :
    ∀ (gs : List Gate) (pool : List ℕ) (ws : Fin 64 → List Bool) (L j o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv pool ws → Jn T N D fam pool j →
    (∀ p : Fin 64, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    N ≤ 1 + (j + gs.length) ∧
      ∀ δ : ℕ, δ < D → 1 + (j + gs.length) = N + δ → ∃ m : ℕ, InF fam δ {m}
  | [], pool, ws, L, j, o, _, _, hI, hJ, hout => by
    obtain ⟨m, hm, hmb⟩ := hI.2.2 o
    have hmT : ∀ p : Fin 64, m.testBit p = T.testBit p := fun p => (hmb p).trans (hout p)
    have hg : Good T {m} := by
      intro p q hp hq
      refine ⟨m, Finset.mem_singleton_self m, ?_⟩
      rw [hmT p, hmT q, hp, hq]
      simp
    have hm0 : (0 : ℕ) ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨p, hp⟩ := hT1
      have h1 := hmT p
      rw [← Finset.mem_singleton.mp e, Nat.zero_testBit, hp] at h1
      exact absurd h1 (by simp)
    have hmA : ALL ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨q, hq⟩ := hT0
      have h1 := hmT q
      rw [← Finset.mem_singleton.mp e, all_bit q, hq] at h1
      exact absurd h1 (by simp)
    obtain ⟨h1, h2⟩ := hJ {m} (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact List.mem_toFinset.mpr hm) hm0 hmA hg
    rw [Finset.card_singleton] at h1 h2
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨by omega, fun δ hδ e => ⟨m, h2 δ hδ (by omega)⟩⟩
  | g :: gs, pool, ws, L, j, o, hg, hL, hI, hJ, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 64, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by
        have h3 := hout p
        rw [List.foldl_cons] at h3
        exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hlen2 : 1 + (j + (g :: gs).length) = 1 + ((j + 1) + gs.length) := by
      simp only [List.length_cons]
      omega
    rw [hlen2]
    by_cases hcin : c ∈ pool
    · exact main T N D fam hcl hT1 hT0 gs pool _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool pool ws L hL hI _ c hcv (fun m hm => hm) hcin)
        (jn_weak T N D fam pool j hJ) hout'
    · exact main T N D fam hcl hT1 hT0 gs (pool ++ [c]) _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        (jn_step T N D fam hcl pool j c hJ hc hcin) hout'

theorem lower (T N D : ℕ) (fam : List (ℕ × List ℕ)) (zs base : List ℕ) (hT : T < 2 ^ 64)
    (hT1 : ∃ p : Fin 64, T.testBit p = true) (hT0 : ∃ q : Fin 64, T.testBit q = false)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hok : ∀ e ∈ fam, OkEntry T zs D fam e) (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : (0, base) ∈ fam) (hcard : base.length = N)
    (C : Circuit) (hC : FanInTwo C) (hev : ∀ p : Fin 64, C.eval (X p) = T.testBit p) :
    N + D ≤ C.gates.length + 1 := by
  have hnd : base.Nodup := (hok _ hbase).1
  obtain ⟨h1, h2⟩ := main T N D fam (clos_of_ok T D zs fam hT hzs hok) hT1 hT0 C.gates pool0 X
    6 0 C.output hC X_len inv0 (jn_base T N D fam zs hT hzs base hpool hnec hbase hcard hnd) hev
  by_contra hlt
  obtain ⟨m, e, he, _, hem⟩ := h2 (1 + (0 + C.gates.length) - N) (by omega) (by omega)
  obtain ⟨hnd', hlen, _⟩ := hok e he
  apply hlen
  rw [← List.toFinset_card_of_nodup hnd', hem, Finset.card_singleton]

def tab : ℕ := 18369900232523578088

def zs : List ℕ := [0, 1, 2, 4, 8, 10, 16, 20, 24, 32, 36, 40, 48, 52, 56]

def base : List ℕ := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]

def fam0 : List (ℕ × List ℕ) := [
  (0, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (0, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (1, [4294967295, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (1, [281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (1, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446462603027742720, 18446744069414584320]),
  (1, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (1, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (1, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam1 : List (ℕ × List ℕ) := [
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073709486080]),
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320, 18446744073709486080]),
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (1, [65535, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920]),
  (1, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446744073709486080]),
  (1, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446744073709486080])]

def fam2 : List (ℕ × List ℕ) := [
  (1, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (1, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709547760]),
  (1, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446744073709486080]),
  (2, [4294967295, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam3 : List (ℕ × List ℕ) := [
  (2, [3689348814741910323, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [6148914691236517205, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [9838263505978427528, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [11574427654092267680, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12249977906276641280, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297641735351828480, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829379609722880, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 13889313184910721216, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam4 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14699973487531969536, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757170082422194176, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395255531667456, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17216961135462248174, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17294086455919964160, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361376567555522560, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641477096079360, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18085043209519168250, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam5 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18229723555195321596, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374686483949813760, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966855136706560, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18422818335611355050, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18442521884633399280, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462598732840960, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446650250148948650, 18446744069414584320])]

def fam6 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446687779573189836, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446742978492890880, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 18446744072277895850]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 18446744072850558156]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 18446744073692839680]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 18446744073709486080])]

def fam7 : List (ℕ × List ℕ) := [
  (2, [65535, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [65535, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [65535, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [252645135, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [4294901760, 4294967295, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920]),
  (2, [4294901760, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [4294967295, 281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920]),
  (2, [4294967295, 71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446462603027742720])]

def fam8 : List (ℕ × List ℕ) := [
  (2, [4294967295, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446462603027742720]),
  (2, [4294967295, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [4294967295, 6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [4294967295, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610621680]),
  (2, [4294967295, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [4294967295, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446462603027742720]),
  (2, [16557098929935, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [281470681743360, 281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920])]

def fam9 : List (ℕ × List ℕ) := [
  (2, [281470681743360, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [281470681808895, 71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446744069414584320]),
  (2, [281470681808895, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446744069414584320]),
  (2, [281470681808895, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [281470681808895, 6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073456906480]),
  (2, [281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [281470681808895, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446744069414584320])]

def fam10 : List (ℕ × List ℕ) := [
  (2, [14355442858917939, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446462603027742720, 18446744069414584320]),
  (2, [71777214294589695, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18446462603027742720, 18446744069414584320]),
  (2, [71777214294589695, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18446462603027742720, 18446744069414584320]),
  (2, [71777214294589695, 6148914691236517205, 14757395258967641292, 17361641481138401520, 18446462603027742720, 18446744069414584320]),
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446462603027742720, 18446744073456906480]),
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446462603027742720, 18446744073709486080]),
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446727516610621680, 18446744069414584320])]

def fam11 : List (ℕ × List ℕ) := [
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446744069414584320, 18446744073709486080]),
  (2, [1085086035472220160, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446744069414584320]),
  (2, [1085086035472220160, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [1085102592318504960, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446462603027742720]),
  (2, [1085102592318504960, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [1085102592571150095, 3689348814741910323, 12297829382473034410, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [1085102592571150095, 6148914691236517205, 14757395258967641292, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080])]

def fam12 : List (ℕ × List ℕ) := [
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446462603027742720, 18446744073709486080]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446744069414584320, 18446744073709486080]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (2, [3674993371882992384, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18446462603027742720, 18446744069414584320]),
  (2, [3674993371882992384, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446462603027742720, 18446744069414584320]),
  (2, [3689348814741910323, 6148914691236517205, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam13 : List (ℕ × List ℕ) := [
  (2, [3689348814741910323, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073709486080]),
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446744069414584320, 18446744073709486080]),
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (2, [6148914691236517205, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073456906480])]

def fam14 : List (ℕ × List ℕ) := [
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073709486080]),
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320, 18446744073709486080]),
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (2, [9838263505978427528, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [11574427654092267680, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12249977906276641280, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297641735351828480, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080])]

def fam15 : List (ℕ × List ℕ) := [
  (2, [12297829379609722880, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382472990720, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 13889313184910721216, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14699973487531969536, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757170082422194176, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395255531667456, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967588864, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 14771750701826559231, 17361641481138401520, 18446462603027742720, 18446744069414584320])]

def fam16 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17216698429492559872, 17361641481138401520, 18374966859414961920, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17216961131453612032, 17361641481138401520, 18374966859414961920, 18446462603027742720]),
  (2, [12297829382473034410, 14757395258967641292, 17216961135462248174, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17294086455919964160, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17294086455919964160, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 17294086455919964160, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361376567555522560, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641477096079360, 17361641481138401520, 18374966859414961920, 18446744073709486080])]

def fam17 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138339840, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 17361641481391046655, 18374966859414961920, 18446462603027742720]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 17361658038237331455, 18374966859414961920, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18014673391583296000, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18085043209519168250, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18229723555195321596, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374686483949813760, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966855136706560, 18374966859414961920, 18446744073709486080])]

def fam18 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414896640, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18422818335611355050, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18442521884633399280, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462598732840960, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446462603027808255]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744071705233544]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744072109465760])]

def fam19 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744072266754560]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744072277852160]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744072648442048]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744072850505728]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073441177600]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073456844800]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073692774400]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744073709547760])]

def fam20 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446612720724707464, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446639212082995360, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446649520004508160, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446650250148904960, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446650250148948650, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446674533894045888, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446687779573137408, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446687779573189836, 18446744073709486080])]

def fam21 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446726485818470400, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610560000, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610621680, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610621680, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446727516610621680, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446742978492825600, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446742978492890880, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320, 18446744069414649855])]

def fam22 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069414584320, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744072277895850, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744072850558156, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073456906480, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073456906480, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073692839680, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080, 18446744073709529770]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080, 18446744073709538508])]

def fam23 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709486080, 18446744073709551360]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18413248040372076424, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18420003542893920160, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18422817605466914560, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18422818335600213760, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18429010879589711808, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432387754677305088, 18446462603027742720, 18446744069414584320])]

def fam24 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630837264128, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446462603027742720, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446744069414584320, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17940362863843014904, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18082228416801733360, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18085032171453214960, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam25 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 18085043209350738160, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18085043209519168250, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 18085043209519168250, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18229710309516177648, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18229723554993205488, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18229723555195321596, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 18229723555195321596, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 17072280789786094828, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam26 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 17207390840222969548, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 17216923606038006988, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 17216961134889585868, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 17216961135462248174, 17361641481138401520, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 17361641481138401520, 18216212550151634124, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 17361641481138401520, 18229723555195321596, 18432388630850633676, 18446462603027742720, 18446744069414584320]),
  (2, [14757395258967641292, 16927600444109941482, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [14757395258967641292, 17216886076613765802, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320])]

def fam27 : List (ℕ × List ℕ) := [
  (2, [14757395258967641292, 17216961134316923562, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [14757395258967641292, 17361641481138401520, 18062524867779689130, 18374966859414961920, 18446462603027742720, 18446744069414584320]),
  (2, [3855, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920]),
  (2, [65535, 71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520]),
  (2, [65535, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920]),
  (2, [65535, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920]),
  (2, [65535, 6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920]),
  (2, [65535, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676])]

def fam28 : List (ℕ × List ℕ) := [
  (2, [14355442858917939, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446744073709486080]),
  (2, [71777214294589695, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18446744073709486080]),
  (2, [71777214294589695, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18446744073709486080]),
  (2, [71777214294589695, 6148914691236517205, 14757395258967641292, 17361641481138401520, 18446744073709486080]),
  (2, [71777214294589695, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446744073709547760]),
  (2, [1085102592571146240, 1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920]),
  (2, [1085102592571146240, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920]),
  (2, [1085102592571150095, 3689348814741910323, 12297829382473034410, 18374966859414961920, 18446744073709486080])]

def fam29 : List (ℕ × List ℕ) := [
  (2, [1085102592571150095, 6148914691236517205, 14757395258967641292, 18374966859414961920, 18446744073709486080]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446479160126668800]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446744069667225600]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18374966859414961920, 18446744073709547760]),
  (2, [1085102592571150095, 12297829382473034410, 14757395258967641292, 18432388630850633676, 18446744073709486080]),
  (2, [3674993371882992384, 3689348814741910323, 12297829382473034410, 17361641481138401520, 18446744073709486080]),
  (2, [3674993371882992384, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18446744073709486080]),
  (2, [3689348814741910323, 6148914691236517205, 17361641481138401520, 18374966859414961920, 18446744073709486080])]

def fam30 : List (ℕ × List ℕ) := [
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18374966859414961920, 18446744073709547760]),
  (2, [3689348814741910323, 12297829382473034410, 17361641481138401520, 18432388630850633676, 18446744073709486080]),
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709547760]),
  (2, [6148914691236517205, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967588864, 17361641481138401520, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 14771750701826559231, 17361641481138401520, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17216961135462187008, 17361641481138401520, 18374966859414961920]),
  (2, [12297829382473034410, 14757395258967641292, 17294086455919964160, 18374966859414961920, 18446744073709547760])]

def fam31 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 17361641481138405375, 18374966859414961920]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18014673391583296000, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446479160126668800]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446725308997369856]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744069667225600]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073423159296]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709521032]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709527200])]

def fam32 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709529600]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709535424]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446744073709547520]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18413248040372076424, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18420003542893920160, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18422817605466914560, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18422818335600213760, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18422818335611354880, 18446744073709486080])]

def fam33 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18429010879589711808, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432387754677305088, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630837264128, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633472, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 17361641481138401520, 18432388630850633676, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 17940362863843014904, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18014673391583296000, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 14757395258967641292, 18014673391583296000, 18446727516610621680, 18446744069414584320])]

def fam34 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 18082228416801733360, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18085032171453214960, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18085043209350738160, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18085043209519165680, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18085043209519168250, 18374966859414961920, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 18229710309516177648, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18229723554993205488, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 14757395258967641292, 18229723555195318512, 18374966859414961920, 18446744073709486080])]

def fam35 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 18229723555195321596, 18374966859414961920, 18446744073709547760]),
  (2, [12297829382473034410, 14757395258967641292, 18374388447579140336, 18374966859414961920, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18374403900635672816, 18374966859414961920, 18446462603027742720]),
  (2, [12297829382473034410, 17072280789786094828, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 17207390840222969548, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 17216923606038006988, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 17216961134889585868, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 17216961135462239436, 17361641481138401520, 18374966859414961920, 18446744073709486080])]

def fam36 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 17216961135462248174, 17361641481138401520, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 17361641481138401520, 18216212550151634124, 18374966859414961920, 18446744073709486080]),
  (2, [12297829382473034410, 17361641481138401520, 18229723555195321596, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 17361641481138401520, 18360329937284300492, 18446462603027742720, 18446744069414584320]),
  (2, [12297829382473034410, 18216212550151634124, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 18216212550151634124, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 18229723555195321596, 18432388630850633676, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 18229723555195321596, 18432388630850633676, 18446727516610621680, 18446744069414584320])]

def fam37 : List (ℕ × List ℕ) := [
  (2, [14757395258967641292, 16927600444109941482, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [14757395258967641292, 17216886076613765802, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [14757395258967641292, 17216961134316923562, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [14757395258967641292, 17216961135462230698, 17361641481138401520, 18374966859414961920, 18446744073709486080]),
  (2, [14757395258967641292, 17361641481138401520, 18062524867779689130, 18374966859414961920, 18446744073709486080]),
  (2, [14757395258967641292, 18062524867779689130, 18374966859414961920, 18446462603027742720, 18446744073456906480]),
  (2, [14757395258967641292, 18062524867779689130, 18374966859414961920, 18446727516610621680, 18446744069414584320]),
  (2, [12297829382473034410, 14757395258967641292, 18014673391583296000, 18446744073709547760])]

def fam38 : List (ℕ × List ℕ) := [
  (2, [12297829382473034410, 14757395258967641292, 18374403900871471344, 18374966859414961920]),
  (2, [12297829382473034410, 17216961135462187008, 17361641481138401520, 18432388630850633676]),
  (2, [12297829382473034410, 17361641481138401520, 18360329937284300492, 18446744073709486080]),
  (2, [12297829382473034410, 18216212550151634124, 18374966859414961920, 18446744073709547760]),
  (2, [12297829382473034410, 18229723555195318512, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 18229723555195321596, 18432388630850633676, 18446744073709547760]),
  (2, [12297829382473034410, 18360329937284300492, 18446462603027742720, 18446744073456906480]),
  (2, [12297829382473034410, 18360329937284300492, 18446727516610621680, 18446744069414584320])]

def fam39 : List (ℕ × List ℕ) := [
  (2, [14757395258967641292, 18062524867779689130, 18374966859414961920, 18446744073709547760]),
  (2, [17216961135462230698, 17361641481138401520, 18432388630850633676, 18446744073709486080]),
  (2, [12297829382473034410, 18360329937284300492, 18446744073709547760]),
  (2, [12297829382473034410, 18374403900871471344, 18432388630850633676])]

def fam : List (ℕ × List ℕ) := fam0 ++ fam1 ++ fam2 ++ fam3 ++ fam4 ++ fam5 ++ fam6 ++ fam7 ++ fam8 ++ fam9 ++ fam10 ++ fam11 ++ fam12 ++ fam13 ++ fam14 ++ fam15 ++ fam16 ++ fam17 ++ fam18 ++ fam19 ++ fam20 ++ fam21 ++ fam22 ++ fam23 ++ fam24 ++ fam25 ++ fam26 ++ fam27 ++ fam28 ++ fam29 ++ fam30 ++ fam31 ++ fam32 ++ fam33 ++ fam34 ++ fam35 ++ fam36 ++ fam37 ++ fam38 ++ fam39

set_option synthInstance.maxSize 4000 in
theorem ok0 : ∀ e ∈ fam0, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok1 : ∀ e ∈ fam1, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok2 : ∀ e ∈ fam2, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok3 : ∀ e ∈ fam3, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok4 : ∀ e ∈ fam4, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok5 : ∀ e ∈ fam5, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok6 : ∀ e ∈ fam6, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok7 : ∀ e ∈ fam7, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok8 : ∀ e ∈ fam8, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok9 : ∀ e ∈ fam9, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok10 : ∀ e ∈ fam10, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok11 : ∀ e ∈ fam11, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok12 : ∀ e ∈ fam12, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok13 : ∀ e ∈ fam13, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok14 : ∀ e ∈ fam14, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok15 : ∀ e ∈ fam15, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok16 : ∀ e ∈ fam16, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok17 : ∀ e ∈ fam17, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok18 : ∀ e ∈ fam18, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok19 : ∀ e ∈ fam19, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok20 : ∀ e ∈ fam20, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok21 : ∀ e ∈ fam21, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok22 : ∀ e ∈ fam22, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok23 : ∀ e ∈ fam23, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok24 : ∀ e ∈ fam24, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok25 : ∀ e ∈ fam25, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok26 : ∀ e ∈ fam26, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok27 : ∀ e ∈ fam27, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok28 : ∀ e ∈ fam28, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok29 : ∀ e ∈ fam29, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok30 : ∀ e ∈ fam30, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok31 : ∀ e ∈ fam31, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok32 : ∀ e ∈ fam32, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok33 : ∀ e ∈ fam33, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok34 : ∀ e ∈ fam34, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok35 : ∀ e ∈ fam35, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok36 : ∀ e ∈ fam36, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok37 : ∀ e ∈ fam37, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok38 : ∀ e ∈ fam38, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok39 : ∀ e ∈ fam39, OkEntry tab zs 3 fam e := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem ok : ∀ e ∈ fam, OkEntry tab zs 3 fam e := by
  intro e he
  simp only [fam, List.mem_append] at he
  rcases he with ((((((((((((((((((((((((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  · exact ok0 e h
  · exact ok1 e h
  · exact ok2 e h
  · exact ok3 e h
  · exact ok4 e h
  · exact ok5 e h
  · exact ok6 e h
  · exact ok7 e h
  · exact ok8 e h
  · exact ok9 e h
  · exact ok10 e h
  · exact ok11 e h
  · exact ok12 e h
  · exact ok13 e h
  · exact ok14 e h
  · exact ok15 e h
  · exact ok16 e h
  · exact ok17 e h
  · exact ok18 e h
  · exact ok19 e h
  · exact ok20 e h
  · exact ok21 e h
  · exact ok22 e h
  · exact ok23 e h
  · exact ok24 e h
  · exact ok25 e h
  · exact ok26 e h
  · exact ok27 e h
  · exact ok28 e h
  · exact ok29 e h
  · exact ok30 e h
  · exact ok31 e h
  · exact ok32 e h
  · exact ok33 e h
  · exact ok34 e h
  · exact ok35 e h
  · exact ok36 e h
  · exact ok37 e h
  · exact ok38 e h
  · exact ok39 e h

theorem tab_lt : tab < 2 ^ 64 := by decide +kernel

theorem tab_one : ∃ p : Fin 64, tab.testBit p = true := by decide +kernel

theorem tab_zero : ∃ q : Fin 64, tab.testBit q = false := by decide +kernel

theorem zs_ok : ∀ q ∈ zs, q < 64 ∧ tab.testBit q = false := by decide +kernel

theorem pool_eq : pool0 = base ++ [0, ALL] := by decide +kernel

theorem nec : ∀ a ∈ base, ¬ GoodL tab zs (base.filter (fun x => decide (x ≠ a))) := by
  decide +kernel

theorem base_mem : (0, base) ∈ fam := by decide +kernel

theorem base_len : base.length = 6 := by decide +kernel

theorem tab_eq : ∀ p : Fin 64, (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)) (fun i : Fin 6 => p.val.testBit i.val) =
    tab.testBit p.val := by
  decide +kernel

end PEqualNP.Outside.L_meta_7285

theorem PEqualNP.Outside.L_meta_7285 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)) t → 8 ≤ t := by
  rintro t ⟨C, hC, hs, hev⟩
  have h := PEqualNP.Outside.L_meta_7285.lower PEqualNP.Outside.L_meta_7285.tab 6 3 PEqualNP.Outside.L_meta_7285.fam PEqualNP.Outside.L_meta_7285.zs PEqualNP.Outside.L_meta_7285.base PEqualNP.Outside.L_meta_7285.tab_lt PEqualNP.Outside.L_meta_7285.tab_one
    PEqualNP.Outside.L_meta_7285.tab_zero PEqualNP.Outside.L_meta_7285.zs_ok PEqualNP.Outside.L_meta_7285.ok PEqualNP.Outside.L_meta_7285.pool_eq PEqualNP.Outside.L_meta_7285.nec PEqualNP.Outside.L_meta_7285.base_mem
    PEqualNP.Outside.L_meta_7285.base_len C hC (fun p => (hev _).trans (PEqualNP.Outside.L_meta_7285.tab_eq p))
  have hs' : C.gates.length ≤ t := hs
  omega
