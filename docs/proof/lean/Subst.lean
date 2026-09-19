/-
  Formalization of Section 2 of "String Substitution Theory for Finite Charset"
  (../main.tex).

  * `subst A B C` is the paper's `[A/B]C` (Definition 1): scan `C` from the
    left and replace every occurrence of the block `B` by `A`, taking
    leftmost-first, non-overlapping matches; the scan never restarts inside
    inserted text.  The paper leaves `[A/ε]` undefined; here the empty block
    never matches, so `subst A []` is the identity.
  * Composition is right-to-left, as in the paper:
    `subst A B (subst C D E)` is `[A/B][C/D]E`.

  Status: every theorem of Section 2 is proven except `repC2_correct` (the
  paper's Theorem (Multiple Substitution): the unrestricted comma-code
  construction, no hypothesis on the patterns beyond `X_i ≠ ε` and
  everything over `σ`; roadmap in its docstring).  For the comma code the
  *code layer* is proven: `enc2Pass_eq` (the pass composition computes the
  block map) and `dec2Pass_enc2` (the decode round trip); the
  phase-locking staging argument is the remaining work.  `repC` is an
  enc-based variant of the construction, which computes `repRef` only under
  the condition that every `X_i` is a single character or does not end in
  `x` (a statement not proven here); it is kept as a demo of the shadowing
  failure.  (Theorem (escaping) is `repC2` on special pair sets; not
  formalized.)  Also proven along the way: the Double Substitution Lemma,
  cat, benc/bdec border coding, eq, ite, head, and tail (the last two need
  `X ⊆ Σ`, as the paper assumes `Σ = {σ₁..σ_N}` throughout).

  Build: `lake build`.  Quick iteration: `lake env lean Subst.lean`.
-/

variable {α : Type} [DecidableEq α]

/-! ## Definition 1: substitution -/

/-- `matchHere B C`: does `C` begin with the block `B`?
    If so, return the rest of `C`, else `none`. -/
def matchHere : List α → List α → Option (List α)
  | [], C => some C
  | _, [] => none
  | b :: B', c :: C' => if b = c then matchHere B' C' else none

theorem matchHere_length : ∀ B C D : List α,
    matchHere B C = some D → D.length + B.length ≤ C.length := by
  intro B
  induction B with
  | nil =>
      intro C D h
      simp only [matchHere] at h
      injection h with h'
      subst h'
      simp only [List.length_nil]
      omega
  | cons b B' ih =>
      intro C D h
      cases C with
      | nil => simp [matchHere] at h
      | cons c C' =>
          by_cases hbc : b = c
          · subst hbc
            simp [matchHere] at h
            have hlen := ih C' D h
            simp only [List.length_cons] at hlen ⊢
            omega
          · simp [matchHere, hbc] at h

/-- The scan of Definition 1, for a nonempty pattern. -/
def substNE (A B : List α) (hB : B ≠ []) : List α → List α
  | [] => []
  | c :: C =>
      match _h : matchHere B (c :: C) with
      | some D => A ++ substNE A B hB D
      | none => c :: substNE A B hB C
termination_by T => T.length
decreasing_by
  · have hlen := matchHere_length B (c :: C) D _h
    have hBpos : 1 ≤ B.length := by
      cases B with
      | nil => exact absurd rfl hB
      | cons _ _ => simp
    omega
  · simp only [List.length_cons]
    omega

/-- Definition 1: `[A/B]C`.  The empty pattern never matches. -/
def subst (A B C : List α) : List α :=
  match B with
  | [] => C
  | b :: B' => substNE A (b :: B') (by simp) C

theorem subst_nil_pattern (A C : List α) : subst A [] C = C := rfl

theorem subst_cons_pattern (A : List α) (b : α) (B' C : List α) :
    subst A (b :: B') C = substNE A (b :: B') (by simp) C := rfl

theorem substNE_nil (A B : List α) (hB : B ≠ []) : substNE A B hB [] = [] := by
  rw [substNE.eq_1]

theorem substNE_cons_match (A B : List α) (hB : B ≠ []) (c : α) (C D : List α)
    (h : matchHere B (c :: C) = some D) :
    substNE A B hB (c :: C) = A ++ substNE A B hB D := by
  rw [substNE.eq_2, h]

theorem substNE_cons_none (A B : List α) (hB : B ≠ []) (c : α) (C : List α)
    (h : matchHere B (c :: C) = none) :
    substNE A B hB (c :: C) = c :: substNE A B hB C := by
  rw [substNE.eq_2, h]

theorem subst_nil (A B : List α) : subst A B [] = [] := by
  cases B with
  | nil => rfl
  | cons b B' => rw [subst_cons_pattern, substNE_nil]

theorem subst_cons_match (A B : List α) (hB : B ≠ []) (c : α) (C D : List α)
    (h : matchHere B (c :: C) = some D) :
    subst A B (c :: C) = A ++ subst A B D := by
  cases B with
  | nil => exact absurd rfl hB
  | cons b B' =>
      rw [subst_cons_pattern, substNE_cons_match _ _ _ _ _ _ h, subst_cons_pattern]

theorem subst_cons_none (A B : List α) (c : α) (C : List α)
    (h : matchHere B (c :: C) = none) :
    subst A B (c :: C) = c :: subst A B C := by
  cases B with
  | nil => rfl
  | cons b B' => rw [subst_cons_pattern, substNE_cons_none _ _ _ _ _ h, subst_cons_pattern]

/-! ### Definition 1, on instances -/

#eval subst ['a', 'b'] ['b'] ['b']                -- [a, b]   ([ab/b]b = ab)
#eval subst ['a', 'b'] ['b'] ['a', 'b']           -- [a, a, b]
#eval subst ['a'] ['a'] ['a', 'a']                -- [a, a]   ([a/a]aa = aa)
#eval subst ['x', 'y'] ['x'] ['y', 'x']           -- [y, x, y] (no restart in inserted text)
#eval subst ['a', 'a'] ['a', 'b', 'a'] ['a', 'b', 'a']  -- [a, a]
#eval subst [] ['a'] ['b', 'a', 'a']              -- [b]      (deletion: A = ε)

/-! ## Theorem 2.2: enc and dec -/

/-- `enc b x = [xb/b]`: escape every `b` into `xb`. -/
def enc (b x : α) (S : List α) : List α := subst [x, b] [b] S

/-- `dec b x = [b/xb]`: the inverse of `enc b x`. -/
def dec (b x : α) (S : List α) : List α := subst [b] [x, b] S

theorem matchHere_one_self (b : α) (S : List α) : matchHere [b] (b :: S) = some S := by
  simp [matchHere]

theorem matchHere_one_ne (b c : α) (S : List α) (h : c ≠ b) :
    matchHere [b] (c :: S) = none := by
  simp [matchHere, Ne.symm h]

theorem matchHere_two_self (x b : α) (T : List α) :
    matchHere [x, b] (x :: b :: T) = some T := by
  simp [matchHere]

theorem matchHere_two_ne (x b c : α) (T : List α) (h : c ≠ x) :
    matchHere [x, b] (c :: T) = none := by
  simp [matchHere, Ne.symm h]

theorem matchHere_two_head (x b : α) (T : List α) (h : matchHere [b] T = none) :
    matchHere [x, b] (x :: T) = none := by
  simp [matchHere, h]

theorem enc_nil (b x : α) : enc b x [] = [] := by rw [enc, subst_nil]

theorem dec_nil (b x : α) : dec b x [] = [] := by rw [dec, subst_nil]

theorem enc_cons_b (b x : α) (S : List α) : enc b x (b :: S) = x :: b :: enc b x S := by
  show subst [x, b] [b] (b :: S) = x :: b :: subst [x, b] [b] S
  rw [subst_cons_match _ _ (by simp) _ _ _ (matchHere_one_self b S)]
  simp only [List.cons_append, List.nil_append]

theorem enc_cons_ne (b x : α) (c : α) (S : List α) (h : c ≠ b) :
    enc b x (c :: S) = c :: enc b x S := by
  show subst [x, b] [b] (c :: S) = c :: subst [x, b] [b] S
  rw [subst_cons_none _ _ _ _ (matchHere_one_ne b c S h)]

theorem dec_cons_xb (b x : α) (T : List α) :
    dec b x (x :: b :: T) = b :: dec b x T := by
  show subst [b] [x, b] (x :: b :: T) = b :: subst [b] [x, b] T
  rw [subst_cons_match _ _ (by simp) _ _ _ (matchHere_two_self x b T)]
  simp only [List.cons_append, List.nil_append]

theorem dec_cons_ne (b x : α) (c : α) (T : List α) (h : c ≠ x) :
    dec b x (c :: T) = c :: dec b x T := by
  show subst [b] [x, b] (c :: T) = c :: subst [b] [x, b] T
  rw [subst_cons_none _ _ _ _ (matchHere_two_ne x b c T h)]

theorem dec_cons_x_ne (b x : α) (T : List α) (h : matchHere [x, b] (x :: T) = none) :
    dec b x (x :: T) = x :: dec b x T := by
  show subst [b] [x, b] (x :: T) = x :: subst [b] [x, b] T
  rw [subst_cons_none _ _ _ _ h]

/-- Theorem 2.2 (F2): an `enc`-image never begins with `b`. -/
theorem enc_not_startsWith_b (b x : α) (hxb : x ≠ b) (S : List α) :
    matchHere [b] (enc b x S) = none := by
  cases S with
  | nil => rw [enc, subst_nil]; rfl
  | cons c S =>
      by_cases hcb : c = b
      · rw [hcb, enc_cons_b]
        exact matchHere_one_ne _ _ _ hxb
      · rw [enc_cons_ne _ _ _ _ hcb]
        exact matchHere_one_ne _ _ _ hcb

/-- Theorem 2.2 (i), first half: `dec ∘ enc = id` (the round trip). -/
theorem dec_enc (b x : α) (hxb : x ≠ b) : ∀ S : List α, dec b x (enc b x S) = S := by
  intro S
  induction S with
  | nil => rw [enc, subst_nil, dec, subst_nil]
  | cons c S ih =>
      by_cases hcb : c = b
      · subst hcb
        rw [enc_cons_b, dec_cons_xb, ih]
      · by_cases hcx : c = x
        · rw [hcx, enc_cons_ne b x x S hxb,
              dec_cons_x_ne b x (enc b x S)
                (matchHere_two_head x b (enc b x S) (enc_not_startsWith_b b x hxb S)), ih]
        · rw [enc_cons_ne b x c S hcb, dec_cons_ne b x c (enc b x S) hcx, ih]

/-- Theorem 2.2 (i), second half: `enc` is a monoid morphism. -/
theorem enc_append (b x : α) (S T : List α) :
    enc b x (S ++ T) = enc b x S ++ enc b x T := by
  induction S with
  | nil =>
      show enc b x ([] ++ T) = enc b x [] ++ enc b x T
      rw [enc_nil]
      rfl
  | cons c S ih =>
      by_cases hcb : c = b
      · subst hcb
        rw [List.cons_append, enc_cons_b, enc_cons_b, ih]
        simp only [List.cons_append]
      · rw [List.cons_append, enc_cons_ne b x c (S ++ T) hcb, enc_cons_ne b x c S hcb, ih]
        rfl

/-! ### Occurrence and the no-`bb` invariant -/

/-- `Occ p l`: `p` occurs in `l` as a contiguous block (the paper's `p ⊂ l`). -/
def Occ (p l : List α) : Prop := ∃ u v, l = u ++ p ++ v

omit [DecidableEq α] in
theorem occ_cons_inv {p : List α} {c : α} {l : List α} (h : Occ p (c :: l)) :
    Occ p l ∨ ∃ v, c :: l = p ++ v := by
  obtain ⟨u, v, hv⟩ := h
  cases u with
  | nil => exact Or.inr ⟨v, hv⟩
  | cons d u =>
      rw [List.cons_append] at hv
      injection hv with _ h2
      exact Or.inl ⟨u, v, h2⟩

/-- Theorem 2.2 (ii) / (F1): an `enc`-image contains no `bb`. -/
theorem no_bb (b x : α) (hxb : x ≠ b) : ∀ S : List α, ¬ Occ [b, b] (enc b x S) := by
  intro S
  induction S with
  | nil => intro ⟨u, v, hv⟩; rw [enc_nil] at hv; simp at hv
  | cons c S ih =>
      by_cases hcb : c = b
      · subst hcb
        intro h
        rw [enc_cons_b] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
          · exact ih h2
          · rw [List.cons_append] at hv'
            injection hv' with _ henc
            exfalso
            have H := enc_not_startsWith_b _ _ hxb S
            rw [henc] at H
            simp only [List.cons_append, List.nil_append] at H
            simp [matchHere] at H
        · rw [List.cons_append] at hv
          injection hv with hx _
          exact hxb hx
      · intro h
        rw [enc_cons_ne b x c S hcb] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · exact ih h1
        · rw [List.cons_append] at hv
          injection hv with hc _
          exact hcb hc

#eval enc 'b' 'x' ['a', 'b', 'a', 'c']                       -- [a, x, b, a, c]
#eval dec 'b' 'x' (enc 'b' 'x' ['a', 'b', 'a', 'c'])          -- [a, b, a, c]
#eval enc 'b' 'x' "abacb".toList ++ enc 'b' 'x' "ba".toList   -- morphism: enc S ++ enc T
#eval enc 'b' 'x' ("abacb" ++ "ba").toList                    -- ... equals enc (S ++ T)

/-! ### Scan and occurrence toolkit -/

theorem matchHere_self (B : List α) : matchHere B B = some [] := by
  induction B with
  | nil => rfl
  | cons b B' ih => simp [matchHere, ih]

theorem matchHere_prefix (B D : List α) : matchHere B (B ++ D) = some D := by
  induction B generalizing D with
  | nil => rfl
  | cons b B' ih => rw [List.cons_append]; simp [matchHere, ih]

theorem matchHere_app : ∀ (B C D : List α), matchHere B C = some D → C = B ++ D := by
  intro B
  induction B with
  | nil =>
      intro C D h
      simp only [matchHere] at h
      injection h with _h
  | cons b B' ih =>
      intro C D h
      cases C with
      | nil => simp [matchHere] at h
      | cons c C' =>
          by_cases hbc : b = c
          · subst hbc
            simp [matchHere] at h
            exact congrArg (b :: ·) (ih C' D h)
          · simp [matchHere, hbc] at h

theorem matchHere_occ {B C D : List α} (h : matchHere B C = some D) : Occ B C :=
  ⟨[], D, by rw [List.nil_append]; exact matchHere_app B C D h⟩

omit [DecidableEq α] in
theorem occ_cons {p : List α} {c : α} {l : List α} (h : Occ p l) : Occ p (c :: l) := by
  obtain ⟨u, v, hv⟩ := h
  exact ⟨c :: u, v, by rw [List.cons_append]; exact congrArg (c :: ·) hv⟩

omit [DecidableEq α] in
theorem occ_left {p q : List α} {l : List α} (h : Occ (p ++ q) l) : Occ p l := by
  obtain ⟨u, v, hv⟩ := h
  refine ⟨u, q ++ v, ?_⟩
  rw [hv]
  simp [List.append_assoc]

omit [DecidableEq α] in
theorem occ_length {p l : List α} (h : Occ p l) : p.length ≤ l.length := by
  obtain ⟨u, v, hv⟩ := h
  rw [hv, List.length_append, List.length_append]
  omega

omit [DecidableEq α] in
theorem occ_single {c : α} {l : List α} : Occ [c] l ↔ c ∈ l := by
  constructor
  · rintro ⟨u, v, hv⟩
    rw [hv]
    simp [List.mem_append]
  · intro h
    induction l with
    | nil => cases h
    | cons d l' ih =>
        rcases List.mem_cons.1 h with h' | h'
        · exact ⟨[], l', by simp [h']⟩
        · exact occ_cons (ih h')

omit [DecidableEq α] in
theorem append_left_cancel : ∀ (a l r : List α), a ++ l = a ++ r → l = r := by
  intro a
  induction a with
  | nil => intro l r h; simpa using h
  | cons c a' ih =>
      intro l r h
      rw [List.cons_append, List.cons_append] at h
      injection h with _ h'
      exact ih l r h'

/-- If `B` does not occur in `C` at all, `[A/B]C = C`. -/
theorem subst_no_occ (A B : List α) : ∀ (C : List α), ¬ Occ B C → subst A B C = C := by
  intro C
  induction C with
  | nil => intro _; exact subst_nil A B
  | cons c C' ih =>
      intro h
      have hC' : ¬ Occ B C' := fun hc => h (occ_cons hc)
      cases B with
      | nil => rfl
      | cons b B' =>
          cases hm : matchHere (b :: B') (c :: C') with
          | none =>
              rw [subst_cons_none _ _ _ _ hm]
              exact congrArg (c :: ·) (ih hC')
          | some D =>
              rw [subst_cons_match _ _ (by simp) _ _ _ hm]
              exact absurd (matchHere_occ hm) h

/-- If the only occurrences of `B` in `C ++ B` end at the end, then
`[A/B](C ++ B) = C ++ A`: the scan passes through `C` and replaces the
final occurrence. -/
theorem subst_suffix_unique (A B : List α) (hB : B ≠ []) : ∀ C : List α,
    (∀ u v, C ++ B = u ++ B ++ v → v = []) → subst A B (C ++ B) = C ++ A := by
  intro C
  induction C with
  | nil =>
      intro _
      cases B with
      | nil => exact absurd rfl hB
      | cons b B' =>
          show subst A (b :: B') (b :: B') = A
          rw [subst_cons_match A (b :: B') hB b B' [] (matchHere_self (b :: B')),
              subst_nil, List.append_nil]
  | cons c C' ih =>
      intro h
      have hC' : ∀ u v, C' ++ B = u ++ B ++ v → v = [] := by
        intro u v hv
        exact h (c :: u) v (by rw [List.cons_append, hv, List.cons_append,
          List.cons_append])
      rw [List.cons_append]
      cases hm : matchHere B (c :: (C' ++ B)) with
      | none =>
          rw [subst_cons_none _ _ _ _ hm]
          exact congrArg (c :: ·) (ih hC')
      | some D =>
          rw [subst_cons_match _ _ hB _ _ _ hm]
          have hD : D = [] := h [] D (by
            rw [List.nil_append]
            exact matchHere_app B (c :: (C' ++ B)) D hm)
          have heq : c :: (C' ++ B) = B ++ D := matchHere_app B _ _ hm
          rw [hD, List.append_nil] at heq
          have hl := congrArg List.length heq
          rw [List.length_cons, List.length_append] at hl
          omega

theorem matchHere_none_ne_cons {b : α} {L : List α} (w : List α)
    (h : matchHere [b] L = none) : L ≠ b :: w := by
  intro he
  rw [he] at h
  simp [matchHere] at h

/-- An `enc`-image followed by the marker `xb²` never begins with `b`. -/
theorem enc_app_head (b x : α) (hxb : x ≠ b) (S : List α) :
    matchHere [b] (enc b x S ++ [x, b, b]) = none := by
  cases hS : enc b x S with
  | nil =>
      have hb : b ≠ x := Ne.symm hxb
      simp [List.nil_append, matchHere, hb]
  | cons d T =>
      have hne : b ≠ d := by
        intro hbd
        have h2 := enc_not_startsWith_b b x hxb S
        rw [hS] at h2
        simp [matchHere, hbd] at h2
      simp [matchHere, List.cons_append, hne]

/-- The marker `xb^k`. -/
def marker (x b : α) (k : Nat) : List α := x :: List.replicate k b

/-- The marker `xb²` does not occur inside any `enc`-image. -/
theorem no_marker_occ (b x : α) (hxb : x ≠ b) : ∀ S : List α,
    ¬ Occ [x, b, b] (enc b x S) := by
  intro S
  induction S with
  | nil =>
      intro ⟨u, v, hv⟩
      rw [enc_nil] at hv
      cases u with
      | nil => simp at hv
      | cons a u' => simp at hv
  | cons c S' ih =>
      intro h
      by_cases hcb : c = b
      · subst hcb
        rw [enc_cons_b] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
          · exact ih h2
          · rw [List.cons_append] at hv'
            injection hv' with hd _
            exact hxb hd.symm
        · rw [List.cons_append] at hv
          injection hv with _ h1
          rw [List.cons_append] at h1
          injection h1 with _ henc
          exact matchHere_none_ne_cons v (enc_not_startsWith_b _ x hxb S') henc
      · rw [enc_cons_ne b x c S' hcb] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · exact ih h1
        · rw [List.cons_append] at hv
          injection hv with _ henc
          exact matchHere_none_ne_cons ([b] ++ v) (enc_not_startsWith_b b x hxb S') henc

/-- The only occurrence of the marker `xb²` in `enc Z ++ xb²` is the final one. -/
theorem m2_suffix_unique (b x : α) (hxb : x ≠ b) : ∀ (Z u v : List α),
    enc b x Z ++ [x, b, b] = u ++ [x, b, b] ++ v → u = enc b x Z ∧ v = [] := by
  intro Z
  induction Z with
  | nil =>
      intro u v hv
      rw [enc_nil, List.nil_append] at hv
      have hl := congrArg List.length hv
      simp only [List.length_append] at hl
      have hu : u = [] := by
        cases u with
        | nil => rfl
        | cons a u' => exfalso; simp only [List.length_cons] at hl; omega
      have hv' : v = [] := by
        cases v with
        | nil => rfl
        | cons a v' => exfalso; simp only [List.length_cons] at hl; omega
      exact ⟨by rw [enc_nil]; exact hu, hv'⟩
  | cons c Z' ih =>
      intro u v hv
      by_cases hcb : c = b
      · subst hcb
        rw [enc_cons_b, List.cons_append, List.cons_append] at hv
        cases u with
        | nil =>
            rw [List.nil_append, List.cons_append, List.cons_append, List.cons_append,
                List.nil_append] at hv
            injection hv with _ h1
            injection h1 with _ h2
            exact ((matchHere_none_ne_cons v (enc_app_head _ x hxb Z')) h2).elim
        | cons a u' =>
            rw [List.cons_append, List.cons_append] at hv
            injection hv with ha h1
            subst ha
            cases u' with
            | nil =>
                rw [List.nil_append, List.cons_append] at h1
                injection h1 with hb' _
                exact (hxb hb'.symm).elim
            | cons a₂ u₂ =>
                rw [List.cons_append, List.cons_append] at h1
                injection h1 with ha₂ h2
                subst ha₂
                refine ⟨?_, (ih u₂ v h2).2⟩
                rw [enc_cons_b, (ih u₂ v h2).1]
      · rw [enc_cons_ne b x c Z' hcb, List.cons_append] at hv
        cases u with
        | nil =>
            rw [List.nil_append, List.cons_append] at hv
            injection hv with _ h1
            exact ((matchHere_none_ne_cons ([b] ++ v) (enc_app_head b x hxb Z')) h1).elim
        | cons a u' =>
            rw [List.cons_append, List.cons_append] at hv
            injection hv with ha h1
            subst ha
            refine ⟨?_, (ih u' v h1).2⟩
            rw [enc_cons_ne b x c Z' hcb, (ih u' v h1).1]

/-! ## Lemma (Double Substitution) -/

/-- `W ⊏ Y`: `W` is a prefix of `Y`. -/
def IsPref (W Y : List α) : Prop := ∃ T, Y = W ++ T

/-- `W ⊐ Y`: `W` is a suffix of `Y`. -/
def IsSuff (W Y : List α) : Prop := ∃ T, Y = T ++ W

/-- `Y` is unbordered: no `W` other than `ε` and `Y` itself is both a
prefix and a suffix of `Y`. -/
def Unbordered (Y : List α) : Prop :=
  ∀ W : List α, (IsPref W Y ∧ IsSuff W Y) → (W = [] ∨ W = Y)

omit [DecidableEq α] in
/-- If `u ++ S = G ++ T` and `|u| ≤ |G|`, then `G` splits right after `u`. -/
theorem pref_of : ∀ (u G S T : List α), u ++ S = G ++ T → u.length ≤ G.length →
    ∃ A, G = u ++ A ∧ S = A ++ T := by
  intro u
  induction u with
  | nil => intro G S T h _; exact ⟨G, rfl, h⟩
  | cons u₀ u' ih =>
      intro G S T h hlen
      cases G with
      | nil => simp at hlen
      | cons g₀ G' =>
          rw [List.cons_append, List.cons_append] at h
          injection h with h₀ h'
          subst h₀
          obtain ⟨A, hG, hS⟩ := ih G' S T h' (by simp only [List.length_cons] at hlen; omega)
          exact ⟨A, by rw [hG]; rfl, hS⟩

omit [DecidableEq α] in
theorem occ_trans {X Y Z : List α} (h1 : Occ X Y) (h2 : Occ Y Z) : Occ X Z := by
  obtain ⟨u, v, hv⟩ := h1
  obtain ⟨s, t, ht⟩ := h2
  refine ⟨s ++ u, v ++ t, ?_⟩
  rw [ht, hv]
  simp [List.append_assoc]

/-- The greedy scan passes through a prefix in which no occurrence of `B`
starts: every `B`-occurrence of the whole text starts at `≥ |P|`. -/
theorem subst_leftmost_pass (A B : List α) :
    ∀ (P T : List α), (∀ u v, P ++ T = u ++ B ++ v → P.length ≤ u.length) →
      subst A B (P ++ T) = P ++ subst A B T := by
  intro P
  induction P with
  | nil => intro T _; rfl
  | cons c P' ih =>
      intro T h
      have hm : matchHere B (c :: (P' ++ T)) = none := by
        cases hme : matchHere B (c :: (P' ++ T)) with
        | none => rfl
        | some D =>
            exact absurd (h [] D (matchHere_app B (c :: (P' ++ T)) D hme)) (by simp)
      rw [List.cons_append, subst_cons_none _ _ _ _ hm]
      exact congrArg (c :: ·) (ih T (fun u v huv => by
        have hh := h (c :: u) v (congrArg (c :: ·) huv)
        simp only [List.length_cons] at hh
        omega))

/-- The greedy scan fires at the first position past such a prefix. -/
theorem subst_leftmost_fire (A B : List α) (hB : B ≠ []) (P T D : List α)
    (hcond : ∀ u v, P ++ T = u ++ B ++ v → P.length ≤ u.length)
    (hm : matchHere B T = some D) :
    subst A B (P ++ T) = P ++ A ++ subst A B D := by
  rw [subst_leftmost_pass A B P T hcond]
  cases B with
  | nil => exact absurd rfl hB
  | cons b B' =>
      have hTB : T = (b :: B') ++ D := matchHere_app (b :: B') T D hm
      rw [hTB] at hm ⊢
      rw [List.cons_append]
      have hm' : matchHere (b :: B') (b :: (B' ++ D)) = some D := hm
      rw [subst_cons_match A (b :: B') hB b (B' ++ D) D hm']
      simp [List.append_assoc]

/-- Every nonempty pattern that occurs has a leftmost occurrence. -/
theorem leftmost_occ (B : List α) (hB : B ≠ []) : ∀ (Z : List α), Occ B Z →
    ∃ G T D, Z = G ++ T ∧ matchHere B T = some D ∧
      (∀ u v, Z = u ++ B ++ v → G.length ≤ u.length) := by
  intro Z
  induction Z with
  | nil =>
      intro ho
      obtain ⟨u, v, hv⟩ := ho
      cases u with
      | nil =>
          rw [List.nil_append] at hv
          cases B with
          | nil => exact absurd rfl hB
          | cons b B' => rw [List.cons_append] at hv; exact nomatch hv
      | cons u₀ u' => rw [List.cons_append, List.cons_append] at hv; exact nomatch hv
  | cons c C ih =>
      intro ho
      cases hm : matchHere B (c :: C)
      · have hC : Occ B C := by
          rcases occ_cons_inv ho with h1 | ⟨v, hv⟩
          · exact h1
          · rw [show c :: C = B ++ v from hv] at hm
            rw [matchHere_prefix B v] at hm
            simp at hm
        obtain ⟨G, T, D, hC', hmT, hmin⟩ := ih hC
        refine ⟨c :: G, T, D, by rw [hC']; rfl, hmT, ?_⟩
        intro u v huv
        cases u with
        | nil =>
            rw [show c :: C = B ++ v from huv] at hm
            rw [matchHere_prefix B v] at hm
            simp at hm
        | cons u₀ u' =>
            have hC2 : C = u' ++ B ++ v := by
              rw [List.cons_append, List.cons_append] at huv
              injection huv with _ hC2'
            have h4 := hmin u' v hC2
            simp only [List.length_cons]
            omega
      · exact ⟨[], c :: C, _, rfl, hm, fun _ _ _ => Nat.zero_le _⟩

/-- Lemma (Double Substitution): with `X ⊂ Y` and `Y` unbordered,
`[X/Y][Y/X]Z = Z`. -/
theorem double_subst_aux (X Y : List α) (hX : X ≠ []) (hY : Unbordered Y) (hXY : Occ X Y) :
    ∀ (n : Nat) (Z : List α), Z.length ≤ n → subst X Y (subst Y X Z) = Z := by
  have hYne : Y ≠ [] := by
    intro he
    obtain ⟨u, v, hv⟩ := hXY
    rw [he] at hv
    cases u with
    | nil =>
        rw [List.nil_append] at hv
        cases X with
        | nil => exact absurd rfl hX
        | cons x₀ X' => rw [List.cons_append] at hv; exact nomatch hv
    | cons u₀ u' => rw [List.cons_append, List.cons_append] at hv; exact nomatch hv
  have h1X : 1 ≤ X.length := by
    cases X with
    | nil => exact absurd rfl hX
    | cons x₀ X' => simp
  intro n
  induction n with
  | zero =>
      intro Z hZ
      cases Z with
      | nil => rw [subst_nil, subst_nil]
      | cons c C => simp at hZ
  | succ n ih =>
      intro Z hZ
      by_cases hocc : Occ X Z
      · obtain ⟨G, T, D, hZT, hmT, hmin⟩ := leftmost_occ X hX Z hocc
        have hTD : T = X ++ D := matchHere_app X T D hmT
        have hGnoX : ¬ Occ X G := by
          intro ho
          obtain ⟨a, b, hGab⟩ := ho
          have hz : Z = a ++ X ++ (b ++ T) := by rw [hZT, hGab]; simp [List.append_assoc]
          have hmin' := hmin a (b ++ T) hz
          have hlen := congrArg List.length hGab
          simp [List.length_append] at hlen
          omega
        have hYcond : ∀ u v, G ++ (Y ++ subst Y X D) = u ++ Y ++ v →
            G.length ≤ u.length := by
          intro u v huv
          by_cases hlt : u.length < G.length
          · exfalso
            simp only [List.append_assoc] at huv
            obtain ⟨A, hG, hS⟩ := pref_of u G (Y ++ v) (Y ++ subst Y X D) huv.symm
              (Nat.le_of_lt hlt)
            have hGA : G.length = u.length + A.length := by
              rw [hG]; exact List.length_append
            have hA0 : 0 < A.length := by omega
            by_cases hAB : A.length < Y.length
            · -- straddle: extract a proper border of Y
              obtain ⟨B, hY1, hS2⟩ := pref_of A Y (Y ++ subst Y X D) v hS.symm
                (Nat.le_of_lt hAB)
              have hYB : Y.length = A.length + B.length := by
                rw [hY1]; exact List.length_append
              obtain ⟨C, hY2, _⟩ := pref_of B Y v (subst Y X D) hS2.symm (by omega)
              rcases hY B ⟨⟨C, hY2⟩, ⟨A, hY1⟩⟩ with hB1 | hB2
              · rw [hB1] at hYB; simp at hYB; omega
              · rw [hB2] at hYB; omega
            · -- ends inside the gap: Y ⊂ G, hence X ⊂ G
              obtain ⟨A', hA', _⟩ := pref_of Y A v (Y ++ subst Y X D) hS (by omega)
              exact hGnoX (occ_trans hXY ⟨u, A', by
                rw [hG, hA']; exact (List.append_assoc u Y A').symm⟩)
          · omega
        have hZlen : Z.length = G.length + T.length := by
          rw [hZT]; exact List.length_append
        have hTlen : T.length = X.length + D.length := by
          rw [hTD]; exact List.length_append
        have hDlen : D.length ≤ n := by omega
        rw [hZT, subst_leftmost_fire Y X hX G T D
            (fun u v huv => hmin u v (by rw [hZT]; exact huv)) hmT,
          List.append_assoc,
          subst_leftmost_fire X Y hYne G (Y ++ subst Y X D) (subst Y X D) hYcond
            (matchHere_prefix Y (subst Y X D)),
          ih D hDlen, hTD]
        exact List.append_assoc G X D
      · have hnoY : ¬ Occ Y Z := fun ho => hocc (occ_trans hXY ho)
        rw [subst_no_occ Y X Z hocc, subst_no_occ X Y Z hnoY]

theorem double_subst {X Y : List α} (hX : X ≠ []) (hY : Unbordered Y) (hXY : Occ X Y)
    (Z : List α) : subst X Y (subst Y X Z) = Z :=
  double_subst_aux X Y hX hY hXY Z.length Z (Nat.le_refl _)

-- The unborderedness hypothesis is essential: `Y = "aba"` is bordered by `"a"`.
#eval subst ['b', 'a'] ['a', 'b', 'a'] (subst ['a', 'b', 'a'] ['b', 'a'] ['b', 'a', 'a', 'b', 'b', 'a'])
-- [b, a, b, a, b, a] ≠ "baabba"

/-! ## Theorem (cat): concatenation -/

/-- Theorem (cat): `dec([enc(Y)/xb³][enc(X)/xb²](xb²xb³))`. -/
def cat (b x : α) (X Y : List α) : List α :=
  dec b x (subst (enc b x X) (marker x b 2)
    (subst (enc b x Y) (marker x b 3) (marker x b 2 ++ marker x b 3)))

theorem cat_step1 (b x : α) (hxb : x ≠ b) (Y : List α) :
    subst (enc b x Y) (marker x b 3) (marker x b 2 ++ marker x b 3)
      = marker x b 2 ++ enc b x Y := by
  have hb : b ≠ x := Ne.symm hxb
  show subst (enc b x Y) [x, b, b, b] (x :: b :: b :: x :: b :: b :: b :: [])
      = x :: b :: b :: enc b x Y
  have h0 : matchHere [x, b, b, b] (x :: b :: b :: x :: b :: b :: b :: []) = none := by
    simp [matchHere, hb]
  rw [subst_cons_none _ _ _ _ h0]
  show x :: subst (enc b x Y) [x, b, b, b] (b :: b :: x :: b :: b :: b :: [])
      = x :: b :: b :: enc b x Y
  have h1 : matchHere [x, b, b, b] (b :: b :: x :: b :: b :: b :: []) = none := by
    simp [matchHere, hb]
  rw [subst_cons_none _ _ _ _ h1]
  show x :: b :: subst (enc b x Y) [x, b, b, b] (b :: x :: b :: b :: b :: [])
      = x :: b :: b :: enc b x Y
  have h2 : matchHere [x, b, b, b] (b :: x :: b :: b :: b :: []) = none := by
    simp [matchHere, hb]
  rw [subst_cons_none _ _ _ _ h2]
  rw [subst_cons_match _ _ (by simp) _ _ [] (matchHere_self [x, b, b, b]), subst_nil,
      List.append_nil]

theorem cat_step2 (b x : α) (hxb : x ≠ b) (X Y : List α) :
    subst (enc b x X) (marker x b 2) (marker x b 2 ++ enc b x Y)
      = enc b x X ++ enc b x Y := by
  have h1 : matchHere [x, b, b] (x :: ([b, b] ++ enc b x Y)) = some (enc b x Y) :=
    matchHere_prefix [x, b, b] (enc b x Y)
  show subst (enc b x X) [x, b, b] (x :: ([b, b] ++ enc b x Y)) = enc b x X ++ enc b x Y
  rw [subst_cons_match _ _ (by simp) _ _ _ h1]
  exact congrArg (enc b x X ++ ·) (subst_no_occ (enc b x X) [x, b, b] (enc b x Y)
    (no_marker_occ b x hxb Y))

theorem cat_correct (b x : α) (hxb : x ≠ b) (X Y : List α) :
    cat b x X Y = X ++ Y := by
  show dec b x (subst (enc b x X) (marker x b 2)
      (subst (enc b x Y) (marker x b 3) (marker x b 2 ++ marker x b 3))) = X ++ Y
  rw [cat_step1 b x hxb Y, cat_step2 b x hxb X Y, ← enc_append, dec_enc b x hxb]

#eval cat 'b' 'x' ['a', 'b'] ['c']                    -- [a, b, c]
#eval cat 'b' 'x' [] []                               -- []
#eval cat 'b' 'x' ['b', 'b', 'x'] ['x', 'x', 'b']     -- marker-poisoned input: [b, b, x, x, x, b]

/-! ## Theorem (benc round trip) and Theorem (eq) -/

/-- `enc` with marker borders. -/
def benc (b x : α) (X : List α) : List α :=
  marker x b 2 ++ enc b x X ++ marker x b 2

/-- Strip the borders. -/
def bdec (b x : α) (S : List α) : List α := subst [] (marker x b 2) S

/-- In a bordered encoding `benc(X)`, the marker `xb²` occurs only as the
two borders. -/
theorem occ_m2_benc (b x : α) (hxb : x ≠ b) (X u v : List α)
    (h : benc b x X = u ++ marker x b 2 ++ v) :
    u = [] ∨ u = marker x b 2 ++ enc b x X := by
  have hm : marker x b 2 = [x, b, b] := rfl
  rw [hm] at h ⊢
  rw [show benc b x X = x :: b :: b :: (enc b x X ++ [x, b, b]) from rfl] at h
  cases u with
  | nil => exact Or.inl rfl
  | cons a u' =>
      rw [List.cons_append, List.cons_append] at h
      injection h with ha h1
      subst ha
      cases u' with
      | nil =>
          rw [List.nil_append, List.cons_append] at h1
          injection h1 with hb' _
          exact (hxb hb'.symm).elim
      | cons a₂ u₂ =>
          rw [List.cons_append, List.cons_append] at h1
          injection h1 with ha₂ h2
          subst ha₂
          cases u₂ with
          | nil =>
              rw [List.nil_append, List.cons_append] at h2
              injection h2 with hb'' _
              exact (hxb hb''.symm).elim
          | cons a₃ u₃ =>
              rw [List.cons_append, List.cons_append] at h2
              injection h2 with ha₃ h3
              subst ha₃
              refine Or.inr ?_
              rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append,
                (m2_suffix_unique b x hxb X u₃ v h3).1]

/-- Border injectivity: if `benc(Y)` occurs in `benc(X)` then `Y = X`. -/
theorem benc_occ_inv (b x : α) (hxb : x ≠ b) (X Y : List α) :
    Occ (benc b x Y) (benc b x X) → Y = X := by
  rintro ⟨u, v, hv⟩
  have hY : benc b x Y = [x, b, b] ++ (enc b x Y ++ [x, b, b]) := rfl
  rw [hY] at hv
  have htrailing : benc b x X = (u ++ [x, b, b] ++ enc b x Y) ++ [x, b, b] ++ v := by
    rw [hv]; simp [List.append_assoc]
  have hleading : benc b x X = u ++ [x, b, b] ++ ((enc b x Y ++ [x, b, b]) ++ v) := by
    rw [hv]; simp [List.append_assoc]
  rcases occ_m2_benc b x hxb X (u ++ [x, b, b] ++ enc b x Y) v htrailing with hw1 | hw2
  · simp at hw1
  · rcases occ_m2_benc b x hxb X u ((enc b x Y ++ [x, b, b]) ++ v) hleading with hu1 | hu2
    · rw [hu1, List.nil_append] at hw2
      have henc : enc b x Y = enc b x X := append_left_cancel [x, b, b] _ _ hw2
      rw [← dec_enc b x hxb Y, henc, dec_enc b x hxb X]
    · rw [hu2] at hw2
      have hl := congrArg List.length hw2
      simp [marker, List.replicate, List.length_append] at hl

theorem bdec_benc (b x : α) (hxb : x ≠ b) (X : List α) :
    bdec b x (benc b x X) = enc b x X := by
  show subst [] [x, b, b] (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = enc b x X
  have h1 : matchHere [x, b, b] (x :: ([b, b] ++ (enc b x X ++ [x, b, b])))
      = some (enc b x X ++ [x, b, b]) :=
    matchHere_prefix [x, b, b] (enc b x X ++ [x, b, b])
  rw [subst_cons_match [] [x, b, b] (by simp) x _ _ h1, List.nil_append]
  have h2 := subst_suffix_unique [] [x, b, b] (by simp) (enc b x X)
    (fun u v hv => (m2_suffix_unique b x hxb X u v hv).2)
  rw [List.append_nil] at h2
  exact h2

/-- Theorem (eq): `[⊥/benc(X)][⊤/benc(Y)]benc(X)`. -/
def eqC (top bot b x : α) (X Y : List α) : List α :=
  subst [bot] (benc b x X) (subst [top] (benc b x Y) (benc b x X))

/-- The paper picks distinct `⊤ ≠ ⊥` merely to name the two outputs; the
proof below needs no distinctness of `⊤`, `⊥` at all. -/
theorem eqC_correct (top bot b x : α) (hxb : x ≠ b) (X Y : List α) :
    eqC top bot b x X Y = if X = Y then [top] else [bot] := by
  have h1 : subst [top] (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = [top] := by
    have hm : matchHere (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = some [] :=
      matchHere_self (benc b x X)
    rw [subst_cons_match [top] (benc b x X) (by simp [benc, marker]) x _ _ hm, subst_nil,
        List.append_nil]
  by_cases hXY : X = Y
  · subst hXY
    show subst [bot] (benc b x X)
        (subst [top] (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))))
      = (if X = X then [top] else [bot])
    rw [h1]
    have h2 : ¬ Occ (benc b x X) [top] := by
      intro ho
      have hl := occ_length ho
      simp [benc, marker, List.replicate, List.length_append] at hl
    rw [subst_no_occ [bot] (benc b x X) [top] h2]
    simp
  · have hne : ¬ Occ (benc b x Y) (benc b x X) :=
      fun ho => hXY (benc_occ_inv b x hxb X Y ho).symm
    show subst [bot] (benc b x X) (subst [top] (benc b x Y) (benc b x X))
      = (if X = Y then [top] else [bot])
    rw [subst_no_occ [top] (benc b x Y) (benc b x X) hne]
    show subst [bot] (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b])))
      = (if X = Y then [top] else [bot])
    have hm : matchHere (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = some [] :=
      matchHere_self (benc b x X)
    rw [subst_cons_match [bot] (benc b x X) (by simp [benc, marker]) x _ _ hm, subst_nil,
        List.append_nil]
    simp [hXY]

#eval eqC 't' 'f' 'b' 'x' ['a', 'b'] ['a', 'b']        -- [t]
#eval eqC 't' 'f' 'b' 'x' ['a', 'b'] ['a', 'c']        -- [f]
#eval eqC 't' 'f' 'b' 'x' [] []                        -- [t]

/-! ## Theorem (Selection, `if`) -/

/-- Theorem (Selection): `[enc(Y)/bb][enc(X)/⊤][bb/⊥]C` (rightmost first). -/
def iteC (top bot b x : α) (C X Y : List α) : List α :=
  dec b x (subst (enc b x Y) [b, b]
    (subst (enc b x X) [top] (subst [b, b] [bot] C)))

theorem iteC_correct (top bot b x : α) (hxb : x ≠ b) (htb : top ≠ b) (htop : top ≠ bot)
    (C X Y : List α) (hC : C = [top] ∨ C = [bot]) :
    iteC top bot b x C X Y = if C = [top] then X else Y := by
  rcases hC with hC | hC
  · subst hC
    have hn1 : ¬ Occ [bot] [top] := by
      intro ho
      have h := occ_single.1 ho
      simp at h
      exact htop h.symm
    have h1 : subst [b, b] [bot] [top] = [top] := subst_no_occ [b, b] [bot] [top] hn1
    have h2 : subst (enc b x X) [top] [top] = enc b x X := by
      rw [subst_cons_match (enc b x X) [top] (by simp) top _ []
            (matchHere_self [top]), subst_nil, List.append_nil]
    have h3 : subst (enc b x Y) [b, b] (enc b x X) = enc b x X :=
      subst_no_occ (enc b x Y) [b, b] (enc b x X) (no_bb b x hxb X)
    show dec b x (subst (enc b x Y) [b, b] (subst (enc b x X) [top] (subst [b, b] [bot] [top])))
      = (if [top] = [top] then X else Y)
    rw [h1, h2, h3, dec_enc b x hxb]
    simp
  · subst hC
    have h1 : subst [b, b] [bot] [bot] = [b, b] := by
      rw [subst_cons_match [b, b] [bot] (by simp) bot _ [] (matchHere_self [bot]), subst_nil,
          List.append_nil]
    have hn2 : ¬ Occ [top] [b, b] := by
      intro ho
      have h := occ_single.1 ho
      rcases List.mem_cons.1 h with h' | h'
      · exact htb h'
      · rcases List.mem_cons.1 h' with h'' | h''
        · exact htb h''
        · cases h''
    have h2 : subst (enc b x X) [top] [b, b] = [b, b] :=
      subst_no_occ (enc b x X) [top] [b, b] hn2
    have h3 : subst (enc b x Y) [b, b] [b, b] = enc b x Y := by
      rw [subst_cons_match (enc b x Y) [b, b] (by simp) b _ [] (matchHere_self [b, b]),
          subst_nil, List.append_nil]
    show dec b x (subst (enc b x Y) [b, b] (subst (enc b x X) [top] (subst [b, b] [bot] [bot])))
      = (if [bot] = [top] then X else Y)
    rw [h1, h2, h3, dec_enc b x hxb]
    have hne : ([bot] : List α) ≠ [top] := by
      intro he
      injection he with h'
      exact htop h'.symm
    simp [hne]

#eval iteC 't' 'f' 'b' 'x' ['t'] ['y', 'e', 's'] ['n', 'o']   -- [y, e, s]
#eval iteC 't' 'f' 'b' 'x' ['f'] ['y', 'e', 's'] ['n', 'o']   -- [n, o]

/-! ## Theorem (head and tail) -/

/-- The deletion cascade of `tail` for the alphabet `σ₁ :: σ₂ :: rest`. -/
def tailCascade (s1 : α) : List α → List α → List α
  | [], T => T
  | c :: cs, T => subst [] [s1, s1, c] (tailCascade s1 cs T)

/-- Theorem (tail): everything but the first character. -/
def tail (sig : List α) (X : List α) : List α :=
  match sig with
  | s1 :: s2 :: rest =>
      dec s1 s2 (subst [] [s1, s1]
        (subst [] [s1, s1, s2]
          (subst [] [s1, s1, s2, s1]
            (tailCascade s1 rest ([s1, s1] ++ enc s1 s2 X)))))
  | _ => X

/-- Theorem (head): the first character. -/
def head (sig : List α) (X : List α) : List α :=
  match sig with
  | s1 :: s2 :: _ =>
      dec s1 s2 (subst [] (enc s1 s2 (tail sig X) ++ [s1, s1])
        (enc s1 s2 X ++ [s1, s1]))
  | _ => X

/-! ### The `tail` cascade -/

/-- No pattern containing `σ₁σ₁` occurs in an `enc`-image (by (F1)). -/
theorem no_s1s1_occ (s1 s2 : α) (hs : s2 ≠ s1) (Z : List α) (c : α) :
    ¬ Occ [s1, s1, c] (enc s1 s2 Z) :=
  fun h => no_bb s1 s2 hs Z (occ_left (p := [s1, s1]) (q := [c]) h)

theorem no_s1s1s2s1_occ (s1 s2 : α) (hs : s2 ≠ s1) (Z : List α) :
    ¬ Occ [s1, s1, s2, s1] (enc s1 s2 Z) :=
  fun h => no_bb s1 s2 hs Z (occ_left (p := [s1, s1]) (q := [s2, s1]) h)

/-- `[ε/σ₁σ₁d]` is inert on `σ₁σ₁·enc(Z)` unless `Z` starts with `d`. -/
theorem no_s1s1c_pref (s1 s2 d : α) (hs : s2 ≠ s1) (hd2 : d ≠ s2)
    (Z : List α) (hZ : ∀ Z', Z ≠ d :: Z') :
    ¬ Occ [s1, s1, d] ([s1, s1] ++ enc s1 s2 Z) := by
  intro h
  rw [List.cons_append, List.cons_append, List.nil_append] at h
  rcases occ_cons_inv h with h1 | ⟨v, hv⟩
  · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
    · exact no_s1s1_occ s1 s2 hs Z d h2
    · rw [List.cons_append] at hv'
      injection hv' with _ henc
      exact matchHere_none_ne_cons ([d] ++ v') (enc_not_startsWith_b s1 s2 hs Z) henc
  · rw [List.cons_append] at hv
    injection hv with _ h1
    rw [List.cons_append] at h1
    injection h1 with _ henc
    cases Z with
    | nil => rw [enc_nil] at henc; simp at henc
    | cons z Z' =>
        by_cases hz : z = s1
        · rw [hz, enc_cons_b, List.cons_append, List.nil_append] at henc
          injection henc with hd0 _
          exact hd2 hd0.symm
        · rw [enc_cons_ne s1 s2 z Z' hz, List.cons_append, List.nil_append] at henc
          injection henc with hd0 _
          exact hZ Z' (by rw [hd0])

/-- `[ε/σ₁σ₁σ₂σ₁]` is inert on `σ₁σ₁·enc(Z)` unless `Z` starts with `σ₁`. -/
theorem no_s1s1s2s1_pref (s1 s2 : α) (hs : s2 ≠ s1) (Z : List α)
    (hZ : ∀ Z', Z ≠ s1 :: Z') :
    ¬ Occ [s1, s1, s2, s1] ([s1, s1] ++ enc s1 s2 Z) := by
  intro h
  rw [List.cons_append, List.cons_append, List.nil_append] at h
  rcases occ_cons_inv h with h1 | ⟨v, hv⟩
  · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
    · exact no_s1s1s2s1_occ s1 s2 hs Z h2
    · rw [List.cons_append] at hv'
      injection hv' with _ henc
      exact matchHere_none_ne_cons ([s2, s1] ++ v') (enc_not_startsWith_b s1 s2 hs Z) henc
  · rw [List.cons_append] at hv
    injection hv with _ h1
    rw [List.cons_append] at h1
    injection h1 with _ h1'
    cases Z with
    | nil => rw [enc_nil] at h1'; simp at h1'
    | cons z Z' =>
        by_cases hz : z = s1
        · exact hZ Z' (by rw [hz])
        · rw [enc_cons_ne s1 s2 z Z' hz, List.cons_append, List.cons_append,
              List.nil_append] at h1'
          injection h1' with hz2 henc'
          exact matchHere_none_ne_cons v (enc_not_startsWith_b s1 s2 hs Z') henc'

theorem subst_prefix_fire (s1 s2 d : α) (hs : s2 ≠ s1) (hd : d ≠ s1) (Z' : List α) :
    subst [] [s1, s1, d] ([s1, s1] ++ enc s1 s2 (d :: Z')) = enc s1 s2 Z' := by
  have h1 : enc s1 s2 (d :: Z') = d :: enc s1 s2 Z' := enc_cons_ne s1 s2 d Z' hd
  rw [h1]
  show subst [] [s1, s1, d] (s1 :: (s1 :: (d :: enc s1 s2 Z'))) = enc s1 s2 Z'
  have hm : matchHere [s1, s1, d] (s1 :: (s1 :: (d :: enc s1 s2 Z')))
      = some (enc s1 s2 Z') :=
    matchHere_prefix [s1, s1, d] (enc s1 s2 Z')
  rw [subst_cons_match [] [s1, s1, d] (by simp) s1 _ _ hm, List.nil_append]
  exact subst_no_occ [] [s1, s1, d] (enc s1 s2 Z') (no_s1s1_occ s1 s2 hs Z' d)

theorem subst_prefix_fire_s1 (s1 s2 : α) (hs : s2 ≠ s1) (Z' : List α) :
    subst [] [s1, s1, s2, s1] ([s1, s1] ++ enc s1 s2 (s1 :: Z')) = enc s1 s2 Z' := by
  have h1 : enc s1 s2 (s1 :: Z') = s2 :: s1 :: enc s1 s2 Z' := enc_cons_b s1 s2 Z'
  rw [h1]
  show subst [] [s1, s1, s2, s1] (s1 :: (s1 :: (s2 :: (s1 :: enc s1 s2 Z'))))
    = enc s1 s2 Z'
  have hm : matchHere [s1, s1, s2, s1] (s1 :: (s1 :: (s2 :: (s1 :: enc s1 s2 Z'))))
      = some (enc s1 s2 Z') :=
    matchHere_prefix [s1, s1, s2, s1] (enc s1 s2 Z')
  rw [subst_cons_match [] [s1, s1, s2, s1] (by simp) s1 _ _ hm, List.nil_append]
  exact subst_no_occ [] [s1, s1, s2, s1] (enc s1 s2 Z') (no_s1s1s2s1_occ s1 s2 hs Z')

/-- The deletion cascade leaves `σ₁σ₁·enc(Z)` untouched when `Z` starts with
none of its characters. -/
theorem tailCascade_inert (s1 s2 : α) (hs : s2 ≠ s1) :
    ∀ (cs Z : List α), (∀ c ∈ cs, c ≠ s1 ∧ c ≠ s2) →
      (∀ c ∈ cs, ∀ Z'', Z ≠ c :: Z'') →
      tailCascade s1 cs ([s1, s1] ++ enc s1 s2 Z) = [s1, s1] ++ enc s1 s2 Z := by
  intro cs
  induction cs with
  | nil => intro Z _ _; rfl
  | cons d cs' ih =>
      intro Z hcs hZ
      have hcs' : ∀ c ∈ cs', c ≠ s1 ∧ c ≠ s2 := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
      have hZ' : ∀ c ∈ cs', ∀ Z'', Z ≠ c :: Z'' :=
        fun c hc Z'' => hZ c (List.mem_cons_of_mem _ hc) Z''
      show subst [] [s1, s1, d] (tailCascade s1 cs' ([s1, s1] ++ enc s1 s2 Z))
        = [s1, s1] ++ enc s1 s2 Z
      rw [ih Z hcs' hZ']
      exact subst_no_occ [] [s1, s1, d] ([s1, s1] ++ enc s1 s2 Z)
        (no_s1s1c_pref s1 s2 d hs (hcs d (List.mem_cons_self ..)).2 Z
          (hZ d (List.mem_cons_self ..)))

/-- If `Z` starts with a character `d` of the cascade, the cascade deletes the
marker and `d`, leaving `enc(Z)`. -/
theorem tailCascade_fire (s1 s2 : α) (hs : s2 ≠ s1) (d : α) (hd : d ≠ s1) (Z' : List α) :
    ∀ (cs : List α), (∀ c ∈ cs, c ≠ s1 ∧ c ≠ s2) → d ∈ cs →
      tailCascade s1 cs ([s1, s1] ++ enc s1 s2 (d :: Z')) = enc s1 s2 Z' := by
  intro cs
  induction cs with
  | nil => intro _ hin; exact absurd hin (by simp)
  | cons e cs' ih =>
      intro hcs hin
      have hcs' : ∀ c ∈ cs', c ≠ s1 ∧ c ≠ s2 := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
      show subst [] [s1, s1, e] (tailCascade s1 cs' ([s1, s1] ++ enc s1 s2 (d :: Z')))
        = enc s1 s2 Z'
      rcases List.mem_cons.1 hin with hde | hin'
      · subst hde
        by_cases hdIn' : d ∈ cs'
        · rw [ih hcs' hdIn']
          exact subst_no_occ [] [s1, s1, d] (enc s1 s2 Z') (no_s1s1_occ s1 s2 hs Z' d)
        · rw [tailCascade_inert s1 s2 hs cs' (d :: Z') hcs'
            (fun c hc Z'' heq => hdIn' (by injection heq with hcd _; rw [hcd]; exact hc))]
          exact subst_prefix_fire s1 s2 d hs hd Z'
      · rw [ih hcs' hin']
        exact subst_no_occ [] [s1, s1, e] (enc s1 s2 Z') (no_s1s1_occ s1 s2 hs Z' e)

theorem tail_correct (sig : List α) (hnd : sig.Pairwise (· ≠ ·)) (h2 : 2 ≤ sig.length)
    (X : List α) (hX : ∀ c ∈ X, c ∈ sig) :
    tail sig X = X.drop 1 := by
  cases sig with
  | nil => simp at h2
  | cons s1 sig' =>
      cases sig' with
      | nil => simp at h2
      | cons s2 rest =>
          rw [List.pairwise_cons] at hnd
          have hnd2 := hnd.2
          rw [List.pairwise_cons] at hnd2
          have hs : s2 ≠ s1 := fun he => hnd.1 s2 (List.mem_cons_self ..) he.symm
          have hrest : ∀ c ∈ rest, c ≠ s1 ∧ c ≠ s2 := by
            intro c hc
            exact ⟨fun he => hnd.1 c (List.mem_cons_of_mem _ hc) he.symm,
                   fun he => hnd2.1 c hc he.symm⟩
          show dec s1 s2 (subst [] [s1, s1]
            (subst [] [s1, s1, s2]
              (subst [] [s1, s1, s2, s1]
                (tailCascade s1 rest ([s1, s1] ++ enc s1 s2 X)))))
            = X.drop 1
          cases X with
          | nil =>
              rw [tailCascade_inert s1 s2 hs rest [] hrest
                (fun c _ Z'' heq => nomatch heq),
                enc_nil, List.append_nil]
              have hn4 : ¬ Occ [s1, s1, s2, s1] [s1, s1] := by
                intro ho
                have hl := occ_length ho
                simp at hl
              rw [subst_no_occ [] [s1, s1, s2, s1] [s1, s1] hn4]
              have hn3 : ¬ Occ [s1, s1, s2] [s1, s1] := by
                intro ho
                have hl := occ_length ho
                simp at hl
              rw [subst_no_occ [] [s1, s1, s2] [s1, s1] hn3,
                subst_cons_match [] [s1, s1] (by simp) s1 _ []
                  (matchHere_self [s1, s1]), subst_nil, List.nil_append, dec_nil]
              simp
          | cons c X' =>
              rcases List.mem_cons.1 (hX c (List.mem_cons_self ..)) with hc | hc
              · rw [hc, tailCascade_inert s1 s2 hs rest (s1 :: X') hrest
                  (fun c' hc' Z'' heq =>
                    (hrest c' hc').1 (by injection heq with hcd _; exact hcd.symm)),
                  subst_prefix_fire_s1 s1 s2 hs X',
                  subst_no_occ [] [s1, s1, s2] (enc s1 s2 X') (no_s1s1_occ s1 s2 hs X' s2),
                  subst_no_occ [] [s1, s1] (enc s1 s2 X') (no_bb s1 s2 hs X'),
                  dec_enc s1 s2 hs]
                simp
              · rcases List.mem_cons.1 hc with hc | hc
                · rw [hc, tailCascade_inert s1 s2 hs rest (s2 :: X') hrest
                    (fun c' hc' Z'' heq =>
                      (hrest c' hc').2 (by injection heq with hcd _; exact hcd.symm)),
                    subst_no_occ [] [s1, s1, s2, s1] ([s1, s1] ++ enc s1 s2 (s2 :: X'))
                      (no_s1s1s2s1_pref s1 s2 hs (s2 :: X')
                        (fun Z'' heq => hs (by injection heq with hcd _))),
                    subst_prefix_fire s1 s2 s2 hs hs X',
                    subst_no_occ [] [s1, s1] (enc s1 s2 X') (no_bb s1 s2 hs X'),
                    dec_enc s1 s2 hs]
                  simp
                · rw [tailCascade_fire s1 s2 hs c (hrest c hc).1 X' rest hrest hc,
                    subst_no_occ [] [s1, s1, s2, s1] (enc s1 s2 X')
                      (no_s1s1s2s1_occ s1 s2 hs X'),
                    subst_no_occ [] [s1, s1, s2] (enc s1 s2 X') (no_s1s1_occ s1 s2 hs X' s2),
                    subst_no_occ [] [s1, s1] (enc s1 s2 X') (no_bb s1 s2 hs X'),
                    dec_enc s1 s2 hs]
                  simp

/-! ### The `head` machinery -/

theorem matchHere_ne (b : α) (B' : List α) (c : α) (C : List α) (hbc : b ≠ c) :
    matchHere (b :: B') (c :: C) = none := by
  simp [matchHere, hbc]

theorem subst_self (A B : List α) (hB : B ≠ []) : subst A B B = A := by
  cases B with
  | nil => exact absurd rfl hB
  | cons b B' =>
      rw [subst_cons_match A (b :: B') hB b B' [] (matchHere_self (b :: B')), subst_nil,
        List.append_nil]

theorem dec_single (s1 s2 : α) (hs : s2 ≠ s1) (c : α) (hc : c ≠ s1) : dec s1 s2 [c] = [c] := by
  have hE : enc s1 s2 [c] = [c] := by rw [enc_cons_ne s1 s2 c [] hc, enc_nil]
  rw [← hE, dec_enc s1 s2 hs [c], hE]

theorem dec_s2s1 (s1 s2 : α) (hs : s2 ≠ s1) : dec s1 s2 [s2, s1] = [s1] := by
  have hE : enc s1 s2 [s1] = [s2, s1] := by rw [enc_cons_b s1 s2 [], enc_nil]
  rw [← hE, dec_enc s1 s2 hs [s1]]

/-- First-position self-match of the head pattern is impossible: for `c ≠ σ₁`,
`c·Q` is never `Q` glued to a tail (the paper's "second candidate" for `a ≠ σ₁`). -/
theorem head_no_pos0 (s1 s2 : α) (hs : s2 ≠ s1) :
    ∀ (X' : List α) (c : α), c ≠ s1 → ∀ D : List α,
      c :: (enc s1 s2 X' ++ [s1, s1]) = (enc s1 s2 X' ++ [s1, s1]) ++ D → False := by
  intro X'
  induction X' with
  | nil =>
      intro c hc D h
      rw [enc_nil, List.nil_append, List.cons_append, List.cons_append,
        List.nil_append] at h
      injection h with h0 _
      exact hc h0
  | cons x X'' ih =>
      intro c hc D h
      by_cases hx : x = s1
      · rw [hx, enc_cons_b s1 s2 X'', List.cons_append, List.cons_append,
          List.cons_append, List.cons_append] at h
        injection h with _ h1
        injection h1 with h2 _
        exact hs h2
      · rw [enc_cons_ne s1 s2 x X'' hx, List.cons_append, List.cons_append] at h
        injection h with hcx h2
        exact ih x (by rw [← hcx]; exact hc) D h2

/-- Two-position self-match is impossible too (the `a = σ₁` candidates): neither
`σ₂σ₁·Q` nor `σ₁σ₂·Q` equals `Q` glued to a tail. -/
theorem no_border_both (s1 s2 : α) (hs : s2 ≠ s1) :
    ∀ (X' D : List α),
      (s2 :: s1 :: (enc s1 s2 X' ++ [s1, s1])
          = (enc s1 s2 X' ++ [s1, s1]) ++ D → False) ∧
      (s1 :: s2 :: (enc s1 s2 X' ++ [s1, s1])
          = (enc s1 s2 X' ++ [s1, s1]) ++ D → False) := by
  intro X'
  induction X' with
  | nil =>
      intro D
      rw [enc_nil, List.nil_append, List.cons_append, List.cons_append, List.nil_append]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · injection h with h0 _
        exact hs h0
      · injection h with _ h1
        injection h1 with h2 _
        exact hs h2
  | cons x X'' ih =>
      intro D
      by_cases hx : x = s1
      · rw [hx, enc_cons_b s1 s2 X'', List.cons_append, List.cons_append,
          List.cons_append, List.cons_append]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · injection h with _ h1
          injection h1 with _ h4
          exact (ih D).1 h4
        · injection h with h1 _
          exact hs h1.symm
      · rw [enc_cons_ne s1 s2 x X'' hx, List.cons_append, List.cons_append]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · injection h with h1 h2
          subst h1
          exact (ih D).2 h2
        · injection h with h1 h2
          subst h1
          exact (ih D).1 h2

theorem head_correct (sig : List α) (hnd : sig.Pairwise (· ≠ ·)) (h2 : 2 ≤ sig.length)
    (X : List α) (hX : ∀ c ∈ X, c ∈ sig) : head sig X = X.take 1 := by
  have htail : tail sig X = X.drop 1 := tail_correct sig hnd h2 X hX
  cases sig with
  | nil => simp at h2
  | cons s1 sig' =>
      cases sig' with
      | nil => simp at h2
      | cons s2 rest =>
          rw [List.pairwise_cons] at hnd
          have hs : s2 ≠ s1 := fun he => hnd.1 s2 (List.mem_cons_self ..) he.symm
          show dec s1 s2 (subst [] (enc s1 s2 (tail (s1 :: s2 :: rest) X) ++ [s1, s1])
            (enc s1 s2 X ++ [s1, s1])) = X.take 1
          rw [htail]
          cases X with
          | nil =>
              show dec s1 s2 (subst [] (enc s1 s2 [] ++ [s1, s1])
                (enc s1 s2 [] ++ [s1, s1])) = []
              rw [enc_nil, List.nil_append,
                subst_cons_match [] [s1, s1] (by simp) s1 _ [] (matchHere_self [s1, s1]),
                subst_nil, List.nil_append, dec_nil]
          | cons c X' =>
              have hQne : enc s1 s2 X' ++ [s1, s1] ≠ [] := by
                intro he
                cases hE : enc s1 s2 X' with
                | nil => rw [hE, List.nil_append] at he; exact nomatch he
                | cons e E' => rw [hE, List.cons_append] at he; exact nomatch he
              show dec s1 s2 (subst [] (enc s1 s2 X' ++ [s1, s1])
                (enc s1 s2 (c :: X') ++ [s1, s1])) = [c]
              by_cases hcb : c = s1
              · rw [hcb, enc_cons_b s1 s2 X', List.cons_append, List.cons_append]
                cases hm0 : matchHere (enc s1 s2 X' ++ [s1, s1])
                    (s2 :: s1 :: (enc s1 s2 X' ++ [s1, s1]))
                · rw [subst_cons_none _ _ _ _ hm0]
                  cases X' with
                  | nil =>
                      rw [enc_nil, List.nil_append]
                      have hm : matchHere [s1, s1] (s1 :: [s1, s1]) = some [s1] :=
                        matchHere_prefix [s1, s1] [s1]
                      have hn : ¬ Occ [s1, s1] [s1] := by
                        intro ho
                        have hl := occ_length ho
                        simp at hl
                      rw [subst_cons_match [] [s1, s1] (by simp) s1 [s1, s1] [s1] hm,
                        List.nil_append, subst_no_occ [] [s1, s1] [s1] hn,
                        dec_s2s1 s1 s2 hs]
                  | cons x X'' =>
                      by_cases hx : x = s1
                      · rw [hx, enc_cons_b s1 s2 X'', List.cons_append, List.cons_append]
                        have hm : matchHere (s2 :: s1 :: (enc s1 s2 X'' ++ [s1, s1]))
                            (s1 :: (s2 :: s1 :: (enc s1 s2 X'' ++ [s1, s1]))) = none :=
                          matchHere_ne s2 _ s1 _ hs
                        have hKne : s2 :: s1 :: (enc s1 s2 X'' ++ [s1, s1]) ≠ [] := by
                          intro he
                          exact nomatch he
                        rw [subst_cons_none _ _ _ _ hm, subst_self _ _ hKne,
                          dec_s2s1 s1 s2 hs]
                      · rw [enc_cons_ne s1 s2 x X'' hx, List.cons_append]
                        have hm : matchHere (x :: (enc s1 s2 X'' ++ [s1, s1]))
                            (s1 :: (x :: (enc s1 s2 X'' ++ [s1, s1]))) = none :=
                          matchHere_ne x _ s1 _ hx
                        have hKne : x :: (enc s1 s2 X'' ++ [s1, s1]) ≠ [] := by
                          intro he
                          exact nomatch he
                        rw [subst_cons_none _ _ _ _ hm, subst_self _ _ hKne,
                          dec_s2s1 s1 s2 hs]
                · exact ((no_border_both s1 s2 hs X' _).1 (matchHere_app _ _ _ hm0)).elim
              · rw [enc_cons_ne s1 s2 c X' hcb, List.cons_append]
                cases hm : matchHere (enc s1 s2 X' ++ [s1, s1])
                    (c :: (enc s1 s2 X' ++ [s1, s1]))
                · rw [subst_cons_none _ _ _ _ hm, subst_self _ _ hQne,
                    dec_single s1 s2 hs c hcb]
                · exact (head_no_pos0 s1 s2 hs X' c hcb _ (matchHere_app _ _ _ hm)).elim

#eval tail ['a', 'b', 'c'] ['c', 'a', 'b']              -- [a, b]
#eval tail ['a', 'b'] ['a', 'a', 'b']                   -- [a, b]  (X starting with σ₁)
#eval tail ['a', 'b'] []                                -- []
#eval head ['a', 'b', 'c'] ['c', 'a', 'b']              -- [c]
#eval head ['a', 'b', 'c'] []                           -- []

/-! ## Definition (freezing) and Theorem (rep_n): multiple substitution -/

/-- If the unfrozen text `T` begins with the block `X`, return the rest. -/
def dropU? : List α → List (α × Option Nat) → Option (List (α × Option Nat))
  | [], T => some T
  | _, [] => none
  | c :: X', (d, none) :: T' => if c = d then dropU? X' T' else none
  | _ :: _, _ :: _ => none

theorem dropU?_length : ∀ (X : List α) (T U : List (α × Option Nat)),
    dropU? X T = some U → U.length + X.length ≤ T.length := by
  intro X
  induction X with
  | nil =>
      intro T U h
      simp only [dropU?] at h
      injection h with h'
      subst h'
      simp only [List.length_nil]
      omega
  | cons c X ih =>
      intro T U h
      cases T with
      | nil => simp [dropU?] at h
      | cons t T' =>
          obtain ⟨d, o⟩ := t
          cases o with
          | none =>
              by_cases hcd : c = d
              · subst hcd
                simp [dropU?] at h
                have hlen := ih T' U h
                simp only [List.length_cons] at hlen ⊢
                omega
              · simp [dropU?, hcd] at h
          | some j => simp [dropU?] at h

/-- The first `k` entries, frozen (they form the matched block). -/
def freezeBlock (i : Nat) : Nat → List (α × Option Nat) → List (α × Option Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, (d, _) :: T' => (d, some i) :: freezeBlock i k T'

/-- One freezing round: scan for `X` leftmost-first, non-overlapping, among
the unfrozen positions, freezing every match (tagged with the round `i`). -/
def freezePass (X : List α) (hX : X ≠ []) (i : Nat) :
    List (α × Option Nat) → List (α × Option Nat)
  | [] => []
  | t :: T' =>
      match _h : dropU? X (t :: T') with
      | some U => freezeBlock i X.length (t :: T') ++ freezePass X hX i U
      | none => t :: freezePass X hX i T'
termination_by T => T.length
decreasing_by
  · have hlen := dropU?_length X (t :: T') U _h
    have : 1 ≤ X.length := by
      cases X with
      | nil => exact absurd rfl hX
      | cons _ _ => simp
    simp only [List.length_cons] at hlen ⊢
    omega
  · simp only [List.length_cons]
    omega

/-- Run the freezing rounds, in order. -/
def markRounds : List (List α × List α) → Nat → List (α × Option Nat) → List (α × Option Nat)
  | [], _, T => T
  | (X, _) :: ps, i, T => markRounds ps (i + 1) (if h : X = [] then T else freezePass X h i T)

/-- Length of the maximal run of round-`i` entries at the head. -/
def runLen : Nat → List (α × Option Nat) → Nat
  | _, [] => 0
  | i, (_, some j) :: T => if j = i then runLen i T + 1 else 0
  | _, (_, none) :: _ => 0

/-- Definition (freezing), final pass: replace each frozen run of round `i`
by one `Y_i` per `|X_i|`-sized chunk; unfrozen characters pass through. -/
def assemble (pairs : List (List α × List α)) : List (α × Option Nat) → List α
  | [] => []
  | (t, none) :: T' => t :: assemble pairs T'
  | (t, some i) :: T' =>
      (List.replicate
        (runLen i ((t, some i) :: T') / (pairs.getD (i - 1) ([], [])).1.length)
        (pairs.getD (i - 1) ([], [])).2).flatten
        ++ assemble pairs (List.drop (runLen i ((t, some i) :: T')) ((t, some i) :: T'))
termination_by T => T.length
decreasing_by
  · simp only [List.length_cons]
    omega
  · have hk : 1 ≤ runLen i ((t, some i) :: T') := by simp [runLen]
    have hd : (List.drop (runLen i ((t, some i) :: T')) ((t, some i) :: T')).length
        = ((t, some i) :: T').length - runLen i ((t, some i) :: T') := List.length_drop
    simp only [List.length_cons] at hd ⊢
    omega

/-- Definition (freezing): the reference semantics of multiple substitution. -/
def repRef (pairs : List (List α × List α)) (S : List α) : List α :=
  assemble pairs (markRounds pairs 1 (S.map (fun c => (c, none))))

/-- Theorem (rep_n), construction: renaming and repair passes, `i = 1..n`. -/
def renameRepair (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRepair b x (i + 1) ps
        (subst (enc b x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc b x Xi) T))

/-- Theorem (rep_n), construction: instantiation passes, `i = n..1`. -/
def instantiate (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T =>
      instantiate b x (i - 1) ps (subst (enc b x Yi) (marker x b (i + 1)) T)

/-- An enc-based variant of the multiple-substitution construction, which
computes the freezing semantics only under the condition that every `X_i`
is a single character or does not end in `x` (a statement not proven in
this file).  Kept for the shadowing demo below. -/
def repC (b x : α) (pairs : List (List α × List α)) (S : List α) : List α :=
  dec b x (instantiate b x pairs.length pairs.reverse
    (renameRepair b x 1 pairs (enc b x S)))

#eval repRef [(['a'], ['b', 'a'])] ['a', 'b', 'a']                     -- [b, a, b, b, a]
#eval repC 'a' 'c' [(['a'], ['b', 'a'])] ['a', 'b', 'a']               -- [b, a, b, b, a]
#eval repRef [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']  -- [c, a]
#eval repC 'a' 'c' [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']  -- [c, a]

-- The single-char / no-trailing-`x` condition is essential — the
-- shadowing example: `X₁ = "ab"` and `X₂ = "bbb"` both end with `x = 'b'`.
#eval repC 'a' 'b' [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
#eval repRef [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
-- the two disagree: a spurious match of enc(X₁) shadows a genuine one

-- Regression sweep: repC against the freezing semantics on the patterns it
-- is meant to handle (b = 'a', x = 'c'; every pattern is a single char or
-- avoids a trailing 'c'), all string shapes over {a, b, c}.
#eval Id.run do
  let mut allOk := true
  let strs : List (List Char) :=
    ["", "a", "b", "c", "ab", "ba", "ca", "bc", "abc", "aab", "bcc"].map String.toList
  let pats : List (List Char) :=
    ["a", "b", "c", "ab", "ba", "aa", "bb", "cab"].map String.toList
  for S in strs do
    for X1 in pats do
      for X2 in pats do
        let pairs := [(X1, ['x']), (X2, ['y'])]
        if repC 'a' 'c' pairs S != repRef pairs S then
          allOk := false
  return allOk
-- true

/-! ## The comma code and the unrestricted multiple substitution

The paper's Theorem (Multiple Substitution): the same
rename/repair/instantiate architecture as `repC`, run over the *comma code*
`enc2` (every character escaped as the block `x·c` -- all code words length
2, phase-locked).  It computes the freezing semantics for *arbitrary*
nonempty patterns: no hypothesis on the patterns is needed (the failure of
the enc-based variant is a remark in the paper -- `repC` above).  The code
layer is proven here (`enc2Pass_eq`, `dec2Pass_enc2`); the staging argument
is stated as `repC2_correct` with a roadmap. -/

/-- The comma code as a function: every character `c` of `S` becomes the
block `x·c`.  The paper defines it as the pass composition `[xx/x]` then
`[xc/c]` per `c ≠ x`; see `enc2Pass_eq` for the bridge. -/
def enc2 (x : α) (S : List α) : List α := (S.map fun c => [x, c]).flatten

omit [DecidableEq α] in
theorem enc2_nil (x : α) : enc2 x [] = [] := rfl

omit [DecidableEq α] in
theorem enc2_cons (x c : α) (S : List α) :
    enc2 x (c :: S) = [x, c] ++ enc2 x S := by
  simp [enc2, List.map_cons, List.flatten_cons]

omit [DecidableEq α] in
theorem enc2_append (x : α) (S T : List α) :
    enc2 x (S ++ T) = enc2 x S ++ enc2 x T := by
  simp [enc2, List.map_append, List.flatten_append]

omit [DecidableEq α] in
theorem enc2_injective (x : α) : ∀ S T : List α, enc2 x S = enc2 x T → S = T := by
  intro S
  induction S with
  | nil =>
      intro T h
      cases T with
      | nil => rfl
      | cons t T' => simp [enc2] at h
  | cons c S' ih =>
      intro T h
      cases T with
      | nil => simp [enc2] at h
      | cons d T' =>
          rw [enc2_cons, enc2_cons] at h
          simp only [List.cons_append, List.nil_append] at h
          injection h with _ h1
          injection h1 with h3 h4
          subst h3
          exact congrArg (c :: ·) (ih T' h4)

/-- A unit of the comma code in progress: the block `x·c` once the character
has been escaped (or is `x` itself, doubled by the first pass), bare before
that.  `l` is the list of already-processed characters. -/
def encUnit (x : α) (l : List α) (c : α) : List α :=
  if c = x ∨ c ∈ l then [x, c] else [c]

/-- The doubling pass `[xx/x]` produces the unit text with nothing
processed: `xx` for each `x`, bare `c` for each `c ≠ x`. -/
theorem subst_double_pass (x : α) : ∀ S : List α,
    subst [x, x] [x] S = (S.map (encUnit x [])).flatten := by
  intro S
  induction S with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons c S ih =>
      by_cases hcx : c = x
      · rw [hcx, subst_cons_match [x, x] [x] (by simp) x S S (matchHere_one_self x S),
          ih]
        simp [encUnit]
      · rw [subst_cons_none [x, x] [x] c S (matchHere_one_ne x c S hcx), ih]
        simp [encUnit, hcx]

/-- A single-character pass never touches a unit that does not contain it. -/
theorem subst_pass_unit {x c : α} : ∀ (u T : List α), c ∉ u →
    subst [x, c] [c] (u ++ T) = u ++ subst [x, c] [c] T := by
  intro u
  induction u with
  | nil => intro T _; rfl
  | cons d u' ih =>
      intro T h
      have hd : d ≠ c := fun he => h (by rw [he]; exact List.mem_cons_self)
      rw [List.cons_append,
        subst_cons_none [x, c] [c] d (u' ++ T) (matchHere_one_ne c d (u' ++ T) hd),
        List.cons_append, ih T (fun hm => h (List.mem_cons_of_mem _ hm))]

/-- The pass escapes exactly its own bare unit. -/
theorem subst_pass_escape {x c : α} (T : List α) :
    subst [x, c] [c] ([c] ++ T) = [x, c] ++ subst [x, c] [c] T := by
  show subst [x, c] [c] (c :: T) = [x, c] ++ subst [x, c] [c] T
  rw [subst_cons_match [x, c] [c] (by simp) c T T (matchHere_one_self c T)]

theorem encUnit_stable {x c d : α} (hdc : d ≠ c) (l : List α) :
    encUnit x (c :: l) d = encUnit x l d := by
  by_cases hdx : d = x
  · subst hdx; simp [encUnit]
  · by_cases hdl : d ∈ l
    · simp [encUnit, hdx, hdl]
    · simp [encUnit, hdx, hdl, hdc]

/-- Inserting the (never processed) `x` into the processed list changes no
unit: `x` is escaped by the doubling pass, not by a `[xc/c]` pass. -/
theorem encUnit_cons_x (x : α) (u w : List α) (d : α) :
    encUnit x (u ++ [x] ++ w) d = encUnit x (u ++ w) d := by
  by_cases hdx : d = x
  · subst hdx; simp [encUnit]
  · simp [encUnit, List.mem_append, hdx]

/-- One encoding pass on a unit text: `[xc/c]` escapes the bare units `c`
and leaves every other unit untouched. -/
theorem subst_pass_units {x c : α} (hcx : c ≠ x) : ∀ (l S : List α), c ∉ l →
    subst [x, c] [c] ((S.map (encUnit x l)).flatten) =
      (S.map (encUnit x (c :: l))).flatten := by
  intro l S hcl
  induction S with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons d S' ih =>
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons]
      by_cases hdc : d = c
      · rw [hdc]
        have hu : encUnit x l c = [c] := by simp [encUnit, hcx, hcl]
        have hu' : encUnit x (c :: l) c = [x, c] := by simp [encUnit]
        rw [hu, subst_pass_escape, ih, hu']
      · have hcu : c ∉ encUnit x l d := by
          by_cases hP : d = x ∨ d ∈ l
          · have hu : encUnit x l d = [x, d] := ite_eq_left hP
            rw [hu]
            intro hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with hc | hc
            · exact absurd hc hcx
            · exact absurd hc.symm hdc
          · have hu : encUnit x l d = [d] := ite_eq_right hP
            rw [hu]
            intro hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            exact absurd hc.symm hdc
        have hu : encUnit x (c :: l) d = encUnit x l d := encUnit_stable hdc l
        rw [subst_pass_unit (encUnit x l d) ((S'.map (encUnit x l)).flatten) hcu, ih, hu]

/-- The encoding passes of the comma code: `[xx/x]` first, then `[xc/c]`
for each `c ∈ σ` with `c ≠ x` (in σ's order; the order is immaterial). -/
def enc2Go (x : α) : List α → List α → List α
  | [], T => T
  | c :: σ, T => if c = x then enc2Go x σ T else enc2Go x σ (subst [x, c] [c] T)

/-- The comma code as the pass composition of the paper. -/
def enc2Pass (x : α) (σ S : List α) : List α := enc2Go x σ (subst [x, x] [x] S)

theorem enc2Go_units (x : α) : ∀ (σ l S : List α), σ.Pairwise (· ≠ ·) →
    (∀ d ∈ l, ∀ e ∈ σ, d ≠ e) →
    enc2Go x σ ((S.map (encUnit x l)).flatten) =
      (S.map (encUnit x (σ.reverse ++ l))).flatten := by
  intro σ
  induction σ with
  | nil => intro l S _ _; rfl
  | cons c σ' ih =>
      intro l S hnd hdis
      rw [List.pairwise_cons] at hnd
      by_cases hcx : c = x
      · simp only [enc2Go]
        rw [ite_eq_left hcx,
          ih l S hnd.2 (fun d hd e he => hdis d hd e (List.mem_cons_of_mem _ he)),
          hcx, List.reverse_cons]
        have hmap : S.map (encUnit x (σ'.reverse ++ l))
            = S.map (encUnit x (σ'.reverse ++ [x] ++ l)) := by
          refine List.map_congr_left fun d _ => ?_
          exact (encUnit_cons_x x σ'.reverse l d).symm
        rw [hmap]
      · have hcl : c ∉ l := fun hc => absurd rfl (hdis c hc c List.mem_cons_self)
        have hdis' : ∀ d ∈ c :: l, ∀ e ∈ σ', d ≠ e := by
          intro d hd e he
          rcases List.mem_cons.mp hd with hd | hd
          · subst hd; exact hnd.1 e he
          · exact hdis d hd e (List.mem_cons_of_mem _ he)
        have happ : σ'.reverse ++ c :: l = (c :: σ').reverse ++ l := by
          rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
        simp only [enc2Go]
        rw [ite_eq_right hcx, subst_pass_units hcx l S hcl,
          ih (c :: l) S hnd.2 hdis', happ]

/-- The pass composition of the paper computes the block map: the comma code
is an expression of the baseline calculus (Lemma (Comma Code) (i), first
half). -/
theorem enc2Pass_eq (x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·)) (S : List α)
    (hS : ∀ c ∈ S, c ∈ σ) : enc2Pass x σ S = enc2 x S := by
  rw [enc2Pass, subst_double_pass, enc2Go_units x σ [] S hnd (by simp), List.append_nil]
  have hunit : ∀ d ∈ S, encUnit x σ.reverse d = [x, d] := by
    intro d hd
    by_cases hdx : d = x
    · subst hdx; simp [encUnit]
    · simp [encUnit, hdx, List.mem_reverse.mpr (hS d hd)]
  have hmap : S.map (encUnit x σ.reverse) = S.map (fun c => [x, c]) :=
    List.map_congr_left hunit
  rw [enc2]
  exact congrArg List.flatten hmap

/-- A decoding unit: the intact block `x·d`, or the bare character `d` once
its block has been collapsed.  The guard `d ≠ x` reflects that `x` is never
processed by these passes (`xx`-blocks are handled by the final halving
pass), and makes the definition insensitive to `x` in the processed list. -/
def decUnit (x : α) (l : List α) (d : α) : List α :=
  if d ≠ x ∧ d ∈ l then [d] else [x, d]

theorem decUnit_stable {x c d : α} (hdc : d ≠ c) (l : List α) :
    decUnit x (c :: l) d = decUnit x l d := by
  by_cases hdx : d = x
  · subst hdx; simp [decUnit]
  · by_cases hdl : d ∈ l
    · simp [decUnit, hdx, hdl]
    · simp [decUnit, hdx, hdl, hdc]

theorem decUnit_cons_x (x : α) (u w : List α) (d : α) :
    decUnit x (u ++ [x] ++ w) d = decUnit x (u ++ w) d := by
  by_cases hdx : d = x
  · subst hdx; simp [decUnit]
  · simp [decUnit, List.mem_append, hdx]

theorem decUnit_collapse {x c : α} (hcx : c ≠ x) (l : List α) :
    decUnit x (c :: l) c = [c] := by
  simp [decUnit, hcx]

/-- In a unit text, no single-character pattern of a not-yet-processed `c`
starts at the head: the flattened units begin with a comma `x` or with an
already-processed character. -/
theorem dec_head_none {x c : α} (hcx : c ≠ x) (l : List α) (hcl : c ∉ l) :
    ∀ Z : List α, matchHere [c] ((Z.map (decUnit x l)).flatten) = none := by
  intro Z
  induction Z with
  | nil => rfl
  | cons d Z' ih =>
      rw [List.map_cons, List.flatten_cons]
      by_cases h : d ≠ x ∧ d ∈ l
      · have hdc : d ≠ c := fun he => hcl (he ▸ h.2)
        have hu : decUnit x l d = [d] := ite_eq_left h
        rw [hu, List.cons_append, matchHere_one_ne c d _ hdc]
      · have hu : decUnit x l d = [x, d] := ite_eq_right h
        rw [hu, List.cons_append, List.cons_append,
          matchHere_one_ne c x _ (Ne.symm hcx)]

/-- One decoding pass on a unit text: `[c/xc]` collapses the intact blocks
`x·c` and leaves every other unit untouched.  (The potential straddle at
the data `x` of an `xx`-block dies by `dec_head_none`.) -/
theorem subst_collapse_units {x c : α} (hcx : c ≠ x) : ∀ (l Z : List α), c ∉ l →
    (∀ e ∈ l, e ≠ x) →
    subst [c] [x, c] ((Z.map (decUnit x l)).flatten) =
      (Z.map (decUnit x (c :: l))).flatten := by
  intro l Z hcl hlx
  induction Z with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons d Z' ih =>
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons]
      by_cases hdc : d = c
      · rw [hdc]
        have hu : decUnit x l c = [x, c] := by simp [decUnit, hcl]
        rw [hu]
        show subst [c] [x, c] (x :: c :: (Z'.map (decUnit x l)).flatten) = _
        rw [subst_cons_match [c] [x, c] (by simp) x
            (c :: (Z'.map (decUnit x l)).flatten) ((Z'.map (decUnit x l)).flatten)
            (matchHere_two_self x c ((Z'.map (decUnit x l)).flatten)),
          ih, decUnit_collapse hcx l]
      · by_cases hdx : d = x
        · rw [hdx]
          have hu : decUnit x l x = [x, x] := by simp [decUnit]
          have hu' : decUnit x (c :: l) x = [x, x] := by simp [decUnit]
          rw [hu, hu']
          show subst [c] [x, c] (x :: x :: (Z'.map (decUnit x l)).flatten) = _
          rw [subst_cons_none [c] [x, c] x (x :: (Z'.map (decUnit x l)).flatten)
              (matchHere_two_head x c (x :: (Z'.map (decUnit x l)).flatten)
                (matchHere_one_ne c x _ (Ne.symm hcx))),
            subst_cons_none [c] [x, c] x ((Z'.map (decUnit x l)).flatten)
              (matchHere_two_head x c ((Z'.map (decUnit x l)).flatten)
                (dec_head_none hcx l hcl Z')),
            ih]
          rfl
        · by_cases hdl : d ∈ l
          · have hbar : decUnit x l d = [d] := by simp [decUnit, hdx, hdl]
            have hu' : decUnit x (c :: l) d = [d] := by
              rw [decUnit_stable hdc l, hbar]
            rw [hbar, hu']
            show subst [c] [x, c] (d :: (Z'.map (decUnit x l)).flatten) = _
            rw [subst_cons_none [c] [x, c] d ((Z'.map (decUnit x l)).flatten)
                (matchHere_two_ne x c d _ hdx), ih]
            rfl
          · have hint : decUnit x l d = [x, d] := by simp [decUnit, hdx, hdl]
            have hu' : decUnit x (c :: l) d = [x, d] := by
              rw [decUnit_stable hdc l, hint]
            rw [hint, hu']
            show subst [c] [x, c] (x :: d :: (Z'.map (decUnit x l)).flatten) = _
            rw [subst_cons_none [c] [x, c] x (d :: (Z'.map (decUnit x l)).flatten)
                (matchHere_two_head x c (d :: (Z'.map (decUnit x l)).flatten)
                  (matchHere_one_ne c d _ hdc)),
              subst_cons_none [c] [x, c] d ((Z'.map (decUnit x l)).flatten)
                (matchHere_two_ne x c d _ hdx), ih]
            rfl

/-- The decoding passes of the comma code: `[c/xc]` for each `c ∈ σ` with
`c ≠ x`, with `[x/xx]` last (the order among the `c`'s is immaterial). -/
def dec2Passes (x : α) : List α → List α → List α
  | [], T => T
  | c :: σ, T => if c = x then dec2Passes x σ T else dec2Passes x σ (subst [c] [x, c] T)

/-- `dec2` as the pass composition of the paper. -/
def dec2Pass (x : α) (σ S : List α) : List α := subst [x] [x, x] (dec2Passes x σ S)

theorem dec2Passes_units (x : α) : ∀ (σ l Z : List α), σ.Pairwise (· ≠ ·) →
    (∀ e ∈ l, e ≠ x) → (∀ d ∈ l, ∀ e ∈ σ, d ≠ e) →
    dec2Passes x σ ((Z.map (decUnit x l)).flatten) =
      (Z.map (decUnit x (σ.reverse ++ l))).flatten := by
  intro σ
  induction σ with
  | nil => intro l Z _ _ _; rfl
  | cons c σ' ih =>
      intro l Z hnd hlx hdis
      rw [List.pairwise_cons] at hnd
      by_cases hcx : c = x
      · simp only [dec2Passes]
        rw [ite_eq_left hcx,
          ih l Z hnd.2 hlx (fun d hd e he => hdis d hd e (List.mem_cons_of_mem _ he)),
          hcx, List.reverse_cons]
        have hmap : Z.map (decUnit x (σ'.reverse ++ l))
            = Z.map (decUnit x (σ'.reverse ++ [x] ++ l)) := by
          refine List.map_congr_left fun d _ => ?_
          exact (decUnit_cons_x x σ'.reverse l d).symm
        rw [hmap]
      · have hcl : c ∉ l := fun hc => absurd rfl (hdis c hc c List.mem_cons_self)
        have hlx' : ∀ e ∈ c :: l, e ≠ x := by
          intro e he
          rcases List.mem_cons.mp he with he | he
          · subst he; exact hcx
          · exact hlx e he
        have hdis' : ∀ d ∈ c :: l, ∀ e ∈ σ', d ≠ e := by
          intro d hd e he
          rcases List.mem_cons.mp hd with hd | hd
          · subst hd; exact hnd.1 e he
          · exact hdis d hd e (List.mem_cons_of_mem _ he)
        have happ : σ'.reverse ++ c :: l = (c :: σ').reverse ++ l := by
          rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
        simp only [dec2Passes]
        rw [ite_eq_right hcx, subst_collapse_units hcx l Z hcl hlx,
          ih (c :: l) Z hnd.2 hlx' hdis', happ]

/-- The final halving pass `[x/xx]` on `Z` with every `x` doubled. -/
theorem subst_halve (x : α) : ∀ Z : List α,
    subst [x] [x, x] ((Z.map (fun d => if d = x then [x, x] else [d])).flatten) = Z := by
  intro Z
  induction Z with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons d Z' ih =>
      rw [List.map_cons, List.flatten_cons]
      by_cases hdx : d = x
      · have hu : (if d = x then [x, x] else [d]) = [x, x] := ite_eq_left hdx
        rw [hu]
        show subst [x] [x, x] (x :: x :: (Z'.map (fun d => if d = x then [x, x] else [d])).flatten) = _
        rw [subst_cons_match [x] [x, x] (by simp) x
            (x :: (Z'.map (fun d => if d = x then [x, x] else [d])).flatten)
            ((Z'.map (fun d => if d = x then [x, x] else [d])).flatten)
            (matchHere_two_self x x ((Z'.map (fun d => if d = x then [x, x] else [d])).flatten)),
          ih]
        rw [hdx]
        rfl
      · have hu : (if d = x then [x, x] else [d]) = [d] := ite_eq_right hdx
        rw [hu]
        show subst [x] [x, x] (d :: (Z'.map (fun d => if d = x then [x, x] else [d])).flatten) = _
        rw [subst_cons_none [x] [x, x] d ((Z'.map (fun d => if d = x then [x, x] else [d])).flatten)
            (matchHere_two_ne x x d _ hdx), ih]

/-- The decode round trip: `dec2` inverts `enc2` on inputs over `σ` (Lemma
(Comma Code) (i), second half). -/
theorem dec2Pass_enc2 (x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·)) (Z : List α)
    (hZ : ∀ c ∈ Z, c ∈ σ) : dec2Pass x σ (enc2 x Z) = Z := by
  have hmap : Z.map (fun c => [x, c]) = Z.map (decUnit x []) := by
    refine List.map_congr_left fun d _ => ?_
    simp [decUnit]
  have hstart : enc2 x Z = (Z.map (decUnit x [])).flatten :=
    congrArg List.flatten hmap
  rw [dec2Pass, hstart, dec2Passes_units x σ [] Z hnd (by simp) (by simp), List.append_nil]
  have hfinal : Z.map (decUnit x σ.reverse)
      = Z.map (fun d => if d = x then [x, x] else [d]) := by
    refine List.map_congr_left fun d hd => ?_
    by_cases hdx : d = x
    · subst hdx; simp [decUnit]
    · have hmem : d ∈ σ.reverse := List.mem_reverse.mpr (hZ d hd)
      simp [decUnit, hdx, hmem]
  rw [hfinal, subst_halve]

/-- Theorem (Multiple Substitution), construction: the same
rename/repair architecture as `repC`, over the comma code. -/
def renameRepair2 (b x : α) (σ : List α) :
    Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRepair2 b x σ (i + 1) ps
        (subst (enc2Pass x σ Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc2Pass x σ Xi) T))

/-- Theorem (Multiple Substitution), construction:
instantiation passes, `i = n..1`. -/
def instantiate2 (b x : α) (σ : List α) :
    Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T =>
      instantiate2 b x σ (i - 1) ps (subst (enc2Pass x σ Yi) (marker x b (i + 1)) T)

/-- Theorem (Multiple Substitution): the construction of the
paper -- `dec2` then instantiation then rename/repair then `enc2`, all as
`subst` passes over the alphabet. -/
def repC2 (b x : α) (σ : List α) (pairs : List (List α × List α)) (S : List α) : List α :=
  dec2Pass x σ (instantiate2 b x σ pairs.length pairs.reverse
    (renameRepair2 b x σ 1 pairs (enc2Pass x σ S)))

/-! ### Normal-form items and occurrence toolkit

  A round's invariant is kept structurally: the intermediate texts are the
  concatenation of *items* -- `enc2`-fragments and markers -- rather than
  raw characters.  A *damaged* marker (`dmg`) is the intermediate state in
  which a spurious round-`i` match has eaten an older marker's first two
  characters; it remembers the eaten fragment tail `W` so that the repair
  pass can restore it. -/

/-- An item of the normal form: an `enc2`-image (a fragment), the round-`i`
marker `x b^{i+1}`, or a damaged marker -- a round-`i` marker followed by
`j` trailing `b`'s (the remains of the round-`j` marker `x b^{j+1}` whose
first two characters were eaten by a spurious match; `W` records the
fragment tail eaten along with them). -/
inductive NFItem (α : Type)
  | frag (W : List α)
  | mark (i : Nat)
  | dmg (W : List α) (i j : Nat)

/-- The flat text of an item list. -/
def itext (b x : α) : List (NFItem α) → List α
  | [] => []
  | NFItem.frag W :: ns => enc2 x W ++ itext b x ns
  | NFItem.mark i :: ns => marker x b (i + 1) ++ itext b x ns
  | NFItem.dmg _ i j :: ns => (marker x b (i + 1) ++ List.replicate j b) ++ itext b x ns

omit [DecidableEq α] in
/-- An occurrence of the middle part of an occurring block. -/
theorem occ_mid {u p v l : List α} (h : Occ (u ++ p ++ v) l) : Occ p l := by
  obtain ⟨s, t, ht⟩ := h
  refine ⟨s ++ u, v ++ t, ?_⟩
  rw [ht]
  simp [List.append_assoc]

omit [DecidableEq α] in
/-- An occurrence of `p` in `l₁ ++ l₂` lies in `l₁`, lies in `l₂`, or
straddles the boundary -- and then a nonempty suffix `p₂` of `p` is a
nonempty prefix of `l₂`. -/
theorem occ_app_cases {p l₁ l₂ : List α} (h : Occ p (l₁ ++ l₂)) :
    Occ p l₁ ∨ Occ p l₂ ∨ ∃ p₁ p₂ v, p = p₁ ++ p₂ ∧ p₁ ≠ [] ∧ p₂ ≠ [] ∧
      l₂ = p₂ ++ v := by
  obtain ⟨u, v, hv⟩ := h
  rw [List.append_assoc] at hv
  by_cases hu1 : l₁.length ≤ u.length
  · obtain ⟨A, hA, hS⟩ := pref_of l₁ u l₂ (p ++ v) hv hu1
    exact Or.inr (Or.inl ⟨A, v, by rw [hS, List.append_assoc]⟩)
  · by_cases hu2 : u.length + p.length ≤ l₁.length
    · obtain ⟨A, hA, hS⟩ := pref_of u l₁ (p ++ v) l₂ hv.symm (by omega)
      -- hA : l₁ = u ++ A,  hS : p ++ v = A ++ l₂
      obtain ⟨B, hA', hB⟩ := pref_of p A v l₂ hS (by
        have hA2 : u.length + A.length = l₁.length := by rw [hA, List.length_append]
        omega)
      refine Or.inl ⟨u, B, ?_⟩
      rw [hA, hA']
      simp [List.append_assoc]
    · obtain ⟨A, hA, hS⟩ := pref_of u l₁ (p ++ v) l₂ hv.symm (by omega)
      -- hA : l₁ = u ++ A,  hS : p ++ v = A ++ l₂
      have hA2 : u.length + A.length = l₁.length := by rw [hA, List.length_append]
      have hAlt : A.length < p.length := by omega
      obtain ⟨p₂, hp2, hS2⟩ := pref_of A p l₂ v hS.symm (by omega)
      have hpp : p.length = A.length + p₂.length := by rw [hp2]; exact List.length_append
      refine Or.inr (Or.inr ⟨A, p₂, v, hp2, ?_, ?_, hS2⟩)
      · cases A with
        | nil => simp only [List.length_nil] at hA2; omega
        | cons a A' => simp
      · cases p₂ with
        | nil => simp only [List.length_nil] at hpp; omega
        | cons c p₂' => simp

/-! ### Text-level facts about `enc2`-images and markers -/

omit [DecidableEq α] in
theorem enc2_head (x c : α) (W : List α) : enc2 x (c :: W) = x :: c :: enc2 x W := by
  simp [enc2_cons]

omit [DecidableEq α] in
theorem replicate_append (a : α) : ∀ (m n : Nat),
    List.replicate m a ++ List.replicate n a = List.replicate (m + n) a := by
  intro m
  induction m with
  | zero => intro n; rw [Nat.zero_add]; rfl
  | succ m ih =>
      intro n
      show a :: (List.replicate m a ++ List.replicate n a) = List.replicate (Nat.succ m + n) a
      rw [ih, Nat.succ_add]
      rfl

omit [DecidableEq α] in
/-- A nonempty suffix of a run of `a`'s starts with `a`. -/
theorem replicate_suffix (a : α) : ∀ (k : Nat) (s p : List α),
    s ++ p = List.replicate k a → p ≠ [] → ∃ r, p = a :: r := by
  intro k
  induction k with
  | zero =>
      intro s p h hp
      cases p with
      | nil => exact absurd rfl hp
      | cons c p' => exact absurd h (by simp)
  | succ k ih =>
      intro s p h hp
      rw [show List.replicate (Nat.succ k) a = a :: List.replicate k a from rfl] at h
      cases s with
      | nil =>
          rw [List.nil_append] at h
          cases p with
          | nil => exact absurd rfl hp
          | cons c p' =>
              injection h with hc _
              exact ⟨p', by rw [hc]⟩
      | cons d s' =>
          rw [List.cons_append] at h
          injection h with hd h'
          subst hd
          exact ih s' p h' hp

omit [DecidableEq α] in
/-- A proper suffix of a marker `x b^k` starts with `b`. -/
theorem marker_straddle (x b : α) (k : Nat) (p₁ p₂ : List α)
    (h : marker x b k = p₁ ++ p₂) (h1 : p₁ ≠ []) (h2 : p₂ ≠ []) :
    ∃ r, p₂ = b :: r := by
  cases p₁ with
  | nil => exact absurd rfl h1
  | cons d s =>
      rw [List.cons_append, marker] at h
      injection h with hd h'
      subst hd
      exact replicate_suffix b k s p₂ h'.symm h2

omit [DecidableEq α] in
/-- The head of an `enc2`-image: empty or comma-first. -/
theorem enc2_nil_or_x (x : α) : ∀ W : List α, enc2 x W = [] ∨ ∃ T, enc2 x W = x :: T := by
  intro W
  cases W with
  | nil => exact Or.inl rfl
  | cons c W' => exact Or.inr ⟨c :: enc2 x W', enc2_head x c W'⟩

omit [DecidableEq α] in
/-- The head of an item list's text: empty or comma/marker-first. -/
theorem itext_nil_or_x (b x : α) : ∀ ns : List (NFItem α),
    itext b x ns = [] ∨ ∃ T, itext b x ns = x :: T := by
  intro ns
  induction ns with
  | nil => exact Or.inl rfl
  | cons it ns ih =>
      cases it with
      | frag W =>
          rcases enc2_nil_or_x x W with h | ⟨T, h⟩
          · rw [itext, h, List.nil_append]; exact ih
          · exact Or.inr ⟨T ++ itext b x ns, by rw [itext, h, List.cons_append]⟩
      | mark i => exact Or.inr ⟨_, rfl⟩
      | dmg W i j => exact Or.inr ⟨_, rfl⟩

omit [DecidableEq α] in
/-- An `enc2`-image contains no `bb` (every `b` is data, followed by the
next block's comma). -/
theorem no_bb_enc2 (x b : α) (hxb : x ≠ b) : ∀ W : List α, ¬ Occ [b, b] (enc2 x W) := by
  intro W
  induction W with
  | nil =>
      intro h
      have hl := occ_length h
      rw [enc2_nil] at hl
      simp at hl
  | cons c W' ih =>
      intro h
      rw [enc2_cons] at h
      rcases occ_app_cases h with h1 | h1 | ⟨p₁, p₂, v, hp, h1, h2, h3⟩
      · -- Occ [b,b] [x,c] forces x = b
        obtain ⟨u, w, hw⟩ := h1
        cases u with
        | nil =>
            rw [List.nil_append, List.cons_append, List.cons_append, List.nil_append] at hw
            injection hw with hx _
            exact hxb hx
        | cons d u' =>
            have hl := congrArg List.length hw
            simp only [List.length_append, List.length_cons] at hl
            omega
      · exact ih h1
      · -- straddle: a nonempty suffix of `[b,b]` starts with `b`, so `enc2 W'`
        -- would start with `b`, but an image is empty or comma-first
        obtain ⟨r, hr⟩ := replicate_suffix b 2 p₁ p₂ (by show p₁ ++ p₂ = [b, b]; rw [hp]) h2
        have hst : enc2 x W' = p₂ ++ v := h3
        rcases enc2_nil_or_x x W' with hnil | ⟨T, hcons⟩
        · rw [hnil] at hst
          cases p₂ with
          | nil => exact absurd rfl h2
          | cons d p' => exact nomatch hst
        · rw [hr, hcons] at hst
          injection hst with hbx _
          exact hxb hbx

omit [DecidableEq α] in
/-- A marker with at least two `b`'s contains `bb`. -/
theorem marker_occ_bb {x b : α} {n : Nat} (l : List α) (hn : 2 ≤ n)
    (h : Occ (marker x b n) l) : Occ [b, b] l := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 m] at hm
  subst hm
  have hsplit : marker x b (m + 2) = ([x] ++ [b, b]) ++ List.replicate m b := rfl
  rw [hsplit] at h
  exact occ_mid h

/-! ### The block lemmas of the phase-locking argument

  The code of every character is the 2-block `x·c`, so a normal text (a
  concatenation of `enc2`-fragments and markers) reads as a sequence of
  2-blocks.  The three facts below classify every match of a code
  `enc2 X` in such a text: it either starts at a block boundary
  (aligned), or it is *shadowed* (an aligned match starts one position
  earlier and fires first), or it is a *spurious* aligned match that eats
  the head of a following marker -- exactly the case the repair pass
  undoes. -/

theorem matchHere_cons_self (c : α) (B C : List α) :
    matchHere (c :: B) (c :: C) = matchHere B C := by
  simp [matchHere]

/-- Inversion for a `matchHere` at a cons-cons position. -/
theorem matchHere_cons_inv {c d : α} {B C D : List α}
    (h : matchHere (c :: B) (d :: C) = some D) : c = d ∧ matchHere B C = some D := by
  by_cases hcd : c = d
  · subst hcd
    rw [matchHere_cons_self] at h
    exact ⟨rfl, h⟩
  · rw [matchHere_ne c B d C hcd] at h
    exact absurd h (by simp)

/-- β-shadowing: if the code `enc2 X` matches starting at a *data*
position -- at the head `w` of the remaining fragment text
`w :: enc2 W' ++ T` -- then it also matches starting one position
earlier, at the fragment's comma.  So once the scan has rejected the
comma position it also rejects the data position, and the scan advances
block by block through a fragment; a misaligned match never fires.
Requires the continuation `T` after the fragment to be empty or
marker-headed (`x b …`), which the round invariant maintains. -/
theorem beta_shadow (x b : α) (hxb : x ≠ b) : ∀ (X : List α) (w : α) (W' T : List α),
    (T = [] ∨ ∃ T₂, T = x :: b :: T₂) → ∀ D : List α,
    matchHere (enc2 x X) (w :: enc2 x W' ++ T) = some D →
    ∃ D', matchHere (enc2 x X) (x :: w :: enc2 x W' ++ T) = some D' := by
  intro X
  induction X with
  | nil =>
      intro w W' T _ D _
      exact ⟨x :: w :: enc2 x W' ++ T, rfl⟩
  | cons c X' ih =>
      intro w W' T hT D h
      rw [enc2_head] at h ⊢
      obtain ⟨hw, h2⟩ := matchHere_cons_inv h
      subst hw
      cases W' with
      | nil =>
          -- the fragment is exhausted; the misaligned match reads `T`
          show ∃ D', matchHere (x :: c :: enc2 x X') (x :: x :: T) = some D'
          have h2' : matchHere (c :: enc2 x X') T = some D := h2
          cases T with
          | nil => simp [matchHere] at h2'
          | cons d T' =>
              obtain ⟨hd, h3⟩ := matchHere_cons_inv h2'
              rcases hT with hT | ⟨T₂, hT⟩
              · exact absurd hT (by simp)
              · injection hT with hdx hT₂
                rw [hdx] at hd
                rw [hdx, hT₂, hd]
                rw [hT₂] at h3
                cases X' with
                | nil => exact ⟨x :: b :: T₂, by simp [matchHere, enc2_nil]⟩
                | cons e X'' =>
                    rw [enc2_head] at h3
                    obtain ⟨hxe, _⟩ := matchHere_cons_inv h3
                    exact absurd hxe hxb
      | cons w₂ W'' =>
          -- the misaligned match recurses one block into the fragment
          have h2' : matchHere (c :: enc2 x X') (x :: w₂ :: enc2 x W'' ++ T) = some D := h2
          obtain ⟨hc, h3⟩ := matchHere_cons_inv h2'
          obtain ⟨D₂, hD₂⟩ := ih w₂ W'' T hT D h3
          refine ⟨D₂, ?_⟩
          show matchHere (x :: c :: enc2 x X') (x :: x :: x :: w₂ :: (enc2 x W'' ++ T))
              = some D₂
          rw [hc, matchHere_cons_self, matchHere_cons_self]
          exact hD₂

/-- L2 (aligned classification): a match of the code `enc2 X` starting at
a block boundary of the fragment text `enc2 W ++ T` is either *genuine*
-- it ends inside the fragment, consuming whole blocks (`W = X ++ W₂`)
-- or *spurious* (γ): it consumes the whole fragment plus the head `x b`
of the following marker, which is only possible when `X = W ++ [b]`.
The continuation `T` must be empty or marker-headed with two `b`'s
(every marker `x b^{j+1}` has `j ≥ 1`). -/
theorem aligned_class (x b : α) (hxb : x ≠ b) : ∀ (W X : List α) (T D : List α),
    (T = [] ∨ ∃ T₃, T = x :: b :: b :: T₃) →
    matchHere (enc2 x X) (enc2 x W ++ T) = some D →
    (∃ W₂, W = X ++ W₂ ∧ D = enc2 x W₂ ++ T) ∨
      (∃ T₃, T = x :: b :: b :: T₃ ∧ X = W ++ [b] ∧ D = b :: T₃) := by
  intro W
  induction W with
  | nil =>
      intro X T D hT h
      have h' : matchHere (enc2 x X) T = some D := h
      cases X with
      | nil =>
          refine Or.inl ⟨[], rfl, ?_⟩
          have h5 : some T = some D := h'
          injection h5 with hD
          exact hD.symm
      | cons c X' =>
          rw [enc2_head] at h'
          cases T with
          | nil => simp [matchHere] at h'
          | cons d T' =>
              obtain ⟨_, h2⟩ := matchHere_cons_inv h'
              rcases hT with hT | ⟨T₃, hT⟩
              · exact absurd hT (by simp)
              · injection hT with hdx hT'
                rw [hdx, hT']
                rw [hT'] at h2
                obtain ⟨hc, h3⟩ := matchHere_cons_inv h2
                rw [hc]
                cases X' with
                | nil =>
                    refine Or.inr ⟨T₃, rfl, rfl, ?_⟩
                    have h4 : some (b :: T₃) = some D := h3
                    injection h4 with hD
                    exact hD.symm
                | cons e X'' =>
                    rw [enc2_head] at h3
                    obtain ⟨hxe, _⟩ := matchHere_cons_inv h3
                    exact absurd hxe hxb
  | cons w W' ih =>
      intro X T D hT h
      cases X with
      | nil =>
          refine Or.inl ⟨w :: W', rfl, ?_⟩
          have h5 : some (enc2 x (w :: W') ++ T) = some D := h
          injection h5 with hD
          exact hD.symm
      | cons c X' =>
          have ha : matchHere (x :: c :: enc2 x X') (x :: w :: (enc2 x W' ++ T))
              = some D := h
          obtain ⟨_, hb⟩ := matchHere_cons_inv ha
          obtain ⟨hcw, h1⟩ := matchHere_cons_inv hb
          rcases ih X' T D hT h1 with ⟨W₂, hW', hD⟩ | ⟨T₃, hT3, hX', hD⟩
          · refine Or.inl ⟨W₂, ?_, hD⟩
            rw [← hcw, hW']
            rfl
          · refine Or.inr ⟨T₃, hT3, ?_, hD⟩
            rw [hX', ← hcw]
            rfl

/-- L1 (aligned fire): a genuine occurrence of `X` at the head of a
fragment fires: the code `enc2 X` matches and the scan resumes exactly
at `enc2 W₂ ++ T`. -/
theorem aligned_fire (x : α) (X W₂ T : List α) :
    matchHere (enc2 x X) (enc2 x (X ++ W₂) ++ T) = some (enc2 x W₂ ++ T) := by
  rw [enc2_append, List.append_assoc]
  exact matchHere_prefix _ _

/-- LM2: the code of the single character `b` matches the head of any
marker `x b^{j+1}`, eating exactly the marker's first two characters. -/
theorem mark_fire (x b : α) (j : Nat) (T : List α) :
    matchHere (enc2 x [b]) (marker x b (j + 1) ++ T) = some (List.replicate j b ++ T) := by
  show matchHere [x, b] (x :: b :: (List.replicate j b ++ T))
      = some (List.replicate j b ++ T)
  rw [matchHere_cons_self, matchHere_cons_self]
  rfl

/-- LM1: no code `enc2 X` with `X` neither empty nor the single
character `b` matches at a marker's head (`x b b …`). -/
theorem mark_none (x b : α) (hxb : x ≠ b) (X R : List α) (hX : X ≠ []) (hXb : X ≠ [b]) :
    matchHere (enc2 x X) (x :: b :: b :: R) = none := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
      show matchHere (x :: c :: enc2 x X') (x :: b :: b :: R) = none
      rw [matchHere_cons_self]
      by_cases hcb : c = b
      · rw [hcb, matchHere_cons_self]
        cases X' with
        | nil => exact absurd (by rw [hcb]) hXb
        | cons e X'' =>
            rw [enc2_head, matchHere_ne x _ b _ hxb]
      · rw [matchHere_ne c _ b _ hcb]

/-- The contrapositive of `beta_shadow`: when the aligned position has
been rejected, the following data position is rejected too, so the scan
skips a whole block of the fragment. -/
theorem beta_skip (x b : α) (hxb : x ≠ b) (X : List α) (w : α) (W' T : List α)
    (hT : T = [] ∨ ∃ T₂, T = x :: b :: T₂)
    (hA : matchHere (enc2 x X) (enc2 x (w :: W') ++ T) = none) :
    matchHere (enc2 x X) (w :: (enc2 x W' ++ T)) = none := by
  cases hM : matchHere (enc2 x X) (w :: (enc2 x W' ++ T)) with
  | none => rfl
  | some D =>
      obtain ⟨D', hD'⟩ := beta_shadow x b hxb X w W' T hT D hM
      have hD2 : matchHere (enc2 x X) (enc2 x (w :: W') ++ T) = some D' := hD'
      rw [hD2] at hA
      exact absurd hA (by simp)

omit [DecidableEq α] in
/-- Prepend the block `x·w` to an item list, merging into a leading
fragment. -/
def shiftItem (w : α) : List (NFItem α) → List (NFItem α)
  | NFItem.frag W :: ns => NFItem.frag (w :: W) :: ns
  | ns => NFItem.frag [w] :: ns

omit [DecidableEq α] in
/-- Prepend the fragment `A` to an item list, merging into a leading
fragment; an empty `A` prepends nothing. -/
def pushFrag (A : List α) : List (NFItem α) → List (NFItem α)
  | NFItem.frag W :: ns => NFItem.frag (A ++ W) :: ns
  | ns => if A = [] then ns else NFItem.frag A :: ns

omit [DecidableEq α] in
/-- Canonical item lists (the round invariant between rounds): every
fragment is nonempty and followed by a marker (or ends the list), every
marker has index `≥ 1`, and there are no damaged markers. -/
def Canon : List (NFItem α) → Prop
  | [] => True
  | NFItem.mark j :: ns => 1 ≤ j ∧ Canon ns
  | NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag _ :: NFItem.frag _ :: _ => False
  | NFItem.frag _ :: NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag W :: NFItem.mark j :: ns => W ≠ [] ∧ 1 ≤ j ∧ Canon ns
  | NFItem.frag W :: [] => W ≠ []

omit [DecidableEq α] in
/-- The shape of a rename round's output: fragments are nonempty and
never adjacent, markers have index `≥ 1` and `≤ i`, and damaged markers
belong to round `i` with at least one leftover `b`. -/
def Rounded (i : Nat) : List (NFItem α) → Prop
  | [] => True
  | NFItem.mark j :: ns => 1 ≤ j ∧ j ≤ i ∧ Rounded i ns
  | NFItem.dmg _ i' j :: ns => i' = i ∧ 1 ≤ j ∧ Rounded i ns
  | NFItem.frag _ :: NFItem.frag _ :: _ => False
  | NFItem.frag _ :: NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag W :: NFItem.mark j :: ns => W ≠ [] ∧ 1 ≤ j ∧ Rounded i ns
  | NFItem.frag W :: [] => W ≠ []

/-- The rename scan through the fragment `W`, which is followed by the
marker `mark j`; the result covers exactly the fragment and the marker.
Round `i`, pattern `X` (nonempty; the `[]` case is a degenerate
pass-through). -/
def fragGo (b x : α) (i : Nat) : List α → List α → Nat → List (NFItem α)
  | [], W, _ => [NFItem.frag W, NFItem.mark 1]
  | c :: X', w :: W', j =>
      if (w :: W').take (c :: X').length = c :: X' then
        NFItem.mark i :: fragGo b x i (c :: X') ((w :: W').drop (c :: X').length) j
      else if (c :: X') = (w :: W') ++ [b] then [NFItem.dmg (w :: W') i j]
      else shiftItem w (fragGo b x i (c :: X') W' j)
  | c :: X', [], j =>
      if (c :: X') = [b] then [NFItem.dmg [] i j] else [NFItem.mark j]
termination_by _ W _ => W.length
decreasing_by
  · have h1 : 1 ≤ (c :: X').length := by simp
    have h2 : ((w :: W').drop (c :: X').length).length = (w :: W').length - (c :: X').length :=
      List.length_drop
    have h3 : 1 ≤ (w :: W').length := by simp
    omega
  · simp only [List.length_cons]
    omega

/-- The rename scan through the final fragment `W`, which is followed by
nothing. -/
def fragEnd (b x : α) (i : Nat) : List α → List α → List (NFItem α)
  | [], W => [NFItem.frag W]
  | c :: X', w :: W' =>
      if (w :: W').take (c :: X').length = c :: X' then
        NFItem.mark i :: fragEnd b x i (c :: X') ((w :: W').drop (c :: X').length)
      else shiftItem w (fragEnd b x i (c :: X') W')
  | _ :: _, [] => []
termination_by _ W => W.length
decreasing_by
  · have h1 : 1 ≤ (c :: X').length := by simp
    have h2 : ((w :: W').drop (c :: X').length).length = (w :: W').length - (c :: X').length :=
      List.length_drop
    have h3 : 1 ≤ (w :: W').length := by simp
    omega
  · simp only [List.length_cons]
    omega

/-- Round `i` of the rename: replace every match of the code `enc2 X` by
the marker `x b^{i+1}`, marking the damage a spurious match does to a
following marker. -/
def renameNF (b x : α) (i : Nat) (X : List α) : List (NFItem α) → List (NFItem α)
  | [] => []
  | NFItem.mark j :: ns =>
      if X = [b] then NFItem.dmg [] i j :: renameNF b x i X ns
      else NFItem.mark j :: renameNF b x i X ns
  | NFItem.frag W :: NFItem.mark j :: ns =>
      fragGo b x i X W j ++ renameNF b x i X ns
  | NFItem.frag W :: ns =>
      fragEnd b x i X W ++ renameNF b x i X ns
  | NFItem.dmg A i' j :: ns => NFItem.dmg A i' j :: renameNF b x i X ns

/-- The repair pass of round `i` (pattern `X`): each damaged marker is
restored to the fragment it ate followed by the eaten marker. -/
def repairNF (b x : α) (i : Nat) (X : List α) : List (NFItem α) → List (NFItem α)
  | [] => []
  | NFItem.mark j :: ns => NFItem.mark j :: repairNF b x i X ns
  | NFItem.dmg A _ j :: ns => pushFrag A (NFItem.mark j :: repairNF b x i X ns)
  | NFItem.frag W :: NFItem.dmg A _ j :: ns =>
      NFItem.frag (W ++ A) :: NFItem.mark j :: repairNF b x i X ns
  | NFItem.frag W :: ns => NFItem.frag W :: repairNF b x i X ns

/-- The instantiation pass `k`: each marker `mark k` becomes the
fragment `Y`. -/
def instNF (b x : α) (k : Nat) (Y : List α) : List (NFItem α) → List (NFItem α)
  | [] => []
  | NFItem.frag W :: ns => NFItem.frag W :: instNF b x k Y ns
  | NFItem.mark j :: ns =>
      if j = k then pushFrag Y (instNF b x k Y ns)
      else NFItem.mark j :: instNF b x k Y ns
  | NFItem.dmg A i' j :: ns => NFItem.dmg A i' j :: instNF b x k Y ns

theorem matchHere_app_left : ∀ (P Q R R' : List α),
    matchHere Q R = some R' → matchHere (P ++ Q) (P ++ R) = some R' := by
  intro P
  induction P with
  | nil => intro Q R R' h; exact h
  | cons a P' ih =>
      intro Q R R' h
      show matchHere (a :: (P' ++ Q)) (a :: (P' ++ R)) = some R'
      rw [matchHere_cons_self]
      exact ih Q R R' h

/-- The γ-fire: when `X = W ++ [b]` and the continuation after the
fragment is marker-headed, the spurious match consumes the fragment and
the marker's head `x b`. -/
theorem gamma_fire (x b : α) (W T₃ : List α) :
    matchHere (enc2 x (W ++ [b])) (enc2 x W ++ (x :: b :: b :: T₃)) = some (b :: T₃) := by
  have h1 : enc2 x (W ++ [b]) = enc2 x W ++ [x, b] := by
    rw [enc2_append]; rfl
  have h2 : matchHere [x, b] (x :: b :: b :: T₃) = some (b :: T₃) := by
    rw [matchHere_cons_self, matchHere_cons_self]
    rfl
  rw [h1]
  exact matchHere_app_left (enc2 x W) [x, b] (x :: b :: b :: T₃) (b :: T₃) h2

omit [DecidableEq α] in
theorem take_append_self : ∀ (X W : List α), (X ++ W).take X.length = X := by
  intro X
  induction X with
  | nil => intro W; rfl
  | cons c X' ih =>
      intro W
      show (c :: (X' ++ W)).take (X'.length + 1) = c :: X'
      rw [List.take_succ_cons, ih W]

omit [DecidableEq α] in
theorem drop_append_self : ∀ (X W : List α), (X ++ W).drop X.length = W := by
  intro X
  induction X with
  | nil => intro W; rfl
  | cons c X' ih =>
      intro W
      show (c :: (X' ++ W)).drop (X'.length + 1) = W
      rw [List.drop_succ_cons, ih W]

omit [DecidableEq α] in
theorem itext_append (b x : α) : ∀ (ns₁ ns₂ : List (NFItem α)),
    itext b x (ns₁ ++ ns₂) = itext b x ns₁ ++ itext b x ns₂ := by
  intro ns₁
  induction ns₁ with
  | nil => intro ns₂; rfl
  | cons n ns ih =>
      intro ns₂
      cases n with
      | frag W => simp only [itext, List.cons_append, ih, List.append_assoc]
      | mark i => simp only [itext, List.cons_append, ih, List.append_assoc]
      | dmg W i j => simp only [itext, List.cons_append, ih, List.append_assoc]

omit [DecidableEq α] in
theorem itext_shift (b x : α) (w : α) (ns : List (NFItem α)) :
    itext b x (shiftItem w ns) = x :: w :: itext b x ns := by
  cases ns with
  | nil => simp [itext, shiftItem, enc2_head, enc2_nil]
  | cons n ns' =>
      cases n with
      | frag W => simp [itext, shiftItem, enc2_head, List.cons_append]
      | mark i => simp [itext, shiftItem, enc2_head, enc2_nil, List.cons_append]
      | dmg W i j => simp [itext, shiftItem, enc2_head, enc2_nil, List.cons_append]

omit [DecidableEq α] in
theorem itext_push (b x : α) (A : List α) (ns : List (NFItem α)) :
    itext b x (pushFrag A ns) = enc2 x A ++ itext b x ns := by
  cases ns with
  | nil =>
      by_cases hA : A = []
      · subst hA; simp [pushFrag, itext, enc2_nil]
      · simp [pushFrag, itext, hA]
  | cons n ns' =>
      cases n with
      | frag W =>
          simp only [pushFrag, itext, enc2_append, List.append_assoc]
      | mark i =>
          by_cases hA : A = []
          · subst hA; simp [pushFrag, itext, enc2_nil]
          · simp [pushFrag, itext, hA]
      | dmg W i j =>
          by_cases hA : A = []
          · subst hA; simp [pushFrag, itext, enc2_nil]
          · simp [pushFrag, itext, hA]

/-! ### The construction over `enc2` directly

  `enc2Pass_eq` and `dec2Pass_enc2` (both proven above) bridge the
  pass-composition definitions to the block map `enc2`.  We record the
  construction in `enc2` form; the remaining work is purely about `subst`
  over texts that are concatenations of `enc2`-images and markers. -/

/-- The rename/repair rounds, `i = 1..n`, with the code layer bridged to
`enc2` (see `renameRepair2_eq`). -/
def renameRR (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRR b x (i + 1) ps
        (subst (enc2 x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc2 x Xi) T))

/-- The instantiation passes, `i = n..1`, in `enc2` form (see
`instantiate2_eq`). -/
def instRR (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T => instRR b x (i - 1) ps (subst (enc2 x Yi) (marker x b (i + 1)) T)

theorem renameRepair2_eq (b x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    ∀ (ps : List (List α × List α)) (i : Nat), (∀ p ∈ ps, p ∈ pairs) → ∀ T : List α,
    renameRepair2 b x σ i ps T = renameRR b x i ps T := by
  intro ps
  induction ps with
  | nil => intro _ _ T; rfl
  | cons p ps ih =>
      intro i hmem T
      have hXi : ∀ c ∈ p.1, c ∈ σ := fun c hc =>
        hp p (hmem p (List.mem_cons_self ..)) c (List.mem_append_left _ hc)
      have hps : ∀ q ∈ ps, q ∈ pairs := fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      show renameRepair2 b x σ (i + 1) ps
          (subst (enc2Pass x σ p.1 ++ [b]) (marker x b (i + 2))
            (subst (marker x b (i + 1)) (enc2Pass x σ p.1) T))
        = renameRR b x (i + 1) ps
          (subst (enc2 x p.1 ++ [b]) (marker x b (i + 2))
            (subst (marker x b (i + 1)) (enc2 x p.1) T))
      rw [enc2Pass_eq x σ hnd p.1 hXi, ih (i + 1) hps _]

theorem instantiate2_eq (b x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    ∀ (ps : List (List α × List α)) (i : Nat), (∀ p ∈ ps, p ∈ pairs) → ∀ T : List α,
    instantiate2 b x σ i ps T = instRR b x i ps T := by
  intro ps
  induction ps with
  | nil => intro _ _ T; rfl
  | cons p ps ih =>
      intro i hmem T
      have hYi : ∀ c ∈ p.2, c ∈ σ := fun c hc =>
        hp p (hmem p (List.mem_cons_self ..)) c (List.mem_append_right _ hc)
      have hps : ∀ q ∈ ps, q ∈ pairs := fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      show instantiate2 b x σ (i - 1) ps (subst (enc2Pass x σ p.2) (marker x b (i + 1)) T)
        = instRR b x (i - 1) ps (subst (enc2 x p.2) (marker x b (i + 1)) T)
      rw [enc2Pass_eq x σ hnd p.2 hYi, ih (i - 1) hps _]

theorem mem_reverse_of {β : Type} {l : List β} {q : β} (h : q ∈ l) : q ∈ l.reverse :=
  List.mem_reverse.mpr h

/-- The construction, with the code layer bridged: everything after this
point works with `enc2` and `subst` only. -/
theorem repC2_eq (b x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (S : List α) (hS : ∀ c ∈ S, c ∈ σ)
    (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    repC2 b x σ pairs S =
      dec2Pass x σ (instRR b x pairs.length pairs.reverse
        (renameRR b x 1 pairs (enc2 x S))) := by
  have hall : ∀ p ∈ pairs.reverse, p ∈ pairs := fun p hp2 =>
    List.mem_reverse.mp hp2
  unfold repC2
  rw [renameRepair2_eq b x σ hnd pairs hp pairs 1 (fun _ h => h),
    instantiate2_eq b x σ hnd pairs hp pairs.reverse pairs.length hall,
    enc2Pass_eq x σ hnd S hS]

/-- Theorem (Multiple Substitution): the comma-code construction
computes the freezing semantics for ARBITRARY nonempty patterns -- no
restriction on the patterns.  The patterns, replacements, and `S` must be
over `σ` (the paper works over a fixed finite alphabet throughout).

The proof is the phase-locking argument: in a normal text (a concatenation
of `enc2`-fragments and markers) every misaligned occurrence of `enc2(X_i)`
is shadowed by an aligned occurrence starting one position earlier (the
all-`x` patterns), and every aligned-but-spurious occurrence runs into a
marker and is exactly repaired by the following pass (the patterns ending
in `b`).  Roadmap: (1) the code layer -- `enc2Pass_eq`, `dec2Pass_enc2` --
is PROVEN above; (2) the normal-form invariant through rename and repair
(fragments + markers, `b`-runs ≤ 1); (3) the occurrence classification
(α)/(β)/(γ) with (β) shadowed; (4) repair exactness; (5) instantiation by
whole markers. -/
theorem repC2_correct (b x : α) (hxb : x ≠ b) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (hne : ∀ p ∈ pairs, p.1 ≠ [])
    (S : List α) (hS : ∀ c ∈ S, c ∈ σ)
    (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    repC2 b x σ pairs S = repRef pairs S := sorry

#eval repC2 'a' 'c' ['a', 'b', 'c'] [(['a'], ['b', 'a'])] ['a', 'b', 'a']  -- [b, a, b, b, a]
#eval repC2 'a' 'c' ['a', 'b', 'c'] [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']  -- [c, a]

-- The shadowing instance of the remark: `X₁ = "ab"` and `X₂ = "bbb"` both
-- end with `x = 'b'`, which the enc-based variant `repC` cannot handle --
-- yet the comma code computes the freezing semantics.
#eval repC2 'a' 'b' ['a', 'b'] [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
#eval repRef [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
-- [b, b, b, a, a, b, b, b, a] both times (`repC` returns [b, b, b, a, a, a, b])

-- Regression sweep: repC2 against the freezing semantics, including
-- patterns that end in `x` (b = 'a', x = 'c'; `ac` and `cc` end with
-- `x = 'c'`); all strings, patterns, and replacements over σ = {a, b, c}.
-- (The full domain -- all strings ≤ 8 over σ -- was verified against the
-- independent Python model: 984,100 evaluations, 0 failures.)
#eval Id.run do
  let mut allOk := true
  let strs : List (List Char) :=
    ["", "a", "b", "c", "ab", "ba", "ca", "bc", "abc", "aab", "bcc", "abaab"].map String.toList
  let pats : List (List Char) :=
    ["a", "b", "c", "ab", "ba", "aa", "bb", "cab", "ac", "cc"].map String.toList
  for S in strs do
    for X1 in pats do
      for X2 in pats do
        let pairs := [(X1, ['a', 'b']), (X2, ['b'])]
        if repC2 'a' 'c' ['a', 'b', 'c'] pairs S != repRef pairs S then
          allOk := false
  return allOk
-- true
