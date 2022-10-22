(* We start by defining natural numbers *)
Inductive nat :=
  | zero : nat
  | succ : nat -> nat.

(* We define addition as relation on three natural numbers *)
Inductive add_to : nat -> nat -> nat -> Prop :=
  | add_zero : forall n : nat, add_to n zero n (* n + 0 = n *)
  | add_succ :
    forall (p q r : nat)
    (_ : add_to p q r), (* p + q = r *)
    add_to p (succ q) (succ r). (* p + (q + 1) = r + 1 *)

(* We need to prove that add_to is at least a partial function *)
Lemma add_to_det :
  forall {p q r1 r2 : nat}, add_to p q r1 -> add_to p q r2 -> r1 = r2.
Proof.
  intros p q.
  induction q.
  intros.
  inversion H.
  inversion H0.
  rewrite <- H3.
  rewrite <- H5.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  remember (IHq r r0 H3 H7).
  f_equal.
  exact e.
Qed.

(* Subtraction works in a similar way *)
Inductive sub_to : nat -> nat -> nat -> Prop :=
  | sub_zero : forall n : nat, sub_to n zero n (* n - 0 = n*)
  | sub_succ :
    forall (p q r : nat)
    (_ : sub_to p q (succ r)), (* p - q = (r + 1) *)
    sub_to p (succ q) r. (* p - (q + 1) = r *)

(* Subtraction is a partial function *)
Lemma sub_to_det :
  forall {p q r1 r2 : nat}, sub_to p q r1 -> sub_to p q r2 -> r1 = r2.
Proof.
  intros p q.
  induction q.
  intros.
  inversion H.
  inversion H0.
  rewrite <-H3.
  rewrite <-H5.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  remember (IHq (succ r1) (succ r2) H3 H7).
  inversion e.
  reflexivity.
Qed.

(* WHILE language also has multiplication, so we need to define that as well *)
Inductive mul_to : nat -> nat -> nat -> Prop :=
  | mul_zero : forall n : nat, mul_to n zero zero (* n * 0 = n *)
  | mul_succ :
    forall (p q r s : nat)
    (_ : mul_to p q r) (* p * q = r *)
    (_ : add_to r p s), (* r + p = s *)
    mul_to p (succ q) s. (* p * (q + 1) = s *)

(* Multiplication is at least a partial function *)
Lemma mul_to_det :
  forall {p q r1 r2 : nat}, mul_to p q r1 -> mul_to p q r2 -> r1 = r2.
Proof.
  intros p q.
  induction q.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  remember (IHq r r0 H2 H7).
  rewrite e in H4.
  remember (add_to_det H4 H9).
  exact e0.
Qed.

(* We will represent variable names as natural numbers for the sake of simplicity *)
Definition atom := nat.

(* Moving on. AST node types for integer expressions (expr),
   boolean expressions (bool), and commands (com) follow *)

(* Binary operation on expressions *)
Inductive eop :=
  | eop_add  (* + *)
  | eop_sub  (* - *)
  | eop_mul. (* * *)

(* Expressions *)
Inductive expr :=
  (* n *)
  | e_nat : nat -> expr
  (* x *)
  | e_atom : atom -> expr
  (* e eop e *)
  | e_eop : expr -> eop -> expr -> expr.

(* Binary operations on booleans *)
Inductive bop :=
  | bop_eq  (* = *)
  | bop_lt. (* < *)

(* Booleans *)
Inductive bool :=
  (* true *)
  | b_true : bool
  (* false *)
  | b_false : bool
  (* b bop b *)
  | b_bop : expr -> bop -> expr -> bool
  (* b && b *)
  | b_and : bool -> bool -> bool
  (* !b *)
  | b_not : bool -> bool.

Inductive com :=
  (* x := n *)
  | c_set : atom -> expr -> com
  (* if b then c else c *)
  | c_if : bool -> com -> com -> com
  (* c; c *)
  | c_seq : com -> com -> com
  (* skip *)
  | c_skip : com
  (* while b do c *)
  | c_while : bool -> com -> com.

(* State is a partial function from var to nat. We define
   it as an inductive type with two constructors *)
Inductive state :=
  (* Empty state with no variables defined *)
  | s_empty : state
  (* Updated state with a new definition for var *)
  | s_update : state -> atom -> nat -> state.

(* We now need to define relation equivalent to s(u) = n
   There are two cases *)
Inductive atom_lookup : state -> atom -> nat -> Prop :=
  (* Irrelevance: if s2 = s1[x2 -> n2], x1 != x2 and
    s1(x1) = n1, then s2(x1) = n1 *)
  | atom_lookup_irrelevant :
    forall (s1 : state) (x1 x2 : atom) (n1 n2 : nat)
    (_ : atom_lookup s1 x1 n1) (* s1(x1) = n1 *)
    (_ : x1 <> x2), (* x1 != x2 *)
    atom_lookup (s_update s1 x2 n2) x1 n1
  (* Most recent definition: if s2 = s1[x -> n] then
     s2(x) = n *)
  | atom_lookup_most_recent :
    forall (s1 : state) (x : atom) (n : nat),
    atom_lookup (s_update s1 x n) x n.

(* To verify the definition of atom_lookup, we show that it
   is determenistic *)
Lemma atom_lookup_det :
  forall {s : state} {x : atom} {n1 n2 : nat}
  (_ : atom_lookup s x n1)
  (_ : atom_lookup s x n2),
  n1 = n2.
Proof.
  intros.
  induction s.
  inversion H.
  inversion H.
  inversion H0.
  exact (IHs H6 H13).
  rewrite H8 in H7.
  remember (H7 (eq_refl x)).
  contradiction.
  inversion H0.
  rewrite H1 in H12.
  remember (H12 (eq_refl x)).
  contradiction.
  rewrite <- H5.
  rewrite <- H10.
  reflexivity.
Qed.

(* We can now define small step semantics for expressions *)
(* We work with configurations - pairs of state and expressions *)
Inductive e_small : state -> expr -> state -> expr -> Prop :=
  (* W-EXP.VAR rule *)
  | e_small_var :
    forall (s : state) (x : atom) (n : nat)
    (_ : atom_lookup s x n), (* s(x) = n *)
    e_small s (e_atom x) s (e_nat n) (* (s, x) -> (s, n) *)
  (* W-EXP.LEFT rule *)
  | e_small_left :
    forall (s s' : state) (e1 e1' e2 : expr) (op : eop)
    (_ : e_small s e1 s' e1'), (* (s, e1) -> (s', e1') *)
    (* (s, e1 @ e2) -> (s', e1' @ e2) *)
    e_small s (e_eop e1 op e2) s' (e_eop e1' op e2)
  (* W-EXP.RIGHT rule *)
  | e_small_right :
    forall (s s' : state) (e e' : expr) (op : eop) (n : nat)
    (_ : e_small s e s' e'), (* (s, e) -> (s', e') *)
    (* (s, n @ e) -> (s', n @ e') *)
    e_small s (e_eop (e_nat n) op e) s' (e_eop (e_nat n) op e')
  (* W-EXP.ADD rule *)
  | e_small_add :
    forall (s : state) (n1 n2 n3 : nat)
    (_ : add_to n1 n2 n3), (* n1 + n2 = n3 *)
    (* (s, n1 + n2) -> (s, n3) *)
    e_small s (e_eop (e_nat n1) eop_add (e_nat n2)) s (e_nat n3)
  (* W-EXP.SUB rule *)
  | e_small_sub :
    forall (s : state) (n1 n2 n3 : nat)
    (_ : sub_to n1 n2 n3), (* n1 - n2 = n3 *)
    (* (s, n1 - n2) -> (s, n3) *)
    e_small s (e_eop (e_nat n1) eop_sub (e_nat n2)) s (e_nat n3)
  (* W-EXP.MUL rule *)
  | e_small_mul :
    forall (s : state) (n1 n2 n3 : nat)
    (_ : mul_to n1 n2 n3), (* n1 * n2 = n3 *)
    (* (s, n1 * n2) -> (s, n3) *)
    e_small s (e_eop (e_nat n1) eop_mul (e_nat n2)) s (e_nat n3).

(* We now show that small step relation we defined earlier is determentistic *)
(* We split the theorem into two lemmas: one about the rewritten expression
   one about new state *)

(* Expression produced by small step reduction of atom will always be the same *)
Lemma e_small_det_e_atom :
  forall {e1 e2 : expr} {s s1 s2 : state} {x : atom}
  (_: e_small s (e_atom x) s1 e1) (* (s, x) -> (s1, e1) *)
  (_: e_small s (e_atom x) s2 e2), (* (s, x) -> (s2, e2) *)
  e1 = e2.
Proof.
  intros.
  inversion H.
  inversion H0.
  rewrite <-H4 in H3.
  rewrite <-H9 in H8.
  f_equal.
  exact (atom_lookup_det H3 H8).
Qed.

(* Reduction of atom does not change state *)
Lemma e_small_pure_atom :
  forall {s s' : state} {e' : expr} {x : atom}
  (_ : e_small s (e_atom x) s' e'),
  s = s'.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

(* Small step relation is determenistic for atoms *)
Lemma e_small_det_atom :
  forall {e1 e2 : expr} {s s1 s2 : state} {x : atom}
  (_: e_small s (e_atom x) s1 e1) (* (s, x) -> (s1, e1) *)
  (_: e_small s (e_atom x) s2 e2), (* (s, x) -> (s2, e2) *)
  e1 = e2 /\ s1 = s2.
Proof.
  intros.
  split.
  exact (e_small_det_e_atom H H0).
  remember (e_small_pure_atom H).
  remember (e_small_pure_atom H0).
  rewrite <-e.
  rewrite <-e0.
  reflexivity.
Qed.

(* If operands are known, small step relation always reduces
   binary operation to the same result *)
(* TODO: avoid repetitions here *)
Lemma e_small_det_e_bin_nat :
  forall {e1 e2 : expr} {s s1 s2 : state} {n1 n2 : nat} {op : eop}
  (_: e_small s (e_eop (e_nat n1) op (e_nat n2)) s1 e1)
  (_: e_small s (e_eop (e_nat n1) op (e_nat n2)) s2 e2),
  e1 = e2.
Proof.
  intros.
  destruct op.
  inversion H.
  inversion H7.
  inversion H7.
  inversion H0.
  inversion H13.
  inversion H13.
  f_equal.
  exact (add_to_det H6 H12).
  intros.
  inversion H.
  inversion H7.
  inversion H7.
  inversion H0.
  inversion H13.
  inversion H13.
  f_equal.
  exact (sub_to_det H6 H12).
  intros.
  inversion H.
  inversion H7.
  inversion H7.
  inversion H0.
  inversion H13.
  inversion H13.
  f_equal.
  exact (mul_to_det H6 H12).
Qed.

(* Binary operations on natural numbers do not modify state *)
Lemma e_small_pure_bin_nat :
  forall {s s' : state} {e' : expr} {n1 n2 : nat} {op : eop}
  (_ : e_small s (e_eop (e_nat n1) op (e_nat n2)) s' e'),
  s = s'.
Proof.
  intros.
  inversion H.
  inversion H6.
  inversion H6.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(* Small step relation is deterministic for binary operations on known
   numbers *)
Lemma e_small_det_bin :
  forall {e1 e2 : expr} {s s1 s2 : state} {n1 n2 : nat} {op : eop}
  (_: e_small s (e_eop (e_nat n1) op (e_nat n2)) s1 e1)
  (_: e_small s (e_eop (e_nat n1) op (e_nat n2)) s2 e2),
  e1 = e2 /\ s1 = s2.
Proof.
  intros.
  split.
  exact (e_small_det_e_bin_nat H H0).
  remember (e_small_pure_bin_nat H).
  remember (e_small_pure_bin_nat H0).
  rewrite <-e.
  rewrite <-e0.
  reflexivity.
Qed.

(* We now prove similar properties for x @ e (binary operator
   applied to a variable) *)

(* x @ e always reduces to the same expression *)
Lemma e_small_det_e_bin_atom :
  forall {e e1 e2 : expr} {s s1 s2 : state} {x : atom} {op : eop}
  (_ : e_small s (e_eop (e_atom x) op e) s1 e1)
  (_ : e_small s (e_eop (e_atom x) op e) s2 e2),
  e1 = e2.
Proof.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  exact (e_small_det_e_atom H7 H14).
Qed.

(* x @ e does not modify state *)
Lemma e_small_pure_bin_atom :
  forall {e e' : expr} {s s' : state} {x : atom} {op : eop}
  (_ : e_small s (e_eop (e_atom x) op e) s' e'),
  s = s'.
Proof.
  intros.
  inversion H.
  exact (e_small_pure_atom H6).
Qed.

(* Small step relation is determenistic for x @ e *)
Lemma e_small_det_bin_atom :
  forall {e e1 e2 : expr} {s s1 s2 : state} {x : atom} {op : eop}
  (_ : e_small s (e_eop (e_atom x) op e) s1 e1)
  (_ : e_small s (e_eop (e_atom x) op e) s2 e2),
  e1 = e2 /\ s1 = s2.
Proof.
  intros.
  split.
  exact (e_small_det_e_bin_atom H H0).
  remember (e_small_pure_bin_atom H).
  remember (e_small_pure_bin_atom H0).
  rewrite <-e0.
  rewrite <-e3.
  reflexivity.
Qed.

(* Small step relation also produces the same expression *)
Lemma e_small_det_e :
  forall {e e1 e2 : expr} {s s1 s2 : state}
  (_ : e_small s e s1 e1)  (* (s, e) -> (s1, e1) *)
  (_ : e_small s e s2 e2), (* (s, e) -> (s2, e2) *)
  e1 = e2.
Proof.
  intros.
  generalize dependent s1.
  generalize dependent s2.
  generalize dependent e1.
  generalize dependent e2.
  induction e.
  intros.
  inversion H0.
  intros.
  exact (e_small_det_e_atom H H0).
  intros.
  destruct e1.
  inversion H0.
  inversion H7.
  inversion H.
  inversion H14.
  f_equal.
  exact (IHe2 _ _ _ H7 _ H14).
  rewrite <-H12 in H7.
  inversion H7.
  rewrite <-H12 in H7.
  inversion H7.
  rewrite <-H12 in H7.
  inversion H7.
  rewrite <-H5 in H0.
  rewrite <-H5 in H.
  rewrite H6.
  exact (e_small_det_e_bin_nat H H0).
  rewrite <-H5 in H0.
  rewrite <-H5 in H.
  rewrite H6.
  exact (e_small_det_e_bin_nat H H0).
  rewrite <-H5 in H0.
  rewrite <-H5 in H.
  rewrite H6.
  exact (e_small_det_e_bin_nat H H0).
  exact (e_small_det_e_bin_atom H H0).
  inversion H0.
  inversion H.
  f_equal.
  exact (IHe1 _ _ _ H7 _ H14).
Qed.

(* Small step relation does not modify expression state *)
Lemma e_small_pure :
  forall {e e' : expr} {s s' : state}
  (_ : e_small s e s' e'),
  s = s'.
Proof.
  intros.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent e'.
  induction e.
  intros.
  inversion H.
  intros.
  exact (e_small_pure_atom H).
  intros.
  inversion H.
  exact (IHe1 _ _ _ H6).
  exact (IHe2 _ _ _ H6).
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(* We can now show that small step relation is determinstic *)
Theorem e_small_det :
  forall {e e1 e2 : expr} {s s1 s2 : state}
  (_ : e_small s e s1 e1)  (* (s, e) -> (s1, e1) *)
  (_ : e_small s e s2 e2), (* (s, e) -> (s2, e2) *)
  e1 = e2 /\ s1 = s2.
Proof.
  split.
  exact (e_small_det_e H H0).
  remember (e_small_pure H).
  remember (e_small_pure H0).
  rewrite <-e0.
  rewrite <-e3.
  reflexivity.
Qed.
