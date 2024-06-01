(* * Определить для данных f : nat → nat и n : nat, является ли ограничение f на {0, ..., n} инъекцией. * *)
Require Import Arith.
Require Import Lia.
Require Import Bool.
Import Nat Peano.

Global Hint Resolve ltb_spec0 leb_spec0 eqb_spec : bdestruct.

Ltac bdestr X H :=
  let e := fresh "e" in
   evar (e : Prop);
   assert (H : reflect e X); subst e;
    [ eauto with bdestruct
    | destruct H as [H | H];
       [ | try first [apply nlt_ge in H | apply nle_gt in H]]].

Tactic Notation "bdestruct" constr(X) := let H := fresh in bdestr X H.

Tactic Notation "bdestruct" constr(X) "as" ident(H) := bdestr X H.

Section Injection.

Variable f: nat -> nat.

Fixpoint search (x n : nat) : bool :=
match n with
| 0 => x =? f n
| S k => if x =? f n then true else search x k
end.

Lemma searchspec1: forall n x, (exists i, i <= n -> f i = x) -> search x n = true.
Admitted.


Definition injective (n : nat) : Prop := forall x y, x <= n -> y <= n -> f x = f y -> x = y.

Fixpoint injb (n : nat) : bool :=
match n with
|0 => true 
|S k => if search (f (S k)) k then false else injb k
end.


Theorem injspec1 : forall n, injective n <-> injb n = true.
Proof.
intros. induction n.
+ split.
++ unfold injective. intros. auto.
++ intro. unfold injective. intros.  assert (K : x = 0).
+++