(*Task 1*)

Definition symmetric {A: Type} (R: A -> A -> Prop) :=
    forall x y: A, R x y -> R y x.

Definition antisymmetric {A: Type} (R: A -> A -> Prop) :=
    forall x y: A, R x y /\ R y x -> x = y.

Definition asymmetric {A: Type} (R: A -> A -> Prop) :=
    forall x y: A, R x y -> ~ R y x.

Definition transitive {A: Type} (R:A -> A -> Prop):= 
    forall x y z:A, R x y -> R y z -> R x z.



(*Task 2*)
(*a*)
Theorem a (A B: Prop) : A -> B -> A.
Proof.
    intros.
    assumption.
Qed.

(*b*)
Theorem b (A B C: Prop) : (A -> B) -> (A -> B -> C) -> (A -> C).
Proof.
    intros.
    apply H0.
    assumption.
    apply H.
    assumption.
Qed.

(*c*)
Theorem c (A B: Prop) : A /\ B -> A.
Proof.
    intros.
    destruct H.
    assumption.
Qed.

(*d*)
Theorem d (A B: Prop) : A /\ B -> B.
Proof.
    intros.
    destruct H.
    assumption.
Qed.

(*e*)
Theorem e (A B: Prop) : A -> B -> A /\ B.
Proof.
    intros.
    split.
    assumption.
    assumption.
Qed.

(*f*)
Theorem f (A B: Prop) : A -> A \/ B.
Proof.
    intros.
    left.
    assumption.
Qed.

(*g*)
Theorem g (A B: Prop) : B -> A \/ B.
Proof.
    intros.
    right.
    assumption.
Qed.

(*h*)
Theorem h (A B C: Prop) : (A -> C) -> (B -> C) -> (A \/ B -> C).
Proof.
    intros.
    destruct H1.
    apply H.
    assumption.
    apply H0.
    assumption.
Qed.

(*i*)
Theorem i (A B: Prop) : (A -> B) -> (A -> ~B) -> ~A.
Proof.
    intros.
    unfold not.
    intros.
    apply H0.
    assumption.
    apply H.
    assumption.
Qed.

(*Task 3*)
Fixpoint add (n m : nat) :  nat :=
    match n with
    | 0 => m
    | S n' => S (add n' m)
    end.

Notation "x :+ y" := (add x y) (at level 61, left associativity).


Theorem add_assoc : forall n m p : nat, n :+ (m :+ p) = (n :+ m) :+ p.
Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

(*Task 4*)
Definition comp {A B C: Type} (g: B -> C) (f: A -> B) : A -> C :=
    fun x : A => g (f  x).

Notation "g :.: f" := (comp g f) (at level 41, right associativity).

(*1 & 2*)
Definition injective {A B: Type} (f: A -> B) :=
    forall x y: A, f x = f y -> x = y.

Theorem id_inj : forall (A: Type), injective (fun x : A => x).
Proof.
    intros.
    unfold injective.
    intros.
    rewrite H.
    reflexivity.
Qed.


(*3 & 4*)
Definition surjective {A B: Type} (f: A -> B) :=
    forall y: B, exists x: A, f x = y.

Theorem id_surj : forall (A : Type), surjective (fun x : A => x).
Proof.
    intros.
    unfold surjective.
    intros.
    exists y.
    reflexivity.
Qed.


(*5 & 6*)
Definition bijective {A B: Type} (f: A -> B) :=
    injective f /\ surjective f.

Theorem comp_inj : forall (A B C: Type) (f: A -> B) (g: B -> C),
    injective f -> injective g -> injective (g :.: f).
Proof.
    intros.
    unfold injective.
    intros.
    unfold comp in H1.
    apply H.
    apply H0.
    assumption.
Qed.

Theorem comp_surj : forall (A B C: Type) (f: A -> B) (g: B -> C),
    surjective f -> surjective g -> surjective (g :.: f).
Proof.
    intros.
    unfold surjective.
    intros.
    unfold comp.
    destruct (H0 y).
    destruct (H x).
    exists x0.
    rewrite H2.
    assumption.
Qed.


Theorem comp_bij : forall (A B C: Type) (f: A -> B) (g: B -> C),
    bijective f -> bijective g -> bijective (g :.: f).
Proof.
    intros.
    unfold bijective.
    split.
    apply comp_inj.
    destruct H.
    assumption.
    destruct H0.
    assumption.
    apply comp_surj.
    destruct H.
    assumption.
    destruct H0.
    assumption.
Qed.
