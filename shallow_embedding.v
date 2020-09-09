(* functional extensionality axiom *)
Require Import Coq.Logic.FunctionalExtensionality.

(* this doesn't seem to work in Coq 8.4 *)
(* Require Import Coq.Logic.PropExtensionality. *)
Axiom propositional_extensionality :
  forall (P Q : Prop), (P <-> Q) -> P = Q.




(* simple types *)
Inductive type : Set :=
| Omega : type
| Unit : type
| Prod : type -> type -> type
| Power : type -> type.

Fixpoint El (a : type) : Type :=
  match a with
  | Omega => Prop
  | Unit => unit
  | Prod b c => prod (El b) (El c)
  | Power b => (forall (x : El b), Prop)
  end.

(* Given (a : type), this allows us abuse notation and write
    (x : a) instead of (x : El a)    *)
Coercion El : type >-> Sortclass.

Definition star : Unit := tt.
Definition compr (a : type) (p : a -> Omega) : Power a := p.
Definition opair {a b : type} (x : a) (y : b) : Prod a b := (x,y).
Definition proj1 {a b : type} (z : Prod a b) := fst z.
Definition proj2 {a b : type} (z : Prod a b) := snd z.
Definition Eq {a : type} (x y : a) : Omega := (x = y).
Definition In {a : type} (x : a) (y : Power a) : Omega := (y x).


(* Logical definitions from Bell (p. 70) *)
Definition Equiv (p q : Omega) : Omega := (Eq p q).
Definition true : Omega := (Eq star star).
Definition And (p q : Omega) : Omega := (Eq (opair p q) (opair true true)).
Definition Imp (p q : Omega) : Omega := (Equiv (And p q) p).
Definition Forall (a : type) (p : a -> Omega) : Omega :=
  (Eq (compr a p) (compr a (fun x => true))).
Definition false : Omega := (Forall Omega (fun x => x)).
Definition Neg (p : Omega) : Omega := (Imp p false).
Definition Or (p q : Omega) : Omega :=
  (Forall Omega (fun r => (Imp (And (Imp p r) (Imp q r))) r)).
Definition Exists (a : type) (p : a -> Omega) : Omega :=
  (Forall Omega (fun r => (Imp (Forall a (fun x => (Imp (p x) r))) r))).

Theorem tautology (p : Omega) : p -> p.
Proof.
  intro. trivial.
Qed.

Theorem unity : forall (x : Unit), (Eq x star).
Proof.
  intro x.
  destruct x. reflexivity.
Qed.

Theorem equality {a : type} (p : a -> a -> a -> Omega) : forall (x y z : a),
  (Eq x y) -> (p x y x) -> (p x y y).
Proof.
  intros x y z.
  intros E H.
  exact (eq_ind x (p x y) H y E).
Qed.

Theorem product_beta1 {a b : type} : forall (x : a) (y : b),
    (Eq (proj1 (opair x y)) x).
Proof.
  intros x y.
  reflexivity.
Qed.

Theorem product_beta2 {a b : type} : forall (x : a) (y : b),
    (Eq (proj2 (opair x y)) y).
Proof.
  intros x y.
  reflexivity.
Qed.

Theorem product_eta {a b : type} : forall (z : Prod a b),
    (Eq (opair (proj1 z) (proj2 z)) z).
Proof.
  intro z.
  destruct z as [x y].
  reflexivity.
Qed.

Theorem comprehension {a : type} (p : a -> Omega) : forall (x : a),
    (Equiv (In x (compr a p)) (p x)).
Proof.
  intro x. unfold Equiv, In, compr.
  reflexivity.
Qed.

Theorem thinning (p q : Omega) : p -> (q -> p).
Proof.
  intros H H'. trivial.
Qed.

Theorem cut (p q : Omega) : q -> (q -> p) -> p.
Proof.
  intros H K. exact (K H).
Qed.

Theorem substitution {a : type} (t : a) (p : a -> Omega) :
  (forall (x : a), (p x)) -> (p t).
Proof.
  intro H. exact (H t).
Qed.

Theorem extensionality {a : type} (s t : Power a) :
  (forall (x : a), (Equiv (In x s) (In x t))) -> (Eq s t).
Proof.
  intro H. unfold Eq, Equiv, In in *.
  exact (functional_extensionality s t H).
Qed.

Theorem equivalence {p q : Omega} :
  (p -> q) -> (q -> p) -> (Equiv p q).
Proof.
  intros H H'.
  apply propositional_extensionality.
  split. trivial. trivial.
Qed.




(* Some additional theorems showing that our language
   is equivalent to the language of Coq *)
Theorem equiv_equivalence {p q : Omega} : (Equiv (Equiv p q) (iff p q)).
Proof.
  apply equivalence.
  - intro. rewrite H. split. trivial. trivial.
  - intro. destruct H. apply equivalence.
    trivial. trivial.
Qed.

Theorem true_equivalence : (Equiv true True).
Proof.
  apply equivalence.
  - intro H. trivial.
  - intro H. reflexivity.
Qed.

Theorem and_equivalence {p q : Omega} : (Equiv (And p q) (p /\ q)).
Proof.
  unfold And.
  apply equivalence.
  - intro.
    pose (f_equal proj1 H) as H1.
    pose (f_equal proj2 H) as H2.
    simpl in H1, H2. rewrite H1, H2.
    rewrite true_equivalence. split; trivial.
  - intro H. destruct H as [H1 H2].
    assert (Eq p True). apply equivalence. trivial. trivial.
    assert (Eq q True). apply equivalence. trivial. trivial.
    rewrite H, H0.
    rewrite true_equivalence.
    reflexivity.
Qed.

Theorem imp_equivalence {p q : Omega} : (Equiv (Imp p q) (p -> q)).
Proof.
  unfold Imp.
  rewrite and_equivalence.
  rewrite equiv_equivalence.
  rewrite equiv_equivalence.
  split.
  - intros H K. destruct H. apply H0. trivial.
  - intro. split. intro. apply H0. intro. split. trivial. apply H. trivial.
Qed.

Theorem forall_equivalence {a : type} {p : a -> Omega} :
  (Equiv (Forall a p) (forall (x : a), (p x))).
Proof.
  apply equivalence.
  - intros H x. unfold Forall, compr in H.
    rewrite H. rewrite true_equivalence.
    trivial.
  - intro H. unfold Forall, compr.
    apply (functional_extensionality p _).
    intro x. rewrite true_equivalence.
    apply propositional_extensionality.
    split.
    + trivial.
    + intro. apply (H x).
Qed.

Theorem false_equivalence : (Equiv false False).
Proof.
  apply equivalence.
  - intro H. unfold false in H.
    rewrite forall_equivalence in H.
    exact (H False).
  - contradiction.
Qed.

Theorem neg_equivalence {p : Omega} : (Equiv (Neg p) (~ p)).
Proof.
  unfold Neg.
  rewrite imp_equivalence.
  rewrite false_equivalence.
  apply equivalence.
  - intro. exact H.
  - intros. contradiction.
Qed.

Theorem or_equivalence {p q : Omega} : (Equiv (Or p q) (p \/ q)).
Proof.
  unfold Or.
  rewrite forall_equivalence.
  apply equivalence.
  - intro H.
    specialize (H (p \/ q)).
    rewrite imp_equivalence, and_equivalence in H.
    repeat rewrite imp_equivalence in H.
    apply H. auto.
  - intros H w.
    rewrite imp_equivalence, and_equivalence.
    repeat rewrite imp_equivalence.
    intro. destruct H0 as [H1 H2].
    destruct H. apply H1. trivial.
    apply H2. trivial.
Qed.

Theorem exists_equivalence {a : type} {p : a -> Omega} :
  (Equiv (Exists a p) (exists (x : a), p x)).
Proof.
  unfold Exists.
  rewrite forall_equivalence.
  apply equivalence.
  - intro H.
    specialize (H (exists x :a, p x)).
    rewrite imp_equivalence in H.
    rewrite forall_equivalence in H.
    apply H. intro x. rewrite imp_equivalence.
    intro. exists x. trivial.
  - intros H w.
    rewrite imp_equivalence, forall_equivalence.
    destruct H. intro K.
    specialize (K x).
    rewrite imp_equivalence in K.
    apply K. trivial.
Qed.



Definition ExistsU (a : type) (p : a -> Omega) : Omega :=
  (Exists a (fun x => p x /\ (Forall a (fun y => (p y) -> (Eq x y))))).

Definition subset {a} (X Y : Power a) : Omega :=
  (Forall a (fun x => (In x X) -> (In x Y))).

Definition bin_intersect {a} (X Y : Power a) : Power a :=
  (compr a (fun x => (In x X) /\ (In x Y))).

Definition bin_union {a} (X Y : Power a) : Power a :=
  (compr a (fun x => (In x X) \/ (In x Y))).

Definition U {a : type} : Power a := compr a (fun x => true).

Definition empty {a : type} : Power a := compr a (fun x => false).

Definition complement {a} (X : Power a) : Power a :=
  (compr a (fun x => (Neg (In x X)))).

Definition power {a} (X : Power a) : Power (Power a) :=
  (compr (Power a) (fun x => (subset x X))).

Definition intersect {a} (U : Power (Power a)) : Power a :=
  (compr a (fun x => (Forall (Power a) (fun u => (In u U) -> (In x u))))).

Definition union {a} (U : Power (Power a)) : Power a :=
  (compr a (fun x => (Exists (Power a) (fun u => (In u U) /\ (In x u))))).

Definition coll_intersect {i a} (I : Power i) (U : i -> Power a) : Power a :=
  (compr a (fun x => (Forall i (fun j => (In j I) -> (In x (U j)))))).

Definition coll_union {i a} (I : Power i) (U : i -> Power a) : Power a :=
  (compr a (fun x => (Exists i (fun j => (In j I) /\ (In x (U j)))))).

Definition singl {a : type} (t : a) : Power a :=
  (compr a (fun x => (Eq x t))).

Definition pair {a : type} (s t : a) : Power a :=
  (compr a (fun x => (Eq x s) \/ (Eq x t))).

(* This is a weak form of replacement *)
Definition replf {a c : type} (t : c -> a) (p : c -> Omega) : Power a :=
  (compr a (fun z => (Exists c (fun x => (Eq z (t x)) /\ (p x))))).

Definition product {a b} (A : Power a) (B : Power b) : Power (Prod a b) :=
  (replf (fun z : Prod a b => z)
         (fun z => (In (proj1 z) A) /\ (In (proj2 z) B))).

Definition coproduct {a b} (A : Power a) (B : Power b) :
  (Power (Prod (Power a) (Power b))) :=
  (bin_union (replf (fun z : Prod (Power a) (Power b) => z)
                    (fun z => (Exists a (fun x =>
                                           (@Eq (Power a) (proj1 z) (singl x))
                                           /\ (In x A)))
                                /\ (@Eq (Power b) (proj2 z) empty)))
             (replf (fun z : Prod (Power a) (Power b) => z)
                    (fun z => (@Eq (Power a) (proj1 z) empty) /\
                              (Exists b (fun y =>
                                           (@Eq (Power b) (proj2 z) (singl y))
                                           /\ (In y B)))))).

Definition function {a b} (A : Power a) (B : Power b) :
  (Power (Power (Prod a b))) :=
  (compr (Power (Prod a b))
         (fun u => (subset u (product A B)) /\
                   (Forall a (fun x => (In x A) ->
                                       (ExistsU b (fun y =>
                                                     (In (opair x y) u))))))).

Definition dep_product {a b} (A : Power a) (X : a -> Power b) :
  (Power (Power (Prod a b))) :=
  (compr (Power (Prod a b))
         (fun u =>
            (In u (function A U)) /\
            (Forall a (fun x =>
                         (In x A) ->
                         (subset (compr b (fun y => (In (opair x y) u)))
                                 (X x)))))).

Definition dep_coproduct {a b} (A : Power a) (X : a -> Power b) :
  (Power (Prod a b)) :=
  (replf (fun z : Prod a b => z)
         (fun z => (In (proj1 z) A) /\ (In (proj2 z) (X (proj1 z))))).
