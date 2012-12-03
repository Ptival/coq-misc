Add LoadPath "~/cpdt/src".

Require Import CpdtTactics.

(** propositional logic *)

(* (10 minutes) Propositional logic often comes with an A <=> B form that is
true when A and B have the same truth values. Show how to define "iff" as
a Coq Prop. *)

Definition iff' (a b : Prop) := a -> b /\ b -> a.

Notation "a <=> b" := (iff' a b) (at level 77, right associativity).
Hint Unfold iff'.

Theorem iff'_refl : forall P : Prop, P <=> P.
  auto.
Qed.

Theorem iff'_sym : forall P Q : Prop, (P <=> Q) <=> (Q <=> P).
  auto.
Qed.

(* How automated can you make these proofs? *)

(* (15 minutes) In college-level logic classes, we learn that implication can
be expressed in terms of not and or operations (rather than in terms of
forall). *)
Definition implies (A B : Prop) : Prop := ~A \/ B.
Notation "a => b" := (implies a b) (at level 75, right associativity).
Hint Unfold implies.

(* One might wonder whether this form of implication is "the same as" Coq's
version that uses forall. State two theorems claiming that each kind of
implication can be converted into the other. Which one(s) can you prove? *)

Theorem imp1 : forall A B : Prop, (A => B) -> (A -> B).
Proof.
  intros. unfold implies in H. intuition.
Qed.

(*
Can't prove:
Theorem imp2 : forall A B : Prop, (A -> B) -> (A => B).
Proof.
  intros. unfold implies. intuition.
Qed.
*)

(* How about... *)
Axiom nowai : forall P : Prop, P \/ ~P.
(* ...now? *)

Theorem imp2 : forall A B : Prop, (A -> B) -> (A => B).
Proof.
  intros. unfold implies. destruct (nowai A); intuition.
Qed.

(* Some handy imports:
   Arith gives us nat, *, and +
   Arith.Even gives us even and odd
   Arith.Div2 gives us div2
*)
Require Import Arith.
Require Import Arith.Even.
Require Import Arith.Div2.
Set Implicit Arguments.
Hint Constructors even odd.

(** propositions with implicit equality *)

(* (35 minutes) The Collatz sequence starting at n is defined as the infinite
sequence obtained by iterating the step function:

step(n) = n/2  if n is even
step(n) = 3n+1 if n is odd

For example, the sequence starting at 11 looks like

11, 34, 17, 52, 26, 13, 40, 20, ...

It is conjectured that all collatz sequences eventually cycle (and in
particular reach 1 if they weren't 0 to begin with). Create an inductive
proposition collatz_cycles which expresses the fact that a particular nat
eventually reaches a cycle, then state and prove the fact that the collatz
sequence starting at 5 eventually cycles.

Don't forget about "Hint Constructors" and "auto n" when creating proofs about
constants!
*)

Definition step n :=
  if even_odd_dec n
  then div2 n
  else 3 * n + 1.

Inductive cycles : nat -> Prop :=
| cycles_1 : cycles 1
| cycles_step : forall n, cycles (step n) -> cycles n
.
Hint Constructors cycles.

Theorem cycles_5 : cycles 5.
Proof.
  (* 5 -> 16 -> 8 -> 4 -> 2 -> 1 : 5 step + 1 *)
  auto 6.
Qed.

(* (45 minutes) We say a list A is a "subsequence" of a list B when you can
produce list A by deleting some elements from list B.  For example, [1,2,3] is
a subsequence of each of the lists
[1,2,3]
[1,1,1,2,2,3]
[1,2,7,3]
[5,6,1,9,9,2,7,3,8]
but it is not a subsequence of any of the lists:
[1,2]
[1,3]
[5,6,2,1,7,3,8]

Define an inductive proposition subsequence that captures what it means to be
a subsequence, then prove that subsequence is transitive. Some hints on
automating this proof:

1. Use Hint Constructors to add your inductive proposition's constructors to
the hint database.
2. Choose which thing you do induction on carefully!
3. Try "crush" and look where it fails -- then add that as a lemma and put it
in your rewriting database. For example, on my first attempt, crush died here
first:

  A : Type
  l1 : list A
  H : subsequence l1 nil
  l : list A
  ============================
   subsequence l1 l

So I added a lemma:

Lemma subsequence_nil_anything : forall A (l1 l2 : list A),
    subsequence l1 nil -> subsequence l1 l2.
(* ... ;-) *)
Qed.

Hint Resolve subsequence_nil_anything.

That let crush get a bit farther, and suggested the next lemma I would need to
prove.
*)

(* I'm not really sure why we're not getting this notation for free, actually.
But we're not, se here it is for convenience. *)
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition sub123 := subsequence [1; 2; 3].
Definition notsub123 := fun l => ~(subsequence [1; 2; 3] l).
Hint Unfold sub123.

Example e1 : sub123 [1; 2; 3]. auto 100. Qed.
Example e2 : sub123 [1; 1; 1; 2; 2; 3]. auto 100. Qed.
Example e3 : sub123 [1; 2; 7; 3]. auto 100. Qed.
Example e4 : sub123 [5; 6; 1; 9; 9; 2; 7; 3; 8]. auto 100. Qed.
(* optional; you'll like inversion and unfold a lot
Example e5 : notsub123 [1; 2]. (* TODO *) Qed.
Example e6 : notsub123 [1; 3]. (* TODO *) Qed.
Example e7 : notsub123 [5; 6; 2; 1; 7; 3; 8]. (* TODO *) Qed.
*)