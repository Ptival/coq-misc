(* CIS670, Homework 4 *)

(* Try to do this assignment "from memory" as much as possible,
    without peeking at CPDT.  If you need a hint, reread the
    appropriate sections in CPDT without touching the keyboard, then
    close the book and try again. *)

Module BinaryTrees.

Inductive binary : Set :=
| leaf : nat -> binary
| node : (binary * binary) -> binary.

Definition indT :=
  forall (P : binary -> Prop),
  (forall n, P (leaf n)) ->
  (forall l r, P l -> P r -> P (node (l, r))) ->
  forall b, P b.

Fixpoint rect P Pleaf Pnode b : P b :=
  match b with
  | leaf n      => Pleaf n
  | node (l, r) => Pnode l r (rect P Pleaf Pnode l) (rect P Pleaf Pnode r)
  end.

Definition indt : indT := rect.

End BinaryTrees.


(* *************************************************************** *)

Module InfiniteBranchingTrees.

Inductive tree : Set :=
| leaf : tree
| node : (nat -> tree) -> tree.

Definition indT :=
  forall (P : tree -> Prop),
  P leaf ->
  (forall f, (forall n, P (f n)) -> P (node f)) ->
  forall t, P t.

Fixpoint rect P Pleaf Pnode t : P t :=
  match t with
  | leaf   => Pleaf
  | node f => Pnode f (fun n => rect P Pleaf Pnode (f n))
  end.

Definition indt : indT := rect.

End InfiniteBranchingTrees.


(* *************************************************************** *)
Module RB.

(* Here is a simple datatype declaration describing one of the key
   structural properties of red-black trees -- the fact that both
   children of a red node must be black. *)

Inductive node : Set := 
| R : red -> node
| B : black -> node

with red : Set :=
| RN : nat -> black -> black -> red

with black : Set := 
| BL : black
| BN : nat -> node -> node -> black.

Definition indT :=
  forall (P : node -> Prop) (PR : red -> Prop) (PB : black -> Prop),
  (forall r, PR r -> P (R r)) ->
  (forall b, PB b -> P (B b)) ->
  (forall n b1 (_ : PB b1) b2 (_ : PB b2), PR (RN n b1 b2)) ->
  PB BL ->
  (forall n n1 (_ : P n1) n2 (_ : P n2), PB (BN n n1 n2)) ->
  forall n, P n.

Scheme node_ind'  := Induction for node  Sort Prop
with   red_ind'   := Induction for red   Sort Prop
with   black_ind' := Induction for black Sort Prop.

Definition node_indt_scheme : indT := node_ind'.

Check node_ind'.

Section Rect.

Variable P : node -> Prop.
Variable PR : red -> Prop.
Variable PB : black -> Prop.
Variable PRr : forall r, PR r -> P (R r).
Variable PBb : forall b, PB b -> P (B b).
Variable PRRN : forall n b1 (_ : PB b1) b2 (_ : PB b2), PR (RN n b1 b2).
Variable PBBL : PB BL.
Variable PBBN : forall n n1 (_ : P n1) n2 (_ : P n2), PB (BN n n1 n2).

Fixpoint rect_node n : P n :=
  match n with
  | R r => PRr r (rect_red r)
  | B b => PBb b (rect_black b)
  end
with rect_red r : PR r :=
  match r with
  | RN n b1 b2 => PRRN n b1 (rect_black b1) b2 (rect_black b2)
  end
with rect_black b : PB b :=
  match b with
  | BL => PBBL
  | BN n n1 n2 => PBBN n n1 (rect_node n1) n2 (rect_node n2)
  end.

End Rect.

Definition indt : indT := rect_node.

End RB.
