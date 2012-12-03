Inductive weird : Set :=
| W : weird -> weird.

Fixpoint weird_empty (w : weird) : False :=
  match w with
  | W w' => weird_empty w'
  end.