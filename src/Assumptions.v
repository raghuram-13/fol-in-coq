Ltac intro_assumption variable_name assumption_name :=
(* We need h to refer to different hypotheses at different times. *)
let rec rec h :=
  let decompose_sum h1 h2 := match type of h with
    | sum _ _ => destruct h as [h1|h2] end in
  let h1 := fresh "is_assumption" in let h2 := fresh "is_assumption" in
  tryif (decompose_sum h1 h2 + (simpl in h; decompose_sum h1 h2)) then
    [> rec h1 | rec h2 ]
  else (* base of recursion *) match type of h with
    | _ = _ => induction h
    | _ => destruct h as assumption_name
    end
in
let h := fresh "is_assumption" in intros variable_name h; rec h.

(* Use instead of intro when introducing a pair of hypotheses of the form of a
   variable p and h of a type (Γ p). Simplifies occurrences of ⊔ and = in Γ,
   generating multiple subcases for the occurrences of ⊔.

   Takes as arguments two optional names for what are called p and h above, with
   priority given to h in case of one argument. The name for p must be an
   identifier, but the name for h can be any or_and_intropattern (i.e. the
   syntax for `destruct` patterns).
   (NOTE: syntactically, any simple_intropattern (i.e. the syntax for `intros`
   patterns) will be accepted, but in any case other than the = cases, will
   cause an error. This is due to the behaviour of the `Tactic Notation`
   command.) *)
Tactic Notation "intro_assumption" ident(variable_name)
                                   simple_intropattern(assumption_name) :=
intro_assumption variable_name assumption_name.
Tactic Notation "intro_assumption" simple_intropattern(name) :=
let var := fresh "assumption" in intro_assumption var name.
Tactic Notation "intro_assumption" := intro_assumption ?.

Ltac detect_assumption hook := repeat (apply inl + apply inr); hook.

(* Constructs goals of the form (Γ p), simplifying occurrences of ⊔ and =
   in Γ. A tactic `hook` can be passed to it to use after this in one of the
   branches due to ⊔.
   The default hook tries both `assumption` and `reflexivity` in each branch.
   `detect_assumption using <hook>` will try the default as well as `hook`.
   `detect_assumption using only <hook>` will try only `hook`.*)
Tactic Notation "detect_assumption" "using" tactic3(hook) :=
(detect_assumption ltac:(assumption + reflexivity + hook)).
Tactic Notation "detect_assumption" "using" "only" tactic3(hook) :=
(detect_assumption ltac:(hook)).
Tactic Notation "detect_assumption" :=
(detect_assumption ltac:(assumption + reflexivity)).
