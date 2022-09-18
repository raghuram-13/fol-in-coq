Set Implicit Arguments. Unset Strict Implicit.

Require Import SetNotations Util Assumptions. Require Lattices.
Import (notations) EqNotations.

(* Misc *)

Ltac done := guard numgoals = 0.


Structure Language := {
  lang_carrier :> Type;
  contradiction : lang_carrier;
  impl : lang_carrier -> lang_carrier -> lang_carrier
}.
Arguments impl {_}.

(* Free languages on a set of atomic propositions as a special case. *)
Section FreeLanguage.
  Variable Atom : Type.

  Inductive FreeLang :=
  | FreeLang_atom : Atom -> FreeLang
  | FreeLang_contradiction : FreeLang
  | FreeLang_impl : FreeLang -> FreeLang -> FreeLang.

  Definition FreeLanguage := {|
    lang_carrier := FreeLang;
    contradiction := FreeLang_contradiction; impl := FreeLang_impl
  |}.
End FreeLanguage.
Arguments FreeLang_contradiction {Atom}.

(* Notation *)
Notation "⊥" := (contradiction _).
Infix "→" := impl (at level 60, right associativity).

Definition neg {l : Language} (p : l) : l := p → ⊥.
Notation "¬ p" := (neg p) (at level 35, right associativity).

(* Semantics *)
Section Semantics. Context {Proposition : Language}.

Structure model := {
  model_fun :> Proposition -> bool;
  model_resp_contra : model_fun ⊥ = false;
  model_resp_impl p q : model_fun (p → q) = implb (model_fun p) (model_fun q)
}.

Definition satisfies (m : model) (Γ : unary_predicate Proposition) : Prop :=
forall p : Proposition, p ∈ Γ -> Is_true (m p).

Definition entails (Γ : unary_predicate Proposition) p :=
forall m : model, satisfies m Γ -> Is_true (m p).

Section ModelTerminology. Variable (assumptions : unary_predicate Proposition).
Definition valid         : Prop := forall m : model, satisfies m assumptions.
Definition unsatisfiable : Prop := forall m : model, ~satisfies m assumptions.
Definition satisfiable   : Prop := exists m : model, satisfies m assumptions.
End ModelTerminology.

End Semantics.
Arguments model Proposition : clear implicits.
#[local] Infix "⊨" := entails (at level 75).
#[export] Hint Rewrite @model_resp_contra @model_resp_impl.

(* For the case of free languages *)
Section FreeLangsSemantics.
  Variable Atom : Type.

  Definition valuation_model (v : Atom -> bool) : model _ := {|
    model_fun := fix models' (p : FreeLanguage Atom) := match p with
    | FreeLang_atom n => v n
    | FreeLang_contradiction => false
    | FreeLang_impl p q => implb (models' p) (models' q)
    end;
    model_resp_contra := eq_refl;
    model_resp_impl _ _ := eq_refl
  |}.
End FreeLangsSemantics.

Section Theory. Context {Proposition : Language}.

(* Proofs *)
Section InductiveDefs. Context {assumptions : Proposition -> Type}.

(* The type of proofs of a given Proposition.

   We allow `assumptions` to be of type `Proposition -> Type` primarily
   for the sake of combining assumptions with ⊔, in which case we can
   distinguish between proofs by assumption as being of the first or
   second set of assumptions.
   A single assumption `p` is represented by `eq p : Proposition -> Prop`. *)
Inductive Proof : Proposition -> Type :=
| by_assumption {p} : assumptions p -> Proof p
| rule_1 p q : Proof (p → q → p)
| rule_2 p q r : Proof ((p → q → r) → (p → q) → (p → r))
| by_contradiction p : Proof (¬¬p → p)
| modus_ponens hyp concl : Proof (hyp → concl) -> Proof hyp -> Proof concl.

(* Predicate expressing provability of a Proposition.

   This has just one constructor which takes only one argument, which
   means it is 'essentially the same' as Proof assumptions p.  The
   difference is the universe: `Provable assumptions p : Prop`, so it
   effectively 'forgets' the exact proof used and behaves like a
   proposition rather than a data type.*)
Definition Provable (p : Proposition) : Prop := inhabited (Proof p).

End InductiveDefs.
(* {assumptions} ensured all constructors infer it automatically.
   But we don't want the type itself to do that! *)
Arguments Proof assumptions : clear implicits.
Arguments Provable assumptions : clear implicits.


(* Proof notations *)
Declare Scope proof_scope. Delimit Scope proof_scope with proof.

Local Notation "Γ |- p"    := (Proof Γ p)      (at level 75) : proof_scope.
Local Notation "|- p"      := (Proof ∅ p)     (at level 75) : proof_scope.
Local Notation ";; p |- q" := (Proof (eq p) q) (at level 75) : proof_scope.

Local Notation "Γ ;; p ; .. ; q |- r" := (Proof (..(Γ ⊔ eq p) .. ⊔ eq q) r)
    (* prevent parsing (q |- r) as a subexpression *)
    (at level 75, q at next level) : proof_scope.
Local Notation ";; p0 ; p ; .. ; q |- r" := (Proof (..(eq p0 ⊔ eq p)..⊔ eq q) r)
    (at level 75, q at next level) : proof_scope.

(* Wrap around any |- expression to turn `Proof` into `Provable`. *)
Local Notation "[ proof ]" := (inhabited proof%proof) : type_scope.

Open Scope proof_scope.


Coercion has_proof (assumptions : Proposition -> Type) p
    : assumptions |- p -> [assumptions |- p] := @inhabits _.

(* Tactics *)

(* TODO consider forcing "solve or fail" behaviour using `solve`. *)
Ltac proof_assumption hook := match goal with
| |- [_ |- _] => apply has_proof; proof_assumption hook
| |- _ |- _ => apply by_assumption; detect_assumption using only hook
end.

(* Automates constructing proofs of statements by assumption,
   simplifying occurrences of ⊔ and =, taking a tactic `hook` to use in
   the branches (this part is the same functionality as
   `detect_assumption`).

   The notation for passing the hook is the same as `detect_assumption`:
   default `assumption` and `reflexivity`, `using <hook>` to try `hook`
   after `assumption` and `reflexivity`, and `using only <hook>` to use
   only `hook`, disabling the use of `assumption` and `reflexivity`. *)
Tactic Notation "proof_assumption" "using" tactic3(hook) :=
(proof_assumption ltac:(assumption + reflexivity + hook)).
Tactic Notation "proof_assumption" "using" "only" tactic3(hook) :=
(proof_assumption ltac:(hook)).
Tactic Notation "proof_assumption" :=
(proof_assumption ltac:(assumption + reflexivity)).


(* Misc *)

Section ConsistencyTerminology. Variable (assumptions : Proposition -> Type).
Definition inconsistent : Prop := [assumptions |- ⊥].
Definition consistent : Prop := ~inconsistent.
End ConsistencyTerminology.

(* Convenience function written on the fly for checking the size of proofs. *)
Fixpoint size {Γ} {p} (proof : Γ |- p) : nat := match proof with
| modus_ponens proof1 proof2 => 1 + (size proof1) + (size proof2)
| _ => 1
end.


(* Properties of this proof system. *)

Definition proof_refl {Γ p} : Γ;; p |- p := ltac:(proof_assumption).
#[global] Arguments proof_refl {Γ p}, [Γ] p.

Section RelationBetweenDifferentAssumptions.
Implicit Type (Γ : Proposition -> Type).

(** Transitivity **)

Fixpoint proof_trans Γ Γ' (h : forall [p], Γ' p -> Γ |- p)
    [p] (proof : Γ' |- p) : Γ |- p := match proof with
| by_assumption h_in'        => h h_in'
| rule_1 p q                 => rule_1 p q
| rule_2 p q r               => rule_2 p q r
| by_contradiction p         => by_contradiction p
| modus_ponens proof1 proof2 => modus_ponens (proof_trans h proof1)
                                             (proof_trans h proof2)
end.

Definition proof_trans' Γ Γ' (h : forall [p], Γ' p -> Γ |- p)
    : forall [p], Γ ⊔ Γ' |- p -> Γ |- p :=
proof_trans (fun p => sum_rect _ by_assumption (h (p := p))).

Definition proof_mono Γ Γ' (h : Γ ⊑ Γ')
    : forall [p], Γ |- p -> Γ' |- p :=
proof_trans (fun p (h' : Γ p) => by_assumption (h _ h')).

Definition provable_trans' Γ Γ' (h : forall [p], Γ' p -> [Γ |- p])
    p (proof : [Γ ⊔ Γ' |- p]) : [Γ |- p] :=
let (proof) := proof in
(* `proof_trans' h proof` doesn't work because `h` returns `Provable`s.
   Unwrapping it would basically be AoC. *)
(fix rec [p] (proof : Γ ⊔ Γ' |- p) : [Γ |- p] :=
 match proof with
 | by_assumption (inl h_in)  => by_assumption h_in
 | by_assumption (inr h_in') => h h_in'
 | rule_1 p q                => rule_1 p q
 | rule_2 p q r              => rule_2 p q r
 | by_contradiction p        => by_contradiction p
 | modus_ponens p1 p2        => match rec p1, rec p2 with
                                | inhabits p1, inhabits p2 => modus_ponens p1 p2
                                end
 end) p proof.

Definition provable_trans Γ Γ' (h : forall [p], Γ' p -> [Γ |- p])
    p : [Γ' |- p] -> [Γ |- p] := fun '(inhabits proof) =>
provable_trans' h (proof_mono (fun _ h => inr h) proof).

Section test.
(* It is slightly verbose, but we _can_ show these results for appending
   a few propositions to Γ using `proof_trans'`/`provable_trans'`
   reasonably. *)
Check fun Γ p (proof : Γ |- p) =>
  proof_trans' (eq_rect p _ proof) : forall q, Γ;; p |- q -> Γ |- q.
Check fun Γ p q
        (proof1 : Γ |- p) (proof2 : Γ;; p |- q) =>
  (fun r proof3 =>
    proof_trans' (eq_rect p _ proof1) (
    proof_trans' (eq_rect q _ proof2)
    proof3))
  : forall r, Γ;; p; q |- r -> Γ |- r.
Check fun Γ p q
        (proof1 : Γ |- p) (proof2 : [Γ;; p |- q]) =>
  (fun r proof3 =>
    let (proof_intermediate) := provable_trans' (eq_rect q _ proof2) proof3 in
    proof_trans' (eq_rect p _ proof1) proof_intermediate)
  : forall r, [Γ;; p; q |- r] -> [Γ |- r].
End test.

End RelationBetweenDifferentAssumptions.

(* Just so happens that these lemmas share the same Γ, so a section works. *)
Section SomeLemmas. Context {Γ : Proposition -> Type}.

Definition modus_ponens_binary p q r (implication : Γ |- p → q → r)
    : Γ |- p -> Γ |-q -> Γ |- r :=
fun proof1 proof2 => modus_ponens (modus_ponens implication proof1) proof2.

(* We prove a few results in a syntax resembling, e.g., Hilbert-style
   proofs, just to demonstrate that we can. *)

Definition id p : Γ |- (p → p) :=
let step_1 : Γ |- p → (p → p) → p       := rule_1 p (p → p) in
let step_2 : Γ |- p → p → p             := rule_1 p p in
let step_3 : Γ |- (p → (p → p) → p) → (p → p → p) → (p → p)
                                        := rule_2 p (p → p) p in
let step_4 : Γ |- (p → p → p) → (p → p) := modus_ponens step_3 step_1 in
modus_ponens step_4 step_2.

Definition add_under_imp p q : Γ |- q -> Γ |- (p → q) :=
modus_ponens (rule_1 q p : Γ |- q → p → q).

Definition modus_ponens_under_imp p hyp concl
    : let P q := Γ |- (p → q) in P (hyp → concl) -> P hyp -> P concl :=
modus_ponens_binary (rule_2 p hyp concl).

End SomeLemmas.


(* Sometimes it's easier to show `Γ;; p |- q` and sometimes it's easier
   to show `Γ |- p → q`. This allows us to reach `concl` from `leaves`
   in the first mode and reach `leaves` in the second. *)
Fixpoint deduction_theorem' {Γ} [leaves] [hyp concl]
        (proof : Γ ⊔ eq hyp ⊔ leaves |- concl)
        (subproofs: forall [q], leaves q -> Γ |- hyp → q)
    : Γ |- hyp → concl := match proof with
| by_assumption (inr h)       => subproofs h
| by_assumption (inl (inr h)) => rew dependent h in id hyp
| by_assumption (inl (inl h)) => add_under_imp hyp (by_assumption h)
| rule_1 _ _                 => add_under_imp hyp (rule_1 _ _)
| rule_2 _ _ _               => add_under_imp hyp (rule_2 _ _ _)
| by_contradiction _         => add_under_imp hyp (by_contradiction _)
| modus_ponens proof1 proof2 => modus_ponens_under_imp
                                  (deduction_theorem' proof1 subproofs)
                                  (deduction_theorem' proof2 subproofs)
end.

Definition deduction_theorem {Γ} [hyp concl] proof : Γ |- hyp → concl :=
deduction_theorem' (leaves := ∅) (proof_mono (fun _ h => inl h) proof)
                                 (fun _ => False_rect _).

Definition deduction_theorem_conv {Γ} [hyp concl] (proof : Γ |- hyp → concl)
    : Γ;; hyp |- concl :=
modus_ponens (proof_mono (fun _ h => inl h) proof) (proof_refl hyp).


(* Helps use deduction_theorem' conveniently. *)
Ltac reducing_deduction_theorem leaves' tactic :=
apply deduction_theorem' with (leaves := leaves'); [
  tactic; proof_assumption; done
  | intro_assumption
].

(* Given a goal (Γ |- p → q), `red_by_dt to <leaves> by <tactic>`
   constructs a proof of q allowing Γ, p and also elements of `leaves`
   as assumptions, automatically filling in proofs of 'obvious'
   assumptions, and leaves goals to construct proofs (Γ |- p → q') for
   all assumptions `q'` of `leaves`.

   The "to" clause can be omitted if the set of leaves is inferrable,
   but this is rarely the case. (Omitting the "by" clause would amount
   to `q` itself being one of the leaves, in which case the tactic
   invocation achieves nothing.)  *)
Tactic Notation "red_by_dt" "to" constr(leaves) "by" tactic3(tactic) :=
reducing_deduction_theorem constr:(leaves) ltac:(tactic).
Tactic Notation "red_by_dt" "by" tactic3(tactic) :=
reducing_deduction_theorem _ ltac:(tactic).


(* More proofs in the proof system. *)

(* `i` stands for inference: this is expressed as an inference rule
   rather than a proof of an implication. *)
Definition interchange_hypotheses_i {Γ} p q r : Γ;; p → q → r |- q → p → r.
red_by_dt to (eq (p → q)) by eapply modus_ponens_under_imp.
exact (rule_1 q p).
Defined.

Definition exfalso {Γ} p : Γ |- ⊥ → p.
red_by_dt to (eq (¬¬p)) by apply (modus_ponens (by_contradiction p)).
exact (rule_1 ⊥ (¬p)).
Defined.

Definition from_contradiction {Γ} p q : Γ |- ¬p → p → q :=
modus_ponens (rule_2 p ⊥ q) (deduction_theorem (exfalso q)).

Definition absurd p q {Γ} : Γ |- p → ¬p → q :=
proof_trans' (Γ' := eq (¬p → p → q))
  ltac:(intro_assumption; exact (from_contradiction p q))
  (interchange_hypotheses_i (¬p) p q).

Definition impl_comp {Γ} p q r : Γ |- (q → r) → (p → q) → (p → r).
apply deduction_theorem.
apply (modus_ponens (rule_2 p q r)). apply deduction_theorem; proof_assumption.
Defined.

(* TODO this could be more legible: something looking more like
     apply interchange_hypotheses_i; exact impl_comp p q r. *)
Definition impl_trans {Γ} p q r : Γ |- (p → q) → (q → r) → (p → r) :=
proof_trans' (Γ' := eq ((q → r) → (p → q) → (p → r)))
  ltac:(intro_assumption; exact (impl_comp p q r))
  (interchange_hypotheses_i _ _ _).

Definition modus_tollens {Γ} p q : Γ |- (p → q) → (¬q → ¬p) :=
impl_trans p q ⊥.

Definition modus_tollens_conv {Γ} p q : Γ |- (¬q → ¬p) → (p → q).
apply deduction_theorem.
red_by_dt to (eq (¬¬q)) by apply (modus_ponens (by_contradiction q)).
apply interchange_hypotheses_i.
Defined.



Section ConnectionWithSemantics.

Theorem soundness_theorem (Γ : unary_predicate Proposition) p
    : [Γ |- p] -> Γ ⊨ p.
intros [proof] m h.
induction proof as [p h_in|p q|p q r|p|p q ? h_i_imp ? h_i_p]; [
  (* by_assumption *)
  exact (h p h_in)
  (* Takes care of no-hypothesis introduction rules. *)
| try unfold neg; autorewrite with core;
  destruct (m p); try destruct (m q); try destruct (m r); reflexivity
..(* modus_ponens *)
| rewrite Is_true_iff_eq_true in h_i_p, h_i_imp |- *;
  autorewrite with core in h_i_imp; rewrite h_i_p in h_i_imp; exact h_i_imp
].
Qed.


Import Coq.Classes.RelationClasses (Reflexive, Transitive, PreOrder).
Implicit Types (Γ : Proposition -> Type) (p q r : Proposition).

Definition provable_le {Γ} p q := [Γ;; p |- q].

Definition provable_le_refl {Γ} : Reflexive provable_le := @proof_refl Γ.

Definition provable_le_trans {Γ} : Transitive provable_le := fun p q r =>
fun proof1 proof2 => provable_trans (Γ := Γ ⊔ eq p) (Γ' := Γ ⊔ eq q)
  ltac:(intro_assumption; [ proof_assumption using only assumption
                          | exact proof1 ])
  proof2.

Instance : forall Γ, PreOrder (provable_le (Γ := Γ)) := fun Γ =>
{| Coq.Classes.RelationClasses.PreOrder_Reflexive := provable_le_refl;
   Coq.Classes.RelationClasses.PreOrder_Transitive := provable_le_trans |}.

Let disj p q := (p → q) → q.
Let conj p q := ¬(p → ¬q).

Let left_proves_disj {Γ} p q : Γ;; p |- disj p q. refine (
deduction_theorem (modus_ponens _ _)
); proof_assumption. Defined.

Let right_proves_disj {Γ} p q : Γ;; q |- disj p q. refine (
deduction_theorem _
); proof_assumption. Defined.

(* We need to use this across multiple Γ to prove distributivity later.
   This is the reason why Γ is not a section variable. *)
Let disj_univ {Γ} p q r (h_p: Γ;;p |- r) (h_q: Γ;;q |- r) : Γ;; disj p q |- r.
apply (modus_ponens (by_contradiction r)), deduction_theorem.
assert (mt_convert: forall p', Γ;; p' |- r -> Γ;; (p → q) → q; ¬r |- ¬p').
{ intros p' proof. apply proof_mono with (Γ := Γ ⊔ eq (¬r)); [
                     intro_assumption; detect_assumption | ].
  apply deduction_theorem in proof. apply deduction_theorem_conv.
  exact (modus_ponens (modus_tollens p' r) proof). }
apply (modus_ponens (mt_convert q h_q)).
apply modus_ponens with (hyp := p → q); [ proof_assumption | ].
apply (modus_ponens (from_contradiction p q)). exact (mt_convert p h_p).
Defined.

Let conj_proves_left {Γ} p q : Γ;; conj p q |- p. refine (
modus_ponens (by_contradiction p) (deduction_theorem (
modus_ponens _ (modus_ponens (from_contradiction p (¬q)) _)))
); proof_assumption. Defined.

Let conj_proves_right {Γ} p q : Γ;; conj p q |- q. refine (
modus_ponens (by_contradiction q) (deduction_theorem (
modus_ponens _ (deduction_theorem _)))
); proof_assumption. Defined.

Let conj_proves' {Γ} p q r : Γ;; p; q |- r -> Γ;; conj p q |- r :=
proof_trans (Γ := Γ ⊔ eq (conj p q)) (Γ' := (Γ ⊔ eq p) ⊔ eq q) (p := r)
  ltac:(intro_assumption; [ proof_assumption using only assumption
                          | apply conj_proves_left | apply conj_proves_right ]).

Let conj_univ' {Γ} p q : Γ;; p; q |- conj p q. refine (
deduction_theorem (modus_ponens_binary _ _ _)
); proof_assumption. Defined.

Let conj_univ {Γ} p q (h_p : Γ |- p) (h_q : Γ |- q) : Γ |- conj p q.
(* eapply (proof_mono (fun _ h => inl h)) in h_p, h_q; exact (
deduction_theorem (modus_ponens_binary proof_refl h_p h_q)). *)
apply proof_trans with (Γ' := eq p ⊔ eq q)
; [ intro_assumption; assumption | ].
apply proof_trans with (Γ' := (∅ ⊔ eq p) ⊔ eq q); [
  intro_assumption; [ contradiction | proof_assumption .. ] | ].
apply conj_univ'.
Defined.

Let false_proves {Γ} p : Γ;; ⊥ |- p := modus_ponens (exfalso p) proof_refl.
Let proves_true {Γ} : Γ |- ¬⊥ := id ⊥.

Let conj_not_proves_false {Γ} p : Γ;; conj p (¬p) |- ⊥ :=
(* conj_proves' (ltac:(eapply modus_ponens; proof_assumption) : Γ;;p;¬p |- ⊥) *)
modus_ponens proof_refl (absurd p ⊥).

Let proves_disj_not {Γ} p : Γ |- disj p (¬p).
apply deduction_theorem.
red_by_dt to (eq (¬p)) by apply modus_ponens with (hyp := p).
exact (proof_refl (p → ¬p)).
Defined.

Let and_distrib_or' {Γ} p q r
    : Γ;; conj p (disj q r) |- disj (conj p q) (conj p r).
apply conj_proves'.
apply disj_univ
; (eapply proof_trans with (Γ' := ∅ ⊔ eq (conj p _)); [
    intro_assumption; [ contradiction | apply conj_univ' ]
  | solve [apply left_proves_disj | apply right_proves_disj] ]).
Defined.

Import (coercions, notations) Lattices.
Import -(notations) Lattices.BooleanAlgebra.
Section LindenbaumTarskiAlgebra.

Variable Γ : Proposition -> Type.

Instance : isBooleanAlgebra (provable_le (Γ := Γ)) := {|
  join := disj; meet := conj; complement p := ¬p; bot := ⊥; top := ¬⊥;

  left_le_join p q := has_proof (left_proves_disj p q);
  right_le_join p q := has_proof (right_proves_disj p q);
  join_le_of_both_le p q r '(inhabits h_p) '(inhabits h_q) := disj_univ h_p h_q;

  (* `has_proof` coercion sometimes not inserted for some reason. *)
  meet_le_left p q := has_proof (conj_proves_left p q);
  meet_le_right p q := has_proof (conj_proves_right p q);
  le_meet_of_le_both p q r '(inhabits h_p) '(inhabits h_q) := conj_univ h_p h_q;

  bot_le p := false_proves p; le_top p := proves_true;

  meet_compl_le_bot p := conj_not_proves_false p;
  top_le_join_compl p := proves_disj_not p;

  meet_distrib_join' p q r := and_distrib_or' p q r
|}.

Definition LindenbaumTarskiAlgebra : BooleanAlgebra :=
@Build_BooleanAlgebra {| Lattices.le := provable_le (Γ := Γ) |} _.

(* Express some properties in terms of the Lindenbaum-Tarski algebra. *)
Lemma proves_iff (p : LindenbaumTarskiAlgebra) : [Γ |- p] <-> (p ∼ top).
split.
+ intros [h].
  apply equiv_top_of_top_le, has_proof, (proof_mono (fun _ h => inl h)).
  exact h.
+ intros [? [h]]. apply has_proof, proof_trans' with (Γ' := eq top)
  ; [ intro_assumption; exact proves_true | exact h ].
Qed.

Definition inconsistent_iff
    : inconsistent Γ <-> ⊥ ∼[LindenbaumTarskiAlgebra] ¬⊥ := proves_iff ⊥.

Definition imp_as_disj (p q : LindenbaumTarskiAlgebra)
    : (p → q : LindenbaumTarskiAlgebra) ∼ disj (¬p) q.
split; apply has_proof.
+ apply deduction_theorem.
  refine (modus_ponens (deduction_theorem _) (proves_disj_not p)).
  apply disj_univ; (eapply modus_ponens
  ; swap 1 2; [apply proof_refl|proof_assumption]).
+ red_by_dt to (eq (¬p → q)) by eapply modus_ponens; exact (absurd p q).
Defined.

End LindenbaumTarskiAlgebra.

Section Completeness.

Theorem Completeness' {Γ : unary_predicate Proposition}
    (h_consistent : consistent Γ) : satisfiable Γ.
set (LTA := LindenbaumTarskiAlgebra Γ).
unfold consistent in h_consistent; rewrite (inconsistent_iff Γ) in h_consistent;
  change (filter_proper (trivial_filter LTA)) in h_consistent.
destruct (ultrafilter_lemma_em (Build_ProperFilter h_consistent))
  as [uf h_incl].
pose (h_uf_em p := Is_true_em (uf p) : p ∈ uf \/ p ∉ uf).
eexists {| model_fun := uf;
  model_resp_contra := ltac:(admit);
  model_resp_impl p q := ltac:(admit) |}.
assert (h_incl' : forall p, p ∈ Γ -> p ∈ uf).
{ intros ? h; apply h_incl, proves_iff; proof_assumption. }
intros ? h; exact (h_incl' _ h).
Admitted.

End Completeness.

End ConnectionWithSemantics.

End Theory.
