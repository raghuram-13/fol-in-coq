Set Implicit Arguments.

Require Import SetNotations. Import (notations) Coq.Init.Logic.EqNotations.
Require Lattices.

(* Miscellany *)
Ltac done := let n := numgoals in guard n = 0.

(* Limit scope of Variable declarations. They seem to be treated as some kind of
   axioms otherwise, whereas the intention is to parametrise future functions
   on them. *)
Section Main. Variable VarIndex : Type.


(* The propositions studied. *)
Inductive Proposition :=
| var : VarIndex -> Proposition
| falsum : Proposition
| imp : Proposition -> Proposition -> Proposition.


(* Other operations and notation. *)

Definition neg (p : Proposition)    : Proposition := imp p falsum.
(* Definition truth                    : Proposition := neg falsum. *)
(* Definition conj (p q : Proposition) : Proposition := neg (imp p (neg q)). *)
(* Definition disj (p q : Proposition) : Proposition := imp (neg p) q. *)

Local Notation "⊥" := falsum.
Local Notation "p '-> q" := (imp p q) (at level 60, right associativity).
Local Notation "¬ p" := (neg p) (at level 35, p at level 35).
(* Local Notation "p '/\ q" := (conj p q) (at level 80, right associativity). *)
(* Local Notation "p '\/ q" := (disj p q) (at level 80, right associativity). *)


(* Semantics *)
Definition valuation := VarIndex -> bool.

Fixpoint models' (v : valuation) (p : Proposition) : bool := match p with
| var n => v n
| ⊥ => false
| p '-> q => implb (models' v p) (models' v q)
end.

Definition models (v : valuation) (Γ : unary_predicate Proposition) : Prop :=
forall p : Proposition, Γ p -> models' v p = true.

Definition entails (Γ : unary_predicate Proposition) p := forall v : valuation, models v Γ -> models' v p = true.

Local Notation "Γ ⊨ p" := (entails Γ p) (at level 75).

Definition unsound (Γ : unary_predicate Proposition) := Γ ⊨ ⊥.

(* Proofs *)

Section InductiveDefs. Context {assumptions : Proposition -> Type}.
(* The type of proofs of a given Proposition. *)
Inductive Proof : Proposition -> Type :=
| by_assumption {p} : assumptions p -> Proof p
| rule_1 p q : Proof (p '-> q '-> p)
| rule_2 p q r : Proof ((p '-> q '-> r) '-> (p '-> q) '-> (p '-> r))
| by_contradiction p : Proof (¬¬p '-> p)
| modus_ponens hyp concl : Proof (hyp '-> concl) -> Proof hyp -> Proof concl.
(* {assumptions} ensured all constructors infer it automatically.
   But we don't want the type itself to do that! *)

(* Predicate expressing provability of a Proposition.

   This has just one constructor which takes only one argument, which means it
   is 'essentially the same' as Proof assumptions p.  The difference is that it
   is declared that `Provable assumptions p : Prop`, which effectively 'forgets'
   the exact proof used, so that it behaves like a proposition rather than a data
   type.*)
Definition Provable (p : Proposition) : Prop := inhabited (Proof p).

End InductiveDefs.
Arguments Proof assumptions : clear implicits.
Arguments Provable assumptions : clear implicits.

(* Proof notations *)
Declare Scope proof_scope. Delimit Scope proof_scope with proof.
Local Notation "Γ |- p"   := (Proof Γ p)      (at level 75) : proof_scope.
Local Notation "|- p"     := (Proof ∅ p)      (at level 75) : proof_scope.
Local Notation ";; p |- q" := (Proof (eq p) q) (at level 75) : proof_scope.

Local Notation "Γ ;; p ; .. ; q |- r" := (Proof ( .. (Γ ⊔ eq p) .. ⊔ eq q) r)
    (* prevent parsing (q |- r) as a subexpression *)
    (at level 75, q at next level) : proof_scope.
Local Notation ";; p0 ; p ; .. ; q |- r" := (Proof ( .. (eq p0 ⊔ eq p) .. ⊔ eq q) r)
    (at level 75, q at next level) : proof_scope.

(* Wrap around any |- expression to turn `Proof` into `Provable`. *)
Local Notation "[ proof ]" := (inhabited proof%proof) : type_scope.

Open Scope proof_scope.


(* Miscellany about proofs *)
Coercion has_proof (assumptions : Proposition -> Type) p
    : assumptions |- p -> [assumptions |- p] := @inhabits _.

Definition inconsistent (assumptions : Proposition -> Type) := [assumptions |- ⊥].

(** Tactics **)

Ltac detect_assumption hook := repeat (apply inl + apply inr); hook.

(* TODO consider forcing "solve or fail" behaviour using `solve`. *)
Ltac proof_assumption hook := match goal with
| |- [_ |- _] => apply has_proof; proof_assumption hook
| |- _ |- _ => apply by_assumption; detect_assumption hook
end.

(* Helps in constructing gaols of the form (Γ p) where Γ is of the kind
   usually encountered here: in particular, deals specially with ⊔ and eq. *)
Tactic Notation "detect_assumption" "using" tactic(hook) :=
(detect_assumption ltac:(assumption + reflexivity + hook)).
Tactic Notation "detect_assumption" "using" "only" tactic(hook) :=
(detect_assumption ltac:(hook)).
Tactic Notation "detect_assumption" :=
(detect_assumption ltac:(assumption + reflexivity)).

(* proof_assumption automates constructing proofs of statements by
   assumption, especially when the set of assumptions consists of
   multiple sets joined by ⊔.

   It can be passed a tactic `hook` with the syntax
      proof_assumption using <hook>
   to construct the assumption proof.  This will automatically try
   some 'obvious' tactics first (`assumption` and `reflexivity`); to
   disable this, use `proof_assumption using only <hook>`. *)
Tactic Notation "proof_assumption" "using" tactic(hook) :=
(proof_assumption ltac:(assumption + reflexivity + hook)).
Tactic Notation "proof_assumption" "using" "only" tactic(hook) :=
(proof_assumption ltac:(hook)).
Tactic Notation "proof_assumption" :=
(proof_assumption ltac:(assumption + reflexivity)).

(* Use instead of intro when introducing an assumption of some assumption set.
   Automatically does case analysis for assumption sets using ⊔ and for
   assumptions of the form `eq p`, reduces to constructing whatever for `p`. *)
Ltac intro_assumption :=
let x := fresh "assumption" in
(* We need h to refer to different hypotheses at different times, and this is
   the only way I can figure out to do it. *)
let rec rec h :=
  let decompose_sum h1 h2 := match type of h with
    | sum _ _ => destruct h as [h1|h2] end in
  let h1 := fresh "is_assumption" in let h2 := fresh "is_assumption" in
  tryif (decompose_sum h1 h2 + (simpl in h; decompose_sum h1 h2)) then
    [> rec h1 | rec h2 ]
  else (* after repeat *) match type of h with | _ = _ => induction h
                              | _ => idtac end
in
let h := fresh "is_assumption" in
intros x h; rec h.


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
proof_trans (fun p => sum_rect (fun _ => Γ |- p) by_assumption (h (p := p))).

Definition proof_mono [Γ Γ'] (h : Γ ⊑ Γ')
    : forall [p], Γ |- p -> Γ' |- p :=
proof_trans (fun p (h' : Γ p) => by_assumption (h _ h')).

Definition provable_trans' Γ Γ' (h : forall [p], Γ' p -> [Γ |- p])
    p (proof : [Γ ⊔ Γ' |- p]) : [Γ |- p] :=
let (proof) := proof in
(* `proof_trans' h proof` doesn't work because `h` returns `Provable`s.
   Unwrapping it would basically be AoC. *)
(fix proof_trans' [p] (proof : Γ ⊔ Γ' |- p) : [Γ |- p] :=
 match proof with
 | by_assumption (inl h_in)   => by_assumption h_in
 | by_assumption (inr h_in')  => h h_in'
 | rule_1 p q                 => rule_1 p q
 | rule_2 p q r               => rule_2 p q r
 | by_contradiction p         => by_contradiction p
 | modus_ponens p1 p2         => match proof_trans' p1, proof_trans' p2 with
                                 | inhabits p1, inhabits p2 => modus_ponens p1 p2
                                 end
 end) p proof.

Definition provable_trans Γ Γ' (h : forall [p], Γ' p -> [Γ |- p])
    p (proof : [Γ' |- p]) : [Γ |- p] :=
provable_trans' h (let (proof) := proof in
                   proof_mono (fun _ h => inr h) proof).

Section test.
(* It is slightly verbose, but we _can_ show these results for appending a
   few propositions to Γ using `proof_trans'`/`provable_trans'` reasonably. *)
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

Definition modus_ponens_binary p q r (implication : Γ |- p '-> q '-> r)
    : Γ |- p -> Γ |-q -> Γ |- r :=
fun proof1 proof2 => modus_ponens (modus_ponens implication proof1) proof2.

(* We prove a few results in a syntax resembling, e.g., Hilbert-style
   proofs, just to show we can. *)
Definition id p : Γ |- (p '-> p) :=
let step_1 : Γ |- p '-> (p '-> p) '-> p         := rule_1 p (p '-> p) in
let step_2 : Γ |- p '-> p '-> p                 := rule_1 p p in
let step_3 : Γ |- (p '-> (p '-> p) '-> p) '-> (p '-> p '-> p) '-> (p '-> p)
                                                := rule_2 p (p '-> p) p in
let step_4 : Γ |- (p '-> p '-> p) '-> (p '-> p) := modus_ponens step_3 step_1 in
modus_ponens step_4 step_2.

Definition add_under_imp p q : Γ |- q -> Γ |- (p '-> q) :=
modus_ponens (rule_1 q p : Γ |- q '-> p '-> q).

Definition modus_ponens_under_imp p hyp concl
    : let P q := Γ |- (p '-> q) in   P (hyp '-> concl) -> P hyp -> P concl :=
modus_ponens_binary (rule_2 p hyp concl).

End SomeLemmas.


(* Sometimes it's easier to show `Γ;; p |- q` and sometimes it's easier
   to show `Γ |- p '-> q`. This allows us to reach `concl` from `leaves`
   in the first mode and reach `leaves` in the second. *)
Fixpoint deduction_theorem' {Γ} [leaves] [hyp concl]
        (proof : Γ ⊔ eq hyp ⊔ leaves |- concl)
        (subproofs: forall [q], leaves q -> Γ |- hyp '-> q)
    : Γ |- hyp '-> concl := match proof with
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

Definition deduction_theorem {Γ} [hyp concl] proof : Γ |- hyp '-> concl :=
deduction_theorem' (leaves := ∅) (proof_mono (fun _ h => inl h) proof)
                                 (fun _ => False_rect _).

Definition deduction_theorem_conv {Γ} [hyp concl]
    (proof : Γ |- hyp '-> concl) : Γ;; hyp |- concl :=
modus_ponens (proof_mono (fun _ h => inl h) proof) (proof_refl hyp).


(* Using deduction_theorem' conveniently. *)
Ltac reducing_deduction_theorem leaves' tactic :=
apply deduction_theorem' with (leaves := leaves'); [
  tactic; proof_assumption; done
  | intro_assumption
].

Tactic Notation "red_by_dt" "to" constr(leaves) "by" tactic(tactic) :=
reducing_deduction_theorem constr:(leaves) ltac:(tactic).
Tactic Notation "red_by_dt" "by" tactic(tactic) :=
reducing_deduction_theorem _ ltac:(tactic).
Tactic Notation "red_by_dt" "to" constr(leaves) :=
reducing_deduction_theorem leaves ltac:(idtac).
Tactic Notation "red_by_dt" := reducing_deduction_theorem _ ltac:(idtac).


Definition interchange_hypotheses_e {Γ} p q r : Γ;; p '-> q '-> r |- q '-> p '-> r.
red_by_dt to (eq (p '-> q)) by eapply modus_ponens_under_imp.
exact (rule_1 q p).
Defined.

Definition exfalso {Γ} p : Γ |- ⊥ '-> p.
red_by_dt to (eq (¬¬p)) by apply (modus_ponens (by_contradiction p)).
exact (rule_1 ⊥ (¬p)).
Defined.

Definition from_contradiction {Γ} p q : Γ |- ¬p '-> p '-> q :=
modus_ponens (rule_2 p ⊥ q) (deduction_theorem (exfalso q)).

Definition absurd p q {Γ} : Γ |- p '-> ¬p '-> q :=
proof_trans' (Γ' := eq (¬p '-> p '-> q))
  ltac:(intro_assumption; exact (from_contradiction p q))
  (interchange_hypotheses_e (¬p) p q).

Definition impl_comp {Γ} p q r : Γ |- (q '-> r) '-> (p '-> q) '-> (p '-> r).
apply deduction_theorem.
apply (modus_ponens (rule_2 p q r)). apply deduction_theorem; proof_assumption.
Defined.

Definition impl_trans {Γ} p q r : Γ |- (p '-> q) '-> (q '-> r) '-> (p '-> r) :=
proof_trans' (Γ' := eq ((q '-> r) '-> (p '-> q) '-> (p '-> r)))
  ltac:(intro_assumption; exact (impl_comp p q r))
  (interchange_hypotheses_e _ _ _).

Definition modus_tollens {Γ} p q : Γ |- (p '-> q) '-> (¬q '-> ¬p) :=
impl_trans p q ⊥.

Definition modus_tollens_conv {Γ} p q : Γ |- (¬q '-> ¬p) '-> (p '-> q).
apply deduction_theorem.
red_by_dt to (eq (¬¬q)) by apply (modus_ponens (by_contradiction q)).
apply interchange_hypotheses_e.
Defined.



Theorem soundness_theorem (Γ : unary_predicate Proposition) p : [Γ |- p] -> Γ ⊨ p.
intros (proof) v h.
induction proof as [p h_in|p q|p q r|p|p q h_imp h_i_imp h_p h_i_p]; [
  (* by_assumption *)
  exact (h _ h_in)
  (* Takes care of no-hypothesis introduction rules. *)
  | try (destruct (models' v p) eqn:h_vp
         ; try destruct (models' v q) eqn:h_vq; try destruct (models' v r) eqn:h_vr
         ; simpl; repeat rewrite h_vp; repeat rewrite h_vq; repeat rewrite h_vr; reflexivity)
  (* modus_ponens *)
  .. | (destruct (models' v q) eqn:h_vq; [
        reflexivity
        | simpl in h_i_imp; rewrite h_i_p, h_vq in h_i_imp; discriminate h_i_imp
       ])
].
Qed.



Section Completeness.

Section BooleanAlgebra.
Import Lattices.
Import Coq.Classes.RelationClasses (Reflexive, Transitive, PreOrder).
Context {Γ : Proposition -> Type}.

Definition provable_le p q := [Γ;; p |- q].

Definition provable_le_refl : Reflexive provable_le := @proof_refl Γ.

Definition provable_le_trans : Transitive provable_le := fun p q r proof1 proof2 =>
provable_trans (Γ := Γ ⊔ eq p) (Γ' := Γ ⊔ eq q)
    ltac:(intro_assumption; [
            proof_assumption using only assumption
          | exact proof1 ])
    proof2.

Instance : PreOrder provable_le :=
{| Coq.Classes.RelationClasses.PreOrder_Reflexive := provable_le_refl;
   Coq.Classes.RelationClasses.PreOrder_Transitive := provable_le_trans |}.

Definition LindenbaumTarksiAlgebra : BooleanAlgebra. refine {|
  preCarrier := {| le := provable_le |};

  or p q := (p '-> q) '-> q; and p q := ¬(p '-> ¬q);
  not p := ¬p; false := ⊥; true := ¬⊥;

  false_spec p := modus_ponens (exfalso p) proof_refl : [Γ;; ⊥ |- p];
  true_spec p  := id ⊥                                : [Γ;; p |- ¬⊥];

  or_spec p q r := conj
    (fun h_or => ltac:(split
        ; refine (provable_le_trans (deduction_theorem _) h_or)
        (* TPT: (Γ;; p; p '-> q |- q) and (Γ;; q; p '-> q |- q) resp. *)
        ; [ apply modus_ponens with (hyp := p) | ]; proof_assumption)
      : [Γ;; p |- r] /\ [Γ;; q |- r])
    (fun '(conj (inhabits h_p) (inhabits h_q)) => has_proof (
      ?[or_spec'] : Γ;; (p '-> q) '-> q |- r));

  and_spec p q r := conj
    (fun h_and => ltac:(split
        ; refine (provable_le_trans h_and (modus_ponens (by_contradiction _) _));
        (red_by_dt to (eq (p '-> ¬q)) by apply modus_ponens with (hyp := p '-> ¬q))
        ; [ exact (from_contradiction p (¬q)) | exact (rule_1 (¬q) p) ])
      : [Γ;; r |- p] /\ [Γ;; r |- q])
    (fun '(conj (inhabits h_p) (inhabits h_q)) => has_proof (
        ltac:(eapply (proof_mono (fun _ h => inl h)) in h_p, h_q; exact (
          deduction_theorem (modus_ponens (modus_ponens proof_refl h_p) h_q)))
        : Γ;; r |- ¬(p '-> ¬q)));

  and_not' p := modus_ponens proof_refl (absurd p ⊥) : [Γ;; ¬(p '-> ¬¬p) |- ⊥];
  or_not' p := ltac:(apply deduction_theorem;
        (red_by_dt to (eq (¬p)) by apply modus_ponens with (hyp := p));
        exact proof_refl)                            : _ |- (p '-> ¬p) '-> ¬p;

  and_distrib_or p q r := ?[and_distrib_or]
|}.

[or_spec']: {
  apply (modus_ponens (by_contradiction r)), deduction_theorem.
  assert (mt_convert : forall p' (proof : Γ;; p' |- r), Γ;; (p '-> q) '-> q; ¬r |- ¬p').
  { intros. apply proof_mono with (Γ := Γ ⊔ eq (¬r)); [
      intro_assumption; detect_assumption |
      apply deduction_theorem in proof; apply deduction_theorem_conv;
      exact (modus_ponens (modus_tollens _ r) proof) ]. }
  apply (modus_ponens (mt_convert q h_q)).
  apply modus_ponens with (hyp := p '-> q); [ proof_assumption |
  apply (modus_ponens (from_contradiction p q)); exact (mt_convert p h_p)].
}

[and_distrib_or]: {
  admit.
}
Admitted.

End BooleanAlgebra.

End Completeness.

End Main.
