Set Implicit Arguments. Unset Strict Implicit.

Require Import SetNotations. Import (notations) Coq.Init.Logic.EqNotations.

Section SomeLogic.
Context [p q : Prop].

Definition or_elim_left (h : p \/ q) (h_np : ~p) : q := match h with
| or_introl h_p => False_ind q (h_np h_p)
| or_intror h_q => h_q
end.
Definition or_elim_right (h : p \/ q) (h_nq : ~q) : p := match h with
| or_introl h_p => h_p
| or_intror h_q => False_ind p (h_nq h_q)
end.

(* sumbool as a class. *)
Existing Class sumbool.
(* From Coq.Bool Require Sumbool.
Existing Instances Sumbool.sumbool_and Sumbool.sumbool_or. *)

Instance sumbool_of_dec_left (h : p \/ q) (dec : {p}+{~p}) : {p}+{q} := match dec with
| left h_p   => left h_p
| right h_np => right (or_elim_left h h_np)
end.
Instance sumbool_of_dec_right (h : p \/ q) (dec : {q}+{~q}) : {p}+{q} := match dec with
| left h_q   => right h_q
| right h_nq => left (or_elim_right h h_nq)
end.
Instance sumbool_of_dec_either (h : p \/ q) (dec : ({p}+{~p}) + ({q}+{~q})) : {p}+{q} :=
match dec with
| inl dec_p => sumbool_of_dec_left h dec_p
| inr dec_q => sumbool_of_dec_right h dec_q
end.

(* If either side of an `or` is known to be true or false, we can eliminate to Type. *)
Section sumbool_or_elim.
Context {dec : ({p}+{~p}) + ({q}+{~q})} (h : p \/ q).

(* Unable to infer {p}+{q}: does not search for p \/ q, _ + _, as they are not typeclasses. *)

Definition dec_or_rect {dec : ({p}+{~p}) + ({q}+{~q})}
    alpha (left : p -> alpha) (right : q -> alpha) (h : p \/ q) : alpha :=
match sumbool_of_dec_either h dec with
| left h_p => left h_p
| right h_q => right h_q
end.

Definition dec_or_rect_on (h : p \/ q) {dec : ({p}+{~p}) + ({q}+{~q})}
    alpha (left : p -> alpha) (right : q -> alpha) : alpha :=
dec_or_rect (dec := dec) left right h.

End sumbool_or_elim.
End SomeLogic.

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

(* The type of proofs of a given Proposition. *)
Inductive Proof {assumptions : unary_predicate Proposition} : Proposition -> Type :=
| by_assumption p : p ∈ assumptions -> Proof p
| rule_1 p q : Proof (p '-> q '-> p)
| rule_2 p q r : Proof ((p '-> q '-> r) '-> (p '-> q) '-> (p '-> r))
| by_contradiction p : Proof (¬¬p '-> p)
| modus_ponens hyp concl : Proof hyp -> Proof (hyp '-> concl) -> Proof concl.
(* {assumptions} ensured all constructors infer it automatically.
   But we don't want the type itself to do that! *)
Arguments Proof assumptions : clear implicits.

(* Predicate expressing provability of a Proposition.

   This has just one constructor which takes only one argument, which means it
   is 'essentially the same' as Proof assumptions p.  The difference is that it
   is declared that `Provable assumptions p : Prop`, which effectively 'forgets'
   the exact proof used, so that it behaves like a proposition rather than a data
   type.*)
Definition Provable assumptions (p : Proposition) : Prop := inhabited (Proof assumptions p).

Local Notation "Γ |- p" := (Proof Γ p) (at level 75).
Local Notation "|- p" := (Proof ∅ p) (at level 75).

Local Notation "Γ , p , .. , q |- r" := (Proof ( .. (Γ ∪ eq p) .. ∪ eq q) r)
    (at level 75, q at next level). (* prevent parsing (q |- r) as a subexpression *)
Local Notation ", p , .. , q |- r" := (Proof ( .. (∅ ∪ eq p) .. ∪ eq q) r)
    (at level 75, q at next level).

(* Wrap around any |- expression to turn `Proof` into `Provable`. *)
Local Notation "[ type ]" := (inhabited type) : type_scope.

Coercion has_proof (assumptions : unary_predicate Proposition) p
    : assumptions |- p -> [assumptions |- p] := @inhabits _.

Definition inconsistent (assumptions : unary_predicate Proposition) := [assumptions |- ⊥].

Section FactsAboutProofSystem.

Section RelationBetweenDifferentAssumptions.

Section Transitivity.
Variables (Γ Γ' : unary_predicate Proposition) (h : forall [p], p ∈ Γ' -> Γ |- p).

Fixpoint proof_trans p (proof : Γ' |- p) : Γ |- p := match proof with
| by_assumption h_in'    => h h_in'
| rule_1 p q             => rule_1 p q
| rule_2 p q r           => rule_2 p q r
| by_contradiction p     => by_contradiction p
| modus_ponens proof_hyp proof_imp => modus_ponens (proof_trans proof_hyp)
                                                   (proof_trans proof_imp)
end.

(* Remark: it is not possible to derive trans' without switching to `Provable`
   instead of `Proof` or assuming some decidability, because otherwise, given
   `p ∈ Γ ∪ Γ'`, we can't tell whether p is in Γ or Γ', and that affects the
   proof of `Γ |- p` constructed. *)
Fixpoint proof_trans' {dec : forall p, ({p ∈ Γ}+{p ∉ Γ}) + ({p ∈ Γ'}+{p ∉ Γ'})}
    p (proof : Γ ∪ Γ' |- p) : Γ |- p := match proof in _ |- p return Γ |- p with
| by_assumption h_in_union   => match sumbool_of_dec_either h_in_union (dec _) with
                                | left h_in   => by_assumption h_in
                                | right h_in' => h h_in'
                                end
| rule_1 p q                 => rule_1 p q
| rule_2 p q r               => rule_2 p q r
| by_contradiction p         => by_contradiction p
| modus_ponens proof1 proof2 => modus_ponens (proof_trans' (dec := dec) proof1)
                                             (proof_trans' (dec := dec) proof2)
end.

Definition provable_trans' (h : forall [p], p ∈ Γ' -> [Γ |- p])
    p (proof : [Γ ∪ Γ' |- p]) : [Γ |- p] := let (proof) := proof in
(* Fixpoint doesn't work because we can't do structural induction on Provable,
   only on Proof. *)
(fix proof_trans' [p] (proof : Γ ∪ Γ' |- p) : [Γ |- p] :=
match proof in _ |- p return [Γ |- p] with
| by_assumption (or_introl h_in)  => by_assumption h_in
| by_assumption (or_intror h_in') => h h_in'
| rule_1 p q          => rule_1 p q
| rule_2 p q r        => rule_2 p q r
| by_contradiction p  => by_contradiction p
| modus_ponens proof1 proof2 => let (proof1') := proof_trans' proof1 in
                                let (proof2') := proof_trans' proof2 in
                                modus_ponens proof1' proof2'
end
) p proof.

End Transitivity.

Definition proof_of_proof_subset Γ Γ' (h : Γ ⊆ Γ')
    : forall p, Γ |- p -> Γ' |- p :=
proof_trans (fun _ h_in => by_assumption (h _ h_in)).

Definition provable_trans Γ Γ' (h : forall [p], p ∈ Γ' -> [Γ |- p])
    p (proof : [Γ' |- p]) : [Γ |- p] :=
provable_trans' h (let (proof) := proof in
                   proof_of_proof_subset (fun _ (h : _ ∈ Γ') => or_intror h) proof).

(* It is perhaps too verbose, but we _can_ use `proof_trans'` to show the corresponding
   result for finitely many propositions in Γ' 'directly'. *)
Check fun Γ p (proof : [Γ |- p]) => (provable_trans' (eq_ind p _ proof)
                                     : forall q, [Γ, p |- q] -> [Γ |- q]).

End RelationBetweenDifferentAssumptions.

Section SomeLemmas.
Context {Γ : unary_predicate Proposition}.

Definition proof_refl p : Γ, p |- p := by_assumption (or_intror eq_refl).

Definition id p : Γ |- (p '-> p) :=
let step_1 : Γ |- p '-> (p '-> p) '-> p         := rule_1 p (p '-> p) in
let step_2 : Γ |- p '-> p '-> p                 := rule_1 p p in
let step_3 : Γ |- (p '-> (p '-> p) '-> p) '-> (p '-> p '-> p) '-> (p '-> p)
                                                := rule_2 p (p '-> p) p in
let step_4 : Γ |- (p '-> p '-> p) '-> (p '-> p) := modus_ponens step_1 step_3 in
modus_ponens step_2 step_4.

Definition add_under_imp p q (proof : Γ |- q) : Γ |- (p '-> q) :=
let step_1 : Γ |- q '-> p '-> q := rule_1 q p in
modus_ponens proof step_1.

Definition modus_ponens_under_imp p hyp concl
    : let P' q := Γ |- (p '-> q) in   P' hyp -> P' (hyp '-> concl) -> P' concl :=
fun proof_hyp proof_imp =>
let step_1 : Γ |- (p '-> hyp '-> concl) '-> (p '-> hyp) '-> (p '-> concl) := rule_2 p hyp concl in
let step_2 := modus_ponens proof_imp step_1 in
modus_ponens proof_hyp step_2.

End SomeLemmas.

Section DeductionTheorem.
Variables (Γ : unary_predicate Proposition) (p q : Proposition).

Definition deduction_theorem (proof : [Γ, p |- q]) : [Γ |- p '-> q] :=
let (proof) := proof in
(fix deduction_theorem [q] (proof : Γ, p |- q) : [Γ |- p '-> q] :=
match proof in _ |- q return [_ |- p '-> q] with
| by_assumption (or_introl h_assum) => add_under_imp p (by_assumption h_assum)
| by_assumption (or_intror h)       => rew dependent h in id p
| rule_1 _ _                 => add_under_imp p (rule_1 (assumptions := Γ) _ _)
| rule_2 _ _ _               => add_under_imp p (rule_2 (assumptions := Γ) _ _ _)
| by_contradiction _         => add_under_imp p (by_contradiction (assumptions := Γ) _)
| modus_ponens proof1 proof2 => let (proof1') := deduction_theorem proof1 in
                                let (proof2') := deduction_theorem proof2 in
                                modus_ponens_under_imp proof1' proof2'
end) q proof.

Fixpoint deduction_theorem' {dec : forall p', ({p' ∈ Γ}+{p' ∉ Γ})+({p = p'}+{p <> p'})}
    q (proof : Γ, p |- q) : Γ |- p '-> q :=
match proof in _ |- q return Γ |- p '-> q with
| by_assumption h_in_adjoin  => match sumbool_of_dec_either h_in_adjoin (dec _) with
                                | left h  => add_under_imp p (by_assumption h)
                                | right h => rew dependent h in id p
                                end
| rule_1 _ _                 => add_under_imp p (rule_1 (assumptions := Γ) _ _)
| rule_2 _ _ _               => add_under_imp p (rule_2 (assumptions := Γ) _ _ _)
| by_contradiction _         => add_under_imp p (by_contradiction (assumptions := Γ) _)
| modus_ponens proof1 proof2 => modus_ponens_under_imp (deduction_theorem' (dec := dec) proof1)
                                                       (deduction_theorem' (dec := dec) proof2)
end.

End DeductionTheorem.

Section SomeMoreLemmas.

Definition interchange_hypotheses {Γ} p q r : Γ |- (p '-> q '-> r) '-> (q '-> p '-> r).
apply (proof_of_proof_subset (Γ := ∅) (fun p => False_ind (p ∈ Γ))).
(* To show: |- ... *)
apply (deduction_theorem' (dec := fun p => inl (right (Datatypes.id : ~False)))).
(* To show: , p '-> q '-> r |- q '-> p '-> r *)
apply modus_ponens_under_imp with (hyp := p '-> q).
+ apply rule_1.
+ apply (add_under_imp q).
  apply modus_ponens with (hyp := p '-> q '-> r).
  - apply by_assumption. exact (or_intror eq_refl).
  - apply rule_2.
Defined.

Definition modus_tollens {Γ} p q : Γ |- (p '-> q) '-> (¬q '-> ¬p).
refine (modus_ponens _ (interchange_hypotheses _ _ _)).
(* Remove the Γ. *)
apply (proof_of_proof_subset (Γ := ∅) (fun p => False_ind (p ∈ Γ))).
(* Take ¬q '-> ¬p to the assumptions. *)
apply (deduction_theorem' (dec := fun p => inl (right (Datatypes.id : ~False)))).
exact (modus_ponens (add_under_imp p (proof_refl (¬q))) (rule_2 _ _ _)).
Defined.

Definition modus_tollens_conv {Γ} p q : Γ |- (¬q '-> ¬p) '-> (p '-> q).
(* Remove the Γ. *)
apply (proof_of_proof_subset (Γ := ∅) (fun p => False_ind (p ∈ Γ))).
(* Take ¬q '-> ¬p to the assumptions. *)
apply (deduction_theorem' (dec := fun p => inl (right (Datatypes.id : ~False)))).
refine (modus_ponens_under_imp _ (add_under_imp p (by_contradiction q))).
exact (modus_ponens (proof_refl (¬q '-> ¬p)) (interchange_hypotheses (¬q) p ⊥)).
Defined.

Definition exfalso {Γ} p : Γ |- ⊥ '-> p :=
let intermediate : Γ |- ¬p '-> ¬⊥ := add_under_imp (¬p) (id ⊥) in
modus_ponens intermediate (modus_tollens_conv ⊥ p).

Definition from_contradiction {Γ} p q : Γ |- ¬p '-> p '-> q :=
modus_ponens (add_under_imp p (exfalso q)) (rule_2 p ⊥ q).

Definition absurd {Γ} p q : Γ |- p '-> ¬p '-> q :=
modus_ponens (from_contradiction p q) (interchange_hypotheses (¬p) p q).

End SomeMoreLemmas.

End FactsAboutProofSystem.

Section Soundness.

Theorem soundness_theorem (Γ : unary_predicate Proposition) p : [Γ |- p] -> Γ ⊨ p.
intros (proof) v h.
induction proof as [p h_in|p q|p q r|p|p q h_p h_i_p h_imp h_i_imp]; [
  (* by_assumption *)
  (apply h; exact h_in)
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

End Soundness.

End Main.