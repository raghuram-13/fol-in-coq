Set Implicit Arguments. Unset Strict Implicit.
 Require Import Coq.Relations.Relation_Definitions.

(* Sets *)
Import Coq.Sets.Ensembles.

(* Ensemble seems like an inappropriate name to use here. *)
Local Definition Subset := Coq.Sets.Ensembles.Ensemble.
(* Define Union in terms of or so that theorems about or can be used for it;
   and also because `Union_introl _ _ _ _ h` and `Union_intror _ _ _ _ h` are
   ridiculously verbose. *)
Local Definition Union U A B := fun x : U => In _ A x \/ In _ B x.
Local Definition Adjoin U A x := fun y : U => In _ A y \/ In _ (Singleton _ x) y.
(* WARNNING: _lower_ levels specify _higher_ precedences. *)

(* Helper:
   If either side of an `or` is known to be true or false, we can eliminate to Type. *)
Definition dec_or_rect [p q] `{dec : ({p}+{~p}) + ({q}+{~q})} 
    alpha (left : p -> alpha) (right : q -> alpha) (h : p \/ q) : alpha :=
match dec with
| inl (left h_p)               => left h_p
| inl (right h_np) => right (match h return q with
                             | or_introl h_p => False_ind _ (h_np h_p)
                             | or_intror h_q => h_q
                             end)
| inr (left h_q)             => right h_q
| inr (right h_nq) => left (match h return p with
                            | or_introl h_p => h_p
                            | or_intror h_q => False_ind _ (h_nq h_q)
                            end)
end.

Definition dec_or_rect_on p q (h : p \/ q) `{dec : ({p}+{~p}) + ({q}+{~q})}
    alpha (left : p -> alpha) (right : q -> alpha) : alpha :=
dec_or_rect (dec := dec) left right h.


Module BooleanAlgebra.

End BooleanAlgebra.


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
Local Notation "p '-> q" := (imp p q) (at level 30, right associativity).
Local Notation "¬ p" := (neg p) (at level 90).
(* Local Notation "p '/\ q" := (conj p q) (at level 80, right associativity). *)
(* Local Notation "p '\/ q" := (disj p q) (at level 80, right associativity). *)


(* Semantics *)
Definition valuation := VarIndex -> bool.

Fixpoint models' (v : valuation) (p : Proposition) : bool := match p with
| var n => v n
| ⊥ => false
| p '-> q => implb (models' v p) (models' v q)
end.

Definition models (v : valuation) (Γ : Subset Proposition) : Prop :=
forall p : Proposition, Γ p -> models' v p = true.

Definition entails (Γ : Subset Proposition) p := forall v : valuation, models v Γ -> models' v p = true.

Local Notation "Γ ⊨ p" := (entails Γ p) (at level 75).

Definition unsound (Γ : Subset Proposition) := Γ ⊨ ⊥.


(* Proofs *)

(* The type of proofs of a given Proposition. *)
Inductive Proof {assumptions : Subset Proposition} : Proposition -> Type :=
| by_assumption p : p ∈ assumptions -> Proof p
| rule_1 p q : Proof (p '-> q '-> p)
| rule_2 p q r : Proof ((p '-> q '-> r) '-> (p '-> q) '-> (p '-> r))
| by_contradiction p : Proof ((¬¬p) '-> p)
| modus_ponens hyp concl : Proof hyp -> Proof (hyp '-> concl) -> Proof concl.
(* {assumptions} ensured all constructors infer it automatically.
   But we don't want the type itself to do that! *)
Arguments Proof assumptions : clear implicits.

Structure nonempty (alpha : Type) : Prop :=
witness { _ : alpha }.
Arguments witness {alpha}.

(* Predicate expressing provability of a Proposition.

   This has just one constructor which takes only one argument, which means it
   is 'essentially the same' as Proof assumptions p.  The difference is that it
   is declared that `Provable assumptions p : Prop`, which effectively 'forgets'
   the exact proof used, so that it behaves like a proposition rather than a data
   type.*)
Definition Provable assumptions (p : Proposition) : Prop := nonempty (Proof assumptions p).

Local Notation "Γ |- p" := (Proof Γ p) (at level 75).
Local Notation "|- p" := (Proof ∅ p) (at level 75).

Local Notation "Γ , p , .. , q |- r" := (Proof (Adjoin .. (Adjoin Γ p) .. q) r)
    (at level 75, q at next level). (* prevent parsing (q |- r) as a subexpression *)
Local Notation ", p , .. , q |- r" := (Proof (Adjoin .. (Adjoin ∅ p) .. q) r)
    (at level 75, q at next level).

(* Wrap around any |- expression to turn `Proof` into `Provable`. *)
Local Notation "[ type ]" := (nonempty type) : type_scope.

Coercion has_proof (assumptions : Subset Proposition) p
    : assumptions |- p -> [assumptions |- p] := witness.

Definition inconsistent (assumptions : Subset Proposition) := [assumptions |- ⊥].

Section FactsAboutProofSystem.

Section RelationBetweenDifferentAssumptions.

Section Transitivity.
Variables (Γ Γ' : Subset Proposition) (h : forall [p], p ∈ Γ' -> Γ |- p).

Fixpoint proof_trans p (proof : Γ' |- p) : Γ |- p := match proof with
| by_assumption h_in'    => h h_in'
| rule_1 p q             => rule_1 p q
| rule_2 p q r           => rule_2 p q r
| by_contradiction p     => by_contradiction p
| modus_ponens proof_hyp proof_imp => modus_ponens (proof_trans proof_hyp) (proof_trans proof_imp)
end.

(* Remark: it is not possible to derive trans' without switching to `Provable` instead of
   `Proof` or assuming some decidability, because otherwise, given `p ∈ Γ ∪ Γ'`, we can't
   tell whether p is in Γ or Γ', and that affects the proof of `Γ |- p` constructed. *)
Fixpoint proof_trans' {dec : forall p, ({p ∈ Γ}+{p ∉ Γ}) + ({p ∈ Γ'}+{p ∉ Γ'})}
    p (proof : Γ ∪ Γ' |- p) : Γ |- p := match proof in _ |- p return Γ |- p with
| by_assumption h_in_union   => dec_or_rect_on (dec := dec _) h_in_union
                                (fun h_in : _ ∈ Γ => by_assumption h_in)
                                (fun h_in' : _ ∈ Γ' => h h_in')
| rule_1 p q                 => rule_1 p q
| rule_2 p q r               => rule_2 p q r
| by_contradiction p         => by_contradiction p
| modus_ponens proof1 proof2 => modus_ponens (proof_trans' (dec := dec) proof1)
                                             (proof_trans' (dec := dec) proof2)
end.

Definition provable_trans' (h : forall [p], p ∈ Γ' -> [Γ |- p])
    p (proof : [Γ ∪ Γ' |- p]) : [Γ |- p] := let (proof) := proof in
(* Fixpoint doesn't work because we can't do structural induction on Provable, only on Proof. *)
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

Definition proof_of_proof_subset (Γ Γ' : Subset Proposition) (h : Γ ⊆ Γ')
    : forall p, Γ |- p -> Γ' |- p :=
proof_trans (fun _ h_in => by_assumption (h _ h_in)).

(* It is perhaps too verbose, but we _can_ use `proof_trans'` to show the corresponding
   result for finitely many propositions in Γ' 'directly'. *)
Check fun Γ p (proof : [Γ |- p]) => (provable_trans' (Singleton_ind _ p _ proof)
                                     : forall q, [Γ, p |- q] -> [Γ |- q]).

End RelationBetweenDifferentAssumptions.

Section SomeLemmas.
Variables (Γ : Subset Proposition) (p q r : Proposition).

Definition id : Γ |- (p '-> p) :=
let step_1 : Γ |- p '-> (p '-> p) '-> p         := rule_1 p (p '-> p) in
let step_2 : Γ |- p '-> p '-> p                 := rule_1 p p in
let step_3 : Γ |- (p '-> (p '-> p) '-> p) '-> (p '-> p '-> p) '-> (p '-> p)
                                                := rule_2 p (p '-> p) p in
let step_4 : Γ |- (p '-> p '-> p) '-> (p '-> p) := modus_ponens step_1 step_3 in
modus_ponens step_2 step_4.

Definition add_under_imp (proof : Γ |- q) : Γ |- (p '-> q) :=
let step_1 : Γ |- q '-> p '-> q := rule_1 q p in
modus_ponens proof step_1.

Definition modus_ponens_under_imp
    : let P' q := Γ |- (p '-> q) in   P' q -> P' (q '-> r) -> P' r :=
fun proof_hyp proof_imp =>
let step_1 : Γ |- (p '-> q '-> r) '-> (p '-> q) '-> (p '-> r) := rule_2 p q r in
let step_2 := modus_ponens proof_imp step_1 in
modus_ponens proof_hyp step_2.
End SomeLemmas.
Arguments id {Γ} {p}.

Section DeductionTheorem.
Variables (Γ : Subset Proposition) (p q : Proposition).

Definition deduction_theorem (proof : [Γ, p |- q]) : [Γ |- p '-> q] :=
let (proof) := proof in
(fix deduction_theorem [q] (proof : Γ, p |- q) : [Γ |- p '-> q] :=
match proof in _ |- q return [_ |- p '-> q] with
| by_assumption (or_introl h_assum) => add_under_imp p (by_assumption h_assum)
| by_assumption (or_intror h)       => Singleton_ind _ _ (fun p' => [Γ |- p '-> p']) id _ h
| rule_1 _ _                 => add_under_imp p (rule_1 (assumptions := Γ) _ _)
| rule_2 _ _ _               => add_under_imp p (rule_2 (assumptions := Γ) _ _ _)
| by_contradiction _         => add_under_imp p (by_contradiction (assumptions := Γ) _)
| modus_ponens proof1 proof2 => let (proof1') := deduction_theorem proof1 in
                                let (proof2') := deduction_theorem proof2 in
                                modus_ponens_under_imp proof1' proof2'
end) q proof.

Fixpoint deduction_theorem' {dec : forall p', ({p' ∈ Γ}+{p' ∉ Γ})+({p = p'}+{p <> p'})}
    q (proof : Γ, p |- q) : Γ |- p '-> q :=
(* Make dec refer to membership in (Singleton _ p) *)
let dec' p' : ({p' ∈ Γ}+{p' ∉ Γ})+({p' ∈ Singleton _ p}+{p' ∉ Singleton _ p}) :=
  match dec p' with
  | inl dec => inl dec
  | inr (left h)   => inr (left (eq_ind p _ (In_singleton _ p) p' h))
  | inr (right h) => inr (right (fun h' : p' ∈ Singleton _ p =>
                                  h (Singleton_ind _ _ _ eq_refl _ h')))
  end
in
match proof in _ |- q return Γ |- p '-> q with
| by_assumption h_in_adjoin  => dec_or_rect_on (dec := dec' _) h_in_adjoin
                                (fun h : _ ∈ Γ => add_under_imp p (by_assumption h))
                                (Singleton_rect _ p (fun p' => Γ |- p '-> p') id _)
| rule_1 _ _                 => add_under_imp p (rule_1 (assumptions := Γ) _ _)
| rule_2 _ _ _               => add_under_imp p (rule_2 (assumptions := Γ) _ _ _)
| by_contradiction _         => add_under_imp p (by_contradiction (assumptions := Γ) _)
| modus_ponens proof1 proof2 => modus_ponens_under_imp (deduction_theorem' (dec := dec) proof1)
                                                       (deduction_theorem' (dec := dec) proof2)
end.

End DeductionTheorem.

End FactsAboutProofSystem.

Section Soundness.

Theorem soundness_theorem (Γ : Subset Proposition) p : [Γ |- p] -> Γ ⊨ p.
(*
(fix rec (proof : Γ |- p) v (h : models v Γ) :=
match proof in _ |- p return models' v p = true with
| by_assumption h_in         => _
| rule_1 p q                 => match models' v p, models' v q with
                                | true, true => eq_refl | true, false => eq_refl
                                | ru
| rule_2 p q r               => eq_refl
| by_contradiction p         => eq_refl
| modus_ponens proof1 proof2 => _
end) proof
*)
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