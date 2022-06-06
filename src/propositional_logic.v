Set Implicit Arguments.

Require Import SetNotations. Import (notations) Coq.Init.Logic.EqNotations.
Require Lattices.

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
| by_assumption [p] : assumptions p -> Proof p
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
Local Notation "; p |- q" := (Proof (eq p) q) (at level 75) : proof_scope.

Local Notation "Γ , p , .. , q |- r" := (Proof ( .. (Γ ⊔ eq p) .. ⊔ eq q) r)
    (* prevent parsing (q |- r) as a subexpression *)
    (at level 75, q at next level) : proof_scope.
Local Notation "; p0 , p , .. , q |- r" := (Proof ( .. (eq p0 ⊔ eq p) .. ⊔ eq q) r)
    (at level 75, q at next level) : proof_scope.

(* Wrap around any |- expression to turn `Proof` into `Provable`. *)
Local Notation "[ proof ]" := (inhabited proof%proof) : type_scope.

Open Scope proof_scope.


Coercion has_proof (assumptions : Proposition -> Type) p
    : assumptions |- p -> [assumptions |- p] := @inhabits _.

Definition inconsistent (assumptions : Proposition -> Type) := [assumptions |- ⊥].

Ltac proof_assumption := match goal with
| [ |- [_ |- _] ] => apply has_proof; proof_assumption
| [ |- ?Γ |- ?p ] => apply by_assumption; repeat constructor; (reflexivity + assumption)
(* | [ |- _ ] => tryif progress simpl then proof_assumption else fail 1 *)
end.

(* Convenience function written on the fly for checking the size of proofs. *)
Fixpoint size {Γ} {p} (proof : Γ |- p) : nat := match proof with
| modus_ponens proof1 proof2 => 1 + (size proof1) + (size proof2)
| _ => 1
end.

Section FactsAboutProofSystem.

Section RelationBetweenDifferentAssumptions.
Implicit Type (Γ : Proposition -> Type).

Section Transitivity.

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
proof_trans (fun p (h' : Γ p + Γ' p) => match h' with
             | inl h_in  => by_assumption h_in
             | inr h_in' => h h_in'
            end).

Definition proof_mono [Γ Γ'] (h : forall [p], Γ p -> Γ' p)
    : forall [p], Γ |- p -> Γ' |- p :=
proof_trans (fun p (h' : Γ p) => by_assumption (h h')).

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
 | modus_ponens proof1 proof2 => let (proof1') := proof_trans' proof1 in
                                 let (proof2') := proof_trans' proof2 in
                                 modus_ponens proof1' proof2'
 end) p proof.

Definition provable_trans Γ Γ' (h : forall [p], Γ' p -> [Γ |- p])
    p (proof : [Γ' |- p]) : [Γ |- p] :=
provable_trans' h (let (proof) := proof in
                   proof_mono (fun p (h : Γ' p) => inr h : (Γ ⊔ Γ') p) proof).

Section test.
(* It is slightly verbose, but we _can_ show these results for appending a
   few propositions to Γ using `proof_trans'`/`provable_trans'` reasonably. *)
Check fun Γ p (proof : Γ |- p) =>
  proof_trans' (eq_rect p _ proof) : forall q, Γ, p |- q -> Γ |- q.
Check fun Γ p q
        (proof1 : Γ |- p) (proof2 : Γ, p |- q) =>
  (fun r proof3 =>
    proof_trans' (eq_rect p _ proof1) (
    proof_trans' (eq_rect q _ proof2)
    proof3))
  : forall r, Γ, p, q |- r -> Γ |- r.
Check fun Γ p q
        (proof1 : Γ |- p) (proof2 : [Γ, p |- q]) =>
  (fun r proof3 =>
    let (proof_intermediate) := provable_trans' (eq_rect q _ proof2) proof3 in
    proof_trans' (eq_rect p _ proof1) proof_intermediate)
  : forall r, [Γ, p, q |- r] -> [Γ |- r].
End test.

End Transitivity.


End RelationBetweenDifferentAssumptions.

Section SomeLemmas.
Context {Γ : Proposition -> Type}.

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
    : let P' q := Γ |- (p '-> q) in   P' (hyp '-> concl) -> P' hyp -> P' concl :=
fun proof_imp proof_hyp =>
let step_1 : Γ |- (p '-> hyp '-> concl) '-> (p '-> hyp) '-> (p '-> concl) := rule_2 p hyp concl in
let step_2 := modus_ponens step_1 proof_imp in
modus_ponens step_2 proof_hyp.

End SomeLemmas.

Fixpoint deduction_theorem {Γ} {hyp} [concl] (proof : Γ, hyp |- concl)
    : Γ |- hyp '-> concl := match proof with
| by_assumption (inl h)      => add_under_imp hyp (by_assumption h)
| by_assumption (inr h)      => rew dependent h in id hyp
| rule_1 _ _                 => add_under_imp hyp (rule_1 _ _)
| rule_2 _ _ _               => add_under_imp hyp (rule_2 _ _ _)
| by_contradiction _         => add_under_imp hyp (by_contradiction (assumptions := Γ) _)
| modus_ponens proof1 proof2 => modus_ponens_under_imp (deduction_theorem proof1)
                                                       (deduction_theorem proof2)
end.

Section SomeMoreLemmas.

(* The deduction theorem can be easily used practically.
   However, note that the the proof objects produced are very large - for
   example, this proof has 161 'nodes' in its proof tree whereas a previous
   version that used the deduction theorem only once due to inconvenience of
   using it at that time only had 29 'nodes'. *)
Definition interchange_hypotheses {Γ} p q r : Γ |- (p '-> q '-> r) '-> (q '-> p '-> r).
do 3 apply deduction_theorem.
(* To show: ; p '-> q '-> r, q, p |- r *)
apply modus_ponens with (hyp := q). apply modus_ponens with (hyp := p).
par:proof_assumption.
Defined.

Definition modus_tollens {Γ} p q : Γ |- (p '-> q) '-> (¬q '-> ¬p).
(* Take ¬q to the assumptions. *)
apply (modus_ponens (interchange_hypotheses _ _ _)), deduction_theorem.
apply (modus_ponens (rule_2 _ _ _)), (add_under_imp p).
proof_assumption.
Defined.

Definition modus_tollens_conv {Γ} p q : Γ |- (¬q '-> ¬p) '-> (p '-> q).
apply deduction_theorem.
apply (modus_ponens_under_imp (add_under_imp p (by_contradiction q))).
apply (modus_ponens (interchange_hypotheses (¬q) p ⊥)).
proof_assumption.
Defined.

Definition exfalso {Γ} p : Γ |- ⊥ '-> p :=
deduction_theorem (
modus_ponens (by_contradiction p) (
add_under_imp (¬p) (ltac:(proof_assumption) : Γ, ⊥ |- ⊥))).

Definition from_contradiction {Γ} p q : Γ |- ¬p '-> p '-> q :=
modus_ponens (rule_2 p ⊥ q) (add_under_imp p (exfalso q)).

Definition absurd {Γ} p q : Γ |- p '-> ¬p '-> q :=
modus_ponens (interchange_hypotheses (¬p) p q) (from_contradiction p q).

End SomeMoreLemmas.

End FactsAboutProofSystem.

Section Soundness.

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

End Soundness.

Section Completeness.

Section BooleanAlgebra.
Import Lattices.
Import Coq.Classes.RelationClasses (Reflexive, Transitive, PreOrder).
Context {Γ : Proposition -> Type}.

Definition provable_le p q := [Γ, p |- q].

Definition provable_le_refl : Reflexive provable_le := fun _ =>
ltac:(unfold provable_le; proof_assumption).

Definition provable_le_trans : Transitive provable_le :=
fun p q r proof1 proof2 =>
(* provable_trans' (fun q' (h : (Γ ⊔ eq q) q') => match h with
                | inl h => ltac:(proof_assumption) : Γ, p |- q'
                | inr h => rew h in proof1
                end)
    (let (proof2) := proof2 in
      proof_mono ((fun _ h => inr h) (* : Γ ⊔ eq q ⊆' (Γ ⊔ eq p) ⊔ (Γ ⊔ eq q) *))
          proof2) *)
provable_trans (fun q' (h : (Γ ⊔ eq q) q') => match h with
                | inl h => ltac:(proof_assumption) : Γ, p |- q'
                | inr h => rew h in proof1
                end) proof2.

Instance : PreOrder provable_le :=
{| Coq.Classes.RelationClasses.PreOrder_Reflexive := provable_le_refl;
   Coq.Classes.RelationClasses.PreOrder_Transitive := provable_le_trans |}.

Definition LindenbaumTarksiAlgebra := {|
  preCarrier := {| le := provable_le |};

  or p q := ¬p '-> q; and p q := ¬(p '-> ¬q);
  or_spec p q r := conj
    (fun h_or => conj
      (provable_le_trans (modus_ponens (absurd p q) (ltac:(proof_assumption) : _, p |- p)) h_or)
      (provable_le_trans (add_under_imp (¬p) (ltac:(proof_assumption) : _, q |- q)) h_or))
    (fun '(conj (inhabits h_p) (inhabits h_q)) => has_proof (
      modus_ponens (by_contradiction r) (
      let mt_transform [p'] (proof : Γ, p' |- r) : Γ, ¬p '-> q, ¬r |- ¬p' :=
          modus_ponens (modus_ponens (modus_tollens p' r)
            (proof_mono (fun _ h => inl (inl h))
              (deduction_theorem proof)))
            (ltac:(proof_assumption) : _, ¬r |- ¬r) in
      deduction_theorem (modus_ponens (mt_transform h_q) (
      modus_ponens (ltac:(proof_assumption) : Γ, ¬p '-> q, ¬r |- ¬p '-> q)
                   (mt_transform h_p))))));
  (* and_spec := _; *)
  (* and_distrib_or := _; *)

  false := ⊥; true := ¬⊥;
  false_spec p := modus_ponens (exfalso p) (ltac:(proof_assumption) : Γ, ⊥ |- ⊥);
  true_spec p := id ⊥;

  not p := ¬p; or_not' p := id (¬p);
  (* and_not' p := _ *)
|}.

End BooleanAlgebra.

End Completeness.

End Main.
