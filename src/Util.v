Require Coq.Bool.Bool.

Section Is_true.
Import Coq.Bool.Bool. Export Coq.Bool.Bool (Is_true).
Variables b b1 b2 : bool.

Lemma Is_true_iff_eq_true : Is_true b <-> b = true. split
;[ apply Is_true_eq_true | apply Is_true_eq_left ].
Qed.

Lemma Is_true_em : Is_true b \/ ~Is_true b.
destruct b; intuition. Qed.

Lemma Is_true_and : Is_true (b1 && b2) <-> Is_true b1 /\ Is_true b2. split
;[ exact (andb_prop_elim b1 b2) | exact (andb_prop_intro b1 b2) ]. Qed.

Lemma Is_true_or : Is_true (b1 || b2) <-> Is_true b1 \/ Is_true b2. split
;[ exact (orb_prop_elim b1 b2) | exact (orb_prop_intro b1 b2) ]. Qed.

Lemma Is_true_impl : Is_true (implb b1 b2) <-> (Is_true b1 -> Is_true b2).
destruct b1, b2; intuition. Qed.

End Is_true.
