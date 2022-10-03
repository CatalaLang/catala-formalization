Require Import Coq.Setoids.Setoid.
Require Import MyTactics.
Require Import MySequences.

(* This file offers a few definitions and tactics that help deal with
   relations and commutative diagrams. *)

(* -------------------------------------------------------------------------- *)

Section Relations.

Context {A : Type}.

Implicit Types R S : A -> A -> Prop.

(* Composition of relations. *)

Definition composition R S a c :=
  exists b, R a b /\ S b c.

(* Transposition of relations. *)

Definition transpose R a b :=
  R b a.

(* Inclusion of relations. *)

Definition inclusion R S :=
  forall a b, R a b -> S a b.

(* A typical (square) commutative diagram, where the composition [R; S] can be
   replaced with the composition [S; R]. This notion can be stated in several
   equivalent ways; see [commutation22_eq] and [commutation22_reverse]. *)

Definition commutation22 R S S' R' :=
  forall a1 b1,
  R a1 b1 ->
  forall b2,
  S b1 b2 ->
  exists a2,
  S' a1 a2 /\ R' a2 b2.

(* A typical diamond diagram, where a divergence [R | S] is resolved
   via [S' | R']. *)

Definition diamond22 R S R' S' :=
  forall a1 b1,
  R a1 b1 ->
  forall a2,
  S a1 a2 ->
  exists b2,
  R' a2 b2 /\ S' b1 b2.

Definition diamond R :=
  diamond22 R R R R.

End Relations.

(* -------------------------------------------------------------------------- *)

(* The tactic [forward1 lemma] applies [lemma], forwards, to a hypothesis
   found in the context. The lemma must have one hypothesis. *)

Ltac forward1 lemma :=
  match type of lemma with
  | (forall _ _, ?R _ _ -> _) =>
      match goal with hR: R ?a1 ?b1 |- _ =>
        generalize (lemma _ _ hR); intro
      end
  | (forall _, ?R _ _ -> _) =>
      match goal with hR: R ?a1 ?b1 |- _ =>
        generalize (lemma _ hR); intro
      end
  end;
  unpack.

(* The tactic [forward2 lemma] applies [lemma], forwards, to two hypotheses
   found in the context. The lemma must be a commutation lemma or a diamond
   lemma, as defined above. *)

Ltac forward2 lemma :=
  match type of lemma with
  | (forall a1 b1, ?R a1 b1 -> forall b2, ?S b1 b2 -> _) =>
      match goal with hR: R ?a1 ?b1, hS: S ?b1 ?b2 |- _ =>
        generalize (lemma _ _ hR _ hS); intro
      end
  | commutation22 ?R ?S _ _ =>
      match goal with hR: R ?a1 ?b1, hS: S ?b1 ?b2 |- _ =>
        generalize (lemma _ _ hR _ hS); intro
      end
  | (forall a1 b1, ?R a1 b1 -> forall a2, ?S a1 a2 -> _) =>
      match goal with hR: R ?a1 ?b1, hS: S ?a1 ?a2 |- _ =>
        generalize (lemma _ _ hR _ hS); intro
      end
  | diamond22 ?R ?S _ _ =>
      match goal with hR: R ?a1 ?b1, hS: S ?a1 ?a2 |- _ =>
        generalize (lemma _ _ hR _ hS); intro
      end
  | diamond ?R =>
      match goal with hR: R ?a1 ?b1, hS: R ?a1 ?a2 |- _ =>
        generalize (lemma _ _ hR _ hS); intro
      end
  end;
  unpack.

(* -------------------------------------------------------------------------- *)

Section RelationLemmas.

Context {A : Type}.

Implicit Types R S : A -> A -> Prop.

(* Inclusion of relations is transitive. *)

Lemma inclusion_transitive:
  forall R S T,
  inclusion R S ->
  inclusion S T ->
  inclusion R T.
Proof.
  unfold inclusion. eauto.
Qed.

(* [star] is covariant with respect to inclusion. *)

Lemma star_covariant_inclusion:
  forall R S,
  inclusion R S ->
  inclusion (star R) (star S).
Proof.
  unfold inclusion. eauto using star_covariant.
Qed.

(* If [R] is reflexive and transitive, then [star R] is [R]. *)

Lemma star_of_reflexive_transitive_relation:
  forall {A} (R : A -> A -> Prop),
  (forall a, R a a) ->
  (forall a b c, R a b -> R b c -> R a c) ->
  inclusion (star R) R.
Proof.
  intros. induction 1; eauto.
Qed.

(* Thus, [star (star R)] is [star R]. *)

Lemma inclusion_star_star:
  forall {A} (R : A -> A -> Prop),
  inclusion (star (star R)) (star R).
Proof.
  intros.
  eapply star_of_reflexive_transitive_relation; eauto with sequences.
Qed.

(* Composition is associative. *)

Lemma composition_assoc_direct:
  forall R S T,
  inclusion
    (composition R (composition S T))
    (composition (composition R S) T).
Proof.
  unfold inclusion, composition. intros. unpack. eauto.
Qed.

Lemma composition_assoc_reverse:
  forall R S T,
  inclusion
    (composition (composition R S) T)
    (composition R (composition S T)).
Proof.
  unfold inclusion, composition. intros. unpack. eauto.
Qed.

(* Composition is covariant. *)

Lemma composition_covariant:
  forall R1 R2 S1 S2,
  inclusion R1 R2 ->
  inclusion S1 S2 ->
  inclusion (composition R1 S1) (composition R2 S2).
Proof.
  unfold inclusion, composition. intros. unpack. eauto.
Qed.

(* A commutative diagram can be stated in terms of inclusion of relations. *)

Lemma commutation22_eq:
  forall R S S' R',
  commutation22 R S S' R' <->
  inclusion (composition R S) (composition S' R').
Proof.
  intros. unfold commutation22, inclusion, composition.
  split; intros; unpack.
  { forward2 H. eauto. }
  { eauto. }
Qed.

(* Thus, two commutative diagrams can be glued. *)

Lemma commutation22_transitive:
  forall R S S' R' S'' R'',
  commutation22 R S S' R' ->
  commutation22 S' R' S'' R'' ->
  commutation22 R S S'' R''.
Proof.
  intros. rewrite !commutation22_eq in *.
  eauto using inclusion_transitive.
Qed.

(* A commutation diagram can also be stated with its two hypotheses in reverse
   order. This can be useful, e.g. when the diagram must be established by
   induction on the second hypothesis. *)

Lemma commutation22_reverse:
  forall R S S' R',
  commutation22 R S S' R' <->
  (
    forall b1 b2,
    S b1 b2 ->
    forall a1,
    R a1 b1 ->
    exists a2,
    S' a1 a2 /\ R' a2 b2
  ).
Proof.
  unfold commutation22. split; eauto.
Qed.

(* [commutation22 R S S' R'] is contravariant in [R] and [S] and
   covariant in [S'] and [R']. *)

Lemma commutation22_variance:
  forall R1 S1 S'1 R'1 R2 S2 S'2 R'2,
  commutation22 R1 S1 S'1 R'1 ->
  (forall a b, R2 a b -> R1 a b) ->
  (forall a b, S2 a b -> S1 a b) ->
  (forall a b, S'1 a b -> S'2 a b) ->
  (forall a b, R'1 a b -> R'2 a b) ->
  commutation22 R2 S2 S'2 R'2.
Proof.
  do 8 intro. intros Hcomm. do 4 intro. intros a1 b1 ? b2 ?.
  assert (R1 a1 b1). { eauto. }
  assert (S1 b1 b2). { eauto. }
  forward2 Hcomm. eauto.
Qed.

(* If [S] can move left through [R], giving rise to (zero or more) [S'],
   then [star S] can move left through [R] in the same manner. Think of
   many [S] sheep jumping right-to-left above one [R] barrier. *)

(* If   [R S ] rewrites to [S'* R]
   then [R S*] rewrites to [S'* R]. *)

(* If desired, [star S'] could be replaced in this statement with any
   reflexive and transitive relation. *)

Lemma commute_R_Sstar:
  forall {R S S'},
  commutation22
    R         S
    (star S') R
  ->
  commutation22
    R  (star S)
    (star S') R.
Proof.
  intros ? ? ? Hdiagram.
  rewrite commutation22_reverse.
  induction 1; intros.
  { eauto with sequences. }
  { forward2 Hdiagram.
    forward1 IHstar.
    eauto with sequences. }
Qed.

(* An analogous result, with [plus] instead of [star]. *)

(* If   [R S ] rewrites to [S'+ R]
   then [R S+] rewrites to [S'+ R]. *)

(* If desired, [plus S'] could be replaced in this statement with any
   transitive relation. *)

Lemma commute_R_Splus:
  forall {R S S'},
  commutation22
    R         S
    (plus S') R
  ->
  commutation22
    R  (plus S)
    (plus S') R.
Proof.
  intros ? ? ? Hcomm.
  rewrite commutation22_reverse.
  induction 1 using plus_ind_direct; intros.
  (* Case: one step. *)
  { forward2 Hcomm. eauto. }
  (* Case: more than one step. *)
  { forward2 Hcomm.
    forward1 IHplus.
    eauto with sequences. }
Qed.

(* If [S] can move left through [R], giving rise to (zero or more) [S],
   then [S] can move left through [star R]. Think of many [S] sheep jumping
   right-to-left above many [R] barriers. *)

(* If   [R  S ] rewrites to [S* R ]
   then [R* S*] rewrites to [S* R*]. *)

Lemma commute_Rstar_Sstar:
  forall {R S},
  commutation22
    R        S
    (star S) R
  ->
  commutation22
    (star R) (star S)
    (star S) (star R).
Proof.
  intros ? ? Hdiagram.
  induction 1; intros.
  { eauto with sequences. }
  { forward1 IHstar.
    forward2 (commute_R_Sstar Hdiagram).
    eauto with sequences. }
Qed.

(* If   [R  S] rewrites to [S+ R ]
   then [R* S] rewrites to [S+ R*]. *)

Lemma commute_Rstar_S:
  forall {R S},
  commutation22
    R        S
    (plus S) R
  ->
  commutation22
    (star R)       S
    (plus S) (star R).
Proof.
  intros ? ? Hdiagram.
  induction 1; intros.
  { eauto with sequences. }
  { forward1 IHstar.
    forward2 (commute_R_Splus Hdiagram).
    eauto with sequences. }
Qed.

(* If   [R  S ] rewrites to [S+ R ]
   then [R* S+] rewrites to [S+ R*]. *)

Lemma commute_Rstar_Splus:
  forall {R S},
  commutation22
    R        S
    (plus S) R
  ->
  commutation22
    (star R) (plus S)
    (plus S) (star R).
Proof.
  intros ? ? Hdiagram.
  assert (Hdiagram2:
    commutation22
      (star R) (star S)
      (star S) (star R)
  ).
  { eapply commute_Rstar_Sstar.
    eauto using commutation22_variance with sequences. }
  (* We have [R* S+]. *)
  induction 2; intros.
  (* We have [R* S S*]. *)
  forward2 (commute_Rstar_S Hdiagram).
  (* We have [S+ R* S*]. *)
  forward2 Hdiagram2.
  (* We have [S+ S* R*]. *)
  eauto with sequences.
Qed.

(* [transpose] is involutive. *)

Lemma transpose_transpose:
  forall R,
  transpose (transpose R) = R.
Proof.
  reflexivity. (* it's just eta-expansion *)
Qed.

(* [diamond22] can be viewed as an instance of [commutation22]. *)

Lemma diamond22_as_commutation22:
  forall R S R' S',
  diamond22 R S R' S' <->
  commutation22 (transpose R) S S' (transpose R').
Proof.
  unfold diamond22, commutation22. split; intros H; intros.
  { unfold transpose in *. forward2 H. eauto. }
  { assert (transpose R b1 a1). { eauto. }
    forward2 H. eauto. }
Qed.

Lemma commutation22_as_diamond22:
  forall R S R' S',
  commutation22 R S S' R' <->
  diamond22 (transpose R) S (transpose R') S'.
Proof.
  intros.
  rewrite diamond22_as_commutation22.
  rewrite !transpose_transpose. tauto.
Qed.

(* [diamond22 is symmetric. *)

Lemma diamond22_symmetric:
  forall R S R' S',
  diamond22 R S R' S' ->
  diamond22 S R S' R'.
Proof.
  intros ? ? ? ? Hcon.
  unfold diamond22. intros.
  forward2 Hcon. eauto.
Qed.

(* If [R] is diamond, then [star R] is diamond. *)

Lemma star_diamond_left:
  forall R R' S,
  diamond22 R S R' S ->
  diamond22 (star R) S (star R') S.
Proof.
  intros R R' S Hcon. induction 1; intros.
  { eauto with sequences. }
  { forward2 Hcon. forward1 IHstar. eauto with sequences. }
Qed.

Lemma star_diamond_right:
  forall R S S',
  diamond22 R S R S' ->
  diamond22 R (star S) R (star S').
Proof.
  eauto using star_diamond_left, diamond22_symmetric.
Qed.

Lemma star_diamond_both:
  forall R S,
  diamond22 R S R S ->
  diamond22 (star R) (star S) (star R) (star S).
Proof.
  eauto using star_diamond_left, star_diamond_right.
Qed.

Lemma star_diamond:
  forall R,
  diamond R ->
  diamond (star R).
Proof.
  unfold diamond. eauto using star_diamond_both.
Qed.

(* If, through a simulation diagram, a step of [R] in the source is
   translated to (at least) one step of [R'] in the target, then
   divergence in the source implies divergence in the target. *)

Lemma infseq_simulation:
  forall R R' S,
  diamond22 R S R' S ->
  forall a,
  infseq R a ->
  forall b,
  S a b ->
  infseq R' b.
Proof.
  intros.
  eapply infseq_coinduction_principle
    with (P := fun b => exists a, S a b /\ infseq R a); [| eauto ].
  clear dependent a. clear b. intros b (a&?&?).
  pick infseq invert.
  pick @diamond22 forward2.
  eauto with sequences.
Qed.

Lemma infseq_simulation_plus:
  forall R R' S,
  diamond22 R S (plus R') S ->
  forall a,
  infseq R a ->
  forall b,
  S a b ->
  infseq R' b.
Proof.
  eauto using infseq_simulation, infseq_plus.
Qed.

End RelationLemmas.
