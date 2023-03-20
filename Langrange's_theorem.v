Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
Require Import Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "a ∉ A" := (~In _ A a) (at level 10).
Notation "A ⊆ B" := (Included _ A B) (at level 70).
Notation "B ∩ C" := (Intersection _ B C) (at level 60, right associativity).
Notation "B ∪ C" := (Union _ B C) (at level 65, right associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).

Theorem classicT : forall P:Prop, {P} + {~P}.
Proof.
  intros. assert {x:bool | if x then P else ~P}.
  { apply constructive_indefinite_description.
    destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.

(* 映射 *)
Definition Map {U V} A B (f : U -> V) :=
  forall a, a ∈ A -> (f a) ∈ B.

(* 原象集 preimage set *)
Definition preimage_set {U V} (f : U -> V) y:= fun x => (f x) = y.

(* f是A到Ā的满射 *)
Definition Surjective {U V} A B (f : U -> V) :=
  Map A B f /\ forall y , y ∈ B -> exists x, x∈A /\ (f x) = y.

(* f是A到Ā的单射 a≠b => f(a)≠f(b) *)
Definition Injective {U V} A B (f : U -> V) :=
  Map A B f /\ forall a b, a ∈ A -> b ∈ A -> f a = f b -> a = b.

(* f是A到Ā的双射 *)
Definition Bijective {U V} A B (f : U -> V) :=
  Surjective A B f /\ Injective A B f.

(* f是A到Ā的双射 *)
Definition Bijective_ex {U V} A B  :=
  exists (f : U -> V), Surjective A B f /\ Injective A B f.

Definition pick {A} {P : A->Prop} (l :exists x, P x) :=
  proj1_sig (constructive_indefinite_description _ l).

(* 运算f在G中的封闭性 *)
Definition Closed {U:Type} (f:U->U->U) (G:Ensemble U):=
  forall a b:U, a∈G -> b∈G -> (f a b)∈G.

(* 函数f在G中封闭性 *)
Definition Closedfun {U:Type} (f:U->U) (G:Ensemble U):=
  forall x:U, x∈G -> (f x)∈G.

(* 结合律 *)
Definition associative {U:Type} (f:U->U->U) (G: Ensemble U):=
  forall x y z: U, x∈G -> y∈G -> z∈G -> f (f x y) z = f x (f y z).

(* 单位元 *)
Definition id {U:Type} f (e:U) x:=
  f e x = x /\ f x e = x.

(* 逆元 *)
Definition idinv {U:Type} (f:U->U->U) (e:U) x y:=
   f x y = e /\ f y x = e.

(*群*)
Class Group (U: Type) :={
  G: Ensemble U;
  mul: U->U->U;
  e: U;
  inv : U->U;
  closed_Gr: Closed mul G;
  assoc_Gr: associative mul G;
  e_In_G : e∈G;
  id_Gr: forall x:U, x∈G ->  id mul e x;
  closedinv_Gr : Closedfun inv G;
  invGr : forall x:U, x∈G -> idinv mul e x (inv x)
  }.
Notation "a · b" := (mul a b)(at level 10, left associativity).
Notation "x ⁻¹" := (inv x)(at level 5, left associativity).

Lemma id_l : forall {U} (GG: Group U) a, a∈G -> e·a=a.
Proof. intros. destruct (id_Gr a); auto. Qed.
Lemma id_r : forall {U} (GG: Group U) a, a∈G -> a·e=a.
Proof. intros. destruct (id_Gr a); auto. Qed.
Lemma inv_l : forall {U} (GG: Group U) a, a∈G -> a⁻¹·a=e.
Proof. intros. destruct (invGr a); auto. Qed.
Lemma inv_r : forall {U} (GG: Group U) a, a∈G -> a·a⁻¹=e.
Proof. intros. destruct (invGr a); auto. Qed.

Ltac simp :=
  repeat (rewrite -> (id_l _ _) ||
          rewrite -> (id_r _  _) ||
          rewrite -> (inv_l _ _) ||
          rewrite -> (inv_r _ _)).
Ltac simpH H:=
         (rewrite -> (id_l _ _)  in H||
          rewrite -> (id_r _  _) in H||
          rewrite -> (inv_l _ _) in H||
          rewrite -> (inv_r _ _) in H).

Class subGroup {U:Type} (Gr:Group U) :={
  H: Ensemble U;
  subsG: H⊆G;
  closed_H : Closed mul H;
  id_H: e∈H;
  closed_H_inv: Closedfun inv H
  }.
Global Hint Resolve e_In_G id_H : group.
Ltac autog :=
  match goal with
  | |- (?a · ?n) ∈ G => apply closed_Gr; autog
  | |- (?a)⁻¹∈ G => apply closedinv_Gr; autog
  | |- (?a=e·?a) => rewrite id_l; autog
  | |- (?a=?a·e) => rewrite id_r; autog
  | |- (e=?a⁻¹·?a) => rewrite inv_l; autog
  | |- (e=?a·?a⁻¹) => rewrite inv_r; autog
  | |- (e·?a=?a) => apply id_l; autog
  | |- (?a·e=?a) => apply id_r; autog
  | |- (?a⁻¹·?a=e) => apply inv_l; autog
  | |- (?a·?a⁻¹=e) => apply inv_r; autog
  | |- e∈G => apply e_In_G
  | |- e∈H => apply id_H
  | |- (?a · ?n) ∈ H => apply closed_H; autog
  | |- (?a)⁻¹∈ H => apply closed_H_inv; autog
  | _ : ?a∈ H |- (?a)∈ G => apply subsG; autog
  | |- _ => auto with group
  end.


(* Definition invariant_subgroup {U} {Gr:Group U} (SG: subGroup Gr) :=
  forall g, g∈G -> forall h, h∈G -> (g·h·g⁻¹) ∈ H. *)

(* 模H同余 *)
Definition congruent {U} {Gr:Group U} (SG: subGroup Gr) a b : Prop :=
  a∈G /\ b∈G /\ exists h, h∈H /\ a = b · h.

Definition reflexive {A:Type} (R:A->A->Prop) (G: Ensemble A):=
  forall x:A, x∈G -> R x x.
Definition transitive {A:Type} (R:A->A->Prop) (G: Ensemble A):=
  forall x y z:A, x∈G -> y∈G -> z∈G -> R x y -> R y z -> R x z.
Definition symmetric {A:Type} (R:A->A->Prop) (G: Ensemble A):=
  forall x y:A, x∈G -> y∈G -> R x y -> R y x.

Class equivalence {A:Type} (R:A->A->Prop) (G: Ensemble A): Prop :=
      { equiv_refl : reflexive R G;
        equiv_trans : transitive R G;
        equiv_sym : symmetric R G}.

Theorem equi_congruent {U} {Gr:Group U} (SG: subGroup Gr): equivalence
  (congruent SG) G.
Proof.
  split.
  - repeat split; auto. exists e. split; autog.
  - repeat split; auto. destruct H3 as [? [? [? []]]], H4 as [? [? [? []]]].
    subst. exists (x1·x0); split; autog. apply assoc_Gr; autog.
  - repeat split; auto. destruct H2 as [? [? [? []]]]. subst.
    exists x0⁻¹. split; autog. rewrite assoc_Gr; autog. simp; autog.
Qed.

(*陪集 *)
Definition coset {U} {Gr:Group U} a (SG: subGroup Gr) :Ensemble U:=
  fun x=> exists h, h∈H /\ x = a·h.
  
Theorem eq_coset_congruent : forall {U} {Gr:Group U} (SG: subGroup Gr) a,
  a∈G -> congruent SG a = coset a SG.
Proof.
  intros. apply Extensionality_Ensembles. split.
  - red; intros. destruct H1 as [? [? [? []]]]. red; red.
    subst. exists x0⁻¹. split; autog. rewrite assoc_Gr; autog. simp; autog.
  - red; intros. destruct H1 as [? []]. subst.
    repeat split; autog. exists x0⁻¹. split; autog.
    rewrite assoc_Gr; autog. simp; autog.
Qed.

(*所有陪集的集族G/H 商集*)
Definition quotient_set {U} (Gr:Group U) (SG: subGroup Gr) :Ensemble (Ensemble U):=
  fun x => exists a, a∈G /\ x = coset a SG.

(*子群是正规子群*)
Definition normal_subgroup {U} {Gr:Group U} (SG: subGroup Gr) :Prop :=
  forall g h, g∈G -> h∈H -> g·h·g⁻¹ ∈H.

(* 子群SG的陪集乘法 *)
Definition mul_coset {U} (Gr:Group U) (SG: subGroup Gr):
  Ensemble U -> Ensemble U -> Ensemble U :=
  fun x y => 
  match (classicT (x∈(quotient_set Gr SG))) with
  | left l0 => match (classicT (y∈(quotient_set Gr SG))) with
               | left l1 => coset ((pick l0)·(pick l1)) SG
               | _ => Empty_set U
               end
  | _ => Empty_set U
  end.

(* 子群SG的陪集的逆运算 *)
Definition inv_coset {U} (Gr:Group U) (SG: subGroup Gr):
  Ensemble U -> Ensemble U:= fun x=> 
  match (classicT (x∈(quotient_set Gr SG))) with
  | left l0 => coset (inv (pick l0)) SG
  | _ => Empty_set U
  end.


Fact inv_inv : forall {U} (Gr:Group U) d, d∈G -> (d ⁻¹) ⁻¹ = d.
Proof.
  intros. pose proof invGr. unfold idinv in H1.
  assert (d ⁻¹ ⁻¹· d⁻¹ = d·d⁻¹).
  { simp; autog. }
  assert (d ⁻¹ ⁻¹ · d ⁻¹ ·d = d · d ⁻¹·d). { rewrite H2; auto. }
  rewrite assoc_Gr in H3; autog. repeat (simpH H3; autog).
Qed.
Global Hint Resolve inv_inv:group.

Lemma distr_inv : forall {U} (Gr:Group U) a b,
  a∈G -> b∈G -> (a·b)⁻¹ = b⁻¹· a⁻¹.
Proof.
  intros. pose proof id_Gr. pose proof invGr. red in H2, H3.
  assert (Ha : a ⁻¹ ∈ G). { apply closedinv_Gr; auto. }
  assert (Hb : b ⁻¹ ∈ G). { apply closedinv_Gr; auto. }
  assert ((a · b) ⁻¹·(a · b) = b ⁻¹ · a ⁻¹·(a · b)).
  { destruct (H3 (a · b)). apply closed_Gr; auto.
    rewrite H5. rewrite assoc_Gr; auto.
    pattern (a ⁻¹ · (a · b)). rewrite <-assoc_Gr; auto.
    destruct (H3 a), (H3 b), (H2 b); auto. rewrite H7, H10, H9. auto.
    apply closed_Gr; auto. }
  assert ((a · b) ⁻¹ · (a · b)·(a · b) ⁻¹ = b ⁻¹ · a ⁻¹ · (a · b)·(a · b) ⁻¹).
  { rewrite H4; auto. }
  destruct (H3 (a · b)). apply closed_Gr; auto.
  rewrite H7 in H5. destruct (H2 (a · b) ⁻¹).
  apply closedinv_Gr; apply closed_Gr; auto. rewrite H8 in H5.
  assert ((a · b) ∈ G). { apply closed_Gr; auto. }
  assert ((a · b) ⁻¹∈ G). { apply closedinv_Gr; auto. }
  rewrite assoc_Gr in H5; auto. rewrite H6 in H5. rewrite H5.
  rewrite assoc_Gr; auto. f_equal. destruct (H2 (a⁻¹)); auto.
  apply e_In_G. apply closed_Gr; auto.
Qed.
Global Hint Resolve distr_inv:group.


Lemma coset_eq : forall {U} (Gr:Group U) (SG: subGroup Gr) a b, a∈G -> b∈G ->
  congruent SG a b <-> coset a SG = coset b SG.
Proof.
  split; intros.
  - destruct H2 as [? [? [? []]]]. apply Extensionality_Ensembles.
    split; red; intros.
    + destruct H6 as [? []]. red; red.
      subst. exists (x · x1). split; autog. apply assoc_Gr; autog.
    + destruct H6 as [? []]. red; red. subst.
      exists (x⁻¹·x1); split; autog. repeat rewrite <-assoc_Gr; autog.
      f_equal. rewrite assoc_Gr; autog. simp; autog.
  - pose proof eq_coset_congruent _ _ H0.
    pose proof eq_coset_congruent _ _ H1.
    rewrite H2 in H3. rewrite <-H4 in H3.
    pose proof equi_congruent _ as [].
    unfold reflexive in *. pose proof equiv_refl0 b.
    rewrite H3; auto.
Qed.

Lemma congruent_inv : forall {U} (Gr:Group U) (SG: subGroup Gr) a b,
  normal_subgroup SG ->
  a∈G -> b∈G -> congruent SG a b ->
  congruent SG a⁻¹ b⁻¹.
Proof.
  intros. repeat split. apply closedinv_Gr; auto. apply closedinv_Gr; auto.
  destruct H3 as [? [? [? []]]]. subst. pose proof subsG x H5.
  rewrite distr_inv; auto. pose proof closedinv_Gr x H6.
  pose proof closedinv_Gr _ H4.
  pose proof closed_H_inv _ H5.
  exists (b·x⁻¹·b⁻¹); split; auto.
  repeat rewrite <-assoc_Gr; auto.
  pose proof id_Gr. pose proof invGr. red in H10, H11.
  destruct (H11 b); auto. rewrite H13. destruct (H10 x ⁻¹); auto.
  rewrite H14; auto. apply closed_Gr; auto.
Qed.




Definition finite_group {U} (Gr: Group U) := Finite _ G.



Lemma empty_not_inhabited : forall {U} (A:Ensemble U),
  (Empty_set _ = A) <-> (~ Inhabited _ A).
Proof.
  split; intros.
  - intro. destruct H1. rewrite <-H0 in H1. destruct H1.
  - apply Extensionality_Ensembles; split.
    + red; intros. destruct H1.
    + red; intros. destruct H0. apply Inhabited_intro with x; auto.
Qed.

Lemma not_empty_inhabited : forall {U} (A:Ensemble U),
  ~(Empty_set _ = A) <-> Inhabited _ A.
Proof.
  split; intros.
  - destruct (classic (Inhabited U A)); auto.
    elim H0. apply Extensionality_Ensembles; split.
    + red; intros. destruct H2.
    + red; intros. destruct H1. apply Inhabited_intro with x; auto.
  - intro. destruct H0. rewrite <-H1 in H0. destruct H0.
Qed.

Lemma singlelen_set : forall {U} (a x: U), a ∈ [x] -> a = x.
Proof.
  intros. destruct H0. auto.
Qed.

Lemma eq_Add_Subtract: forall {U} (x:U) A,
  x ∈ A ->  Add U (Subtract U A x) x = A.
Proof.
  intros.
  apply Extensionality_Ensembles; split.
  - red; intros.
    destruct H1.
    + destruct H1; auto.
    + destruct H1; auto.
  - red; intros. destruct (classic (x0 ∈ [x])).
    + apply Union_intror. auto.
    + apply Union_introl. split; auto.
Qed.

Theorem bijection_card : forall n {U V} A B (f : U -> V),
  Bijective A B (f : U -> V) -> cardinal _ A n
  -> cardinal _ B n.
Proof.
  intro. induction n; intros.
  - apply cardinalO_empty in H1.
    destruct H0 as [[][]].
    destruct (classic (B=(Empty_set _))).
    + rewrite H5. constructor.
    + assert (Inhabited _ B).
      { apply not_empty_inhabited; auto. }
      destruct H6. apply H2 in H6 as [x0 []].
      rewrite H1 in H6; destruct H6.
  - assert (Inhabited _ A).
    { destruct (classic (Inhabited U A)); auto.
      apply empty_not_inhabited in H2.
      rewrite <-H2 in H1. pose proof cardinal_Empty U _ H1.
      inversion H3.
      }
    destruct H2.
    pose proof card_soustr_1 _ _ _ H1 _ H2. simpl in H3.
    assert (HSx: Bijective (Subtract U A x) (Subtract V B (f x)) f).
    { destruct H0 as [[][]].
      split.
      - split.
        + red; intros. destruct H7. split. apply H0; auto.
          intro. elim H8. apply singlelen_set in H9.
          apply H6 in H9; autog. subst; split.
        + intros. destruct H7. apply H4 in H7 as [x0 []].
          exists x0. split; auto. split; auto.
          intro. elim H8. apply singlelen_set in H10.
          subst. split.
      - split.
        + red; intros. destruct H7. split.
          apply H0; auto. intro. destruct H8.
          apply singlelen_set in H9. apply H6 in H9; autog.
          subst. split.
        + intros. apply H6; auto.
          * destruct H7; auto.
          * destruct H8; auto.
    }
    pose proof IHn _ _ _ _ _ HSx H3.
    assert (A = Add _ (Subtract U A x) x).
    { apply Extensionality_Ensembles. split.
      - red; intros. rewrite eq_Add_Subtract; auto.
      - rewrite eq_Add_Subtract; auto.
        red; intro; auto.
      }
    assert (B = Add _ (Subtract V B (f x)) (f x)).
    { apply Extensionality_Ensembles. split.
      - red; intros. rewrite eq_Add_Subtract; auto.
        apply H0; auto.
      - rewrite eq_Add_Subtract; auto.
        red; intro; auto. apply H0; auto.
      }
    rewrite H6. constructor; auto. intro.
    destruct H7. destruct H8. split.
Qed.



Definition family_union {U} (A: Ensemble (Ensemble U)) : Ensemble U:=
  fun x => exists X, x∈X /\ X∈A.

Lemma empty_family_empty : 
  forall {U}, (family_union (Empty_set (Ensemble U))) = Empty_set _.
Proof.
  intros. apply Extensionality_Ensembles; split.
  - red; intros. destruct H0 as [? [? []]].
  - red; intros. destruct H0.
Qed.

Theorem card_union : forall N {U} (A B: Ensemble U) M,
  cardinal _ A M -> cardinal _ B N ->
  A ∩ B = (Empty_set _) ->
  cardinal _ (A∪B) (N+M).
Proof.
  intro. induction N.
  - intros. simpl. apply cardinalO_empty in H1. rewrite H1.
    assert ((A ∪ Empty_set U)=A).
    { apply Extensionality_Ensembles; split.
      - red; intros. destruct H3; auto. destruct H3.
      - red; intros. apply Union_introl; auto.
      }
    rewrite H3; auto.
  - intros.
    assert (Inhabited _ B).
    { destruct (classic (Inhabited _ B)); auto.
      apply empty_not_inhabited in H3.
      rewrite <-H3 in H1. pose proof cardinal_Empty _ _ H1.
      inversion H4.
      } destruct H3 as [a ?].
    assert (cardinal _ (Subtract _ B a) N).
    { pose proof card_soustr_1 _ _ _ H1 _ H3. simpl in H4. auto. }
    assert (~a∈A). { intro. assert (a∈(A ∩ B)). split; auto.
      rewrite H2 in H6. destruct H6. }
    assert (cardinal _ (Add _ A a) (S M)).
      { apply card_add; auto. }
    assert ((Add U A a)∪(Subtract U B a)=A∪B).
      { apply Extensionality_Ensembles. split.
        - red; intros. destruct H7.
          + destruct H7. apply Union_introl; auto.
            destruct H7. apply Union_intror; auto.
          + destruct H7. apply Union_intror; auto.
        - red; intros. destruct H7.
          + apply Union_introl. apply Union_introl; auto.
          + destruct (classic (x∈[a])).
            * destruct H8. apply Union_introl.
              apply Union_intror; split.
            * apply Union_intror. split; auto.
        }
    assert ((Add U A a)∩(Subtract U B a)= (Empty_set _)).
      { apply Extensionality_Ensembles. split.
        - red; intros. destruct H8. destruct H9.
          destruct H8.
          + rewrite <- H2; split; auto.
          + tauto.
        - red; intros. destruct H8.
        } simpl.
    rewrite PeanoNat.Nat.add_comm.
    assert (((S M) + N)=(S (M + N))). { simpl. auto. }
    rewrite <- H9. rewrite PeanoNat.Nat.add_comm.
    pose proof IHN _ _ _ _ H6 H4 H8. rewrite H7 in H10.
    auto.
Qed.


Theorem family_add : forall N {U} (A:Ensemble (Ensemble U)) x M,
  cardinal _ (family_union A) M -> cardinal _ x N ->
  (forall X, X∈A -> X ∩ x = (Empty_set _)) ->
  cardinal _ (family_union (Add (Ensemble U) A x)) (N+M).
Proof.
  intro. induction N.
  - intros. simpl. pose proof cardinalO_empty _ _ H1.
    rewrite H3 in *.
    assert ((family_union A) = (family_union (Add (Ensemble U) A x))).
    { apply Extensionality_Ensembles; split.
      - red; intros. destruct H4 as [? []].
        rewrite H3. unfold family_union. exists x1. split; auto.
        apply Union_introl; auto.
      - red; intros. destruct H4 as [? []].
        red. red. unfold Add in H5. rewrite H3 in H5.
        destruct H5. eauto. destruct H5. destruct H4.
      }
    rewrite H3 in *. rewrite <-H4. auto.
  - intros. simpl. 
    assert ((family_union (Add (Ensemble U) A x) = (family_union A)∪x)).
    { apply Extensionality_Ensembles; split.
      - red; intros.
        destruct H3. destruct H3. destruct H4.
        + apply Union_introl. exists x1; auto.
        + destruct H4.
          apply Union_intror. auto.
      - red; intros. destruct H3.
        + destruct H3. destruct H3. 
          exists x1. split; auto. unfold Add.
          apply Union_introl. auto.
        + red. red. exists x.
          split; auto.
          apply Union_intror; split. }
    rewrite H3.
    assert (S (N + M) = S N + M); auto.
    rewrite H4. apply card_union; auto.
    apply Extensionality_Ensembles; split.
    + red; intros.
      destruct H5, H5, H5.
      pose proof H2 _ H7. rewrite <- H8.
      split; auto.
    + red; intros. destruct H5.
Qed.

Theorem family_card : 
  forall {U} Q (A:Ensemble (Ensemble U)) n,cardinal _ A Q ->
  (forall X, X∈A -> cardinal _ X n) ->
  (forall X Y, X∈A -> Y∈A -> X<>Y -> X ∩ Y = (Empty_set _)) ->
  cardinal _ (family_union A) (Q*n).
Proof.
  intros U Q. induction Q.
  - intros. simpl. pose proof cardinalO_empty _ _ H0.
    rewrite H3. rewrite empty_family_empty. constructor.
  - intros. assert (Inhabited _ A).
    { destruct (classic (Inhabited _ A)); auto.
      apply empty_not_inhabited in H3.
      rewrite <-H3 in H0. pose proof cardinal_Empty _ _ H0.
      inversion H4.
      } destruct H3 as [a ?].
    assert (cardinal _ (Subtract _ A a) Q).
    { pose proof card_soustr_1 _ _ _ H0 _ H3. simpl in H4. auto. }
    assert (HS1: forall X, X ∈ (Subtract _ A a) -> cardinal U X n).
    { intros. apply H1. destruct H5; auto. }
    assert (HS2: forall X Y, X ∈ (Subtract _ A a) -> Y ∈ (Subtract _ A a)
     -> X<>Y -> X ∩ Y = Empty_set _).
    { intros. apply H2; destruct H5; auto. destruct H6; auto. }
    pose proof IHQ _ _ H4 HS1 HS2.
    assert (Add _ (Subtract (Ensemble U) A a) a = A).
      { apply eq_Add_Subtract; auto. }
    simpl. rewrite <-H6.
    apply family_add; auto. intros. destruct H7.
    apply H2; auto. intro. elim H8. subst; split.
Qed.

(* 集合的阶 *)
Definition order {U} (A:Ensemble U) (FA: Finite _ A) :=
  pick (finite_cardinal _ _ FA).

Theorem eq_order : forall {U V} A B (f:U->V) (FA: Finite _ A)
  (FB: Finite _ B), Bijective A B f -> order _ FA = order _ FB.
Proof.
  intros.
  unfold order. unfold pick.
  repeat destruct constructive_indefinite_description; simpl.
  pose proof bijection_card _ _ _ _ H0 c.
  pose proof cardinal_unicity _ _ _ c0 _ H1. auto.
Qed.

(* Langrange's_theorem *)
Section Langrange's_theorem.

Context 
  {U}
  (Gr: Group U)
  (SG : subGroup Gr)
  (FG: finite_group Gr).

(* 群的阶 *)
Definition order_group :=
  order G FG.


Lemma finite_subgroup : Finite _ H. 
Proof.
  apply Finite_downward_closed with G; auto. apply subsG.
Qed.

Definition map_H_coset a := fun h => a·h.

Lemma bijective_H_coset :
  forall a, a∈G -> Bijective H (coset a SG) (map_H_coset a).
Proof.
  intros. split.
  - split.
    + red; intros. red; red. exists a0.
      split; auto.
    + intros. unfold map_H_coset.
      destruct H1 as [? []]. exists x; split; auto.
  - split.
    + red; intros. red; red. exists a0.
      split; auto.
    + intros. unfold map_H_coset in H3.
      assert (a⁻¹ ·(a · a0) = a⁻¹ ·(a · b)).
      { rewrite H3; auto. }
      rewrite <- assoc_Gr in H4; autog. simpH H4; autog.
      simpH H4; autog. rewrite <- assoc_Gr in H4; autog.
      simpH H4; autog. simpH H4; autog.
Qed.

Lemma finite_coset :
  forall a, a∈G -> Finite _ (coset a SG).
Proof.
  pose proof finite_cardinal _ _ finite_subgroup as [N CH].
  intros. pose proof bijection_card.
  pose proof H1 N _ _ _ _ _ (bijective_H_coset _ H0) CH.
  apply cardinal_finite in H2. auto.
Qed.
(* Theorem H_im_is_coset : forall a, a∈G -> 
  (Im _ _ H (map_H_coset a)) = (coset a SG).
Proof.
  intros. *)

Definition map_G_quotient :U -> Ensemble U:=
  fun a => coset a SG.

Lemma im_is_quotient_set: (Im _ _ G map_G_quotient) = (quotient_set Gr SG).
Proof.
  apply Extensionality_Ensembles; split.
  - red; intros.
    destruct H0.
    unfold map_G_quotient in H1.
    red; red.
    exists x; split; auto.
  - red; intros.
    destruct H0 as [? []].
    unfold map_G_quotient.
    pose proof Im_intro _ _ G map_G_quotient x0 H0.
    apply H2.
    unfold map_G_quotient; auto.
Qed.

Theorem finite_quotient_set :
  Finite _ (quotient_set Gr SG).
Proof.
  pose proof finite_image.
  pose proof H0 _ _ G map_G_quotient FG.
  rewrite im_is_quotient_set in H1; auto.
Qed.

Theorem quotient_set_inter_empty : 
  forall X Y, X∈(quotient_set Gr SG) -> Y∈(quotient_set Gr SG) ->
    X<>Y -> X∩Y= (Empty_set _).
Proof.
  intros. destruct H0, H0, H1, H1.
  apply Extensionality_Ensembles; split.
  - red; intros. elim H2. rewrite H3, H4.
    apply coset_eq; autog. destruct H5.
    repeat split; auto.
    rewrite H3 in H5. rewrite H4 in H6.
    destruct H5 as [? []], H6 as [? []].
    rewrite H7 in H8. assert (x · x2· x2⁻¹ = x0 · x3· x2⁻¹).
    { rewrite H8; auto. }
    rewrite assoc_Gr in H9; autog. simpH H9; autog.
    simpH H9; autog. rewrite assoc_Gr in H9; autog.
    exists (x3 · x2 ⁻¹); split; autog.
  - red; intros. destruct H5.
Qed.

Theorem family_quotient_set_eq_G :
  (family_union (quotient_set Gr SG)) = G.  
Proof.
  apply Extensionality_Ensembles; split.
  - red; intros. destruct H0 as [? []].
    destruct H1 as [? []]. rewrite H2 in H0.
    destruct H0 as [? []]. subst. autog.
  - red; intros. red; red.
    exists (coset x _); split.
    + red; red. exists e; split; autog.
    + red; red. exists x; split; auto.
Qed.

Theorem Langrange's_theorem :
  (order _ FG) = (order _ finite_quotient_set)* (order _ finite_subgroup).
Proof.
  pose proof finite_cardinal _ _ finite_quotient_set as [Q ?].
  assert ((order _ finite_quotient_set) = Q).
  { unfold order. unfold pick.
    destruct constructive_indefinite_description; simpl.
    pose proof cardinal_unicity _ _ _ H0 _ c. auto. }
  rewrite H1.
  pose proof finite_cardinal _ _ finite_subgroup as [N ?].
  assert ((order _ finite_subgroup) = N).
  { unfold order. unfold pick.
    destruct constructive_indefinite_description; simpl.
    pose proof cardinal_unicity _ _ _ H2 _ c.
    auto. }
  rewrite H3.
  assert (forall a (ag: a∈G),N = order (coset a SG) (finite_coset _ ag) ).
  { intros. rewrite <- H3.
    apply eq_order with (map_H_coset a). apply bijective_H_coset; auto. }
  assert (forall A, A∈(quotient_set Gr SG) -> cardinal _ A N).
  { intros. destruct H5. destruct H5. pose proof H4 _ H5.
    unfold order in H7. unfold pick in H7.
    destruct constructive_indefinite_description in H7. simpl in H7.
    subst; auto. }  
  pose proof family_card _ _ _ H0 H5 quotient_set_inter_empty.
  rewrite family_quotient_set_eq_G in H6.
  unfold order. unfold pick.
  destruct constructive_indefinite_description; simpl.
  pose proof cardinal_is_functional _ _ _ c _  _ H6.
  apply H7; auto.
Qed.
 
  
  





