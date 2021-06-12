From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section seq_eqType.

Variable T1 : eqType.

Lemma sorted_trans (leT1 leT2 : rel T1) s :
  {in s &, (forall x y, leT1 x y -> leT2 x y)} ->
  sorted leT1 s -> sorted leT2 s.
Proof.
elim: s=> // a [] //= b l IHl leT12 /andP [leT1ab pleT1].
rewrite leT12 ?inE ?eqxx ?orbT // IHl // => x y xbcl ybcl leT1xy.
  by rewrite leT12 // mem_behead.
Qed.


End seq_eqType.

Section FinType.

Lemma enum_ord_enum n : enum 'I_n = ord_enum n.
Proof. by rewrite enumT unlock. Qed.

End FinType.


Section Finfun.

Variables (aT : finType) (rT : eqType).
Variables (f g : aT -> rT).
Variable (P : pred aT).
Hypothesis (Hf : injective f) (Hg : injective g).

Lemma uniq_image (h : aT -> rT):
  injective h -> uniq (image h P).
Proof. by move/map_inj_uniq=> ->; rewrite enum_uniq. Qed.

Lemma perm_eq_image :  {subset (image f P) <= (image g P)} ->
  perm_eq (image f P) (image g P).
Proof.
move=> imfsubimg.
rewrite uniq_perm_eq // ?uniq_image //.
have []:= (leq_size_perm (uniq_image Hf) imfsubimg)=> //.
by rewrite !size_map.
Qed.

End Finfun.

Section BigOp.

Variables (T : Type) (idx : T) (op : Monoid.com_law idx).

Lemma sumn_big s : sumn s = (\sum_(i <- s) i)%N.
Proof.
elim: s=> /= [|a l ->]; first by rewrite big_nil.
by rewrite big_cons.
Qed.
(***Not in bigop.v and I not found a short way to prove this. ****)
Lemma big_lift_ord n F j :
  \big[op/idx]_( i < n.+1 | j != i ) F i = \big[op/idx]_i F (lift j i).
Proof.
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [k /unlift_some[i] | i _]; have:= n0 i.
rewrite (reindex (lift j)).
  by apply: eq_bigl=> k; rewrite neq_lift.
exists (fun k => odflt k0 (unlift j k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

Variable R : idomainType.
Open Scope ring_scope.

Lemma lead_coef_prod (s : seq {poly R}) :
  \prod_(p <- s) lead_coef p = lead_coef (\prod_(p <- s) p).
Proof.
elim: s=> [|a l IHl]; first by rewrite !big_nil lead_coef1.
by rewrite !big_cons lead_coefM -IHl.
Qed.

Import GRing.Theory.

Lemma monic_leadVMp (p : {poly R}) : (lead_coef p) \is a GRing.unit ->
  ((lead_coef p)^-1 *: p) \is monic.
Proof. by move=> *; apply/monicP; rewrite lead_coefZ mulVr. Qed.

End BigOp.

Section Matrix.
Import GRing.Theory.
Local Open Scope ring_scope.


Section matrix_Type.

Variable T : Type.
(**** This lemma is useful to rewrite in a big expression, and it is unsightly
to do a "have" in a proof for proving that. *********)
Lemma matrix_comp k l m n (E : 'I_k -> 'I_l -> T) (F : 'I_n -> 'I_k) G :
  \matrix_(i < n, j < m) ((\matrix_(i0 < k, j0 < l) E i0 j0) (F i) (G j)) =
  \matrix_(i, j) (E (F i) (G j)).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End matrix_Type.
End Matrix.
