From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
