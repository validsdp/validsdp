(** * Bounds on the rounding error of dotproduct $c - \sum_{i=0}^k a_i b_i$#c - \sum_{i=0}^k a_i b_i#

    Notations are similar to the one in [fsum]. *)

Require Import Reals Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun ssralg bigop.

Require Import binary64_infnan.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum.
Require Import binary64_infnan.

Require Import ZArith.
Require Import Fcore Fappli_IEEE Fappli_IEEE_bits.

(* Slow!

Definition fhalf : full_float :=
  F754_finite false 1 (-1).
Print valid_binary.
Definition bhalf : binary64 :=
  (* FF2B 53 1024 fhalf (refl_equal true). *)
  binary_normalize 53 1024 (refl_equal Lt) (refl_equal Lt) mode_NE 1 (-1) false.
Compute b64_mult mode_NE bhalf bhalf.
*)

Definition b64_normalize (f : float radix2) :=
  binary_normalize 53 1024 (refl_equal Lt) (refl_equal Lt) mode_NE (Fnum f) (Fexp f) false.

Definition B2F {p emax} (x : binary_float p emax) : float radix2 :=
  match x with
  | B754_finite s m e _ => Float radix2 (cond_Zopp s (Zpos m)) e
  | _ => Float radix2 0 0
  end.

Definition Z2B (n : Z) := b64_normalize (Float radix2 n 0).

(*
Definition b64_finite_pos {p emax} (x : binary_float p emax) : bool :=
  match x with
  | B754_finite s m e _ =>
  | _ => false
  end.
*)

Require Import Fcalc_ops.

Definition half := b64_normalize (Float radix2 1 (-1)).
Definition one := b64_plus mode_NE half half.
Time Eval vm_compute in B2F one.

Time Eval vm_compute in B2F (fisqrt (Z2B 4)).

Time Eval vm_compute in is_finite _ _ (b64_normalize (Float radix2 1 4096)).

Time Eval vm_compute in is_nan _ _ (fisqrt (b64_normalize (Float radix2 (-1) 0))).

Definition F64 := binary64_infnan.

Require Import matrix seqmatrix refinements.

Section seq_cholesky.

Fixpoint seq_stilde k c a b :=
  match k, a, b with
    | O, _, _ => c
    | S k, [::], _ => c
    | S k, _, [::] => c
    | S k, a1 :: a2, b1 :: b2 => seq_stilde k (fiplus c (fiopp (fimult a1 b1))) a2 b2
  end.

Definition seq_ytilded k c a b bk := fidiv (seq_stilde k c a b) bk.

Definition seq_ytildes k c a := fisqrt (seq_stilde k c a a).

Fixpoint seq_store T s n (v : T) :=
  match n, s with
    | _, [::] => [::]
    | O, _ :: t => v :: t
    | S n, h :: t => h :: seq_store t n v
  end.

Fixpoint store T m i j (v : T) :=
  match i, m with
    | _, [::] => [::]
    | O, h :: t => seq_store h j v :: t
    | S i, h :: t => h :: store t i j v
  end.

Definition m_id := [:: [:: one; FI0]; [:: FI0; one]].
Definition m_0 := [:: [:: FI0; FI0]; [:: FI0; FI0]].

Time Eval vm_compute in map (map B2F) (store m_id 0 1 half).

Require Import Recdef.

(* note: R is transposed with respect to cholesky.v *)
Section InnerLoop.
Variable j : nat.
Function inner_loop A R (i : nat)
         {measure (fun i => (j - i)%N) i} :=
  if (i < j)%N then
    let R := store R j i (seq_ytilded i (nth FI0 (nth [::] A i) j)
                                      (nth [::] R i) (nth [::] R j)
                                      (nth FI0 (nth [::] R i) i)) in
    inner_loop A R (i + 1)
  else
    R.
move=> _ _ i H; apply /ltP; rewrite addn1 subnSK //.
Defined.
End InnerLoop.

Section OuterLoop.
Variable n : nat.
Function outer_loop A R (j : nat)
         {measure (fun i => (n - j)%N) j} :=
  if (j < n)%N then
    let R := inner_loop j A R 0 in
    let R := store R j j (seq_ytildes j (nth FI0 (nth [::] A j) j)
                                      (nth [::] R j)) in
    outer_loop A R (j + 1)
  else
    R.
move=> _ _ j H; apply /ltP; rewrite addn1 subnSK //.
Defined.
End OuterLoop.

(* note: the result is transposed with respect to cholesky.v *)
Definition cholesky A :=
  let sz := size A in
  outer_loop sz A A 0.

Time Eval vm_compute in map (map B2F) (cholesky m_id).

Definition m2 := [:: [:: Z2B 2; Z2B (-3); Z2B 1]; [:: Z2B (-3); Z2B 5; Z2B 0]; [:: Z2B 1; Z2B 0; Z2B 5]].

Time Eval vm_compute in map (map B2F) (cholesky m2).

(* returns approx:

[ sqrt 2,  -3,     1;
  -2.1213, 0.7071, 0;
  0.7071,  2.1213, 0 ]

then R is almost:

1 / sqrt 2 * [ 2, -3, 1;
               0,  1, 3;
               0,  0, 0 ]
*)

(* size 6, unknown *)
Definition m0 := map (map b64_normalize)
  [:: [:: Float radix2 (5719847880691986) (-45); Float radix2 (5625299890123522) (-65); Float radix2 (-5780611600734441) (-53); Float radix2 (-4882944613594210) (-61); Float radix2 (5183265426126046) (-57);
          Float radix2 (-4857367378817515) (-53)];
      [:: Float radix2 (5625299890123522) (-65); Float radix2 (5248980136204050) (-54); Float radix2 (-7419780026011946) (-59); Float radix2 (-5557861014200314) (-57); Float radix2 (-4507887159164158) (-58);
          Float radix2 (5583285604844652) (-60)];
      [:: Float radix2 (-5780611600734441) (-53); Float radix2 (-7419780026011946) (-59); Float radix2 (5379935414981466) (-57); Float radix2 (5249887442315180) (-59); Float radix2 (-5121630631684668) (-62);
          Float radix2 (-8086292666891304) (-59)];
      [:: Float radix2 (-4882944613594210) (-61); Float radix2 (-5557861014200314) (-57); Float radix2 (5249887442315180) (-59); Float radix2 (7088553734440087) (-56); Float radix2 (5846422154977144) (-62);
          Float radix2 (-6136631189395992) (-60)];
      [:: Float radix2 (5183265426126046) (-57); Float radix2 (-4507887159164158) (-58); Float radix2 (-5121630631684668) (-62); Float radix2 (5846422154977144) (-62); Float radix2 (-7947167790052128) (-65);
          Float radix2 (4518342517623414) (-63)];
      [:: Float radix2 (-4857367378817515) (-53); Float radix2 (5583285604844652) (-60); Float radix2 (-8086292666891304) (-59); Float radix2 (-6136631189395992) (-60); Float radix2 (4518342517623414) (-63);
          Float radix2 (8458192727047538) (-60)]].

(* size 6, positive definite *)
Definition m1 := map (map b64_normalize)
  [:: [:: Float radix2 (4844268357668941) (-51); Float radix2 (-6010289013563096) (-55); Float radix2 (-8527459789388090) (-59); Float radix2 (-4778266098206664) (-50); Float radix2 (5667663619731675) (-55);
          Float radix2 (4683274154211911) (-51)];
      [:: Float radix2 (-6010289013563096) (-55); Float radix2 (7396430339592472) (-51); Float radix2 (-7289940589024767) (-57); Float radix2 (-6805625889340557) (-58); Float radix2 (-6772467775663301) (-51);
          Float radix2 (5856798786847734) (-55)];
      [:: Float radix2 (-8527459789388090) (-59); Float radix2 (-7289940589024767) (-57); Float radix2 (4853298392673210) (-52); Float radix2 (-6022680283661423) (-56); Float radix2 (-6234500978567578) (-55);
          Float radix2 (7135901130999799) (-56)];
      [:: Float radix2 (-4778266098206664) (-50); Float radix2 (-6805625889340557) (-58); Float radix2 (-6022680283661423) (-56); Float radix2 (4783306079007354) (-49); Float radix2 (5238162149477632) (-57);
          Float radix2 (-4748548273910727) (-50)];
      [:: Float radix2 (5667663619731675) (-55); Float radix2 (-6772467775663301) (-51); Float radix2 (-6234500978567578) (-55); Float radix2 (5238162149477632) (-57); Float radix2 (6311840486445046) (-51);
          Float radix2 (-6079338910151020) (-55)];
      [:: Float radix2 (4683274154211911) (-51); Float radix2 (5856798786847734) (-55); Float radix2 (7135901130999799) (-56); Float radix2 (-4748548273910727) (-50); Float radix2 (-6079338910151020) (-55);
          Float radix2 (4765808075135984) (-51)]].

Time Eval vm_compute in map (map B2F) (cholesky m0).
Time Eval vm_compute in map (map B2F) (cholesky m1).

(* size 10, unknown *)
Definition m3 := map (map b64_normalize)
  [:: [:: Float radix2 (8287947700165527) (-50); Float radix2 (-6464882188503222) (-60); Float radix2 (-4996507117802270) (-51); Float radix2 (-6957039294340888) (-58); Float radix2 (-5165727764910364) (-61);
          Float radix2 (-7307607512985528) (-53); Float radix2 (-5606624179017392) (-53); Float radix2 (-7247886577400432) (-53); Float radix2 (-5648530176357532) (-54); Float radix2 (5272997662954966) (-57)];
      [:: Float radix2 (-6464882188503222) (-60); Float radix2 (6045558154750239) (-50); Float radix2 (-8176074238283312) (-55); Float radix2 (-5161952999371402) (-52); Float radix2 (6225369793112940) (-52);
          Float radix2 (-4552386189112408) (-52); Float radix2 (-8575103767793578) (-54); Float radix2 (-5416425828321882) (-55); Float radix2 (-8093621162538540) (-57); Float radix2 (-7527047706269988) (-61)];
      [:: Float radix2 (-4996507117802270) (-51); Float radix2 (-8176074238283312) (-55); Float radix2 (5774173704216997) (-51); Float radix2 (-6813249774596506) (-54); Float radix2 (4538583549008056) (-52);
          Float radix2 (6263064761186482) (-54); Float radix2 (-6790069387505464) (-54); Float radix2 (-7952165342629518) (-53); Float radix2 (-6434072117764500) (-57); Float radix2 (6992597609679130) (-56)];
      [:: Float radix2 (-6957039294340888) (-58); Float radix2 (-5161952999371402) (-52); Float radix2 (-6813249774596506) (-54); Float radix2 (4949261397436096) (-53); Float radix2 (-5944749216752500) (-53);
          Float radix2 (6566643015934850) (-54); Float radix2 (6758080192326284) (-54); Float radix2 (5577431870712244) (-54); Float radix2 (-5806682485174680) (-58); Float radix2 (-4793557537649682) (-57)];
      [:: Float radix2 (-5165727764910364) (-61); Float radix2 (6225369793112940) (-52); Float radix2 (4538583549008056) (-52); Float radix2 (-5944749216752500) (-53); Float radix2 (6527545558829529) (-51);
          Float radix2 (-5209641514336346) (-54); Float radix2 (-4728648205548506) (-52); Float radix2 (-5277547483687560) (-52); Float radix2 (-6669297240016810) (-55); Float radix2 (6563758949351482) (-56)];
      [:: Float radix2 (-7307607512985528) (-53); Float radix2 (-4552386189112408) (-52); Float radix2 (6263064761186482) (-54); Float radix2 (6566643015934850) (-54); Float radix2 (-5209641514336346) (-54);
          Float radix2 (5920321358063340) (-53); Float radix2 (6506706197449886) (-54); Float radix2 (4804664336611616) (-54); Float radix2 (4566395033657208) (-56); Float radix2 (-8914855917203838) (-59)];
      [:: Float radix2 (-5606624179017392) (-53); Float radix2 (-8575103767793578) (-54); Float radix2 (-6790069387505464) (-54); Float radix2 (6758080192326284) (-54); Float radix2 (-4728648205548506) (-52);
          Float radix2 (6506706197449886) (-54); Float radix2 (5217152178940018) (-53); Float radix2 (5982609032665740) (-53); Float radix2 (7563620990290556) (-56); Float radix2 (-7989235180073878) (-57)];
      [:: Float radix2 (-7247886577400432) (-53); Float radix2 (-5416425828321882) (-55); Float radix2 (-7952165342629518) (-53); Float radix2 (5577431870712244) (-54); Float radix2 (-5277547483687560) (-52);
          Float radix2 (4804664336611616) (-54); Float radix2 (5982609032665740) (-53); Float radix2 (4762717653254896) (-52); Float radix2 (7908437533966512) (-55); Float radix2 (-6048758871407710) (-56)];
      [:: Float radix2 (-5648530176357532) (-54); Float radix2 (-8093621162538540) (-57); Float radix2 (-6434072117764500) (-57); Float radix2 (-5806682485174680) (-58);
          Float radix2 (-6669297240016810) (-55); Float radix2 (4566395033657208) (-56); Float radix2 (7563620990290556) (-56); Float radix2 (7908437533966512) (-55); Float radix2 (6257425785518130) (-56);
          Float radix2 (-6722996779008738) (-59)];
      [:: Float radix2 (5272997662954966) (-57); Float radix2 (-7527047706269988) (-61); Float radix2 (6992597609679130) (-56); Float radix2 (-4793557537649682) (-57); Float radix2 (6563758949351482) (-56);
          Float radix2 (-8914855917203838) (-59); Float radix2 (-7989235180073878) (-57); Float radix2 (-6048758871407710) (-56); Float radix2 (-6722996779008738) (-59); Float radix2 (8577618660920051) (-60)]].

(* size 10, positive definite *)
Definition m4 := map (map b64_normalize)
  [:: [:: Float radix2 (6516238871284264) (-51); Float radix2 (-5971104173935053) (-55); Float radix2 (-8926911489220793) (-53); Float radix2 (-5873420906072778) (-62); Float radix2 (-5579440337556541) (-51);
          Float radix2 (-5479226782777909) (-56); Float radix2 (5397540915778874) (-54); Float radix2 (-6404653080960544) (-52); Float radix2 (5047189884153633) (-54); Float radix2 (5243069352447445) (-52)];
      [:: Float radix2 (-5971104173935053) (-55); Float radix2 (5392771920885342) (-50); Float radix2 (-4643373328136263) (-56); Float radix2 (-8884806450165764) (-53); Float radix2 (-6767698343305760) (-55);
          Float radix2 (-5281063518510283) (-51); Float radix2 (8041461808675752) (-56); Float radix2 (6374094168234379) (-55); Float radix2 (-7931460713719950) (-52); Float radix2 (8268138033459430) (-56)];
      [:: Float radix2 (-8926911489220793) (-53); Float radix2 (-4643373328136263) (-56); Float radix2 (6391406230333612) (-50); Float radix2 (-7634469317435608) (-55); Float radix2 (7116294551377074) (-53);
          Float radix2 (8358297597789343) (-59); Float radix2 (-5776751256809078) (-51); Float radix2 (5071353910877271) (-55); Float radix2 (-5406929894230197) (-54); Float radix2 (-7252230262190889) (-58)];
      [:: Float radix2 (-5873420906072778) (-62); Float radix2 (-8884806450165764) (-53); Float radix2 (-7634469317435608) (-55); Float radix2 (6125822831086625) (-50); Float radix2 (5861383394304360) (-56);
          Float radix2 (7663042943140194) (-53); Float radix2 (-5612175689038576) (-54); Float radix2 (-8031469681129529) (-57); Float radix2 (-4829250823398546) (-55); Float radix2 (-8365901301359781) (-61)];
      [:: Float radix2 (-5579440337556541) (-51); Float radix2 (-6767698343305760) (-55); Float radix2 (7116294551377074) (-53); Float radix2 (5861383394304360) (-56); Float radix2 (5534077710598227) (-50);
          Float radix2 (6076337244597776) (-56); Float radix2 (-7273343426163666) (-54); Float radix2 (-4915745298568293) (-52); Float radix2 (5147780804043492) (-57); Float radix2 (-5435268802680230) (-52)];
      [:: Float radix2 (-5479226782777909) (-56); Float radix2 (-5281063518510283) (-51); Float radix2 (8358297597789343) (-59); Float radix2 (7663042943140194) (-53); Float radix2 (6076337244597776) (-56);
          Float radix2 (6671513220695459) (-50); Float radix2 (-6310129194442444) (-54); Float radix2 (-8878205213080279) (-58); Float radix2 (-7479021065470418) (-51); Float radix2 (4843728631705794) (-59)];
      [:: Float radix2 (5397540915778874) (-54); Float radix2 (8041461808675752) (-56); Float radix2 (-5776751256809078) (-51); Float radix2 (-5612175689038576) (-54); Float radix2 (-7273343426163666) (-54);
          Float radix2 (-6310129194442444) (-54); Float radix2 (6011764543103443) (-50); Float radix2 (8090579652152651) (-54); Float radix2 (-5591593090707792) (-55); Float radix2 (-5180581827431268) (-54)];
      [:: Float radix2 (-6404653080960544) (-52); Float radix2 (6374094168234379) (-55); Float radix2 (5071353910877271) (-55); Float radix2 (-8031469681129529) (-57); Float radix2 (-4915745298568293) (-52);
          Float radix2 (-8878205213080279) (-58); Float radix2 (8090579652152651) (-54); Float radix2 (5951259647604226) (-50); Float radix2 (-6922579558862590) (-55); Float radix2 (-6377899283130783) (-51)];
      [:: Float radix2 (5047189884153633) (-54); Float radix2 (-7931460713719950) (-52); Float radix2 (-5406929894230197) (-54); Float radix2 (-4829250823398546) (-55); Float radix2 (5147780804043492) (-57);
          Float radix2 (-7479021065470418) (-51); Float radix2 (-5591593090707792) (-55); Float radix2 (-6922579558862590) (-55); Float radix2 (5265523507928877) (-50); Float radix2 (-5514589751857350) (-56)];
      [:: Float radix2 (5243069352447445) (-52); Float radix2 (8268138033459430) (-56); Float radix2 (-7252230262190889) (-58); Float radix2 (-8365901301359781) (-61); Float radix2 (-5435268802680230) (-52);
          Float radix2 (4843728631705794) (-59); Float radix2 (-5180581827431268) (-54); Float radix2 (-6377899283130783) (-51); Float radix2 (-5514589751857350) (-56); Float radix2 (6073611356579071) (-51)]].

Time Eval vm_compute in map (map B2F) (cholesky m3).
Time Eval vm_compute in map (map B2F) (cholesky m4).

(* size 15, positive definite *)
Definition m5 := map (map b64_normalize)
  [:: [:: Float radix2 (7012064963153224) (-55); Float radix2 (-5663027446228264) (-56); Float radix2 (-6792307907493682) (-61); Float radix2 (-5986117583869434) (-57); Float radix2 (8414481773163468) (-60);
          Float radix2 (-6056032378445724) (-56); Float radix2 (-7593402459777936) (-59); Float radix2 (4824596228008260) (-61); Float radix2 (-8751070479128042) (-61); Float radix2 (-6926917937932206) (-58);
          Float radix2 (4638683589447984) (-61); Float radix2 (-4910019456391330) (-59); Float radix2 (-6599060545682248) (-57); Float radix2 (-5728531107640998) (-63); Float radix2 (-4887650152279606) (-60)];
      [:: Float radix2 (-5663027446228264) (-56); Float radix2 (7661519740931312) (-55); Float radix2 (-6067302265633224) (-57); Float radix2 (8450192732608804) (-62); Float radix2 (-4884564464519530) (-57);
          Float radix2 (8423329774632580) (-59); Float radix2 (-5390102916650782) (-60); Float radix2 (-8088960851268212) (-60); Float radix2 (-4793771436946828) (-62); Float radix2 (5089667611389016) (-60);
          Float radix2 (-6858693681571354) (-58); Float radix2 (5781630339352540) (-60); Float radix2 (7872061560105944) (-59); Float radix2 (-5403004831774690) (-60); Float radix2 (5875255190993400) (-59)];
      [:: Float radix2 (-6792307907493682) (-61); Float radix2 (-6067302265633224) (-57); Float radix2 (7139462228363612) (-55); Float radix2 (-4960877495551254) (-57); Float radix2 (-7219772604583392) (-60);
          Float radix2 (-5790680292669480) (-60); Float radix2 (-7289086011766660) (-60); Float radix2 (-7385050769523194) (-61); Float radix2 (-6382534811809308) (-61);
          Float radix2 (-6736417914340724) (-59); Float radix2 (4827850181812180) (-63); Float radix2 (-7012331164863962) (-59); Float radix2 (-7292126205124350) (-63); Float radix2 (-7685648794133190) (-63);
          Float radix2 (-5737751035779456) (-59)];
      [:: Float radix2 (-5986117583869434) (-57); Float radix2 (8450192732608804) (-62); Float radix2 (-4960877495551254) (-57); Float radix2 (7071785946876828) (-55); Float radix2 (-6105300931736864) (-57);
          Float radix2 (5889996080794950) (-59); Float radix2 (-7412617764981612) (-64); Float radix2 (-7002311179354150) (-61); Float radix2 (5606533391356452) (-64); Float radix2 (8012889528724238) (-61);
          Float radix2 (-6309224637352588) (-58); Float radix2 (5277961448525906) (-60); Float radix2 (7814532264639542) (-60); Float radix2 (-5778406155010576) (-62); Float radix2 (4776259013663874) (-59)];
      [:: Float radix2 (8414481773163468) (-60); Float radix2 (-4884564464519530) (-57); Float radix2 (-7219772604583392) (-60); Float radix2 (-6105300931736864) (-57); Float radix2 (6120668700316112) (-55);
          Float radix2 (7962654336587956) (-61); Float radix2 (-6673777102559380) (-62); Float radix2 (-5216989226077700) (-63); Float radix2 (-8273648847113952) (-61); Float radix2 (-9004655728060684) (-60);
          Float radix2 (7871149180850748) (-62); Float radix2 (-5065993698128348) (-57); Float radix2 (5953237524550174) (-60); Float radix2 (4616122862178388) (-63); Float radix2 (-5831516454480000) (-58)];
      [:: Float radix2 (-6056032378445724) (-56); Float radix2 (8423329774632580) (-59); Float radix2 (-5790680292669480) (-60); Float radix2 (5889996080794950) (-59); Float radix2 (7962654336587956) (-61);
          Float radix2 (7248987899262084) (-55); Float radix2 (-7135125128864034) (-62); Float radix2 (-5679722705111954) (-58); Float radix2 (-4730033907217516) (-61); Float radix2 (-5132536672694310) (-57);
          Float radix2 (-8795570064307242) (-61); Float radix2 (8552817839395328) (-60); Float radix2 (-8956064052528118) (-61); Float radix2 (-5542945129197534) (-61); Float radix2 (-4672533804289196) (-57)];
      [:: Float radix2 (-7593402459777936) (-59); Float radix2 (-5390102916650782) (-60); Float radix2 (-7289086011766660) (-60); Float radix2 (-7412617764981612) (-64);
          Float radix2 (-6673777102559380) (-62); Float radix2 (-7135125128864034) (-62); Float radix2 (6469128574849628) (-55); Float radix2 (-5993921651770864) (-60); Float radix2 (-5408553217585904) (-58);
          Float radix2 (-5050088146126688) (-61); Float radix2 (-6556894242845236) (-60); Float radix2 (-8119356166788608) (-62); Float radix2 (8486990545493026) (-63); Float radix2 (-6104043003693902) (-58);
          Float radix2 (6725702258679372) (-61)];
      [:: Float radix2 (4824596228008260) (-61); Float radix2 (-8088960851268212) (-60); Float radix2 (-7385050769523194) (-61); Float radix2 (-7002311179354150) (-61); Float radix2 (-5216989226077700) (-63);
          Float radix2 (-5679722705111954) (-58); Float radix2 (-5993921651770864) (-60); Float radix2 (6483310640302532) (-55); Float radix2 (-5056079985274176) (-60); Float radix2 (5766562454591746) (-62);
          Float radix2 (-5079212017709042) (-61); Float radix2 (-5418725673451190) (-61); Float radix2 (-6134980287154584) (-58); Float radix2 (-7016524880353894) (-62); Float radix2 (6738464021496200) (-62)];
      [:: Float radix2 (-8751070479128042) (-61); Float radix2 (-4793771436946828) (-62); Float radix2 (-6382534811809308) (-61); Float radix2 (5606533391356452) (-64); Float radix2 (-8273648847113952) (-61);
          Float radix2 (-4730033907217516) (-61); Float radix2 (-5408553217585904) (-58); Float radix2 (-5056079985274176) (-60); Float radix2 (5784017613420106) (-55); Float radix2 (-5945795870686000) (-63);
          Float radix2 (-6130344395871316) (-62); Float radix2 (-7036861878418120) (-64); Float radix2 (-4985919917102614) (-64); Float radix2 (-8608624932093626) (-58); Float radix2 (6070696580300750) (-62)];
      [:: Float radix2 (-6926917937932206) (-58); Float radix2 (5089667611389016) (-60); Float radix2 (-6736417914340724) (-59); Float radix2 (8012889528724238) (-61); Float radix2 (-9004655728060684) (-60);
          Float radix2 (-5132536672694310) (-57); Float radix2 (-5050088146126688) (-61); Float radix2 (5766562454591746) (-62); Float radix2 (-5945795870686000) (-63); Float radix2 (6755695138739546) (-55);
          Float radix2 (-6593235613507442) (-61); Float radix2 (-5824636343428708) (-59); Float radix2 (-4871660691934746) (-57); Float radix2 (5575044483077888) (-63); Float radix2 (-8360479168776436) (-59)];
      [:: Float radix2 (4638683589447984) (-61); Float radix2 (-6858693681571354) (-58); Float radix2 (4827850181812180) (-63); Float radix2 (-6309224637352588) (-58); Float radix2 (7871149180850748) (-62);
          Float radix2 (-8795570064307242) (-61); Float radix2 (-6556894242845236) (-60); Float radix2 (-5079212017709042) (-61); Float radix2 (-6130344395871316) (-62);
          Float radix2 (-6593235613507442) (-61); Float radix2 (6411040167156194) (-55); Float radix2 (-5669306150382106) (-61); Float radix2 (4848218262051540) (-63); Float radix2 (-6326316915697314) (-60);
          Float radix2 (7624556381060632) (-63)];
      [:: Float radix2 (-4910019456391330) (-59); Float radix2 (5781630339352540) (-60); Float radix2 (-7012331164863962) (-59); Float radix2 (5277961448525906) (-60); Float radix2 (-5065993698128348) (-57);
          Float radix2 (8552817839395328) (-60); Float radix2 (-8119356166788608) (-62); Float radix2 (-5418725673451190) (-61); Float radix2 (-7036861878418120) (-64); Float radix2 (-5824636343428708) (-59);
          Float radix2 (-5669306150382106) (-61); Float radix2 (6631407169244802) (-55); Float radix2 (6723402913237298) (-60); Float radix2 (-5387975609684466) (-63); Float radix2 (-5030150552225478) (-57)];
      [:: Float radix2 (-6599060545682248) (-57); Float radix2 (7872061560105944) (-59); Float radix2 (-7292126205124350) (-63); Float radix2 (7814532264639542) (-60); Float radix2 (5953237524550174) (-60);
          Float radix2 (-8956064052528118) (-61); Float radix2 (8486990545493026) (-63); Float radix2 (-6134980287154584) (-58); Float radix2 (-4985919917102614) (-64); Float radix2 (-4871660691934746) (-57);
          Float radix2 (4848218262051540) (-63); Float radix2 (6723402913237298) (-60); Float radix2 (6918396718288366) (-55); Float radix2 (8089471010929966) (-65); Float radix2 (-6427833814872586) (-57)];
      [:: Float radix2 (-5728531107640998) (-63); Float radix2 (-5403004831774690) (-60); Float radix2 (-7685648794133190) (-63); Float radix2 (-5778406155010576) (-62); Float radix2 (4616122862178388) (-63);
          Float radix2 (-5542945129197534) (-61); Float radix2 (-6104043003693902) (-58); Float radix2 (-7016524880353894) (-62); Float radix2 (-8608624932093626) (-58); Float radix2 (5575044483077888) (-63);
          Float radix2 (-6326316915697314) (-60); Float radix2 (-5387975609684466) (-63); Float radix2 (8089471010929966) (-65); Float radix2 (5689665535621306) (-55); Float radix2 (4530665277681950) (-61)];
      [:: Float radix2 (-4887650152279606) (-60); Float radix2 (5875255190993400) (-59); Float radix2 (-5737751035779456) (-59); Float radix2 (4776259013663874) (-59); Float radix2 (-5831516454480000) (-58);
          Float radix2 (-4672533804289196) (-57); Float radix2 (6725702258679372) (-61); Float radix2 (6738464021496200) (-62); Float radix2 (6070696580300750) (-62); Float radix2 (-8360479168776436) (-59);
          Float radix2 (7624556381060632) (-63); Float radix2 (-5030150552225478) (-57); Float radix2 (-6427833814872586) (-57); Float radix2 (4530665277681950) (-61); Float radix2 (5951444319197092) (-55)]].

Time Eval vm_compute in map (map B2F) (cholesky m5).

(* size 20, positive definite *)
Definition m6 := map (map b64_normalize)
  [:: [:: Float radix2 (7004141682982129) (-54); Float radix2 (7663117067739586) (-65); Float radix2 (-4768994609630018) (-56); Float radix2 (7598369244698418) (-64); Float radix2 (7412648481282282) (-60);
          Float radix2 (-4765434420431130) (-62); Float radix2 (-5539844974277560) (-61); Float radix2 (-5705123011701558) (-56); Float radix2 (8880958159935330) (-64); Float radix2 (4816352727020266) (-64);
          Float radix2 (6999799551794340) (-59); Float radix2 (-7456413355319842) (-63); Float radix2 (-6393191794751778) (-61); Float radix2 (8117240772441746) (-62); Float radix2 (5470959774039018) (-63);
          Float radix2 (-8822859736949810) (-62); Float radix2 (-5325821475029160) (-56); Float radix2 (5186486607788782) (-62); Float radix2 (-5196904707764804) (-61); Float radix2 (8615839339975414) (-65)];
      [:: Float radix2 (7663117067739586) (-65); Float radix2 (7816732277094335) (-54); Float radix2 (8241160147143100) (-66); Float radix2 (-8001978709665686) (-56); Float radix2 (-8368387034055360) (-64);
          Float radix2 (7417325456085286) (-63); Float radix2 (-8173399178362182) (-63); Float radix2 (4541789937968528) (-65); Float radix2 (-7979136100768394) (-57); Float radix2 (-5891409753705722) (-63);
          Float radix2 (-8317042863566298) (-63); Float radix2 (7743282699420812) (-61); Float radix2 (7921643961564758) (-64); Float radix2 (5815266897465820) (-66); Float radix2 (8614777287031012) (-62);
          Float radix2 (-7151010508619152) (-64); Float radix2 (5956937315293004) (-63); Float radix2 (-7409720442386956) (-57); Float radix2 (-6120566570906488) (-63); Float radix2 (-4933884289419416) (-67)];
      [:: Float radix2 (-4768994609630018) (-56); Float radix2 (8241160147143100) (-66); Float radix2 (8256365101200047) (-54); Float radix2 (-7934185605871908) (-61); Float radix2 (-4815920860844168) (-61);
          Float radix2 (-4554714313120538) (-66); Float radix2 (5926823897116564) (-60); Float radix2 (-5752541093298398) (-57); Float radix2 (5227067692615372) (-67); Float radix2 (7131857834244490) (-65);
          Float radix2 (-5095243021528932) (-61); Float radix2 (5182469449827636) (-62); Float radix2 (5223272925156556) (-59); Float radix2 (-5209235647724986) (-63); Float radix2 (-7785699488995148) (-62);
          Float radix2 (-6837940999760548) (-63); Float radix2 (-5987111288097666) (-57); Float radix2 (-8758113624533448) (-63); Float radix2 (-5586308651432164) (-64); Float radix2 (5274828341555790) (-63)];
      [:: Float radix2 (7598369244698418) (-64); Float radix2 (-8001978709665686) (-56); Float radix2 (-7934185605871908) (-61); Float radix2 (4537010937766774) (-53); Float radix2 (-5819561848079096) (-63);
          Float radix2 (5572565005903328) (-60); Float radix2 (5711434732432446) (-64); Float radix2 (5965494547409622) (-66); Float radix2 (-6065856735967688) (-56); Float radix2 (-8439619383799354) (-64);
          Float radix2 (-5989088461499516) (-67); Float radix2 (5073956721564380) (-59); Float radix2 (-5762394168707010) (-62); Float radix2 (-4976526590224862) (-62); Float radix2 (-6660605915093542) (-61);
          Float radix2 (-7949843712601746) (-65); Float radix2 (-6149112773110064) (-63); Float radix2 (-6512713589386974) (-56); Float radix2 (5029719096006230) (-63); Float radix2 (-5501215801925664) (-67)];
      [:: Float radix2 (7412648481282282) (-60); Float radix2 (-8368387034055360) (-64); Float radix2 (-4815920860844168) (-61); Float radix2 (-5819561848079096) (-63); Float radix2 (7614305469912389) (-54);
          Float radix2 (4800276670579946) (-64); Float radix2 (-7578049217301356) (-57); Float radix2 (4770774320289136) (-61); Float radix2 (-8590239396417482) (-63); Float radix2 (-8136693706281090) (-56);
          Float radix2 (7970299315343160) (-64); Float radix2 (5556109163265260) (-66); Float radix2 (5103252333881436) (-62); Float radix2 (4847023963623996) (-60); Float radix2 (-8378352084102550) (-66);
          Float radix2 (5516846888646728) (-61); Float radix2 (-8684731538273222) (-62); Float radix2 (-5907989575168690) (-63); Float radix2 (-7313948422843130) (-57); Float radix2 (5755634895631614) (-61)];
      [:: Float radix2 (-4765434420431130) (-62); Float radix2 (7417325456085286) (-63); Float radix2 (-4554714313120538) (-66); Float radix2 (5572565005903328) (-60); Float radix2 (4800276670579946) (-64);
          Float radix2 (8016213377382865) (-54); Float radix2 (-7692682832879118) (-62); Float radix2 (7522037009704644) (-66); Float radix2 (6467776244679412) (-60); Float radix2 (-7527716358941974) (-62);
          Float radix2 (7284136276664322) (-67); Float radix2 (-7187971528508492) (-63); Float radix2 (-7349313123301282) (-62); Float radix2 (7887646037408206) (-63); Float radix2 (8951648976303060) (-60);
          Float radix2 (-7479851571448340) (-62); Float radix2 (5236324422825726) (-63); Float radix2 (8303641126888054) (-63); Float radix2 (-6499825003566952) (-63); Float radix2 (-8538987180348766) (-63)];
      [:: Float radix2 (-5539844974277560) (-61); Float radix2 (-8173399178362182) (-63); Float radix2 (5926823897116564) (-60); Float radix2 (5711434732432446) (-64); Float radix2 (-7578049217301356) (-57);
          Float radix2 (-7692682832879118) (-62); Float radix2 (8663958328732141) (-54); Float radix2 (7493179110819714) (-63); Float radix2 (8218784752876932) (-64); Float radix2 (-5956282307099498) (-56);
          Float radix2 (5404605146998176) (-62); Float radix2 (-7217308355048580) (-62); Float radix2 (-5101352340423694) (-61); Float radix2 (4908308695809498) (-61); Float radix2 (5278078502692274) (-62);
          Float radix2 (-5114773870237402) (-64); Float radix2 (-8696387067028516) (-65); Float radix2 (4886862330870682) (-62); Float radix2 (-6995147915788572) (-57); Float radix2 (5391926950796064) (-64)];
      [:: Float radix2 (-5705123011701558) (-56); Float radix2 (4541789937968528) (-65); Float radix2 (-5752541093298398) (-57); Float radix2 (5965494547409622) (-66); Float radix2 (4770774320289136) (-61);
          Float radix2 (7522037009704644) (-66); Float radix2 (7493179110819714) (-63); Float radix2 (8238214506136493) (-54); Float radix2 (-7871563714030348) (-62); Float radix2 (5169784075987976) (-59);
          Float radix2 (-7670213031282456) (-62); Float radix2 (5372102088452788) (-64); Float radix2 (-5621601377571096) (-63); Float radix2 (-8398689649450532) (-62); Float radix2 (-8142565489630000) (-62);
          Float radix2 (8191976195029978) (-60); Float radix2 (-5790637528728602) (-57); Float radix2 (-5588600848633700) (-69); Float radix2 (5706128541655066) (-63); Float radix2 (-6405522938058694) (-63)];
      [:: Float radix2 (8880958159935330) (-64); Float radix2 (-7979136100768394) (-57); Float radix2 (5227067692615372) (-67); Float radix2 (-6065856735967688) (-56); Float radix2 (-8590239396417482) (-63);
          Float radix2 (6467776244679412) (-60); Float radix2 (8218784752876932) (-64); Float radix2 (-7871563714030348) (-62); Float radix2 (8640550884890265) (-54); Float radix2 (6496526420541874) (-63);
          Float radix2 (-7748821660295454) (-64); Float radix2 (6447862585369526) (-62); Float radix2 (6508008188138720) (-64); Float radix2 (-7442604004502272) (-62); Float radix2 (-8760420748964588) (-61);
          Float radix2 (8977434523809418) (-64); Float radix2 (7443135421902614) (-66); Float radix2 (-7048765795003242) (-57); Float radix2 (4880017606951414) (-62); Float radix2 (8041750476957138) (-71)];
      [:: Float radix2 (4816352727020266) (-64); Float radix2 (-5891409753705722) (-63); Float radix2 (7131857834244490) (-65); Float radix2 (-8439619383799354) (-64); Float radix2 (-8136693706281090) (-56);
          Float radix2 (-7527716358941974) (-62); Float radix2 (-5956282307099498) (-56); Float radix2 (5169784075987976) (-59); Float radix2 (6496526420541874) (-63); Float radix2 (8933186566360665) (-54);
          Float radix2 (5199482042440758) (-61); Float radix2 (-5151734852082758) (-62); Float radix2 (5405030082737476) (-63); Float radix2 (7648342972118966) (-60); Float radix2 (5106922293228370) (-63);
          Float radix2 (-5328790410175810) (-60); Float radix2 (-7865085902751582) (-66); Float radix2 (5411406939179618) (-63); Float radix2 (-6460109440667598) (-56); Float radix2 (-5227798202875602) (-63)];
      [:: Float radix2 (6999799551794340) (-59); Float radix2 (-8317042863566298) (-63); Float radix2 (-5095243021528932) (-61); Float radix2 (-5989088461499516) (-67); Float radix2 (7970299315343160) (-64);
          Float radix2 (7284136276664322) (-67); Float radix2 (5404605146998176) (-62); Float radix2 (-7670213031282456) (-62); Float radix2 (-7748821660295454) (-64); Float radix2 (5199482042440758) (-61);
          Float radix2 (7642269557033113) (-54); Float radix2 (6731564019954102) (-63); Float radix2 (-7367966748453192) (-57); Float radix2 (6016580911477948) (-62); Float radix2 (-5604761468596194) (-62);
          Float radix2 (-7679631321246430) (-57); Float radix2 (8803617555509100) (-61); Float radix2 (4911700310758476) (-65); Float radix2 (6540138837531234) (-61); Float radix2 (-7366488495008130) (-56)];
      [:: Float radix2 (-7456413355319842) (-63); Float radix2 (7743282699420812) (-61); Float radix2 (5182469449827636) (-62); Float radix2 (5073956721564380) (-59); Float radix2 (5556109163265260) (-66);
          Float radix2 (-7187971528508492) (-63); Float radix2 (-7217308355048580) (-62); Float radix2 (5372102088452788) (-64); Float radix2 (6447862585369526) (-62); Float radix2 (-5151734852082758) (-62);
          Float radix2 (6731564019954102) (-63); Float radix2 (8020187552314375) (-54); Float radix2 (-5686434963569906) (-61); Float radix2 (7491315665856180) (-65); Float radix2 (5012155800437296) (-60);
          Float radix2 (-8442356283240604) (-65); Float radix2 (8010572984634982) (-62); Float radix2 (5378225644728976) (-59); Float radix2 (-6521749561719994) (-62); Float radix2 (-6119893913182850) (-61)];
      [:: Float radix2 (-6393191794751778) (-61); Float radix2 (7921643961564758) (-64); Float radix2 (5223272925156556) (-59); Float radix2 (-5762394168707010) (-62); Float radix2 (5103252333881436) (-62);
          Float radix2 (-7349313123301282) (-62); Float radix2 (-5101352340423694) (-61); Float radix2 (-5621601377571096) (-63); Float radix2 (6508008188138720) (-64); Float radix2 (5405030082737476) (-63);
          Float radix2 (-7367966748453192) (-57); Float radix2 (-5686434963569906) (-61); Float radix2 (8604988747297419) (-54); Float radix2 (4683880478915546) (-62); Float radix2 (7372785840735458) (-62);
          Float radix2 (-6526638025448964) (-57); Float radix2 (4591111212859154) (-61); Float radix2 (7082812212576050) (-62); Float radix2 (-7243272510122574) (-64); Float radix2 (-6008545048938474) (-56)];
      [:: Float radix2 (8117240772441746) (-62); Float radix2 (5815266897465820) (-66); Float radix2 (-5209235647724986) (-63); Float radix2 (-4976526590224862) (-62); Float radix2 (4847023963623996) (-60);
          Float radix2 (7887646037408206) (-63); Float radix2 (4908308695809498) (-61); Float radix2 (-8398689649450532) (-62); Float radix2 (-7442604004502272) (-62); Float radix2 (7648342972118966) (-60);
          Float radix2 (6016580911477948) (-62); Float radix2 (7491315665856180) (-65); Float radix2 (4683880478915546) (-62); Float radix2 (7972935092684563) (-54); Float radix2 (-8189190826655646) (-62);
          Float radix2 (6351784112360756) (-60); Float radix2 (-4704874400310998) (-61); Float radix2 (-6635141921030644) (-62); Float radix2 (4794316451502984) (-59); Float radix2 (8665086704054558) (-61)];
      [:: Float radix2 (5470959774039018) (-63); Float radix2 (8614777287031012) (-62); Float radix2 (-7785699488995148) (-62); Float radix2 (-6660605915093542) (-61); Float radix2 (-8378352084102550) (-66);
          Float radix2 (8951648976303060) (-60); Float radix2 (5278078502692274) (-62); Float radix2 (-8142565489630000) (-62); Float radix2 (-8760420748964588) (-61); Float radix2 (5106922293228370) (-63);
          Float radix2 (-5604761468596194) (-62); Float radix2 (5012155800437296) (-60); Float radix2 (7372785840735458) (-62); Float radix2 (-8189190826655646) (-62); Float radix2 (8445886403340381) (-54);
          Float radix2 (7992777020933992) (-62); Float radix2 (-7456948593754672) (-62); Float radix2 (-5074091787877336) (-60); Float radix2 (8454142284970078) (-62); Float radix2 (8888847370640882) (-62)];
      [:: Float radix2 (-8822859736949810) (-62); Float radix2 (-7151010508619152) (-64); Float radix2 (-6837940999760548) (-63); Float radix2 (-7949843712601746) (-65); Float radix2 (5516846888646728) (-61);
          Float radix2 (-7479851571448340) (-62); Float radix2 (-5114773870237402) (-64); Float radix2 (8191976195029978) (-60); Float radix2 (8977434523809418) (-64); Float radix2 (-5328790410175810) (-60);
          Float radix2 (-7679631321246430) (-57); Float radix2 (-8442356283240604) (-65); Float radix2 (-6526638025448964) (-57); Float radix2 (6351784112360756) (-60); Float radix2 (7992777020933992) (-62);
          Float radix2 (8571115120441317) (-54); Float radix2 (5506671600389980) (-63); Float radix2 (6548784845130856) (-64); Float radix2 (-4647856975253678) (-60); Float radix2 (-6062358217234566) (-56)];
      [:: Float radix2 (-5325821475029160) (-56); Float radix2 (5956937315293004) (-63); Float radix2 (-5987111288097666) (-57); Float radix2 (-6149112773110064) (-63); Float radix2 (-8684731538273222) (-62);
          Float radix2 (5236324422825726) (-63); Float radix2 (-8696387067028516) (-65); Float radix2 (-5790637528728602) (-57); Float radix2 (7443135421902614) (-66); Float radix2 (-7865085902751582) (-66);
          Float radix2 (8803617555509100) (-61); Float radix2 (8010572984634982) (-62); Float radix2 (4591111212859154) (-61); Float radix2 (-4704874400310998) (-61); Float radix2 (-7456948593754672) (-62);
          Float radix2 (5506671600389980) (-63); Float radix2 (8176996122011185) (-54); Float radix2 (-6343418444064328) (-61); Float radix2 (5097123828304360) (-60); Float radix2 (7013528363231696) (-59)];
      [:: Float radix2 (5186486607788782) (-62); Float radix2 (-7409720442386956) (-57); Float radix2 (-8758113624533448) (-63); Float radix2 (-6512713589386974) (-56); Float radix2 (-5907989575168690) (-63);
          Float radix2 (8303641126888054) (-63); Float radix2 (4886862330870682) (-62); Float radix2 (-5588600848633700) (-69); Float radix2 (-7048765795003242) (-57); Float radix2 (5411406939179618) (-63);
          Float radix2 (4911700310758476) (-65); Float radix2 (5378225644728976) (-59); Float radix2 (7082812212576050) (-62); Float radix2 (-6635141921030644) (-62); Float radix2 (-5074091787877336) (-60);
          Float radix2 (6548784845130856) (-64); Float radix2 (-6343418444064328) (-61); Float radix2 (8480073745810711) (-54); Float radix2 (7170440491793888) (-62); Float radix2 (5733698695163186) (-63)];
      [:: Float radix2 (-5196904707764804) (-61); Float radix2 (-6120566570906488) (-63); Float radix2 (-5586308651432164) (-64); Float radix2 (5029719096006230) (-63); Float radix2 (-7313948422843130) (-57);
          Float radix2 (-6499825003566952) (-63); Float radix2 (-6995147915788572) (-57); Float radix2 (5706128541655066) (-63); Float radix2 (4880017606951414) (-62); Float radix2 (-6460109440667598) (-56);
          Float radix2 (6540138837531234) (-61); Float radix2 (-6521749561719994) (-62); Float radix2 (-7243272510122574) (-64); Float radix2 (4794316451502984) (-59); Float radix2 (8454142284970078) (-62);
          Float radix2 (-4647856975253678) (-60); Float radix2 (5097123828304360) (-60); Float radix2 (7170440491793888) (-62); Float radix2 (8470524952754521) (-54); Float radix2 (-6945921840934982) (-60)];
      [:: Float radix2 (8615839339975414) (-65); Float radix2 (-4933884289419416) (-67); Float radix2 (5274828341555790) (-63); Float radix2 (-5501215801925664) (-67); Float radix2 (5755634895631614) (-61);
          Float radix2 (-8538987180348766) (-63); Float radix2 (5391926950796064) (-64); Float radix2 (-6405522938058694) (-63); Float radix2 (8041750476957138) (-71); Float radix2 (-5227798202875602) (-63);
          Float radix2 (-7366488495008130) (-56); Float radix2 (-6119893913182850) (-61); Float radix2 (-6008545048938474) (-56); Float radix2 (8665086704054558) (-61); Float radix2 (8888847370640882) (-62);
          Float radix2 (-6062358217234566) (-56); Float radix2 (7013528363231696) (-59); Float radix2 (5733698695163186) (-63); Float radix2 (-6945921840934982) (-60); Float radix2 (8400447441679581) (-54)]].

Time Eval vm_compute in map (map B2F) (cholesky m6).

(* size 35, positive definite *)
Definition m7 := map (map b64_normalize)
  [:: [:: Float radix2 (8001857318853769) (-54); Float radix2 (8105978872199155) (-59); Float radix2 (-8540524745963883) (-56); Float radix2 (-5971048931863984) (-59); Float radix2 (-5732807073904006) (-58);
          Float radix2 (-7034130402091584) (-58); Float radix2 (-4660801789586397) (-59); Float radix2 (-5159588567717965) (-58); Float radix2 (-4931114837325580) (-60);
          Float radix2 (-7354821284144091) (-55); Float radix2 (-8178491482311809) (-64); Float radix2 (6588345257080901) (-60); Float radix2 (5944025091388110) (-58); Float radix2 (-8461975588223993) (-61);
          Float radix2 (-6568705447492194) (-58); Float radix2 (-6967046967161806) (-58); Float radix2 (-5883318804343310) (-57); Float radix2 (-7122825209740845) (-59);
          Float radix2 (-4705362910783311) (-59); Float radix2 (6730265665484937) (-61); Float radix2 (-5949632433843820) (-62); Float radix2 (-5067837646303356) (-60); Float radix2 (5181573916732463) (-60);
          Float radix2 (6862485057834478) (-65); Float radix2 (-5185768042465135) (-61); Float radix2 (-8484330173520993) (-55); Float radix2 (4664990395501441) (-60); Float radix2 (-6803106471437698) (-59);
          Float radix2 (-6277990303912070) (-58); Float radix2 (4541720166634813) (-60); Float radix2 (-6270136240798972) (-58); Float radix2 (5708641416327253) (-60); Float radix2 (-4941811810265669) (-59);
          Float radix2 (-4771630765502464) (-60); Float radix2 (-8738214033659113) (-57)];
      [:: Float radix2 (8105978872199155) (-59); Float radix2 (6473201363065632) (-53); Float radix2 (-4677362808452413) (-60); Float radix2 (-4767400912176875) (-54); Float radix2 (-4921719325092118) (-62);
          Float radix2 (-5167661018612407) (-58); Float radix2 (-6744575497587320) (-56); Float radix2 (-6277355111666405) (-60); Float radix2 (-6198033076874567) (-58); Float radix2 (6719265591752822) (-61);
          Float radix2 (8405443995422055) (-57); Float radix2 (7960179432287573) (-63); Float radix2 (-5241762759586644) (-61); Float radix2 (-4803585793731932) (-58); Float radix2 (8450352010415979) (-61);
          Float radix2 (-5276279573545719) (-56); Float radix2 (-5262063236568881) (-55); Float radix2 (-5712051443460551) (-57); Float radix2 (-5207058100076011) (-57); Float radix2 (7485375033378406) (-57);
          Float radix2 (-8562069243083717) (-60); Float radix2 (6160434642641930) (-60); Float radix2 (-4888472943166285) (-58); Float radix2 (-8674900283127138) (-59); Float radix2 (8542613821174353) (-59);
          Float radix2 (7484103548263041) (-58); Float radix2 (-8563867698723896) (-59); Float radix2 (6219262727315090) (-62); Float radix2 (-4921057633548201) (-59); Float radix2 (-7421943121368884) (-59);
          Float radix2 (6559314116117508) (-60); Float radix2 (-4609465268840614) (-59); Float radix2 (-6749026478138281) (-57); Float radix2 (8228663750642723) (-59); Float radix2 (5517847183251995) (-59)];
      [:: Float radix2 (-8540524745963883) (-56); Float radix2 (-4677362808452413) (-60); Float radix2 (7033929409131254) (-53); Float radix2 (-8277163415275975) (-62); Float radix2 (-8581079797913498) (-56);
          Float radix2 (-6250550472117656) (-57); Float radix2 (6305591953355021) (-67); Float radix2 (-7564265102940564) (-58); Float radix2 (-4627268335839618) (-60); Float radix2 (7879845315376648) (-56);
          Float radix2 (8435425263974828) (-62); Float radix2 (6784798422178857) (-57); Float radix2 (7488928149021427) (-61); Float radix2 (4760500721357682) (-65); Float radix2 (6749241428591227) (-57);
          Float radix2 (-8122257469506310) (-57); Float radix2 (-4703893120704933) (-57); Float radix2 (-7210972096460403) (-57); Float radix2 (-4904599098578396) (-57); Float radix2 (4658669709821335) (-60);
          Float radix2 (4958807650707688) (-59); Float radix2 (-5383356411112396) (-60); Float radix2 (-6893288150263804) (-59); Float radix2 (-8866881211149593) (-63); Float radix2 (6306085435507872) (-60);
          Float radix2 (5453647653997608) (-56); Float radix2 (7009045353064656) (-60); Float radix2 (5116135845666350) (-59); Float radix2 (-6722840933484610) (-61); Float radix2 (4862297682823602) (-61);
          Float radix2 (5533600830736471) (-57); Float radix2 (4685087017233202) (-58); Float radix2 (-5074699812125137) (-59); Float radix2 (7992774080840037) (-60); Float radix2 (7987339031999777) (-57)];
      [:: Float radix2 (-5971048931863984) (-59); Float radix2 (-4767400912176875) (-54); Float radix2 (-8277163415275975) (-62); Float radix2 (7176948745312328) (-53); Float radix2 (4874253323048613) (-61);
          Float radix2 (8637504373491419) (-63); Float radix2 (-7174185589211554) (-59); Float radix2 (-6867187410661832) (-60); Float radix2 (-6875110780351578) (-57); Float radix2 (4649513214171855) (-60);
          Float radix2 (6815726348070503) (-59); Float radix2 (4830781126261447) (-59); Float radix2 (-7164527652227812) (-62); Float radix2 (-8625052088706654) (-60); Float radix2 (5874777060519231) (-60);
          Float radix2 (6758519285354963) (-61); Float radix2 (-7394729697917917) (-58); Float radix2 (-4814259184620201) (-57); Float radix2 (-6146501687222052) (-56); Float radix2 (-5292590115958625) (-61);
          Float radix2 (8497124948679090) (-64); Float radix2 (7642213521889024) (-58); Float radix2 (7684642548563593) (-62); Float radix2 (-5293641603171228) (-58); Float radix2 (7320647348393100) (-61);
          Float radix2 (-4748020439419376) (-66); Float radix2 (-6742999695706110) (-60); Float radix2 (6467361502754368) (-58); Float radix2 (-5032715019038397) (-63); Float radix2 (-8715127238646429) (-59);
          Float radix2 (4873511592831936) (-60); Float radix2 (7615889291713915) (-60); Float radix2 (-7994505573433851) (-59); Float radix2 (8140285263809966) (-61); Float radix2 (8373839662416763) (-60)];
      [:: Float radix2 (-5732807073904006) (-58); Float radix2 (-4921719325092118) (-62); Float radix2 (-8581079797913498) (-56); Float radix2 (4874253323048613) (-61); Float radix2 (4544094344054625) (-53);
          Float radix2 (-7932233153178552) (-62); Float radix2 (-4708888871901324) (-60); Float radix2 (-8198994276820730) (-58); Float radix2 (-8917545173732781) (-63); Float radix2 (8412471880727991) (-57);
          Float radix2 (8833232778404643) (-60); Float radix2 (-7256472582996773) (-57); Float radix2 (-5934265100687522) (-60); Float radix2 (-8473935841918097) (-61); Float radix2 (-6176278488506899) (-58);
          Float radix2 (-7082057269840988) (-62); Float radix2 (-8438493484548458) (-59); Float radix2 (-7330098486852007) (-57); Float radix2 (-5269619711826117) (-60); Float radix2 (7289447407929700) (-60);
          Float radix2 (8114362825636645) (-59); Float radix2 (6198230228733664) (-59); Float radix2 (-5338135386744968) (-59); Float radix2 (-6531618570648909) (-60); Float radix2 (4652503742414448) (-59);
          Float radix2 (8449593709356208) (-57); Float radix2 (8873702242274584) (-59); Float radix2 (-5560536192904777) (-57); Float radix2 (-7310241944451472) (-60); Float radix2 (-5406730821905944) (-59);
          Float radix2 (-5387573365950041) (-60); Float radix2 (-5600123780875602) (-61); Float radix2 (-4571062136939352) (-59); Float radix2 (6190367946856795) (-59); Float radix2 (-4870398793673857) (-59)];
      [:: Float radix2 (-7034130402091584) (-58); Float radix2 (-5167661018612407) (-58); Float radix2 (-6250550472117656) (-57); Float radix2 (8637504373491419) (-63); Float radix2 (-7932233153178552) (-62);
          Float radix2 (4968622061514831) (-53); Float radix2 (5485823844256675) (-60); Float radix2 (5932610483345586) (-57); Float radix2 (-8448278107917695) (-63); Float radix2 (-6784577197873266) (-60);
          Float radix2 (-7744130900368848) (-60); Float radix2 (-4604486246328463) (-59); Float radix2 (-4750914567334418) (-54); Float radix2 (7804762846964525) (-63); Float radix2 (4568425844439156) (-63);
          Float radix2 (5979245880695135) (-59); Float radix2 (6158489870792966) (-57); Float radix2 (5487082178189390) (-61); Float radix2 (5711581568332730) (-59); Float radix2 (-8837385070632621) (-57);
          Float radix2 (-8002865934487872) (-59); Float radix2 (-5653053283910742) (-60); Float radix2 (-7803014757952139) (-65); Float radix2 (6862985973342458) (-61); Float radix2 (-7533594346948033) (-59);
          Float radix2 (-5347573023869073) (-57); Float radix2 (-8573771434234696) (-60); Float radix2 (-4946956543689282) (-59); Float radix2 (-7143285474641004) (-57);
          Float radix2 (-6615775759042921) (-62); Float radix2 (-8712023044943202) (-59); Float radix2 (5649531496189314) (-59); Float radix2 (6313274800757743) (-59); Float radix2 (-6587423049902345) (-58);
          Float radix2 (6640981809727570) (-63)];
      [:: Float radix2 (-4660801789586397) (-59); Float radix2 (-6744575497587320) (-56); Float radix2 (6305591953355021) (-67); Float radix2 (-7174185589211554) (-59); Float radix2 (-4708888871901324) (-60);
          Float radix2 (5485823844256675) (-60); Float radix2 (5040337854210771) (-52); Float radix2 (-4605152911020776) (-61); Float radix2 (6977733891504202) (-58); Float radix2 (-5219504059048359) (-62);
          Float radix2 (-5814224090907956) (-57); Float radix2 (7708473722184499) (-62); Float radix2 (5521664124350374) (-60); Float radix2 (5086145084159217) (-57); Float radix2 (-6635811946391457) (-60);
          Float radix2 (5523441676143573) (-57); Float radix2 (-5531729392814709) (-64); Float radix2 (6971462812118074) (-58); Float radix2 (5051224466184918) (-63); Float radix2 (-5317296099465510) (-57);
          Float radix2 (-8493044077633789) (-58); Float radix2 (-8653372030291983) (-61); Float radix2 (6557397063108422) (-58); Float radix2 (-4720083909489096) (-60); Float radix2 (-6481547109530631) (-58);
          Float radix2 (-5946442071589170) (-68); Float radix2 (-6820991370979537) (-58); Float radix2 (7859363356467028) (-64); Float radix2 (5905619140240408) (-60); Float radix2 (8194376824685340) (-58);
          Float radix2 (-8100387124417850) (-63); Float radix2 (-6192514087041253) (-59); Float radix2 (8939472581055462) (-62); Float radix2 (-6582863331598878) (-59); Float radix2 (-5033830414689625) (-60)];
      [:: Float radix2 (-5159588567717965) (-58); Float radix2 (-6277355111666405) (-60); Float radix2 (-7564265102940564) (-58); Float radix2 (-6867187410661832) (-60);
          Float radix2 (-8198994276820730) (-58); Float radix2 (5932610483345586) (-57); Float radix2 (-4605152911020776) (-61); Float radix2 (4887431164695802) (-52); Float radix2 (8862299262408440) (-60);
          Float radix2 (-6843942456001701) (-62); Float radix2 (-4999809948633002) (-62); Float radix2 (-7214586904471519) (-58); Float radix2 (4993800029176661) (-58); Float radix2 (7953767701607658) (-61);
          Float radix2 (-8313544283269458) (-59); Float radix2 (5408737189534644) (-62); Float radix2 (7499408070502758) (-58); Float radix2 (5253249982466977) (-61); Float radix2 (5548655769056458) (-57);
          Float radix2 (-8327448456206470) (-58); Float radix2 (-8526889667847244) (-60); Float radix2 (-5494060314063300) (-57); Float radix2 (5254032089221036) (-61); Float radix2 (7394406686228207) (-59);
          Float radix2 (-5687053629014304) (-57); Float radix2 (7564069343359153) (-60); Float radix2 (-4686654023653189) (-60); Float radix2 (-6870871849348119) (-58); Float radix2 (8540499966029261) (-58);
          Float radix2 (4844387800866581) (-60); Float radix2 (-7110167990082442) (-59); Float radix2 (8022312083160281) (-60); Float radix2 (5675826359606285) (-59); Float radix2 (-5888132686789721) (-58);
          Float radix2 (-8206693663761531) (-64)];
      [:: Float radix2 (-4931114837325580) (-60); Float radix2 (-6198033076874567) (-58); Float radix2 (-4627268335839618) (-60); Float radix2 (-6875110780351578) (-57);
          Float radix2 (-8917545173732781) (-63); Float radix2 (-8448278107917695) (-63); Float radix2 (6977733891504202) (-58); Float radix2 (8862299262408440) (-60); Float radix2 (8431405105806416) (-53);
          Float radix2 (6713005263277066) (-62); Float radix2 (-7295592445084842) (-58); Float radix2 (-5671288925019050) (-62); Float radix2 (5126192644019724) (-61); Float radix2 (-4545208245129432) (-55);
          Float radix2 (-6895777524148143) (-61); Float radix2 (4617336084225538) (-59); Float radix2 (-8354153524074992) (-65); Float radix2 (5393448919784923) (-57); Float radix2 (5013699710087359) (-58);
          Float radix2 (-4612908164501594) (-60); Float radix2 (-7897918614283815) (-58); Float radix2 (-5493351397420103) (-59); Float radix2 (6900083588850960) (-60); Float radix2 (7324982675253623) (-60);
          Float radix2 (-7684833257450936) (-61); Float radix2 (4692312418424077) (-62); Float radix2 (-6978764518402699) (-58); Float radix2 (-8378353012958665) (-59); Float radix2 (5203153271691735) (-61);
          Float radix2 (-7614272600210628) (-58); Float radix2 (-6596855755729763) (-61); Float radix2 (6694328824514921) (-62); Float radix2 (7707980789018594) (-59); Float radix2 (-5836438995781107) (-60);
          Float radix2 (-6625825400594019) (-60)];
      [:: Float radix2 (-7354821284144091) (-55); Float radix2 (6719265591752822) (-61); Float radix2 (7879845315376648) (-56); Float radix2 (4649513214171855) (-60); Float radix2 (8412471880727991) (-57);
          Float radix2 (-6784577197873266) (-60); Float radix2 (-5219504059048359) (-62); Float radix2 (-6843942456001701) (-62); Float radix2 (6713005263277066) (-62); Float radix2 (7167334733145703) (-53);
          Float radix2 (6975262137444300) (-61); Float radix2 (7581081612584873) (-57); Float radix2 (-8781604133199894) (-59); Float radix2 (-4585928136490982) (-60); Float radix2 (-8893527330139454) (-56);
          Float radix2 (-7347706312633982) (-58); Float radix2 (5409853594733123) (-60); Float radix2 (-8351442331563962) (-62); Float radix2 (6453878096305544) (-61); Float radix2 (-6750803805638971) (-61);
          Float radix2 (6052475108826878) (-60); Float radix2 (-7450360130775002) (-62); Float radix2 (-8900297841925059) (-58); Float radix2 (-6056183681406527) (-59); Float radix2 (-6032885070787185) (-61);
          Float radix2 (7883460567542657) (-56); Float radix2 (6782888384205992) (-63); Float radix2 (5475772845977994) (-57); Float radix2 (-6079651306744070) (-59); Float radix2 (6139722813412647) (-62);
          Float radix2 (8924406917047022) (-59); Float radix2 (5563161997513331) (-60); Float radix2 (5973687799965329) (-63); Float radix2 (6098486017815159) (-61); Float radix2 (5731384728303096) (-56)];
      [:: Float radix2 (-8178491482311809) (-64); Float radix2 (8405443995422055) (-57); Float radix2 (8435425263974828) (-62); Float radix2 (6815726348070503) (-59); Float radix2 (8833232778404643) (-60);
          Float radix2 (-7744130900368848) (-60); Float radix2 (-5814224090907956) (-57); Float radix2 (-4999809948633002) (-62); Float radix2 (-7295592445084842) (-58); Float radix2 (6975262137444300) (-61);
          Float radix2 (4935059635942523) (-52); Float radix2 (8756526066990948) (-61); Float radix2 (-8768341225254869) (-60); Float radix2 (-6764926154353873) (-57); Float radix2 (6244588938361010) (-59);
          Float radix2 (-5279511131799277) (-58); Float radix2 (-6008134375294141) (-57); Float radix2 (-5637963909734539) (-59); Float radix2 (-5505304714352070) (-57); Float radix2 (6953438173920171) (-58);
          Float radix2 (-5202146941190046) (-60); Float radix2 (7116895621508856) (-59); Float radix2 (-7778310105085064) (-58); Float radix2 (-6597934672519133) (-57); Float radix2 (5881980068916478) (-57);
          Float radix2 (6044155705117596) (-60); Float radix2 (4734867202506566) (-57); Float radix2 (7150938230564770) (-60); Float radix2 (-8695023495997368) (-61); Float radix2 (-4533863868550823) (-58);
          Float radix2 (4624941156619394) (-58); Float radix2 (-8970634281622268) (-62); Float radix2 (-7365924342327502) (-58); Float radix2 (5658011789286759) (-59); Float radix2 (5099490020020974) (-59)];
      [:: Float radix2 (6588345257080901) (-60); Float radix2 (7960179432287573) (-63); Float radix2 (6784798422178857) (-57); Float radix2 (4830781126261447) (-59); Float radix2 (-7256472582996773) (-57);
          Float radix2 (-4604486246328463) (-59); Float radix2 (7708473722184499) (-62); Float radix2 (-7214586904471519) (-58); Float radix2 (-5671288925019050) (-62); Float radix2 (7581081612584873) (-57);
          Float radix2 (8756526066990948) (-61); Float radix2 (8517220156695673) (-53); Float radix2 (-7384892293040157) (-58); Float radix2 (-6307140956670594) (-65); Float radix2 (-7484719353469238) (-57);
          Float radix2 (-4766922272256365) (-59); Float radix2 (-8399118444031282) (-60); Float radix2 (-8874200243543459) (-58); Float radix2 (-5877573225328990) (-59); Float radix2 (4610024477028551) (-61);
          Float radix2 (5069873052119435) (-59); Float radix2 (7528542467534131) (-60); Float radix2 (-5195597970842975) (-57); Float radix2 (-4818229744766802) (-60); Float radix2 (7732210625950622) (-59);
          Float radix2 (4947973537345177) (-58); Float radix2 (6709768440598246) (-60); Float radix2 (-4589960754425058) (-60); Float radix2 (-7303586319983576) (-59); Float radix2 (-7094793491073222) (-61);
          Float radix2 (-4518572111089271) (-62); Float radix2 (-5131956902384632) (-60); Float radix2 (-8152157559149795) (-60); Float radix2 (5326427555737276) (-59); Float radix2 (-7698304735706010) (-59)];
      [:: Float radix2 (5944025091388110) (-58); Float radix2 (-5241762759586644) (-61); Float radix2 (7488928149021427) (-61); Float radix2 (-7164527652227812) (-62); Float radix2 (-5934265100687522) (-60);
          Float radix2 (-4750914567334418) (-54); Float radix2 (5521664124350374) (-60); Float radix2 (4993800029176661) (-58); Float radix2 (5126192644019724) (-61); Float radix2 (-8781604133199894) (-59);
          Float radix2 (-8768341225254869) (-60); Float radix2 (-7384892293040157) (-58); Float radix2 (6928409724737799) (-53); Float radix2 (7149337608788955) (-59); Float radix2 (-5120670853444418) (-58);
          Float radix2 (-7978925741967885) (-63); Float radix2 (-7060699366533622) (-62); Float radix2 (8911409368494647) (-61); Float radix2 (6249109076865629) (-61); Float radix2 (-4928670869045309) (-58);
          Float radix2 (-6623088652449508) (-59); Float radix2 (-6722992572304046) (-58); Float radix2 (7785397176280393) (-61); Float radix2 (7557364509922231) (-58); Float radix2 (-7668205220715809) (-57);
          Float radix2 (6096688338324116) (-63); Float radix2 (-5196470718968794) (-61); Float radix2 (-6055703858434278) (-60); Float radix2 (-6424042962021901) (-61); Float radix2 (6440486667704297) (-59);
          Float radix2 (-8407029030268321) (-58); Float radix2 (5098361265345352) (-60); Float radix2 (8065429762292332) (-61); Float radix2 (-6867960650284458) (-59); Float radix2 (-5128700895915827) (-60)];
      [:: Float radix2 (-8461975588223993) (-61); Float radix2 (-4803585793731932) (-58); Float radix2 (4760500721357682) (-65); Float radix2 (-8625052088706654) (-60); Float radix2 (-8473935841918097) (-61);
          Float radix2 (7804762846964525) (-63); Float radix2 (5086145084159217) (-57); Float radix2 (7953767701607658) (-61); Float radix2 (-4545208245129432) (-55); Float radix2 (-4585928136490982) (-60);
          Float radix2 (-6764926154353873) (-57); Float radix2 (-6307140956670594) (-65); Float radix2 (7149337608788955) (-59); Float radix2 (8464054268287132) (-53); Float radix2 (-8753495331610589) (-61);
          Float radix2 (5044933016363529) (-59); Float radix2 (5726055293110507) (-62); Float radix2 (4984916702172169) (-59); Float radix2 (8662788001580701) (-60); Float radix2 (-6324836227842804) (-58);
          Float radix2 (-4963675723207822) (-57); Float radix2 (-7981383620176191) (-61); Float radix2 (5382412939951708) (-57); Float radix2 (6828251067190893) (-59); Float radix2 (-4728399984202940) (-58);
          Float radix2 (7755178853663395) (-64); Float radix2 (-6549945009880701) (-59); Float radix2 (-8101108203458347) (-61); Float radix2 (8145393308112384) (-59); Float radix2 (-6831237428642647) (-58);
          Float radix2 (-8746735125265330) (-59); Float radix2 (6576190340003877) (-62); Float radix2 (4704023918854727) (-59); Float radix2 (-5915150968428948) (-59); Float radix2 (-6670367064548203) (-60)];
      [:: Float radix2 (-6568705447492194) (-58); Float radix2 (8450352010415979) (-61); Float radix2 (6749241428591227) (-57); Float radix2 (5874777060519231) (-60); Float radix2 (-6176278488506899) (-58);
          Float radix2 (4568425844439156) (-63); Float radix2 (-6635811946391457) (-60); Float radix2 (-8313544283269458) (-59); Float radix2 (-6895777524148143) (-61); Float radix2 (-8893527330139454) (-56);
          Float radix2 (6244588938361010) (-59); Float radix2 (-7484719353469238) (-57); Float radix2 (-5120670853444418) (-58); Float radix2 (-8753495331610589) (-61); Float radix2 (4568712041256524) (-53);
          Float radix2 (-6100564596673815) (-63); Float radix2 (-6012939198737629) (-61); Float radix2 (-7269030621822830) (-60); Float radix2 (-8175840755747912) (-61); Float radix2 (6831714338350268) (-60);
          Float radix2 (8668699146590164) (-59); Float radix2 (5754785727384975) (-59); Float radix2 (-4982612470564168) (-57); Float radix2 (-7449993847953119) (-60); Float radix2 (7205210144027715) (-59);
          Float radix2 (8818879112409731) (-57); Float radix2 (4509311266889734) (-59); Float radix2 (-7960182446040696) (-60); Float radix2 (-8890692337596229) (-59); Float radix2 (-5931689018835261) (-59);
          Float radix2 (-5446134544788932) (-57); Float radix2 (-6339798675991341) (-61); Float radix2 (-6749276946966837) (-60); Float radix2 (4575532916125241) (-58); Float radix2 (-4954967325270290) (-59)];
      [:: Float radix2 (-6967046967161806) (-58); Float radix2 (-5276279573545719) (-56); Float radix2 (-8122257469506310) (-57); Float radix2 (6758519285354963) (-61); Float radix2 (-7082057269840988) (-62);
          Float radix2 (5979245880695135) (-59); Float radix2 (5523441676143573) (-57); Float radix2 (5408737189534644) (-62); Float radix2 (4617336084225538) (-59); Float radix2 (-7347706312633982) (-58);
          Float radix2 (-5279511131799277) (-58); Float radix2 (-4766922272256365) (-59); Float radix2 (-7978925741967885) (-63); Float radix2 (5044933016363529) (-59); Float radix2 (-6100564596673815) (-63);
          Float radix2 (8743884809476505) (-54); Float radix2 (6233216176930602) (-57); Float radix2 (-8085535736056355) (-62); Float radix2 (8111473609185043) (-60); Float radix2 (-5080314771577110) (-56);
          Float radix2 (-8059225083941385) (-61); Float radix2 (-4646145086487770) (-60); Float radix2 (-8452532212769776) (-58); Float radix2 (7477374311161263) (-61); Float radix2 (-5314842641151528) (-59);
          Float radix2 (-8093861353782361) (-58); Float radix2 (-5634556711229719) (-57); Float radix2 (-8911810349570188) (-60); Float radix2 (6680973997191003) (-59); Float radix2 (-5087260572259764) (-62);
          Float radix2 (-4625339702895069) (-59); Float radix2 (-6301523242698668) (-54); Float radix2 (6042713986939664) (-59); Float radix2 (-6355784736326387) (-58); Float radix2 (-4973783275457683) (-59)];
      [:: Float radix2 (-5883318804343310) (-57); Float radix2 (-5262063236568881) (-55); Float radix2 (-4703893120704933) (-57); Float radix2 (-7394729697917917) (-58);
          Float radix2 (-8438493484548458) (-59); Float radix2 (6158489870792966) (-57); Float radix2 (-5531729392814709) (-64); Float radix2 (7499408070502758) (-58); Float radix2 (-8354153524074992) (-65);
          Float radix2 (5409853594733123) (-60); Float radix2 (-6008134375294141) (-57); Float radix2 (-8399118444031282) (-60); Float radix2 (-7060699366533622) (-62); Float radix2 (5726055293110507) (-62);
          Float radix2 (-6012939198737629) (-61); Float radix2 (6233216176930602) (-57); Float radix2 (4578564396324818) (-52); Float radix2 (6122155681145367) (-58); Float radix2 (-5512409938483148) (-58);
          Float radix2 (-5496139445954873) (-58); Float radix2 (-6490517182468588) (-58); Float radix2 (-5321896003666315) (-61); Float radix2 (6078727437302366) (-59); Float radix2 (4945447289646592) (-57);
          Float radix2 (-8847808018126878) (-60); Float radix2 (-8460717161516971) (-58); Float radix2 (-6510634343789394) (-56); Float radix2 (-6301360226329954) (-58); Float radix2 (6421695838972408) (-58);
          Float radix2 (-6146123055482762) (-60); Float radix2 (-4522548092923158) (-59); Float radix2 (8324627759577981) (-59); Float radix2 (-6409070738052936) (-59); Float radix2 (-6008864462078564) (-59);
          Float radix2 (-5994107462158557) (-58)];
      [:: Float radix2 (-7122825209740845) (-59); Float radix2 (-5712051443460551) (-57); Float radix2 (-7210972096460403) (-57); Float radix2 (-4814259184620201) (-57);
          Float radix2 (-7330098486852007) (-57); Float radix2 (5487082178189390) (-61); Float radix2 (6971462812118074) (-58); Float radix2 (5253249982466977) (-61); Float radix2 (5393448919784923) (-57);
          Float radix2 (-8351442331563962) (-62); Float radix2 (-5637963909734539) (-59); Float radix2 (-8874200243543459) (-58); Float radix2 (8911409368494647) (-61); Float radix2 (4984916702172169) (-59);
          Float radix2 (-7269030621822830) (-60); Float radix2 (-8085535736056355) (-62); Float radix2 (6122155681145367) (-58); Float radix2 (4631040719865023) (-52); Float radix2 (4870494831297063) (-57);
          Float radix2 (-5463869379597813) (-58); Float radix2 (-8985168803906909) (-61); Float radix2 (-8486480497976401) (-58); Float radix2 (5666520667169283) (-57); Float radix2 (7898257554732515) (-60);
          Float radix2 (-6441947193944638) (-59); Float radix2 (-7018782598344227) (-61); Float radix2 (-8481383541690514) (-58); Float radix2 (-7836578604654379) (-57); Float radix2 (6805145795240910) (-60);
          Float radix2 (7034183206969981) (-59); Float radix2 (-4923513343163087) (-58); Float radix2 (5832024691115991) (-59); Float radix2 (4581804371011370) (-58); Float radix2 (-7116516637258538) (-58);
          Float radix2 (-4592564266098837) (-58)];
      [:: Float radix2 (-4705362910783311) (-59); Float radix2 (-5207058100076011) (-57); Float radix2 (-4904599098578396) (-57); Float radix2 (-6146501687222052) (-56);
          Float radix2 (-5269619711826117) (-60); Float radix2 (5711581568332730) (-59); Float radix2 (5051224466184918) (-63); Float radix2 (5548655769056458) (-57); Float radix2 (5013699710087359) (-58);
          Float radix2 (6453878096305544) (-61); Float radix2 (-5505304714352070) (-57); Float radix2 (-5877573225328990) (-59); Float radix2 (6249109076865629) (-61); Float radix2 (8662788001580701) (-60);
          Float radix2 (-8175840755747912) (-61); Float radix2 (8111473609185043) (-60); Float radix2 (-5512409938483148) (-58); Float radix2 (4870494831297063) (-57); Float radix2 (8513882595668861) (-53);
          Float radix2 (-6199676612903043) (-60); Float radix2 (-6478634240196011) (-58); Float radix2 (-5229489669341165) (-58); Float radix2 (7333694874541383) (-60); Float radix2 (-7264154959101802) (-58);
          Float radix2 (-8838640323164375) (-60); Float radix2 (6585711711933162) (-62); Float radix2 (-7211734062631992) (-57); Float radix2 (-6039529401090514) (-58); Float radix2 (8433270928372334) (-60);
          Float radix2 (7063975374202625) (-59); Float radix2 (-5333006808883480) (-60); Float radix2 (4744605881947415) (-60); Float radix2 (-8414009049843652) (-56); Float radix2 (-7259953232377783) (-60);
          Float radix2 (-5881589636544012) (-62)];
      [:: Float radix2 (6730265665484937) (-61); Float radix2 (7485375033378406) (-57); Float radix2 (4658669709821335) (-60); Float radix2 (-5292590115958625) (-61); Float radix2 (7289447407929700) (-60);
          Float radix2 (-8837385070632621) (-57); Float radix2 (-5317296099465510) (-57); Float radix2 (-8327448456206470) (-58); Float radix2 (-4612908164501594) (-60);
          Float radix2 (-6750803805638971) (-61); Float radix2 (6953438173920171) (-58); Float radix2 (4610024477028551) (-61); Float radix2 (-4928670869045309) (-58); Float radix2 (-6324836227842804) (-58);
          Float radix2 (6831714338350268) (-60); Float radix2 (-5080314771577110) (-56); Float radix2 (-5496139445954873) (-58); Float radix2 (-5463869379597813) (-58); Float radix2 (-6199676612903043) (-60);
          Float radix2 (8412940108662351) (-53); Float radix2 (8388434353791316) (-61); Float radix2 (7932689865174135) (-58); Float radix2 (-5564379855878448) (-57); Float radix2 (-6006421948063065) (-61);
          Float radix2 (-5850496629882871) (-57); Float radix2 (6980677402326155) (-59); Float radix2 (5914450350758001) (-58); Float radix2 (5486181163162092) (-61); Float radix2 (-8306351848804065) (-57);
          Float radix2 (-6203956894906021) (-59); Float radix2 (5066927710245013) (-60); Float radix2 (-6935513610998852) (-59); Float radix2 (-5015871945332737) (-59); Float radix2 (-6639482490809418) (-57);
          Float radix2 (6977914357137050) (-59)];
      [:: Float radix2 (-5949632433843820) (-62); Float radix2 (-8562069243083717) (-60); Float radix2 (4958807650707688) (-59); Float radix2 (8497124948679090) (-64); Float radix2 (8114362825636645) (-59);
          Float radix2 (-8002865934487872) (-59); Float radix2 (-8493044077633789) (-58); Float radix2 (-8526889667847244) (-60); Float radix2 (-7897918614283815) (-58); Float radix2 (6052475108826878) (-60);
          Float radix2 (-5202146941190046) (-60); Float radix2 (5069873052119435) (-59); Float radix2 (-6623088652449508) (-59); Float radix2 (-4963675723207822) (-57); Float radix2 (8668699146590164) (-59);
          Float radix2 (-8059225083941385) (-61); Float radix2 (-6490517182468588) (-58); Float radix2 (-8985168803906909) (-61); Float radix2 (-6478634240196011) (-58); Float radix2 (8388434353791316) (-61);
          Float radix2 (4887726331095142) (-52); Float radix2 (7947778048429753) (-61); Float radix2 (-4639530532707294) (-60); Float radix2 (-7539220818752949) (-59); Float radix2 (8682789800478703) (-59);
          Float radix2 (-8092802351007176) (-61); Float radix2 (-7891935903492275) (-61); Float radix2 (4801418309862585) (-59); Float radix2 (-7302480004597008) (-59); Float radix2 (-6297827804854500) (-58);
          Float radix2 (5559412397351294) (-59); Float radix2 (-4709207325162500) (-61); Float radix2 (-6419166852205714) (-58); Float radix2 (4598161021719893) (-59); Float radix2 (6326069708770137) (-59)];
      [:: Float radix2 (-5067837646303356) (-60); Float radix2 (6160434642641930) (-60); Float radix2 (-5383356411112396) (-60); Float radix2 (7642213521889024) (-58); Float radix2 (6198230228733664) (-59);
          Float radix2 (-5653053283910742) (-60); Float radix2 (-8653372030291983) (-61); Float radix2 (-5494060314063300) (-57); Float radix2 (-5493351397420103) (-59);
          Float radix2 (-7450360130775002) (-62); Float radix2 (7116895621508856) (-59); Float radix2 (7528542467534131) (-60); Float radix2 (-6722992572304046) (-58); Float radix2 (-7981383620176191) (-61);
          Float radix2 (5754785727384975) (-59); Float radix2 (-4646145086487770) (-60); Float radix2 (-5321896003666315) (-61); Float radix2 (-8486480497976401) (-58); Float radix2 (-5229489669341165) (-58);
          Float radix2 (7932689865174135) (-58); Float radix2 (7947778048429753) (-61); Float radix2 (4595559357521213) (-52); Float radix2 (-7225102604027896) (-59); Float radix2 (-6380258493410434) (-60);
          Float radix2 (-7027168824688157) (-58); Float radix2 (-8409581360489134) (-62); Float radix2 (6351241724506392) (-59); Float radix2 (7366076884010916) (-59); Float radix2 (-6134944852995568) (-58);
          Float radix2 (-5620018813279283) (-60); Float radix2 (4676440282458263) (-59); Float radix2 (-5443622212464147) (-59); Float radix2 (-6340424781237710) (-60); Float radix2 (-6609175249960636) (-58);
          Float radix2 (7317335460458723) (-59)];
      [:: Float radix2 (5181573916732463) (-60); Float radix2 (-4888472943166285) (-58); Float radix2 (-6893288150263804) (-59); Float radix2 (7684642548563593) (-62); Float radix2 (-5338135386744968) (-59);
          Float radix2 (-7803014757952139) (-65); Float radix2 (6557397063108422) (-58); Float radix2 (5254032089221036) (-61); Float radix2 (6900083588850960) (-60); Float radix2 (-8900297841925059) (-58);
          Float radix2 (-7778310105085064) (-58); Float radix2 (-5195597970842975) (-57); Float radix2 (7785397176280393) (-61); Float radix2 (5382412939951708) (-57); Float radix2 (-4982612470564168) (-57);
          Float radix2 (-8452532212769776) (-58); Float radix2 (6078727437302366) (-59); Float radix2 (5666520667169283) (-57); Float radix2 (7333694874541383) (-60); Float radix2 (-5564379855878448) (-57);
          Float radix2 (-4639530532707294) (-60); Float radix2 (-7225102604027896) (-59); Float radix2 (4536591466704827) (-52); Float radix2 (4747245574336447) (-58); Float radix2 (-6999854997707730) (-57);
          Float radix2 (-5483090463772583) (-59); Float radix2 (-5798882733716080) (-59); Float radix2 (-5282746672916282) (-58); Float radix2 (8948521762385279) (-60); Float radix2 (6763216118894219) (-59);
          Float radix2 (-6102555967356045) (-57); Float radix2 (7730750403547324) (-59); Float radix2 (6845952524639821) (-59); Float radix2 (-8293665449696832) (-58); Float radix2 (-8568121636531293) (-59)];
      [:: Float radix2 (6862485057834478) (-65); Float radix2 (-8674900283127138) (-59); Float radix2 (-8866881211149593) (-63); Float radix2 (-5293641603171228) (-58); Float radix2 (-6531618570648909) (-60);
          Float radix2 (6862985973342458) (-61); Float radix2 (-4720083909489096) (-60); Float radix2 (7394406686228207) (-59); Float radix2 (7324982675253623) (-60); Float radix2 (-6056183681406527) (-59);
          Float radix2 (-6597934672519133) (-57); Float radix2 (-4818229744766802) (-60); Float radix2 (7557364509922231) (-58); Float radix2 (6828251067190893) (-59); Float radix2 (-7449993847953119) (-60);
          Float radix2 (7477374311161263) (-61); Float radix2 (4945447289646592) (-57); Float radix2 (7898257554732515) (-60); Float radix2 (-7264154959101802) (-58); Float radix2 (-6006421948063065) (-61);
          Float radix2 (-7539220818752949) (-59); Float radix2 (-6380258493410434) (-60); Float radix2 (4747245574336447) (-58); Float radix2 (4609446855370198) (-52); Float radix2 (-5436074542707389) (-58);
          Float radix2 (-5589184145935569) (-62); Float radix2 (-6901149208251840) (-58); Float radix2 (-5603137236336308) (-60); Float radix2 (6390039530099393) (-59); Float radix2 (8192010021404664) (-60);
          Float radix2 (-6503737397991459) (-59); Float radix2 (6606666051946033) (-60); Float radix2 (-6075649495273776) (-58); Float radix2 (-7142406058934399) (-60); Float radix2 (-8029554550752268) (-60)];
      [:: Float radix2 (-5185768042465135) (-61); Float radix2 (8542613821174353) (-59); Float radix2 (6306085435507872) (-60); Float radix2 (7320647348393100) (-61); Float radix2 (4652503742414448) (-59);
          Float radix2 (-7533594346948033) (-59); Float radix2 (-6481547109530631) (-58); Float radix2 (-5687053629014304) (-57); Float radix2 (-7684833257450936) (-61);
          Float radix2 (-6032885070787185) (-61); Float radix2 (5881980068916478) (-57); Float radix2 (7732210625950622) (-59); Float radix2 (-7668205220715809) (-57); Float radix2 (-4728399984202940) (-58);
          Float radix2 (7205210144027715) (-59); Float radix2 (-5314842641151528) (-59); Float radix2 (-8847808018126878) (-60); Float radix2 (-6441947193944638) (-59); Float radix2 (-8838640323164375) (-60);
          Float radix2 (-5850496629882871) (-57); Float radix2 (8682789800478703) (-59); Float radix2 (-7027168824688157) (-58); Float radix2 (-6999854997707730) (-57); Float radix2 (-5436074542707389) (-58);
          Float radix2 (8400465650395621) (-53); Float radix2 (6066646387439147) (-61); Float radix2 (5902274491633825) (-59); Float radix2 (5299075850777317) (-59); Float radix2 (-5254058878260702) (-57);
          Float radix2 (-6295689591246655) (-59); Float radix2 (7306721535929430) (-58); Float radix2 (-7019744823433178) (-61); Float radix2 (-8855555958644283) (-60); Float radix2 (-8516645493777699) (-56);
          Float radix2 (7163636509631833) (-59)];
      [:: Float radix2 (-8484330173520993) (-55); Float radix2 (7484103548263041) (-58); Float radix2 (5453647653997608) (-56); Float radix2 (-4748020439419376) (-66); Float radix2 (8449593709356208) (-57);
          Float radix2 (-5347573023869073) (-57); Float radix2 (-5946442071589170) (-68); Float radix2 (7564069343359153) (-60); Float radix2 (4692312418424077) (-62); Float radix2 (7883460567542657) (-56);
          Float radix2 (6044155705117596) (-60); Float radix2 (4947973537345177) (-58); Float radix2 (6096688338324116) (-63); Float radix2 (7755178853663395) (-64); Float radix2 (8818879112409731) (-57);
          Float radix2 (-8093861353782361) (-58); Float radix2 (-8460717161516971) (-58); Float radix2 (-7018782598344227) (-61); Float radix2 (6585711711933162) (-62); Float radix2 (6980677402326155) (-59);
          Float radix2 (-8092802351007176) (-61); Float radix2 (-8409581360489134) (-62); Float radix2 (-5483090463772583) (-59); Float radix2 (-5589184145935569) (-62); Float radix2 (6066646387439147) (-61);
          Float radix2 (6318957824145272) (-53); Float radix2 (5290743779001394) (-59); Float radix2 (4891850418938320) (-57); Float radix2 (-5428434833273956) (-58); Float radix2 (4552971403904251) (-61);
          Float radix2 (8950710108942693) (-58); Float radix2 (-4593334504745570) (-57); Float radix2 (-5361312510395852) (-57); Float radix2 (-4568696746587290) (-66); Float radix2 (-7807138951486828) (-55)];
      [:: Float radix2 (4664990395501441) (-60); Float radix2 (-8563867698723896) (-59); Float radix2 (7009045353064656) (-60); Float radix2 (-6742999695706110) (-60); Float radix2 (8873702242274584) (-59);
          Float radix2 (-8573771434234696) (-60); Float radix2 (-6820991370979537) (-58); Float radix2 (-4686654023653189) (-60); Float radix2 (-6978764518402699) (-58); Float radix2 (6782888384205992) (-63);
          Float radix2 (4734867202506566) (-57); Float radix2 (6709768440598246) (-60); Float radix2 (-5196470718968794) (-61); Float radix2 (-6549945009880701) (-59); Float radix2 (4509311266889734) (-59);
          Float radix2 (-5634556711229719) (-57); Float radix2 (-6510634343789394) (-56); Float radix2 (-8481383541690514) (-58); Float radix2 (-7211734062631992) (-57); Float radix2 (5914450350758001) (-58);
          Float radix2 (-7891935903492275) (-61); Float radix2 (6351241724506392) (-59); Float radix2 (-5798882733716080) (-59); Float radix2 (-6901149208251840) (-58); Float radix2 (5902274491633825) (-59);
          Float radix2 (5290743779001394) (-59); Float radix2 (4657405260136479) (-52); Float radix2 (6839240760755112) (-59); Float radix2 (-5794766802253475) (-59); Float radix2 (-8021479260409048) (-58);
          Float radix2 (6064989680462334) (-59); Float radix2 (-6227954707484199) (-57); Float radix2 (-7111065065388154) (-56); Float radix2 (5524997004904658) (-57); Float radix2 (4523830379650100) (-57)];
      [:: Float radix2 (-6803106471437698) (-59); Float radix2 (6219262727315090) (-62); Float radix2 (5116135845666350) (-59); Float radix2 (6467361502754368) (-58); Float radix2 (-5560536192904777) (-57);
          Float radix2 (-4946956543689282) (-59); Float radix2 (7859363356467028) (-64); Float radix2 (-6870871849348119) (-58); Float radix2 (-8378353012958665) (-59); Float radix2 (5475772845977994) (-57);
          Float radix2 (7150938230564770) (-60); Float radix2 (-4589960754425058) (-60); Float radix2 (-6055703858434278) (-60); Float radix2 (-8101108203458347) (-61); Float radix2 (-7960182446040696) (-60);
          Float radix2 (-8911810349570188) (-60); Float radix2 (-6301360226329954) (-58); Float radix2 (-7836578604654379) (-57); Float radix2 (-6039529401090514) (-58); Float radix2 (5486181163162092) (-61);
          Float radix2 (4801418309862585) (-59); Float radix2 (7366076884010916) (-59); Float radix2 (-5282746672916282) (-58); Float radix2 (-5603137236336308) (-60); Float radix2 (5299075850777317) (-59);
          Float radix2 (4891850418938320) (-57); Float radix2 (6839240760755112) (-59); Float radix2 (8516883002626477) (-53); Float radix2 (-6084607495931748) (-58); Float radix2 (-5012105178911385) (-60);
          Float radix2 (4955811229100140) (-61); Float radix2 (-4505046761672599) (-57); Float radix2 (-4804153403596400) (-58); Float radix2 (4900335781269930) (-58); Float radix2 (-5352589911130568) (-57)];
      [:: Float radix2 (-6277990303912070) (-58); Float radix2 (-4921057633548201) (-59); Float radix2 (-6722840933484610) (-61); Float radix2 (-5032715019038397) (-63);
          Float radix2 (-7310241944451472) (-60); Float radix2 (-7143285474641004) (-57); Float radix2 (5905619140240408) (-60); Float radix2 (8540499966029261) (-58); Float radix2 (5203153271691735) (-61);
          Float radix2 (-6079651306744070) (-59); Float radix2 (-8695023495997368) (-61); Float radix2 (-7303586319983576) (-59); Float radix2 (-6424042962021901) (-61); Float radix2 (8145393308112384) (-59);
          Float radix2 (-8890692337596229) (-59); Float radix2 (6680973997191003) (-59); Float radix2 (6421695838972408) (-58); Float radix2 (6805145795240910) (-60); Float radix2 (8433270928372334) (-60);
          Float radix2 (-8306351848804065) (-57); Float radix2 (-7302480004597008) (-59); Float radix2 (-6134944852995568) (-58); Float radix2 (8948521762385279) (-60); Float radix2 (6390039530099393) (-59);
          Float radix2 (-5254058878260702) (-57); Float radix2 (-5428434833273956) (-58); Float radix2 (-5794766802253475) (-59); Float radix2 (-6084607495931748) (-58); Float radix2 (4526782730768656) (-52);
          Float radix2 (4742259706785168) (-59); Float radix2 (-8435345746546200) (-58); Float radix2 (6889420923567203) (-59); Float radix2 (5258453606739826) (-57); Float radix2 (-4827970348131696) (-56);
          Float radix2 (-8811121688943077) (-58)];
      [:: Float radix2 (4541720166634813) (-60); Float radix2 (-7421943121368884) (-59); Float radix2 (4862297682823602) (-61); Float radix2 (-8715127238646429) (-59); Float radix2 (-5406730821905944) (-59);
          Float radix2 (-6615775759042921) (-62); Float radix2 (8194376824685340) (-58); Float radix2 (4844387800866581) (-60); Float radix2 (-7614272600210628) (-58); Float radix2 (6139722813412647) (-62);
          Float radix2 (-4533863868550823) (-58); Float radix2 (-7094793491073222) (-61); Float radix2 (6440486667704297) (-59); Float radix2 (-6831237428642647) (-58); Float radix2 (-5931689018835261) (-59);
          Float radix2 (-5087260572259764) (-62); Float radix2 (-6146123055482762) (-60); Float radix2 (7034183206969981) (-59); Float radix2 (7063975374202625) (-59); Float radix2 (-6203956894906021) (-59);
          Float radix2 (-6297827804854500) (-58); Float radix2 (-5620018813279283) (-60); Float radix2 (6763216118894219) (-59); Float radix2 (8192010021404664) (-60); Float radix2 (-6295689591246655) (-59);
          Float radix2 (4552971403904251) (-61); Float radix2 (-8021479260409048) (-58); Float radix2 (-5012105178911385) (-60); Float radix2 (4742259706785168) (-59); Float radix2 (4612689890239209) (-52);
          Float radix2 (-5794616929248311) (-60); Float radix2 (4950335867279399) (-58); Float radix2 (7647887503466057) (-59); Float radix2 (-8589234022073261) (-59); Float radix2 (-7388639568873813) (-59)];
      [:: Float radix2 (-6270136240798972) (-58); Float radix2 (6559314116117508) (-60); Float radix2 (5533600830736471) (-57); Float radix2 (4873511592831936) (-60); Float radix2 (-5387573365950041) (-60);
          Float radix2 (-8712023044943202) (-59); Float radix2 (-8100387124417850) (-63); Float radix2 (-7110167990082442) (-59); Float radix2 (-6596855755729763) (-61); Float radix2 (8924406917047022) (-59);
          Float radix2 (4624941156619394) (-58); Float radix2 (-4518572111089271) (-62); Float radix2 (-8407029030268321) (-58); Float radix2 (-8746735125265330) (-59); Float radix2 (-5446134544788932) (-57);
          Float radix2 (-4625339702895069) (-59); Float radix2 (-4522548092923158) (-59); Float radix2 (-4923513343163087) (-58); Float radix2 (-5333006808883480) (-60); Float radix2 (5066927710245013) (-60);
          Float radix2 (5559412397351294) (-59); Float radix2 (4676440282458263) (-59); Float radix2 (-6102555967356045) (-57); Float radix2 (-6503737397991459) (-59); Float radix2 (7306721535929430) (-58);
          Float radix2 (8950710108942693) (-58); Float radix2 (6064989680462334) (-59); Float radix2 (4955811229100140) (-61); Float radix2 (-8435345746546200) (-58); Float radix2 (-5794616929248311) (-60);
          Float radix2 (8561222113297284) (-53); Float radix2 (-6048214439207616) (-58); Float radix2 (-7277083357691165) (-59); Float radix2 (5228332224123435) (-58); Float radix2 (-4963889675640899) (-57)];
      [:: Float radix2 (5708641416327253) (-60); Float radix2 (-4609465268840614) (-59); Float radix2 (4685087017233202) (-58); Float radix2 (7615889291713915) (-60); Float radix2 (-5600123780875602) (-61);
          Float radix2 (5649531496189314) (-59); Float radix2 (-6192514087041253) (-59); Float radix2 (8022312083160281) (-60); Float radix2 (6694328824514921) (-62); Float radix2 (5563161997513331) (-60);
          Float radix2 (-8970634281622268) (-62); Float radix2 (-5131956902384632) (-60); Float radix2 (5098361265345352) (-60); Float radix2 (6576190340003877) (-62); Float radix2 (-6339798675991341) (-61);
          Float radix2 (-6301523242698668) (-54); Float radix2 (8324627759577981) (-59); Float radix2 (5832024691115991) (-59); Float radix2 (4744605881947415) (-60); Float radix2 (-6935513610998852) (-59);
          Float radix2 (-4709207325162500) (-61); Float radix2 (-5443622212464147) (-59); Float radix2 (7730750403547324) (-59); Float radix2 (6606666051946033) (-60); Float radix2 (-7019744823433178) (-61);
          Float radix2 (-4593334504745570) (-57); Float radix2 (-6227954707484199) (-57); Float radix2 (-4505046761672599) (-57); Float radix2 (6889420923567203) (-59); Float radix2 (4950335867279399) (-58);
          Float radix2 (-6048214439207616) (-58); Float radix2 (5754039302135893) (-53); Float radix2 (5290890936331768) (-57); Float radix2 (-6627363809839561) (-57); Float radix2 (-5193788451379052) (-57)];
      [:: Float radix2 (-4941811810265669) (-59); Float radix2 (-6749026478138281) (-57); Float radix2 (-5074699812125137) (-59); Float radix2 (-7994505573433851) (-59);
          Float radix2 (-4571062136939352) (-59); Float radix2 (6313274800757743) (-59); Float radix2 (8939472581055462) (-62); Float radix2 (5675826359606285) (-59); Float radix2 (7707980789018594) (-59);
          Float radix2 (5973687799965329) (-63); Float radix2 (-7365924342327502) (-58); Float radix2 (-8152157559149795) (-60); Float radix2 (8065429762292332) (-61); Float radix2 (4704023918854727) (-59);
          Float radix2 (-6749276946966837) (-60); Float radix2 (6042713986939664) (-59); Float radix2 (-6409070738052936) (-59); Float radix2 (4581804371011370) (-58); Float radix2 (-8414009049843652) (-56);
          Float radix2 (-5015871945332737) (-59); Float radix2 (-6419166852205714) (-58); Float radix2 (-6340424781237710) (-60); Float radix2 (6845952524639821) (-59); Float radix2 (-6075649495273776) (-58);
          Float radix2 (-8855555958644283) (-60); Float radix2 (-5361312510395852) (-57); Float radix2 (-7111065065388154) (-56); Float radix2 (-4804153403596400) (-58); Float radix2 (5258453606739826) (-57);
          Float radix2 (7647887503466057) (-59); Float radix2 (-7277083357691165) (-59); Float radix2 (5290890936331768) (-57); Float radix2 (8459816650497900) (-53); Float radix2 (-6814714779620365) (-58);
          Float radix2 (-7002652545937249) (-58)];
      [:: Float radix2 (-4771630765502464) (-60); Float radix2 (8228663750642723) (-59); Float radix2 (7992774080840037) (-60); Float radix2 (8140285263809966) (-61); Float radix2 (6190367946856795) (-59);
          Float radix2 (-6587423049902345) (-58); Float radix2 (-6582863331598878) (-59); Float radix2 (-5888132686789721) (-58); Float radix2 (-5836438995781107) (-60); Float radix2 (6098486017815159) (-61);
          Float radix2 (5658011789286759) (-59); Float radix2 (5326427555737276) (-59); Float radix2 (-6867960650284458) (-59); Float radix2 (-5915150968428948) (-59); Float radix2 (4575532916125241) (-58);
          Float radix2 (-6355784736326387) (-58); Float radix2 (-6008864462078564) (-59); Float radix2 (-7116516637258538) (-58); Float radix2 (-7259953232377783) (-60);
          Float radix2 (-6639482490809418) (-57); Float radix2 (4598161021719893) (-59); Float radix2 (-6609175249960636) (-58); Float radix2 (-8293665449696832) (-58); Float radix2 (-7142406058934399) (-60);
          Float radix2 (-8516645493777699) (-56); Float radix2 (-4568696746587290) (-66); Float radix2 (5524997004904658) (-57); Float radix2 (4900335781269930) (-58); Float radix2 (-4827970348131696) (-56);
          Float radix2 (-8589234022073261) (-59); Float radix2 (5228332224123435) (-58); Float radix2 (-6627363809839561) (-57); Float radix2 (-6814714779620365) (-58); Float radix2 (8306393908720505) (-53);
          Float radix2 (8354800077964592) (-58)];
      [:: Float radix2 (-8738214033659113) (-57); Float radix2 (5517847183251995) (-59); Float radix2 (7987339031999777) (-57); Float radix2 (8373839662416763) (-60); Float radix2 (-4870398793673857) (-59);
          Float radix2 (6640981809727570) (-63); Float radix2 (-5033830414689625) (-60); Float radix2 (-8206693663761531) (-64); Float radix2 (-6625825400594019) (-60); Float radix2 (5731384728303096) (-56);
          Float radix2 (5099490020020974) (-59); Float radix2 (-7698304735706010) (-59); Float radix2 (-5128700895915827) (-60); Float radix2 (-6670367064548203) (-60); Float radix2 (-4954967325270290) (-59);
          Float radix2 (-4973783275457683) (-59); Float radix2 (-5994107462158557) (-58); Float radix2 (-4592564266098837) (-58); Float radix2 (-5881589636544012) (-62); Float radix2 (6977914357137050) (-59);
          Float radix2 (6326069708770137) (-59); Float radix2 (7317335460458723) (-59); Float radix2 (-8568121636531293) (-59); Float radix2 (-8029554550752268) (-60); Float radix2 (7163636509631833) (-59);
          Float radix2 (-7807138951486828) (-55); Float radix2 (4523830379650100) (-57); Float radix2 (-5352589911130568) (-57); Float radix2 (-8811121688943077) (-58); Float radix2 (-7388639568873813) (-59);
          Float radix2 (-4963889675640899) (-57); Float radix2 (-5193788451379052) (-57); Float radix2 (-7002652545937249) (-58); Float radix2 (8354800077964592) (-58); Float radix2 (4619325037790885) (-53)]].

Time Eval vm_compute in map (map B2F) (cholesky m7).

(* size 45, positive definite *)
Definition m8 := map (map b64_normalize)
  [:: [:: Float radix2 (5634501000325769) (-54); Float radix2 (4551613732055798) (-62); Float radix2 (-5573498022286128) (-54); Float radix2 (-7383097951879188) (-58); Float radix2 (-7852224951391412) (-56);
          Float radix2 (-6182043157762072) (-57); Float radix2 (-6572508033330928) (-57); Float radix2 (-6080490340986404) (-57); Float radix2 (-7386726254675176) (-59); Float radix2 (7966587851151892) (-59);
          Float radix2 (-8002470523870614) (-57); Float radix2 (-7650744585040702) (-57); Float radix2 (-5765706170231300) (-57); Float radix2 (-5257004087507880) (-57);
          Float radix2 (-8437748680594542) (-58); Float radix2 (-8445439278622704) (-58); Float radix2 (-8465006557781832) (-58); Float radix2 (-4541971290842208) (-54);
          Float radix2 (-5339007384174714) (-56); Float radix2 (-7062122969746640) (-58); Float radix2 (-5930952263952290) (-57); Float radix2 (4808324460115096) (-60); Float radix2 (-8525482828466518) (-58);
          Float radix2 (5615288358367336) (-59); Float radix2 (-4737038720658120) (-56); Float radix2 (-5815735609972978) (-57); Float radix2 (-5783894486249982) (-57); Float radix2 (-8158432522499944) (-58);
          Float radix2 (-7577755907129754) (-58); Float radix2 (-7942647862844690) (-58); Float radix2 (-7122063683258006) (-56); Float radix2 (-5650959767140964) (-57);
          Float radix2 (-7457480049077902) (-62); Float radix2 (-7033985053027872) (-58); Float radix2 (8033732925470086) (-60); Float radix2 (-5446793921934910) (-56); Float radix2 (-8889975167257972) (-58);
          Float radix2 (-5133469146403844) (-57); Float radix2 (-8105636125466376) (-58); Float radix2 (-7443775803904786) (-57); Float radix2 (-7995631704009046) (-58);
          Float radix2 (-7361128551397682) (-60); Float radix2 (-4709532446408148) (-56); Float radix2 (-4528558144288422) (-57); Float radix2 (-7636973110341414) (-57)];
      [:: Float radix2 (4551613732055798) (-62); Float radix2 (7028522025748758) (-53); Float radix2 (-8196008047132306) (-57); Float radix2 (-5637546451226083) (-53); Float radix2 (-5511806352630790) (-56);
          Float radix2 (-5283801623631040) (-54); Float radix2 (-7808095593839752) (-57); Float radix2 (-8532495958392678) (-56); Float radix2 (-8095988051915882) (-57); Float radix2 (8093790047894330) (-58);
          Float radix2 (-5959304474877588) (-57); Float radix2 (-5670578927580478) (-59); Float radix2 (-6404124732742700) (-59); Float radix2 (-5714308178062366) (-59);
          Float radix2 (-8169256683658616) (-60); Float radix2 (-8500510623072442) (-59); Float radix2 (-5075619571537724) (-58); Float radix2 (-4701771230895522) (-56);
          Float radix2 (-7029236919720692) (-55); Float radix2 (-7899790543651092) (-58); Float radix2 (-7018700514771894) (-57); Float radix2 (-6146277029941110) (-59); Float radix2 (7067145423215922) (-60);
          Float radix2 (-5256079871112528) (-58); Float radix2 (5655550509397182) (-60); Float radix2 (-7079090153833342) (-58); Float radix2 (-8438556944167468) (-59); Float radix2 (-7210904052652538) (-60);
          Float radix2 (-4957368578917454) (-58); Float radix2 (-4567031615196384) (-58); Float radix2 (4579505801121752) (-62); Float radix2 (-7977716628387650) (-57); Float radix2 (4968495382205426) (-62);
          Float radix2 (4845789589756170) (-59); Float radix2 (-6563039445247458) (-59); Float radix2 (-5987699930397472) (-61); Float radix2 (-6388343512967440) (-59); Float radix2 (-7954900233296084) (-59);
          Float radix2 (-5642074975334222) (-59); Float radix2 (6455896965525616) (-59); Float radix2 (-6211350059734020) (-60); Float radix2 (-5487019684369790) (-59); Float radix2 (-4803003435055892) (-59);
          Float radix2 (-4826142269040368) (-59); Float radix2 (-7709312860808540) (-60)];
      [:: Float radix2 (-5573498022286128) (-54); Float radix2 (-8196008047132306) (-57); Float radix2 (6949385445399386) (-52); Float radix2 (-6212112507786636) (-56); Float radix2 (-8657987943563526) (-54);
          Float radix2 (-7175702321988178) (-58); Float radix2 (-4719104530508184) (-54); Float radix2 (5416510628552218) (-59); Float radix2 (-4985089781496220) (-55); Float radix2 (-6136437975350788) (-58);
          Float radix2 (5378320066414952) (-56); Float radix2 (6887253177999890) (-57); Float radix2 (8621953267924242) (-57); Float radix2 (5569123311939828) (-57); Float radix2 (5508834478946518) (-57);
          Float radix2 (5936706705534780) (-58); Float radix2 (8608251871411136) (-59); Float radix2 (7995370859567664) (-56); Float radix2 (4858156645224950) (-56); Float radix2 (-7691576603729194) (-57);
          Float radix2 (6921050415478540) (-57); Float radix2 (-6467661296102982) (-58); Float radix2 (5188948371493160) (-57); Float radix2 (5527841703869974) (-59); Float radix2 (6174144519554676) (-56);
          Float radix2 (5852898850748374) (-57); Float radix2 (5682603522922206) (-57); Float radix2 (6892203972192212) (-58); Float radix2 (4738635929574928) (-58); Float radix2 (5343970836185086) (-59);
          Float radix2 (7299237939284872) (-56); Float radix2 (8890162258480550) (-57); Float radix2 (8062685024174374) (-61); Float radix2 (4927591319735058) (-57); Float radix2 (5785559582623188) (-58);
          Float radix2 (6489189157878876) (-56); Float radix2 (7928578370295452) (-58); Float radix2 (8986421551191778) (-58); Float radix2 (8901663979041946) (-59); Float radix2 (6864498037078556) (-56);
          Float radix2 (5659011303437058) (-57); Float radix2 (5599799806874930) (-57); Float radix2 (5640259959985006) (-56); Float radix2 (4646072998687058) (-58); Float radix2 (5433649846264550) (-55)];
      [:: Float radix2 (-7383097951879188) (-58); Float radix2 (-5637546451226083) (-53); Float radix2 (-6212112507786636) (-56); Float radix2 (8453119394025261) (-52); Float radix2 (-4864837093906136) (-58);
          Float radix2 (-5524768078724750) (-54); Float radix2 (5228843248853404) (-58); Float radix2 (-7695302812136082) (-55); Float radix2 (6739030482924818) (-58); Float radix2 (8129171652716410) (-62);
          Float radix2 (8781108273512038) (-57); Float radix2 (4814413137162422) (-56); Float radix2 (5988198480847736) (-57); Float radix2 (6864440858511966) (-57); Float radix2 (6945719434029928) (-58);
          Float radix2 (5105969938142028) (-58); Float radix2 (6531988922397136) (-58); Float radix2 (5792093291630908) (-57); Float radix2 (-5920158939071762) (-58); Float radix2 (6391302534999480) (-57);
          Float radix2 (-6169761039264394) (-57); Float radix2 (8705525907347444) (-58); Float radix2 (-7122083654443804) (-57); Float radix2 (8339323153095870) (-59); Float radix2 (5079987227742868) (-62);
          Float radix2 (5920996506949334) (-57); Float radix2 (7756992882217432) (-58); Float radix2 (8541291694875872) (-59); Float radix2 (7371074393168852) (-59); Float radix2 (5262899293993306) (-58);
          Float radix2 (6836339045913012) (-58); Float radix2 (-8908950440229038) (-61); Float radix2 (6002374529926046) (-58); Float radix2 (-7617757374344892) (-58); Float radix2 (5821574197023788) (-59);
          Float radix2 (5938911389711198) (-60); Float radix2 (5544778852790110) (-58); Float radix2 (8143977921030682) (-59); Float radix2 (6356582013572330) (-59); Float radix2 (5759388251237058) (-60);
          Float radix2 (-5356376380708200) (-59); Float radix2 (8148240233131118) (-59); Float radix2 (7072629826201820) (-65); Float radix2 (5168509628756856) (-59); Float radix2 (7601802294109542) (-59)];
      [:: Float radix2 (-7852224951391412) (-56); Float radix2 (-5511806352630790) (-56); Float radix2 (-8657987943563526) (-54); Float radix2 (-4864837093906136) (-58); Float radix2 (4604632139595079) (-51);
          Float radix2 (7869854617472166) (-58); Float radix2 (-7491714583491664) (-55); Float radix2 (7230763720317298) (-58); Float radix2 (-7591137387749536) (-55); Float radix2 (-6108574151854706) (-64);
          Float radix2 (5925364808394106) (-56); Float radix2 (5306490709986154) (-56); Float radix2 (8925670030166958) (-57); Float radix2 (6860748433735648) (-57); Float radix2 (7434135477941474) (-58);
          Float radix2 (5612748042623706) (-57); Float radix2 (7036537865187080) (-57); Float radix2 (5928315651795864) (-56); Float radix2 (6527466083604292) (-56); Float radix2 (-5945228258664286) (-58);
          Float radix2 (7967149614527142) (-57); Float radix2 (-6203453114670840) (-57); Float radix2 (8422668461287778) (-58); Float radix2 (-5604482232757282) (-63); Float radix2 (6099518219014776) (-57);
          Float radix2 (5358399048928132) (-57); Float radix2 (5682146820057618) (-57); Float radix2 (5465078639147268) (-58); Float radix2 (4571400473328546) (-57); Float radix2 (6293216057432744) (-58);
          Float radix2 (7748192724884754) (-57); Float radix2 (6706528015657548) (-57); Float radix2 (-6695711639534094) (-59); Float radix2 (6882711435003516) (-58); Float radix2 (8429455490153796) (-59);
          Float radix2 (5335529682329294) (-57); Float radix2 (5455361668217462) (-58); Float radix2 (8430073304792180) (-58); Float radix2 (7835756930425692) (-59); Float radix2 (6196198118022848) (-57);
          Float radix2 (8534436610675266) (-58); Float radix2 (6338098853815494) (-57); Float radix2 (7617860154639514) (-58); Float radix2 (8141405791517510) (-59); Float radix2 (8892759711277622) (-56)];
      [:: Float radix2 (-6182043157762072) (-57); Float radix2 (-5283801623631040) (-54); Float radix2 (-7175702321988178) (-58); Float radix2 (-5524768078724750) (-54); Float radix2 (7869854617472166) (-58);
          Float radix2 (4764160321763588) (-51); Float radix2 (4965174645300354) (-57); Float radix2 (-5345723881507408) (-54); Float radix2 (7466601294625480) (-57); Float radix2 (-7887071010998084) (-61);
          Float radix2 (5281857839453832) (-56); Float radix2 (5408638446474756) (-56); Float radix2 (6741741105922490) (-57); Float radix2 (5911551592375430) (-57); Float radix2 (5518841881473022) (-57);
          Float radix2 (7741186964512184) (-57); Float radix2 (8080669701487210) (-57); Float radix2 (8536689088070836) (-57); Float radix2 (4665442947361932) (-59); Float radix2 (8026326184975096) (-57);
          Float radix2 (-8690825536796494) (-57); Float radix2 (8259640224363982) (-58); Float radix2 (-5710952398386776) (-56); Float radix2 (6959263348459706) (-57); Float radix2 (5310755887792582) (-60);
          Float radix2 (5365360500171582) (-57); Float radix2 (4631825137042246) (-57); Float radix2 (8441053137203036) (-58); Float radix2 (4766654946583158) (-57); Float radix2 (5171206845532138) (-57);
          Float radix2 (5158997231547168) (-58); Float radix2 (-5109747320025502) (-58); Float radix2 (6009511365794384) (-58); Float radix2 (-6719466415635180) (-57); Float radix2 (8711384157916658) (-58);
          Float radix2 (5739298782693944) (-59); Float radix2 (6224198836423194) (-58); Float radix2 (7527086327728516) (-58); Float radix2 (6947742095267796) (-58); Float radix2 (7222893343766008) (-59);
          Float radix2 (-8384857745883972) (-59); Float radix2 (8712389130460260) (-58); Float radix2 (4967216011789264) (-58); Float radix2 (7790784749200516) (-58); Float radix2 (5423200968213758) (-57)];
      [:: Float radix2 (-6572508033330928) (-57); Float radix2 (-7808095593839752) (-57); Float radix2 (-4719104530508184) (-54); Float radix2 (5228843248853404) (-58); Float radix2 (-7491714583491664) (-55);
          Float radix2 (4965174645300354) (-57); Float radix2 (4795258824037163) (-51); Float radix2 (6881873127471390) (-57); Float radix2 (-8258195722759220) (-56); Float radix2 (-5588613527817902) (-67);
          Float radix2 (5393923336351904) (-56); Float radix2 (5614276599544710) (-56); Float radix2 (6610586940146346) (-57); Float radix2 (4583946630689730) (-56); Float radix2 (8014616834182732) (-57);
          Float radix2 (5460929496687794) (-56); Float radix2 (6195392457961800) (-56); Float radix2 (5104975952430512) (-56); Float radix2 (6207380987888490) (-56); Float radix2 (-5051739922525640) (-58);
          Float radix2 (7250805679721336) (-57); Float radix2 (-6604554164935854) (-57); Float radix2 (8964005263948476) (-57); Float radix2 (7405704907638710) (-60); Float radix2 (8849223571282772) (-59);
          Float radix2 (4648201917564122) (-57); Float radix2 (7610429734117970) (-57); Float radix2 (4682437298053288) (-57); Float radix2 (7332748371156394) (-57); Float radix2 (7250367027643680) (-57);
          Float radix2 (4974501712952714) (-57); Float radix2 (5720628713137590) (-57); Float radix2 (-5764824956016892) (-59); Float radix2 (6037921306755300) (-57); Float radix2 (4915306166500066) (-58);
          Float radix2 (5471459243945480) (-58); Float radix2 (6575742313511470) (-58); Float radix2 (6070035659571174) (-57); Float radix2 (4969581528164432) (-57); Float radix2 (7160449112747158) (-57);
          Float radix2 (5687385804952588) (-57); Float radix2 (5796573647477834) (-57); Float radix2 (4614394612227160) (-57); Float radix2 (4920367658775482) (-57); Float radix2 (5077633779529286) (-55)];
      [:: Float radix2 (-6080490340986404) (-57); Float radix2 (-8532495958392678) (-56); Float radix2 (5416510628552218) (-59); Float radix2 (-7695302812136082) (-55); Float radix2 (7230763720317298) (-58);
          Float radix2 (-5345723881507408) (-54); Float radix2 (6881873127471390) (-57); Float radix2 (4840844444317174) (-51); Float radix2 (5955088693724458) (-55); Float radix2 (-8525921883271372) (-59);
          Float radix2 (4948924969418338) (-56); Float radix2 (4662425901793480) (-56); Float radix2 (8433914186436678) (-57); Float radix2 (5493575161297686) (-56); Float radix2 (5119749352278672) (-56);
          Float radix2 (6885661036201658) (-56); Float radix2 (5979604819406744) (-56); Float radix2 (7298834306446562) (-57); Float radix2 (6783628782863546) (-60); Float radix2 (7105006317325160) (-57);
          Float radix2 (-4913159140289116) (-56); Float radix2 (8340834543648028) (-57); Float radix2 (-6418503281475352) (-56); Float radix2 (7054286046007382) (-56); Float radix2 (6003447126424564) (-60);
          Float radix2 (7005061772400268) (-57); Float radix2 (7798854788351118) (-57); Float radix2 (6587798094353724) (-57); Float radix2 (4717820431872398) (-56); Float radix2 (4917514433306936) (-56);
          Float radix2 (7803282707720094) (-59); Float radix2 (-5734857445372008) (-58); Float radix2 (5924517600926180) (-57); Float radix2 (-8840859330066986) (-57); Float radix2 (5060463875971598) (-56);
          Float radix2 (5985022368960354) (-58); Float radix2 (4981821940365222) (-57); Float radix2 (8110554854100554) (-57); Float radix2 (8148523052449862) (-57); Float radix2 (4757295885076852) (-57);
          Float radix2 (-5548767824861902) (-57); Float radix2 (8690053288680376) (-57); Float radix2 (7216222237044500) (-57); Float radix2 (7928628345232172) (-57); Float radix2 (6459972511989286) (-56)];
      [:: Float radix2 (-7386726254675176) (-59); Float radix2 (-8095988051915882) (-57); Float radix2 (-4985089781496220) (-55); Float radix2 (6739030482924818) (-58); Float radix2 (-7591137387749536) (-55);
          Float radix2 (7466601294625480) (-57); Float radix2 (-8258195722759220) (-56); Float radix2 (5955088693724458) (-55); Float radix2 (5240215220997490) (-51); Float radix2 (-6928508149966754) (-58);
          Float radix2 (5681265888565614) (-56); Float radix2 (8772590930901064) (-56); Float radix2 (6971038477357922) (-56); Float radix2 (8947519237227546) (-56); Float radix2 (8378401603946274) (-56);
          Float radix2 (4821548678799834) (-55); Float radix2 (6267867583352826) (-56); Float radix2 (7219287182422702) (-56); Float radix2 (6772545310130690) (-56); Float radix2 (5652972003578088) (-57);
          Float radix2 (6868415690073242) (-56); Float radix2 (7500145761923476) (-60); Float radix2 (4760735375658254) (-55); Float radix2 (-7593678793080698) (-56); Float radix2 (6607628736433616) (-59);
          Float radix2 (8949667474492806) (-57); Float radix2 (6569373039817876) (-56); Float radix2 (5301840765691780) (-56); Float radix2 (7354080657890404) (-56); Float radix2 (8952387150946440) (-56);
          Float radix2 (6796303805895940) (-56); Float radix2 (5230230986030612) (-56); Float radix2 (6317386555227244) (-57); Float radix2 (7024552006960516) (-56); Float radix2 (-4836257039445228) (-57);
          Float radix2 (6609176992702910) (-58); Float radix2 (8205974791748322) (-57); Float radix2 (6554681738356750) (-56); Float radix2 (8113159316068172) (-56); Float radix2 (8960867265706210) (-56);
          Float radix2 (5785758576753686) (-56); Float radix2 (6119783606730258) (-57); Float radix2 (8880958337196128) (-57); Float radix2 (8157395388231058) (-56); Float radix2 (4516938180296910) (-54)];
      [:: Float radix2 (7966587851151892) (-59); Float radix2 (8093790047894330) (-58); Float radix2 (-6136437975350788) (-58); Float radix2 (8129171652716410) (-62); Float radix2 (-6108574151854706) (-64);
          Float radix2 (-7887071010998084) (-61); Float radix2 (-5588613527817902) (-67); Float radix2 (-8525921883271372) (-59); Float radix2 (-6928508149966754) (-58); Float radix2 (8193169712848352) (-53);
          Float radix2 (-5003398856057138) (-55); Float radix2 (-4827654553826482) (-54); Float radix2 (-7273475619212480) (-57); Float radix2 (-7675277565035880) (-56);
          Float radix2 (-5422252273794480) (-58); Float radix2 (-5594081357829526) (-57); Float radix2 (-8054071696697216) (-59); Float radix2 (-5459030466867216) (-55);
          Float radix2 (-5203326334347718) (-58); Float radix2 (-6214338621875494) (-60); Float radix2 (-5383624712006952) (-58); Float radix2 (4849198016088172) (-60); Float radix2 (-6011041863937234) (-58);
          Float radix2 (-6903416837091540) (-59); Float radix2 (-5261207098971253) (-53); Float radix2 (-4703151398431712) (-57); Float radix2 (-6118461011007210) (-56);
          Float radix2 (-4973294057092602) (-59); Float radix2 (-5121485991429936) (-58); Float radix2 (-8307156662216054) (-59); Float radix2 (-5767946045470962) (-55);
          Float radix2 (-6080240071786810) (-58); Float radix2 (-6851263184199686) (-59); Float radix2 (-6668792618078498) (-58); Float radix2 (-4530931179546818) (-58);
          Float radix2 (-5142770797983562) (-54); Float radix2 (-5239375595025462) (-59); Float radix2 (-8578658960915372) (-58); Float radix2 (-5660164575125680) (-58);
          Float radix2 (-8062546982040370) (-56); Float radix2 (-6248151488247924) (-58); Float radix2 (-5047888939892976) (-57); Float radix2 (-5159036757121510) (-55);
          Float radix2 (-4978237507088716) (-58); Float radix2 (-5077935334828322) (-55)];
      [:: Float radix2 (-8002470523870614) (-57); Float radix2 (-5959304474877588) (-57); Float radix2 (5378320066414952) (-56); Float radix2 (8781108273512038) (-57); Float radix2 (5925364808394106) (-56);
          Float radix2 (5281857839453832) (-56); Float radix2 (5393923336351904) (-56); Float radix2 (4948924969418338) (-56); Float radix2 (5681265888565614) (-56); Float radix2 (-5003398856057138) (-55);
          Float radix2 (8075076621640965) (-52); Float radix2 (8419365456102378) (-58); Float radix2 (-8356113746991928) (-55); Float radix2 (7852612654164016) (-57); Float radix2 (-8183229024844402) (-56);
          Float radix2 (8431298154764792) (-57); Float radix2 (-6235518585472082) (-57); Float radix2 (5462899299550076) (-56); Float radix2 (5668770566725454) (-56); Float radix2 (6209395801170106) (-56);
          Float radix2 (6219624806574266) (-56); Float radix2 (8039847190283094) (-57); Float radix2 (8950214968189316) (-57); Float radix2 (6543521837281682) (-57); Float radix2 (5121380774401888) (-56);
          Float radix2 (-7145318055703042) (-55); Float radix2 (5810973033939028) (-56); Float radix2 (-5074857114194260) (-56); Float radix2 (7856041701111420) (-57); Float radix2 (-6974510757802238) (-59);
          Float radix2 (6043863129059396) (-56); Float radix2 (4870459721949762) (-56); Float radix2 (8521636918716292) (-57); Float radix2 (8221258625148396) (-57); Float radix2 (5858370741628900) (-57);
          Float radix2 (6973412867119864) (-56); Float radix2 (-6270701575529918) (-56); Float radix2 (4738191482646974) (-56); Float radix2 (-7861102953552726) (-60); Float radix2 (5984621269683700) (-56);
          Float radix2 (4732738070800020) (-56); Float radix2 (7914340667765332) (-57); Float radix2 (6709666213975984) (-56); Float radix2 (-6221425316992926) (-58); Float radix2 (8188985704976572) (-56)];
      [:: Float radix2 (-7650744585040702) (-57); Float radix2 (-5670578927580478) (-59); Float radix2 (6887253177999890) (-57); Float radix2 (4814413137162422) (-56); Float radix2 (5306490709986154) (-56);
          Float radix2 (5408638446474756) (-56); Float radix2 (5614276599544710) (-56); Float radix2 (4662425901793480) (-56); Float radix2 (8772590930901064) (-56); Float radix2 (-4827654553826482) (-54);
          Float radix2 (8419365456102378) (-58); Float radix2 (4851058701191067) (-51); Float radix2 (8897525540951034) (-57); Float radix2 (-8987005197269542) (-56); Float radix2 (4753571509515032) (-56);
          Float radix2 (-6833532160222390) (-56); Float radix2 (4535084646671998) (-56); Float radix2 (8493185549253118) (-56); Float radix2 (8547508234721862) (-56); Float radix2 (6884591976225856) (-56);
          Float radix2 (6290854365044646) (-56); Float radix2 (4820579502964092) (-56); Float radix2 (4703187487478600) (-56); Float radix2 (5535661709016882) (-56); Float radix2 (-5573495305372628) (-58);
          Float radix2 (6295085982397180) (-56); Float radix2 (-8606665551614828) (-57); Float radix2 (8813092968250574) (-57); Float radix2 (-7376547815221018) (-57); Float radix2 (8047163374903868) (-57);
          Float radix2 (8765748896866418) (-56); Float radix2 (5970914430937142) (-56); Float radix2 (4908523791487284) (-56); Float radix2 (8466573616076122) (-57); Float radix2 (8742221193259522) (-57);
          Float radix2 (6963584425930958) (-58); Float radix2 (4800194017013460) (-56); Float radix2 (-7205115744971364) (-58); Float radix2 (8616784477207354) (-57); Float radix2 (8661896665679734) (-56);
          Float radix2 (8485267684295822) (-57); Float radix2 (5468328751456858) (-56); Float radix2 (4969071898678524) (-57); Float radix2 (5430853655311472) (-56); Float radix2 (6307279331472880) (-55)];
      [:: Float radix2 (-5765706170231300) (-57); Float radix2 (-6404124732742700) (-59); Float radix2 (8621953267924242) (-57); Float radix2 (5988198480847736) (-57); Float radix2 (8925670030166958) (-57);
          Float radix2 (6741741105922490) (-57); Float radix2 (6610586940146346) (-57); Float radix2 (8433914186436678) (-57); Float radix2 (6971038477357922) (-56); Float radix2 (-7273475619212480) (-57);
          Float radix2 (-8356113746991928) (-55); Float radix2 (8897525540951034) (-57); Float radix2 (4971111649168742) (-51); Float radix2 (8919860911791944) (-57); Float radix2 (-4610738511731934) (-55);
          Float radix2 (7056360645138372) (-57); Float radix2 (-6338677800141922) (-56); Float radix2 (6269357125648054) (-57); Float radix2 (7356126571070534) (-56); Float radix2 (5278812968579464) (-56);
          Float radix2 (4841913047991172) (-56); Float radix2 (6657101453624846) (-57); Float radix2 (8670684596182594) (-57); Float radix2 (7425282620785662) (-57); Float radix2 (6640183996415680) (-57);
          Float radix2 (-6077698241833126) (-56); Float radix2 (8521117668269212) (-57); Float radix2 (-5812746194201364) (-56); Float radix2 (5911585932975152) (-57); Float radix2 (-6874846395523512) (-57);
          Float radix2 (6303835787965032) (-57); Float radix2 (4631673601129850) (-56); Float radix2 (6508223441944994) (-57); Float radix2 (6499329975842892) (-57); Float radix2 (5160243830666702) (-57);
          Float radix2 (5888236279758894) (-57); Float radix2 (-8651130303265456) (-57); Float radix2 (6937025841826436) (-57); Float radix2 (-6987071813205924) (-58); Float radix2 (5510436931595492) (-57);
          Float radix2 (6165374170543664) (-57); Float radix2 (6307814442854798) (-57); Float radix2 (7314969530207498) (-57); Float radix2 (-5137208665291358) (-58); Float radix2 (6148353383444628) (-56)];
      [:: Float radix2 (-5257004087507880) (-57); Float radix2 (-5714308178062366) (-59); Float radix2 (5569123311939828) (-57); Float radix2 (6864440858511966) (-57); Float radix2 (6860748433735648) (-57);
          Float radix2 (5911551592375430) (-57); Float radix2 (4583946630689730) (-56); Float radix2 (5493575161297686) (-56); Float radix2 (8947519237227546) (-56); Float radix2 (-7675277565035880) (-56);
          Float radix2 (7852612654164016) (-57); Float radix2 (-8987005197269542) (-56); Float radix2 (8919860911791944) (-57); Float radix2 (5029895553238382) (-51); Float radix2 (7330170328031990) (-57);
          Float radix2 (-8919867983995720) (-56); Float radix2 (5424526202694794) (-56); Float radix2 (5983881892376796) (-56); Float radix2 (6326028327584298) (-56); Float radix2 (5115108437186408) (-56);
          Float radix2 (4580339165863060) (-56); Float radix2 (8846253865856226) (-57); Float radix2 (4548707732437590) (-56); Float radix2 (5279985616744564) (-56); Float radix2 (-8638722510244646) (-60);
          Float radix2 (8372341519237582) (-57); Float radix2 (-4770139794663226) (-56); Float radix2 (6059635852908828) (-57); Float radix2 (-5570458437072112) (-56); Float radix2 (8091340105341064) (-57);
          Float radix2 (4884244825844094) (-56); Float radix2 (8293925511839322) (-57); Float radix2 (7467236248260384) (-57); Float radix2 (6819000912525406) (-57); Float radix2 (7886582249123708) (-57);
          Float radix2 (-4738202919172788) (-59); Float radix2 (6574400942267704) (-57); Float radix2 (-5620124290762562) (-57); Float radix2 (7393494157086166) (-57); Float radix2 (4600262680006884) (-56);
          Float radix2 (6695570820703524) (-57); Float radix2 (4920993448057736) (-56); Float radix2 (-6013373338417160) (-63); Float radix2 (8033549631072668) (-57); Float radix2 (5126088568660316) (-55)];
      [:: Float radix2 (-8437748680594542) (-58); Float radix2 (-8169256683658616) (-60); Float radix2 (5508834478946518) (-57); Float radix2 (6945719434029928) (-58); Float radix2 (7434135477941474) (-58);
          Float radix2 (5518841881473022) (-57); Float radix2 (8014616834182732) (-57); Float radix2 (5119749352278672) (-56); Float radix2 (8378401603946274) (-56); Float radix2 (-5422252273794480) (-58);
          Float radix2 (-8183229024844402) (-56); Float radix2 (4753571509515032) (-56); Float radix2 (-4610738511731934) (-55); Float radix2 (7330170328031990) (-57); Float radix2 (5020858049254656) (-51);
          Float radix2 (4957272576557092) (-56); Float radix2 (-7365037320664524) (-56); Float radix2 (7367544636037998) (-58); Float radix2 (5358490418007410) (-56); Float radix2 (7210693720578768) (-57);
          Float radix2 (8613674584374730) (-57); Float radix2 (6477308057183208) (-57); Float radix2 (8607156117867170) (-57); Float radix2 (8951926340905022) (-57); Float radix2 (5724743890635000) (-58);
          Float radix2 (-4750080688688934) (-56); Float radix2 (6325357876794924) (-57); Float radix2 (-6070654266198422) (-56); Float radix2 (6897737072398512) (-57); Float radix2 (-4981781643860270) (-56);
          Float radix2 (6051018740689450) (-58); Float radix2 (6717508140110616) (-57); Float radix2 (5054360458902020) (-57); Float radix2 (6090952019037832) (-57); Float radix2 (6061709355894108) (-57);
          Float radix2 (6783742217942368) (-58); Float radix2 (-7059549485570422) (-57); Float radix2 (6644729347707078) (-57); Float radix2 (-8051839479251230) (-57); Float radix2 (8442101413922118) (-58);
          Float radix2 (6092878393141932) (-57); Float radix2 (6674322163409598) (-57); Float radix2 (5575639971657294) (-57); Float radix2 (-5376985405968398) (-57); Float radix2 (6428535741135422) (-56)];
      [:: Float radix2 (-8445439278622704) (-58); Float radix2 (-8500510623072442) (-59); Float radix2 (5936706705534780) (-58); Float radix2 (5105969938142028) (-58); Float radix2 (5612748042623706) (-57);
          Float radix2 (7741186964512184) (-57); Float radix2 (5460929496687794) (-56); Float radix2 (6885661036201658) (-56); Float radix2 (4821548678799834) (-55); Float radix2 (-5594081357829526) (-57);
          Float radix2 (8431298154764792) (-57); Float radix2 (-6833532160222390) (-56); Float radix2 (7056360645138372) (-57); Float radix2 (-8919867983995720) (-56); Float radix2 (4957272576557092) (-56);
          Float radix2 (5022209232963192) (-51); Float radix2 (7574790846734078) (-56); Float radix2 (7549231318755150) (-57); Float radix2 (4807018481789696) (-56); Float radix2 (4645354238068462) (-56);
          Float radix2 (8933228324550312) (-57); Float radix2 (8708974770691406) (-57); Float radix2 (5400833079838250) (-56); Float radix2 (6174147726080128) (-56); Float radix2 (-8015255839779546) (-59);
          Float radix2 (5882705873785510) (-57); Float radix2 (-4773894177043670) (-56); Float radix2 (6762298559106132) (-57); Float radix2 (-6918717311307270) (-56); Float radix2 (5678058083114394) (-56);
          Float radix2 (6161342419424136) (-57); Float radix2 (6957975730110146) (-57); Float radix2 (6884893341083368) (-57); Float radix2 (7943128471804772) (-57); Float radix2 (4875921441286478) (-56);
          Float radix2 (-5731013122227988) (-59); Float radix2 (6147223718965728) (-57); Float radix2 (-5021628879730896) (-56); Float radix2 (8314430763075818) (-57); Float radix2 (8263337027671928) (-57);
          Float radix2 (7731987922600632) (-57); Float radix2 (5236235263321436) (-56); Float radix2 (-8789053238205116) (-58); Float radix2 (8123639643461170) (-57); Float radix2 (4575707050322780) (-55)];
      [:: Float radix2 (-8465006557781832) (-58); Float radix2 (-5075619571537724) (-58); Float radix2 (8608251871411136) (-59); Float radix2 (6531988922397136) (-58); Float radix2 (7036537865187080) (-57);
          Float radix2 (8080669701487210) (-57); Float radix2 (6195392457961800) (-56); Float radix2 (5979604819406744) (-56); Float radix2 (6267867583352826) (-56); Float radix2 (-8054071696697216) (-59);
          Float radix2 (-6235518585472082) (-57); Float radix2 (4535084646671998) (-56); Float radix2 (-6338677800141922) (-56); Float radix2 (5424526202694794) (-56); Float radix2 (-7365037320664524) (-56);
          Float radix2 (7574790846734078) (-56); Float radix2 (4818274947040212) (-51); Float radix2 (5938389942787808) (-59); Float radix2 (5357662571103884) (-56); Float radix2 (7729116355876892) (-57);
          Float radix2 (4520241541712796) (-56); Float radix2 (8710465161876706) (-57); Float radix2 (5398128913274568) (-56); Float radix2 (7287436721132182) (-56); Float radix2 (6985983020788040) (-59);
          Float radix2 (-8380977678356388) (-58); Float radix2 (8383074070711010) (-57); Float radix2 (-4845103110976608) (-56); Float radix2 (5632207438064558) (-56); Float radix2 (-5889842671793434) (-55);
          Float radix2 (4532472527111346) (-58); Float radix2 (6759002175027542) (-57); Float radix2 (6824518791336710) (-57); Float radix2 (8484446959930006) (-57); Float radix2 (6340606689254846) (-56);
          Float radix2 (4560866503770012) (-57); Float radix2 (-6095661381565118) (-57); Float radix2 (4618823169546238) (-56); Float radix2 (-4771331606487784) (-55); Float radix2 (6637446180064074) (-57);
          Float radix2 (7419722120062860) (-57); Float radix2 (6515920970490836) (-56); Float radix2 (7989932515035288) (-57); Float radix2 (-8968788212144722) (-56); Float radix2 (5249750662838926) (-55)];
      [:: Float radix2 (-4541971290842208) (-54); Float radix2 (-4701771230895522) (-56); Float radix2 (7995370859567664) (-56); Float radix2 (5792093291630908) (-57); Float radix2 (5928315651795864) (-56);
          Float radix2 (8536689088070836) (-57); Float radix2 (5104975952430512) (-56); Float radix2 (7298834306446562) (-57); Float radix2 (7219287182422702) (-56); Float radix2 (-5459030466867216) (-55);
          Float radix2 (5462899299550076) (-56); Float radix2 (8493185549253118) (-56); Float radix2 (6269357125648054) (-57); Float radix2 (5983881892376796) (-56); Float radix2 (7367544636037998) (-58);
          Float radix2 (7549231318755150) (-57); Float radix2 (5938389942787808) (-59); Float radix2 (7257782318635283) (-52); Float radix2 (7453272950808372) (-58); Float radix2 (-5898807594188740) (-56);
          Float radix2 (7726251570006752) (-58); Float radix2 (-7546305522035314) (-58); Float radix2 (7349418589291824) (-59); Float radix2 (7477546100301150) (-59); Float radix2 (-5817534032080388) (-55);
          Float radix2 (6579103380449822) (-57); Float radix2 (4843724910481788) (-56); Float radix2 (5941501146963296) (-58); Float radix2 (6060366067981694) (-57); Float radix2 (8268750035173960) (-60);
          Float radix2 (-7501100441689336) (-54); Float radix2 (7650556038535124) (-58); Float radix2 (-6386323194150262) (-57); Float radix2 (5632191323171780) (-60); Float radix2 (6455052635704450) (-60);
          Float radix2 (-8905974274607702) (-57); Float radix2 (7604956452478470) (-58); Float radix2 (6095378701667716) (-57); Float radix2 (-6552171396768808) (-61); Float radix2 (-8865900898290236) (-55);
          Float radix2 (7983108038189908) (-59); Float radix2 (-6519998601347924) (-59); Float radix2 (-8715819170116492) (-59); Float radix2 (-5266293184603584) (-60); Float radix2 (-6450699784183342) (-55)];
      [:: Float radix2 (-5339007384174714) (-56); Float radix2 (-7029236919720692) (-55); Float radix2 (4858156645224950) (-56); Float radix2 (-5920158939071762) (-58); Float radix2 (6527466083604292) (-56);
          Float radix2 (4665442947361932) (-59); Float radix2 (6207380987888490) (-56); Float radix2 (6783628782863546) (-60); Float radix2 (6772545310130690) (-56); Float radix2 (-5203326334347718) (-58);
          Float radix2 (5668770566725454) (-56); Float radix2 (8547508234721862) (-56); Float radix2 (7356126571070534) (-56); Float radix2 (6326028327584298) (-56); Float radix2 (5358490418007410) (-56);
          Float radix2 (4807018481789696) (-56); Float radix2 (5357662571103884) (-56); Float radix2 (7453272950808372) (-58); Float radix2 (4897668133473454) (-51); Float radix2 (5982699688787114) (-56);
          Float radix2 (-5417014773238030) (-56); Float radix2 (7653912029719666) (-57); Float radix2 (-6991929837827886) (-57); Float radix2 (7167841050304420) (-57); Float radix2 (5038459971607534) (-56);
          Float radix2 (6461412021559466) (-56); Float radix2 (6760467936574164) (-56); Float radix2 (5223137458119664) (-56); Float radix2 (4521764211286032) (-56); Float radix2 (8846820345681168) (-57);
          Float radix2 (4794100364279622) (-56); Float radix2 (-7866847120638000) (-56); Float radix2 (8744605446049540) (-57); Float radix2 (-8098781733441180) (-57); Float radix2 (7340803586319424) (-57);
          Float radix2 (5808794165199200) (-56); Float radix2 (6257470173068746) (-56); Float radix2 (4999048143511020) (-56); Float radix2 (4528587408825782) (-56); Float radix2 (5813889239684972) (-56);
          Float radix2 (-5740104780427212) (-56); Float radix2 (5607332404901132) (-56); Float radix2 (4732318572200914) (-56); Float radix2 (5653449446009212) (-56); Float radix2 (5668113623329494) (-55)];
      [:: Float radix2 (-7062122969746640) (-58); Float radix2 (-7899790543651092) (-58); Float radix2 (-7691576603729194) (-57); Float radix2 (6391302534999480) (-57); Float radix2 (-5945228258664286) (-58);
          Float radix2 (8026326184975096) (-57); Float radix2 (-5051739922525640) (-58); Float radix2 (7105006317325160) (-57); Float radix2 (5652972003578088) (-57); Float radix2 (-6214338621875494) (-60);
          Float radix2 (6209395801170106) (-56); Float radix2 (6884591976225856) (-56); Float radix2 (5278812968579464) (-56); Float radix2 (5115108437186408) (-56); Float radix2 (7210693720578768) (-57);
          Float radix2 (4645354238068462) (-56); Float radix2 (7729116355876892) (-57); Float radix2 (-5898807594188740) (-56); Float radix2 (5982699688787114) (-56); Float radix2 (5174887257140745) (-51);
          Float radix2 (7998845584759440) (-57); Float radix2 (-7984545220642622) (-57); Float radix2 (5814378020348068) (-57); Float radix2 (-4753596123436914) (-59); Float radix2 (4860170082244726) (-56);
          Float radix2 (5314797081092540) (-56); Float radix2 (5061703573023890) (-56); Float radix2 (6775405186457300) (-57); Float radix2 (7323232844514144) (-57); Float radix2 (5457519805823888) (-57);
          Float radix2 (-7719378258715984) (-58); Float radix2 (8261527387281680) (-57); Float radix2 (-6750354227117188) (-57); Float radix2 (5903699283920232) (-57); Float radix2 (-7520952903331564) (-62);
          Float radix2 (5344087801974888) (-56); Float radix2 (6561340801703782) (-57); Float radix2 (7662563228475042) (-57); Float radix2 (5088787676390254) (-57); Float radix2 (-6807363357728386) (-60);
          Float radix2 (7454681689281580) (-57); Float radix2 (5031112105783030) (-59); Float radix2 (8937442921429150) (-57); Float radix2 (6776290367180634) (-57); Float radix2 (5910521026878414) (-56)];
      [:: Float radix2 (-5930952263952290) (-57); Float radix2 (-7018700514771894) (-57); Float radix2 (6921050415478540) (-57); Float radix2 (-6169761039264394) (-57); Float radix2 (7967149614527142) (-57);
          Float radix2 (-8690825536796494) (-57); Float radix2 (7250805679721336) (-57); Float radix2 (-4913159140289116) (-56); Float radix2 (6868415690073242) (-56); Float radix2 (-5383624712006952) (-58);
          Float radix2 (6219624806574266) (-56); Float radix2 (6290854365044646) (-56); Float radix2 (4841913047991172) (-56); Float radix2 (4580339165863060) (-56); Float radix2 (8613674584374730) (-57);
          Float radix2 (8933228324550312) (-57); Float radix2 (4520241541712796) (-56); Float radix2 (7726251570006752) (-58); Float radix2 (-5417014773238030) (-56); Float radix2 (7998845584759440) (-57);
          Float radix2 (5132330941568343) (-51); Float radix2 (5348904342087956) (-57); Float radix2 (-5626560378634416) (-56); Float radix2 (7609321721569758) (-57); Float radix2 (5152313367592230) (-57);
          Float radix2 (4954249182310972) (-56); Float radix2 (4595952762859894) (-56); Float radix2 (6974654923605152) (-57); Float radix2 (6978079389417630) (-57); Float radix2 (7076695136356040) (-57);
          Float radix2 (8151853702829364) (-58); Float radix2 (-5286608319072880) (-56); Float radix2 (6260646881917364) (-57); Float radix2 (-4651218087119414) (-56); Float radix2 (6648811648352388) (-57);
          Float radix2 (5000631896851598) (-57); Float radix2 (7235042793699318) (-57); Float radix2 (7546075143732062) (-57); Float radix2 (7645696548145768) (-57); Float radix2 (6968173706706218) (-57);
          Float radix2 (-4711924439433356) (-56); Float radix2 (8421868547125960) (-57); Float radix2 (7430271597278148) (-57); Float radix2 (5040479259278096) (-56); Float radix2 (8292893990428252) (-56)];
      [:: Float radix2 (4808324460115096) (-60); Float radix2 (-6146277029941110) (-59); Float radix2 (-6467661296102982) (-58); Float radix2 (8705525907347444) (-58); Float radix2 (-6203453114670840) (-57);
          Float radix2 (8259640224363982) (-58); Float radix2 (-6604554164935854) (-57); Float radix2 (8340834543648028) (-57); Float radix2 (7500145761923476) (-60); Float radix2 (4849198016088172) (-60);
          Float radix2 (8039847190283094) (-57); Float radix2 (4820579502964092) (-56); Float radix2 (6657101453624846) (-57); Float radix2 (8846253865856226) (-57); Float radix2 (6477308057183208) (-57);
          Float radix2 (8708974770691406) (-57); Float radix2 (8710465161876706) (-57); Float radix2 (-7546305522035314) (-58); Float radix2 (7653912029719666) (-57); Float radix2 (-7984545220642622) (-57);
          Float radix2 (5348904342087956) (-57); Float radix2 (5171281490329255) (-51); Float radix2 (6373084259587878) (-57); Float radix2 (-8043343316389766) (-58); Float radix2 (4727897802108338) (-57);
          Float radix2 (6300337508939246) (-57); Float radix2 (7204430673589540) (-57); Float radix2 (4672658585455562) (-57); Float radix2 (6440466071998196) (-57); Float radix2 (5807456054488894) (-57);
          Float radix2 (-6783332782435954) (-58); Float radix2 (5642349213409056) (-57); Float radix2 (-5947332691609766) (-57); Float radix2 (5392416215328332) (-57); Float radix2 (-4731247797095876) (-57);
          Float radix2 (7832725188985288) (-58); Float radix2 (8834721059903624) (-58); Float radix2 (7090156263066478) (-57); Float radix2 (5097594283973526) (-57); Float radix2 (-8754008831935288) (-60);
          Float radix2 (5543435367371616) (-57); Float radix2 (-8248225954480356) (-59); Float radix2 (7497551865720014) (-57); Float radix2 (6667019919670726) (-57); Float radix2 (5004201026610204) (-56)];
      [:: Float radix2 (-8525482828466518) (-58); Float radix2 (7067145423215922) (-60); Float radix2 (5188948371493160) (-57); Float radix2 (-7122083654443804) (-57); Float radix2 (8422668461287778) (-58);
          Float radix2 (-5710952398386776) (-56); Float radix2 (8964005263948476) (-57); Float radix2 (-6418503281475352) (-56); Float radix2 (4760735375658254) (-55); Float radix2 (-6011041863937234) (-58);
          Float radix2 (8950214968189316) (-57); Float radix2 (4703187487478600) (-56); Float radix2 (8670684596182594) (-57); Float radix2 (4548707732437590) (-56); Float radix2 (8607156117867170) (-57);
          Float radix2 (5400833079838250) (-56); Float radix2 (5398128913274568) (-56); Float radix2 (7349418589291824) (-59); Float radix2 (-6991929837827886) (-57); Float radix2 (5814378020348068) (-57);
          Float radix2 (-5626560378634416) (-56); Float radix2 (6373084259587878) (-57); Float radix2 (5104184288482431) (-51); Float radix2 (5716354925485004) (-56); Float radix2 (5906637098375106) (-58);
          Float radix2 (7305360783341598) (-57); Float radix2 (7746578808929492) (-57); Float radix2 (6426748999116462) (-57); Float radix2 (8179000256709352) (-57); Float radix2 (4531160929656908) (-56);
          Float radix2 (5228159279876010) (-58); Float radix2 (-7693829347245930) (-57); Float radix2 (6283187594489384) (-57); Float radix2 (-6484876714235434) (-56); Float radix2 (8141794198980706) (-57);
          Float radix2 (8272403763928152) (-58); Float radix2 (6993479028013466) (-57); Float radix2 (8554650749894128) (-57); Float radix2 (8580787882838114) (-57); Float radix2 (6394828838107202) (-57);
          Float radix2 (-5581639204629914) (-56); Float radix2 (8971423048371490) (-57); Float radix2 (4540997534634486) (-56); Float radix2 (4514992845924774) (-56); Float radix2 (4959071779322868) (-55)];
      [:: Float radix2 (5615288358367336) (-59); Float radix2 (-5256079871112528) (-58); Float radix2 (5527841703869974) (-59); Float radix2 (8339323153095870) (-59); Float radix2 (-5604482232757282) (-63);
          Float radix2 (6959263348459706) (-57); Float radix2 (7405704907638710) (-60); Float radix2 (7054286046007382) (-56); Float radix2 (-7593678793080698) (-56); Float radix2 (-6903416837091540) (-59);
          Float radix2 (6543521837281682) (-57); Float radix2 (5535661709016882) (-56); Float radix2 (7425282620785662) (-57); Float radix2 (5279985616744564) (-56); Float radix2 (8951926340905022) (-57);
          Float radix2 (6174147726080128) (-56); Float radix2 (7287436721132182) (-56); Float radix2 (7477546100301150) (-59); Float radix2 (7167841050304420) (-57); Float radix2 (-4753596123436914) (-59);
          Float radix2 (7609321721569758) (-57); Float radix2 (-8043343316389766) (-58); Float radix2 (5716354925485004) (-56); Float radix2 (5156687665832959) (-51); Float radix2 (4997789169571538) (-58);
          Float radix2 (5645770589347272) (-57); Float radix2 (8232385893256376) (-57); Float radix2 (6163703649772960) (-57); Float radix2 (4863630586218480) (-56); Float radix2 (6028941360884100) (-56);
          Float radix2 (8578429271084360) (-58); Float radix2 (6952841002800564) (-57); Float radix2 (-5753544425982912) (-58); Float radix2 (8034879346256906) (-57); Float radix2 (-4764731309693302) (-56);
          Float radix2 (8448362530751178) (-58); Float radix2 (5733161760028270) (-57); Float radix2 (4602696307234490) (-56); Float radix2 (5179069376184562) (-56); Float radix2 (4720369973795288) (-57);
          Float radix2 (7470271346076606) (-57); Float radix2 (-7764704974649698) (-57); Float radix2 (7423856577638464) (-57); Float radix2 (5126039845688406) (-56); Float radix2 (8706942139305310) (-57)];
      [:: Float radix2 (-4737038720658120) (-56); Float radix2 (5655550509397182) (-60); Float radix2 (6174144519554676) (-56); Float radix2 (5079987227742868) (-62); Float radix2 (6099518219014776) (-57);
          Float radix2 (5310755887792582) (-60); Float radix2 (8849223571282772) (-59); Float radix2 (6003447126424564) (-60); Float radix2 (6607628736433616) (-59); Float radix2 (-5261207098971253) (-53);
          Float radix2 (5121380774401888) (-56); Float radix2 (-5573495305372628) (-58); Float radix2 (6640183996415680) (-57); Float radix2 (-8638722510244646) (-60); Float radix2 (5724743890635000) (-58);
          Float radix2 (-8015255839779546) (-59); Float radix2 (6985983020788040) (-59); Float radix2 (-5817534032080388) (-55); Float radix2 (5038459971607534) (-56); Float radix2 (4860170082244726) (-56);
          Float radix2 (5152313367592230) (-57); Float radix2 (4727897802108338) (-57); Float radix2 (5906637098375106) (-58); Float radix2 (4997789169571538) (-58); Float radix2 (8782473794307644) (-52);
          Float radix2 (5675014860756984) (-57); Float radix2 (-6623252674633840) (-57); Float radix2 (6940202234526300) (-59); Float radix2 (-4771913851324524) (-57); Float radix2 (6840905981657180) (-59);
          Float radix2 (-5553868549761696) (-57); Float radix2 (7066328975928208) (-57); Float radix2 (7471363705124500) (-57); Float radix2 (4592784632519172) (-58); Float radix2 (5331934722010452) (-58);
          Float radix2 (-4835991376498926) (-54); Float radix2 (5914378113954546) (-58); Float radix2 (-7536252850108512) (-57); Float radix2 (4606518228624414) (-58); Float radix2 (6714567437454310) (-59);
          Float radix2 (4576204784908920) (-58); Float radix2 (7981879511272536) (-58); Float radix2 (-7006431808223374) (-55); Float radix2 (6214524647769224) (-58); Float radix2 (6365330299893606) (-57)];
      [:: Float radix2 (-5815735609972978) (-57); Float radix2 (-7079090153833342) (-58); Float radix2 (5852898850748374) (-57); Float radix2 (5920996506949334) (-57); Float radix2 (5358399048928132) (-57);
          Float radix2 (5365360500171582) (-57); Float radix2 (4648201917564122) (-57); Float radix2 (7005061772400268) (-57); Float radix2 (8949667474492806) (-57); Float radix2 (-4703151398431712) (-57);
          Float radix2 (-7145318055703042) (-55); Float radix2 (6295085982397180) (-56); Float radix2 (-6077698241833126) (-56); Float radix2 (8372341519237582) (-57); Float radix2 (-4750080688688934) (-56);
          Float radix2 (5882705873785510) (-57); Float radix2 (-8380977678356388) (-58); Float radix2 (6579103380449822) (-57); Float radix2 (6461412021559466) (-56); Float radix2 (5314797081092540) (-56);
          Float radix2 (4954249182310972) (-56); Float radix2 (6300337508939246) (-57); Float radix2 (7305360783341598) (-57); Float radix2 (5645770589347272) (-57); Float radix2 (5675014860756984) (-57);
          Float radix2 (5028205106023333) (-51); Float radix2 (8327795763168170) (-57); Float radix2 (-5627363949503592) (-56); Float radix2 (5719470110056762) (-57); Float radix2 (-8242564718926256) (-58);
          Float radix2 (8257034327814518) (-57); Float radix2 (5980231658109228) (-56); Float radix2 (6724556202358324) (-57); Float radix2 (7221183694964106) (-57); Float radix2 (5125764029083174) (-57);
          Float radix2 (6513504056724428) (-57); Float radix2 (-7642721865650544) (-56); Float radix2 (7582660783573554) (-57); Float radix2 (-6028318282917926) (-57); Float radix2 (6479686562218874) (-57);
          Float radix2 (8812973680859942) (-57); Float radix2 (8008829575611878) (-57); Float radix2 (7605658360798332) (-57); Float radix2 (-8360936637120718) (-57); Float radix2 (8348050633893708) (-56)];
      [:: Float radix2 (-5783894486249982) (-57); Float radix2 (-8438556944167468) (-59); Float radix2 (5682603522922206) (-57); Float radix2 (7756992882217432) (-58); Float radix2 (5682146820057618) (-57);
          Float radix2 (4631825137042246) (-57); Float radix2 (7610429734117970) (-57); Float radix2 (7798854788351118) (-57); Float radix2 (6569373039817876) (-56); Float radix2 (-6118461011007210) (-56);
          Float radix2 (5810973033939028) (-56); Float radix2 (-8606665551614828) (-57); Float radix2 (8521117668269212) (-57); Float radix2 (-4770139794663226) (-56); Float radix2 (6325357876794924) (-57);
          Float radix2 (-4773894177043670) (-56); Float radix2 (8383074070711010) (-57); Float radix2 (4843724910481788) (-56); Float radix2 (6760467936574164) (-56); Float radix2 (5061703573023890) (-56);
          Float radix2 (4595952762859894) (-56); Float radix2 (7204430673589540) (-57); Float radix2 (7746578808929492) (-57); Float radix2 (8232385893256376) (-57); Float radix2 (-6623252674633840) (-57);
          Float radix2 (8327795763168170) (-57); Float radix2 (5176092473562275) (-51); Float radix2 (6143541039116250) (-57); Float radix2 (-8111697946537412) (-57); Float radix2 (7251718958067910) (-57);
          Float radix2 (5789799405535040) (-56); Float radix2 (4506989609829500) (-56); Float radix2 (8004364712076664) (-57); Float radix2 (7198582319640446) (-57); Float radix2 (8434581273296438) (-57);
          Float radix2 (-6487888619774370) (-57); Float radix2 (7460276343683832) (-57); Float radix2 (-7522731415067314) (-57); Float radix2 (7267510945462788) (-57); Float radix2 (6035240123917054) (-56);
          Float radix2 (8613461171213838) (-57); Float radix2 (6391118293145504) (-56); Float radix2 (-8844221052171038) (-58); Float radix2 (4673041133288360) (-56); Float radix2 (7699942999984098) (-55)];
      [:: Float radix2 (-8158432522499944) (-58); Float radix2 (-7210904052652538) (-60); Float radix2 (6892203972192212) (-58); Float radix2 (8541291694875872) (-59); Float radix2 (5465078639147268) (-58);
          Float radix2 (8441053137203036) (-58); Float radix2 (4682437298053288) (-57); Float radix2 (6587798094353724) (-57); Float radix2 (5301840765691780) (-56); Float radix2 (-4973294057092602) (-59);
          Float radix2 (-5074857114194260) (-56); Float radix2 (8813092968250574) (-57); Float radix2 (-5812746194201364) (-56); Float radix2 (6059635852908828) (-57); Float radix2 (-6070654266198422) (-56);
          Float radix2 (6762298559106132) (-57); Float radix2 (-4845103110976608) (-56); Float radix2 (5941501146963296) (-58); Float radix2 (5223137458119664) (-56); Float radix2 (6775405186457300) (-57);
          Float radix2 (6974654923605152) (-57); Float radix2 (4672658585455562) (-57); Float radix2 (6426748999116462) (-57); Float radix2 (6163703649772960) (-57); Float radix2 (6940202234526300) (-59);
          Float radix2 (-5627363949503592) (-56); Float radix2 (6143541039116250) (-57); Float radix2 (5148725987005420) (-51); Float radix2 (5622348505584852) (-57); Float radix2 (-5051442284444146) (-56);
          Float radix2 (4648112554316050) (-58); Float radix2 (7114536792955452) (-57); Float radix2 (4892895976504256) (-57); Float radix2 (6714979840430486) (-57); Float radix2 (5348300708582318) (-57);
          Float radix2 (7041514717191954) (-58); Float radix2 (-5523136464070662) (-56); Float radix2 (6090814827283822) (-57); Float radix2 (-4874601599974312) (-56); Float radix2 (5119920405488218) (-57);
          Float radix2 (8622984657154268) (-57); Float radix2 (7938850143090502) (-57); Float radix2 (6071553092101014) (-57); Float radix2 (-6846447917403978) (-57); Float radix2 (7820405378497060) (-56)];
      [:: Float radix2 (-7577755907129754) (-58); Float radix2 (-4957368578917454) (-58); Float radix2 (4738635929574928) (-58); Float radix2 (7371074393168852) (-59); Float radix2 (4571400473328546) (-57);
          Float radix2 (4766654946583158) (-57); Float radix2 (7332748371156394) (-57); Float radix2 (4717820431872398) (-56); Float radix2 (7354080657890404) (-56); Float radix2 (-5121485991429936) (-58);
          Float radix2 (7856041701111420) (-57); Float radix2 (-7376547815221018) (-57); Float radix2 (5911585932975152) (-57); Float radix2 (-5570458437072112) (-56); Float radix2 (6897737072398512) (-57);
          Float radix2 (-6918717311307270) (-56); Float radix2 (5632207438064558) (-56); Float radix2 (6060366067981694) (-57); Float radix2 (4521764211286032) (-56); Float radix2 (7323232844514144) (-57);
          Float radix2 (6978079389417630) (-57); Float radix2 (6440466071998196) (-57); Float radix2 (8179000256709352) (-57); Float radix2 (4863630586218480) (-56); Float radix2 (-4771913851324524) (-57);
          Float radix2 (5719470110056762) (-57); Float radix2 (-8111697946537412) (-57); Float radix2 (5622348505584852) (-57); Float radix2 (5103009340970241) (-51); Float radix2 (8057570402543966) (-57);
          Float radix2 (5287004242014384) (-57); Float radix2 (6688093759157496) (-57); Float radix2 (7361008820905568) (-57); Float radix2 (7259306823761900) (-57); Float radix2 (8778865868821392) (-57);
          Float radix2 (-5743235710041892) (-57); Float radix2 (5662321648798400) (-57); Float radix2 (-5655272543519904) (-56); Float radix2 (6941671465223806) (-57); Float radix2 (5079147038645946) (-56);
          Float radix2 (8771167335412694) (-57); Float radix2 (5337180430592346) (-56); Float radix2 (-5512923480344194) (-57); Float radix2 (5116296808699804) (-56); Float radix2 (5776864848772244) (-55)];
      [:: Float radix2 (-7942647862844690) (-58); Float radix2 (-4567031615196384) (-58); Float radix2 (5343970836185086) (-59); Float radix2 (5262899293993306) (-58); Float radix2 (6293216057432744) (-58);
          Float radix2 (5171206845532138) (-57); Float radix2 (7250367027643680) (-57); Float radix2 (4917514433306936) (-56); Float radix2 (8952387150946440) (-56); Float radix2 (-8307156662216054) (-59);
          Float radix2 (-6974510757802238) (-59); Float radix2 (8047163374903868) (-57); Float radix2 (-6874846395523512) (-57); Float radix2 (8091340105341064) (-57); Float radix2 (-4981781643860270) (-56);
          Float radix2 (5678058083114394) (-56); Float radix2 (-5889842671793434) (-55); Float radix2 (8268750035173960) (-60); Float radix2 (8846820345681168) (-57); Float radix2 (5457519805823888) (-57);
          Float radix2 (7076695136356040) (-57); Float radix2 (5807456054488894) (-57); Float radix2 (4531160929656908) (-56); Float radix2 (6028941360884100) (-56); Float radix2 (6840905981657180) (-59);
          Float radix2 (-8242564718926256) (-58); Float radix2 (7251718958067910) (-57); Float radix2 (-5051442284444146) (-56); Float radix2 (8057570402543966) (-57); Float radix2 (4992783369325683) (-51);
          Float radix2 (6980568836172574) (-59); Float radix2 (7395318289494948) (-57); Float radix2 (5884252388466658) (-57); Float radix2 (8078566903076776) (-57); Float radix2 (5122173907485384) (-56);
          Float radix2 (7652421827176110) (-58); Float radix2 (-8518220658437140) (-57); Float radix2 (7793906527448230) (-57); Float radix2 (-5381713099712016) (-55); Float radix2 (7367578840364474) (-57);
          Float radix2 (7798154179623974) (-57); Float radix2 (5571756346381514) (-56); Float radix2 (4893664508773944) (-56); Float radix2 (-8353516434164502) (-56); Float radix2 (5737014148144790) (-55)];
      [:: Float radix2 (-7122063683258006) (-56); Float radix2 (4579505801121752) (-62); Float radix2 (7299237939284872) (-56); Float radix2 (6836339045913012) (-58); Float radix2 (7748192724884754) (-57);
          Float radix2 (5158997231547168) (-58); Float radix2 (4974501712952714) (-57); Float radix2 (7803282707720094) (-59); Float radix2 (6796303805895940) (-56); Float radix2 (-5767946045470962) (-55);
          Float radix2 (6043863129059396) (-56); Float radix2 (8765748896866418) (-56); Float radix2 (6303835787965032) (-57); Float radix2 (4884244825844094) (-56); Float radix2 (6051018740689450) (-58);
          Float radix2 (6161342419424136) (-57); Float radix2 (4532472527111346) (-58); Float radix2 (-7501100441689336) (-54); Float radix2 (4794100364279622) (-56); Float radix2 (-7719378258715984) (-58);
          Float radix2 (8151853702829364) (-58); Float radix2 (-6783332782435954) (-58); Float radix2 (5228159279876010) (-58); Float radix2 (8578429271084360) (-58); Float radix2 (-5553868549761696) (-57);
          Float radix2 (8257034327814518) (-57); Float radix2 (5789799405535040) (-56); Float radix2 (4648112554316050) (-58); Float radix2 (5287004242014384) (-57); Float radix2 (6980568836172574) (-59);
          Float radix2 (4719061371238100) (-51); Float radix2 (5089177352145916) (-57); Float radix2 (-6390299910905406) (-57); Float radix2 (5242492421367164) (-58); Float radix2 (6553353829664326) (-59);
          Float radix2 (4901211887605404) (-58); Float radix2 (4696252677947548) (-58); Float radix2 (6190543931810000) (-57); Float radix2 (8525760189799400) (-59); Float radix2 (-6358167134404280) (-55);
          Float radix2 (6902549093294544) (-58); Float radix2 (8348346766568556) (-60); Float radix2 (8153332196146832) (-58); Float radix2 (8467377396062094) (-58); Float radix2 (-7504924686065434) (-55)];
      [:: Float radix2 (-5650959767140964) (-57); Float radix2 (-7977716628387650) (-57); Float radix2 (8890162258480550) (-57); Float radix2 (-8908950440229038) (-61); Float radix2 (6706528015657548) (-57);
          Float radix2 (-5109747320025502) (-58); Float radix2 (5720628713137590) (-57); Float radix2 (-5734857445372008) (-58); Float radix2 (5230230986030612) (-56); Float radix2 (-6080240071786810) (-58);
          Float radix2 (4870459721949762) (-56); Float radix2 (5970914430937142) (-56); Float radix2 (4631673601129850) (-56); Float radix2 (8293925511839322) (-57); Float radix2 (6717508140110616) (-57);
          Float radix2 (6957975730110146) (-57); Float radix2 (6759002175027542) (-57); Float radix2 (7650556038535124) (-58); Float radix2 (-7866847120638000) (-56); Float radix2 (8261527387281680) (-57);
          Float radix2 (-5286608319072880) (-56); Float radix2 (5642349213409056) (-57); Float radix2 (-7693829347245930) (-57); Float radix2 (6952841002800564) (-57); Float radix2 (7066328975928208) (-57);
          Float radix2 (5980231658109228) (-56); Float radix2 (4506989609829500) (-56); Float radix2 (7114536792955452) (-57); Float radix2 (6688093759157496) (-57); Float radix2 (7395318289494948) (-57);
          Float radix2 (5089177352145916) (-57); Float radix2 (5066226199522652) (-51); Float radix2 (7343781716082500) (-57); Float radix2 (-5446434806578706) (-56); Float radix2 (6630367684059188) (-57);
          Float radix2 (5517278834347432) (-57); Float radix2 (4693217180068346) (-56); Float radix2 (8971581558162696) (-57); Float radix2 (4929846918924248) (-56); Float radix2 (7945579945169656) (-57);
          Float radix2 (-6909022834119286) (-56); Float radix2 (5089148476202710) (-56); Float radix2 (4960394929328228) (-56); Float radix2 (8135897539983644) (-56); Float radix2 (5235518204119618) (-55)];
      [:: Float radix2 (-7457480049077902) (-62); Float radix2 (4968495382205426) (-62); Float radix2 (8062685024174374) (-61); Float radix2 (6002374529926046) (-58); Float radix2 (-6695711639534094) (-59);
          Float radix2 (6009511365794384) (-58); Float radix2 (-5764824956016892) (-59); Float radix2 (5924517600926180) (-57); Float radix2 (6317386555227244) (-57); Float radix2 (-6851263184199686) (-59);
          Float radix2 (8521636918716292) (-57); Float radix2 (4908523791487284) (-56); Float radix2 (6508223441944994) (-57); Float radix2 (7467236248260384) (-57); Float radix2 (5054360458902020) (-57);
          Float radix2 (6884893341083368) (-57); Float radix2 (6824518791336710) (-57); Float radix2 (-6386323194150262) (-57); Float radix2 (8744605446049540) (-57); Float radix2 (-6750354227117188) (-57);
          Float radix2 (6260646881917364) (-57); Float radix2 (-5947332691609766) (-57); Float radix2 (6283187594489384) (-57); Float radix2 (-5753544425982912) (-58); Float radix2 (7471363705124500) (-57);
          Float radix2 (6724556202358324) (-57); Float radix2 (8004364712076664) (-57); Float radix2 (4892895976504256) (-57); Float radix2 (7361008820905568) (-57); Float radix2 (5884252388466658) (-57);
          Float radix2 (-6390299910905406) (-57); Float radix2 (7343781716082500) (-57); Float radix2 (5210221922660188) (-51); Float radix2 (5966278839867418) (-57); Float radix2 (-8083366674233104) (-58);
          Float radix2 (6573016668512046) (-57); Float radix2 (6322696616040822) (-57); Float radix2 (5176381048538140) (-56); Float radix2 (7270578149887832) (-57); Float radix2 (-7495731361459338) (-59);
          Float radix2 (7589939356868904) (-57); Float radix2 (7929066284926508) (-60); Float radix2 (7536313351446028) (-56); Float radix2 (4976720244107814) (-56); Float radix2 (8022526045111370) (-56)];
      [:: Float radix2 (-7033985053027872) (-58); Float radix2 (4845789589756170) (-59); Float radix2 (4927591319735058) (-57); Float radix2 (-7617757374344892) (-58); Float radix2 (6882711435003516) (-58);
          Float radix2 (-6719466415635180) (-57); Float radix2 (6037921306755300) (-57); Float radix2 (-8840859330066986) (-57); Float radix2 (7024552006960516) (-56); Float radix2 (-6668792618078498) (-58);
          Float radix2 (8221258625148396) (-57); Float radix2 (8466573616076122) (-57); Float radix2 (6499329975842892) (-57); Float radix2 (6819000912525406) (-57); Float radix2 (6090952019037832) (-57);
          Float radix2 (7943128471804772) (-57); Float radix2 (8484446959930006) (-57); Float radix2 (5632191323171780) (-60); Float radix2 (-8098781733441180) (-57); Float radix2 (5903699283920232) (-57);
          Float radix2 (-4651218087119414) (-56); Float radix2 (5392416215328332) (-57); Float radix2 (-6484876714235434) (-56); Float radix2 (8034879346256906) (-57); Float radix2 (4592784632519172) (-58);
          Float radix2 (7221183694964106) (-57); Float radix2 (7198582319640446) (-57); Float radix2 (6714979840430486) (-57); Float radix2 (7259306823761900) (-57); Float radix2 (8078566903076776) (-57);
          Float radix2 (5242492421367164) (-58); Float radix2 (-5446434806578706) (-56); Float radix2 (5966278839867418) (-57); Float radix2 (5100165278420334) (-51); Float radix2 (6819547213672600) (-57);
          Float radix2 (4851542839107852) (-57); Float radix2 (4590847948198512) (-56); Float radix2 (4802269725896774) (-56); Float radix2 (8581090429059022) (-57); Float radix2 (7235406387984282) (-57);
          Float radix2 (-5671228092950932) (-56); Float radix2 (5773686686393560) (-56); Float radix2 (5454639159606112) (-56); Float radix2 (6216236124789562) (-56); Float radix2 (5811064249017172) (-55)];
      [:: Float radix2 (8033732925470086) (-60); Float radix2 (-6563039445247458) (-59); Float radix2 (5785559582623188) (-58); Float radix2 (5821574197023788) (-59); Float radix2 (8429455490153796) (-59);
          Float radix2 (8711384157916658) (-58); Float radix2 (4915306166500066) (-58); Float radix2 (5060463875971598) (-56); Float radix2 (-4836257039445228) (-57); Float radix2 (-4530931179546818) (-58);
          Float radix2 (5858370741628900) (-57); Float radix2 (8742221193259522) (-57); Float radix2 (5160243830666702) (-57); Float radix2 (7886582249123708) (-57); Float radix2 (6061709355894108) (-57);
          Float radix2 (4875921441286478) (-56); Float radix2 (6340606689254846) (-56); Float radix2 (6455052635704450) (-60); Float radix2 (7340803586319424) (-57); Float radix2 (-7520952903331564) (-62);
          Float radix2 (6648811648352388) (-57); Float radix2 (-4731247797095876) (-57); Float radix2 (8141794198980706) (-57); Float radix2 (-4764731309693302) (-56); Float radix2 (5331934722010452) (-58);
          Float radix2 (5125764029083174) (-57); Float radix2 (8434581273296438) (-57); Float radix2 (5348300708582318) (-57); Float radix2 (8778865868821392) (-57); Float radix2 (5122173907485384) (-56);
          Float radix2 (6553353829664326) (-59); Float radix2 (6630367684059188) (-57); Float radix2 (-8083366674233104) (-58); Float radix2 (6819547213672600) (-57); Float radix2 (5119022027240461) (-51);
          Float radix2 (6536952590923150) (-57); Float radix2 (6886113606044790) (-57); Float radix2 (4729732881824776) (-56); Float radix2 (4615280923804782) (-56); Float radix2 (5173165665799860) (-57);
          Float radix2 (4987678848121518) (-56); Float radix2 (-5411020604784310) (-57); Float radix2 (5725558183011240) (-56); Float radix2 (6373783430989070) (-56); Float radix2 (8652012760595706) (-59)];
      [:: Float radix2 (-5446793921934910) (-56); Float radix2 (-5987699930397472) (-61); Float radix2 (6489189157878876) (-56); Float radix2 (5938911389711198) (-60); Float radix2 (5335529682329294) (-57);
          Float radix2 (5739298782693944) (-59); Float radix2 (5471459243945480) (-58); Float radix2 (5985022368960354) (-58); Float radix2 (6609176992702910) (-58); Float radix2 (-5142770797983562) (-54);
          Float radix2 (6973412867119864) (-56); Float radix2 (6963584425930958) (-58); Float radix2 (5888236279758894) (-57); Float radix2 (-4738202919172788) (-59); Float radix2 (6783742217942368) (-58);
          Float radix2 (-5731013122227988) (-59); Float radix2 (4560866503770012) (-57); Float radix2 (-8905974274607702) (-57); Float radix2 (5808794165199200) (-56); Float radix2 (5344087801974888) (-56);
          Float radix2 (5000631896851598) (-57); Float radix2 (7832725188985288) (-58); Float radix2 (8272403763928152) (-58); Float radix2 (8448362530751178) (-58); Float radix2 (-4835991376498926) (-54);
          Float radix2 (6513504056724428) (-57); Float radix2 (-6487888619774370) (-57); Float radix2 (7041514717191954) (-58); Float radix2 (-5743235710041892) (-57); Float radix2 (7652421827176110) (-58);
          Float radix2 (4901211887605404) (-58); Float radix2 (5517278834347432) (-57); Float radix2 (6573016668512046) (-57); Float radix2 (4851542839107852) (-57); Float radix2 (6536952590923150) (-57);
          Float radix2 (4850102595277787) (-51); Float radix2 (8556087156028404) (-58); Float radix2 (-7663681482596228) (-57); Float radix2 (4844635188740926) (-57); Float radix2 (6459128761136864) (-57);
          Float radix2 (6944777875948838) (-57); Float radix2 (6655093878374322) (-56); Float radix2 (-4586695404317680) (-54); Float radix2 (7391779804784046) (-57); Float radix2 (4947016939814436) (-55)];
      [:: Float radix2 (-8889975167257972) (-58); Float radix2 (-6388343512967440) (-59); Float radix2 (7928578370295452) (-58); Float radix2 (5544778852790110) (-58); Float radix2 (5455361668217462) (-58);
          Float radix2 (6224198836423194) (-58); Float radix2 (6575742313511470) (-58); Float radix2 (4981821940365222) (-57); Float radix2 (8205974791748322) (-57); Float radix2 (-5239375595025462) (-59);
          Float radix2 (-6270701575529918) (-56); Float radix2 (4800194017013460) (-56); Float radix2 (-8651130303265456) (-57); Float radix2 (6574400942267704) (-57); Float radix2 (-7059549485570422) (-57);
          Float radix2 (6147223718965728) (-57); Float radix2 (-6095661381565118) (-57); Float radix2 (7604956452478470) (-58); Float radix2 (6257470173068746) (-56); Float radix2 (6561340801703782) (-57);
          Float radix2 (7235042793699318) (-57); Float radix2 (8834721059903624) (-58); Float radix2 (6993479028013466) (-57); Float radix2 (5733161760028270) (-57); Float radix2 (5914378113954546) (-58);
          Float radix2 (-7642721865650544) (-56); Float radix2 (7460276343683832) (-57); Float radix2 (-5523136464070662) (-56); Float radix2 (5662321648798400) (-57); Float radix2 (-8518220658437140) (-57);
          Float radix2 (4696252677947548) (-58); Float radix2 (4693217180068346) (-56); Float radix2 (6322696616040822) (-57); Float radix2 (4590847948198512) (-56); Float radix2 (6886113606044790) (-57);
          Float radix2 (8556087156028404) (-58); Float radix2 (5094983161521185) (-51); Float radix2 (7875689757795198) (-57); Float radix2 (-7412624076869620) (-57); Float radix2 (7740065203982784) (-57);
          Float radix2 (7586342797352936) (-56); Float radix2 (5549722888347802) (-56); Float radix2 (8644822358006828) (-57); Float radix2 (-5295612048381484) (-57); Float radix2 (5222506801138606) (-55)];
      [:: Float radix2 (-5133469146403844) (-57); Float radix2 (-7954900233296084) (-59); Float radix2 (8986421551191778) (-58); Float radix2 (8143977921030682) (-59); Float radix2 (8430073304792180) (-58);
          Float radix2 (7527086327728516) (-58); Float radix2 (6070035659571174) (-57); Float radix2 (8110554854100554) (-57); Float radix2 (6554681738356750) (-56); Float radix2 (-8578658960915372) (-58);
          Float radix2 (4738191482646974) (-56); Float radix2 (-7205115744971364) (-58); Float radix2 (6937025841826436) (-57); Float radix2 (-5620124290762562) (-57); Float radix2 (6644729347707078) (-57);
          Float radix2 (-5021628879730896) (-56); Float radix2 (4618823169546238) (-56); Float radix2 (6095378701667716) (-57); Float radix2 (4999048143511020) (-56); Float radix2 (7662563228475042) (-57);
          Float radix2 (7546075143732062) (-57); Float radix2 (7090156263066478) (-57); Float radix2 (8554650749894128) (-57); Float radix2 (4602696307234490) (-56); Float radix2 (-7536252850108512) (-57);
          Float radix2 (7582660783573554) (-57); Float radix2 (-7522731415067314) (-57); Float radix2 (6090814827283822) (-57); Float radix2 (-5655272543519904) (-56); Float radix2 (7793906527448230) (-57);
          Float radix2 (6190543931810000) (-57); Float radix2 (8971581558162696) (-57); Float radix2 (5176381048538140) (-56); Float radix2 (4802269725896774) (-56); Float radix2 (4729732881824776) (-56);
          Float radix2 (-7663681482596228) (-57); Float radix2 (7875689757795198) (-57); Float radix2 (5198790608945012) (-51); Float radix2 (5380211377785962) (-56); Float radix2 (8719576810195586) (-56);
          Float radix2 (6118941040488666) (-56); Float radix2 (8050119745353120) (-56); Float radix2 (-8058307885859638) (-59); Float radix2 (7107551190317622) (-56); Float radix2 (5151532197835158) (-54)];
      [:: Float radix2 (-8105636125466376) (-58); Float radix2 (-5642074975334222) (-59); Float radix2 (8901663979041946) (-59); Float radix2 (6356582013572330) (-59); Float radix2 (7835756930425692) (-59);
          Float radix2 (6947742095267796) (-58); Float radix2 (4969581528164432) (-57); Float radix2 (8148523052449862) (-57); Float radix2 (8113159316068172) (-56); Float radix2 (-5660164575125680) (-58);
          Float radix2 (-7861102953552726) (-60); Float radix2 (8616784477207354) (-57); Float radix2 (-6987071813205924) (-58); Float radix2 (7393494157086166) (-57); Float radix2 (-8051839479251230) (-57);
          Float radix2 (8314430763075818) (-57); Float radix2 (-4771331606487784) (-55); Float radix2 (-6552171396768808) (-61); Float radix2 (4528587408825782) (-56); Float radix2 (5088787676390254) (-57);
          Float radix2 (7645696548145768) (-57); Float radix2 (5097594283973526) (-57); Float radix2 (8580787882838114) (-57); Float radix2 (5179069376184562) (-56); Float radix2 (4606518228624414) (-58);
          Float radix2 (-6028318282917926) (-57); Float radix2 (7267510945462788) (-57); Float radix2 (-4874601599974312) (-56); Float radix2 (6941671465223806) (-57); Float radix2 (-5381713099712016) (-55);
          Float radix2 (8525760189799400) (-59); Float radix2 (4929846918924248) (-56); Float radix2 (7270578149887832) (-57); Float radix2 (8581090429059022) (-57); Float radix2 (4615280923804782) (-56);
          Float radix2 (4844635188740926) (-57); Float radix2 (-7412624076869620) (-57); Float radix2 (5380211377785962) (-56); Float radix2 (5043925050886501) (-51); Float radix2 (4910210093655990) (-56);
          Float radix2 (5874860986888950) (-56); Float radix2 (7185672173276914) (-56); Float radix2 (6343282919455326) (-56); Float radix2 (-4679512014279132) (-55); Float radix2 (7400737766417018) (-55)];
      [:: Float radix2 (-7443775803904786) (-57); Float radix2 (6455896965525616) (-59); Float radix2 (6864498037078556) (-56); Float radix2 (5759388251237058) (-60); Float radix2 (6196198118022848) (-57);
          Float radix2 (7222893343766008) (-59); Float radix2 (7160449112747158) (-57); Float radix2 (4757295885076852) (-57); Float radix2 (8960867265706210) (-56); Float radix2 (-8062546982040370) (-56);
          Float radix2 (5984621269683700) (-56); Float radix2 (8661896665679734) (-56); Float radix2 (5510436931595492) (-57); Float radix2 (4600262680006884) (-56); Float radix2 (8442101413922118) (-58);
          Float radix2 (8263337027671928) (-57); Float radix2 (6637446180064074) (-57); Float radix2 (-8865900898290236) (-55); Float radix2 (5813889239684972) (-56); Float radix2 (-6807363357728386) (-60);
          Float radix2 (6968173706706218) (-57); Float radix2 (-8754008831935288) (-60); Float radix2 (6394828838107202) (-57); Float radix2 (4720369973795288) (-57); Float radix2 (6714567437454310) (-59);
          Float radix2 (6479686562218874) (-57); Float radix2 (6035240123917054) (-56); Float radix2 (5119920405488218) (-57); Float radix2 (5079147038645946) (-56); Float radix2 (7367578840364474) (-57);
          Float radix2 (-6358167134404280) (-55); Float radix2 (7945579945169656) (-57); Float radix2 (-7495731361459338) (-59); Float radix2 (7235406387984282) (-57); Float radix2 (5173165665799860) (-57);
          Float radix2 (6459128761136864) (-57); Float radix2 (7740065203982784) (-57); Float radix2 (8719576810195586) (-56); Float radix2 (4910210093655990) (-56); Float radix2 (4948016218908487) (-51);
          Float radix2 (4876098836954858) (-56); Float radix2 (5911793375808846) (-56); Float radix2 (7271891496418916) (-56); Float radix2 (6285912886035696) (-56); Float radix2 (4861057341471284) (-56)];
      [:: Float radix2 (-7995631704009046) (-58); Float radix2 (-6211350059734020) (-60); Float radix2 (5659011303437058) (-57); Float radix2 (-5356376380708200) (-59); Float radix2 (8534436610675266) (-58);
          Float radix2 (-8384857745883972) (-59); Float radix2 (5687385804952588) (-57); Float radix2 (-5548767824861902) (-57); Float radix2 (5785758576753686) (-56); Float radix2 (-6248151488247924) (-58);
          Float radix2 (4732738070800020) (-56); Float radix2 (8485267684295822) (-57); Float radix2 (6165374170543664) (-57); Float radix2 (6695570820703524) (-57); Float radix2 (6092878393141932) (-57);
          Float radix2 (7731987922600632) (-57); Float radix2 (7419722120062860) (-57); Float radix2 (7983108038189908) (-59); Float radix2 (-5740104780427212) (-56); Float radix2 (7454681689281580) (-57);
          Float radix2 (-4711924439433356) (-56); Float radix2 (5543435367371616) (-57); Float radix2 (-5581639204629914) (-56); Float radix2 (7470271346076606) (-57); Float radix2 (4576204784908920) (-58);
          Float radix2 (8812973680859942) (-57); Float radix2 (8613461171213838) (-57); Float radix2 (8622984657154268) (-57); Float radix2 (8771167335412694) (-57); Float radix2 (7798154179623974) (-57);
          Float radix2 (6902549093294544) (-58); Float radix2 (-6909022834119286) (-56); Float radix2 (7589939356868904) (-57); Float radix2 (-5671228092950932) (-56); Float radix2 (4987678848121518) (-56);
          Float radix2 (6944777875948838) (-57); Float radix2 (7586342797352936) (-56); Float radix2 (6118941040488666) (-56); Float radix2 (5874860986888950) (-56); Float radix2 (4876098836954858) (-56);
          Float radix2 (5172285344424103) (-51); Float radix2 (7619757675118764) (-56); Float radix2 (6651750739131824) (-56); Float radix2 (5576088635315968) (-55); Float radix2 (5793337377927518) (-55)];
      [:: Float radix2 (-7361128551397682) (-60); Float radix2 (-5487019684369790) (-59); Float radix2 (5599799806874930) (-57); Float radix2 (8148240233131118) (-59); Float radix2 (6338098853815494) (-57);
          Float radix2 (8712389130460260) (-58); Float radix2 (5796573647477834) (-57); Float radix2 (8690053288680376) (-57); Float radix2 (6119783606730258) (-57); Float radix2 (-5047888939892976) (-57);
          Float radix2 (7914340667765332) (-57); Float radix2 (5468328751456858) (-56); Float radix2 (6307814442854798) (-57); Float radix2 (4920993448057736) (-56); Float radix2 (6674322163409598) (-57);
          Float radix2 (5236235263321436) (-56); Float radix2 (6515920970490836) (-56); Float radix2 (-6519998601347924) (-59); Float radix2 (5607332404901132) (-56); Float radix2 (5031112105783030) (-59);
          Float radix2 (8421868547125960) (-57); Float radix2 (-8248225954480356) (-59); Float radix2 (8971423048371490) (-57); Float radix2 (-7764704974649698) (-57); Float radix2 (7981879511272536) (-58);
          Float radix2 (8008829575611878) (-57); Float radix2 (6391118293145504) (-56); Float radix2 (7938850143090502) (-57); Float radix2 (5337180430592346) (-56); Float radix2 (5571756346381514) (-56);
          Float radix2 (8348346766568556) (-60); Float radix2 (5089148476202710) (-56); Float radix2 (7929066284926508) (-60); Float radix2 (5773686686393560) (-56); Float radix2 (-5411020604784310) (-57);
          Float radix2 (6655093878374322) (-56); Float radix2 (5549722888347802) (-56); Float radix2 (8050119745353120) (-56); Float radix2 (7185672173276914) (-56); Float radix2 (5911793375808846) (-56);
          Float radix2 (7619757675118764) (-56); Float radix2 (5297004933374997) (-51); Float radix2 (6191252103208176) (-55); Float radix2 (4884387483530326) (-55); Float radix2 (6087921752663004) (-56)];
      [:: Float radix2 (-4709532446408148) (-56); Float radix2 (-4803003435055892) (-59); Float radix2 (5640259959985006) (-56); Float radix2 (7072629826201820) (-65); Float radix2 (7617860154639514) (-58);
          Float radix2 (4967216011789264) (-58); Float radix2 (4614394612227160) (-57); Float radix2 (7216222237044500) (-57); Float radix2 (8880958337196128) (-57); Float radix2 (-5159036757121510) (-55);
          Float radix2 (6709666213975984) (-56); Float radix2 (4969071898678524) (-57); Float radix2 (7314969530207498) (-57); Float radix2 (-6013373338417160) (-63); Float radix2 (5575639971657294) (-57);
          Float radix2 (-8789053238205116) (-58); Float radix2 (7989932515035288) (-57); Float radix2 (-8715819170116492) (-59); Float radix2 (4732318572200914) (-56); Float radix2 (8937442921429150) (-57);
          Float radix2 (7430271597278148) (-57); Float radix2 (7497551865720014) (-57); Float radix2 (4540997534634486) (-56); Float radix2 (7423856577638464) (-57); Float radix2 (-7006431808223374) (-55);
          Float radix2 (7605658360798332) (-57); Float radix2 (-8844221052171038) (-58); Float radix2 (6071553092101014) (-57); Float radix2 (-5512923480344194) (-57); Float radix2 (4893664508773944) (-56);
          Float radix2 (8153332196146832) (-58); Float radix2 (4960394929328228) (-56); Float radix2 (7536313351446028) (-56); Float radix2 (5454639159606112) (-56); Float radix2 (5725558183011240) (-56);
          Float radix2 (-4586695404317680) (-54); Float radix2 (8644822358006828) (-57); Float radix2 (-8058307885859638) (-59); Float radix2 (6343282919455326) (-56); Float radix2 (7271891496418916) (-56);
          Float radix2 (6651750739131824) (-56); Float radix2 (6191252103208176) (-55); Float radix2 (5099189091485583) (-51); Float radix2 (5782296156810944) (-56); Float radix2 (5251605121861420) (-54)];
      [:: Float radix2 (-4528558144288422) (-57); Float radix2 (-4826142269040368) (-59); Float radix2 (4646072998687058) (-58); Float radix2 (5168509628756856) (-59); Float radix2 (8141405791517510) (-59);
          Float radix2 (7790784749200516) (-58); Float radix2 (4920367658775482) (-57); Float radix2 (7928628345232172) (-57); Float radix2 (8157395388231058) (-56); Float radix2 (-4978237507088716) (-58);
          Float radix2 (-6221425316992926) (-58); Float radix2 (5430853655311472) (-56); Float radix2 (-5137208665291358) (-58); Float radix2 (8033549631072668) (-57); Float radix2 (-5376985405968398) (-57);
          Float radix2 (8123639643461170) (-57); Float radix2 (-8968788212144722) (-56); Float radix2 (-5266293184603584) (-60); Float radix2 (5653449446009212) (-56); Float radix2 (6776290367180634) (-57);
          Float radix2 (5040479259278096) (-56); Float radix2 (6667019919670726) (-57); Float radix2 (4514992845924774) (-56); Float radix2 (5126039845688406) (-56); Float radix2 (6214524647769224) (-58);
          Float radix2 (-8360936637120718) (-57); Float radix2 (4673041133288360) (-56); Float radix2 (-6846447917403978) (-57); Float radix2 (5116296808699804) (-56); Float radix2 (-8353516434164502) (-56);
          Float radix2 (8467377396062094) (-58); Float radix2 (8135897539983644) (-56); Float radix2 (4976720244107814) (-56); Float radix2 (6216236124789562) (-56); Float radix2 (6373783430989070) (-56);
          Float radix2 (7391779804784046) (-57); Float radix2 (-5295612048381484) (-57); Float radix2 (7107551190317622) (-56); Float radix2 (-4679512014279132) (-55); Float radix2 (6285912886035696) (-56);
          Float radix2 (5576088635315968) (-55); Float radix2 (4884387483530326) (-55); Float radix2 (5782296156810944) (-56); Float radix2 (5081151666169579) (-51); Float radix2 (7517649830094456) (-55)];
      [:: Float radix2 (-7636973110341414) (-57); Float radix2 (-7709312860808540) (-60); Float radix2 (5433649846264550) (-55); Float radix2 (7601802294109542) (-59); Float radix2 (8892759711277622) (-56);
          Float radix2 (5423200968213758) (-57); Float radix2 (5077633779529286) (-55); Float radix2 (6459972511989286) (-56); Float radix2 (4516938180296910) (-54); Float radix2 (-5077935334828322) (-55);
          Float radix2 (8188985704976572) (-56); Float radix2 (6307279331472880) (-55); Float radix2 (6148353383444628) (-56); Float radix2 (5126088568660316) (-55); Float radix2 (6428535741135422) (-56);
          Float radix2 (4575707050322780) (-55); Float radix2 (5249750662838926) (-55); Float radix2 (-6450699784183342) (-55); Float radix2 (5668113623329494) (-55); Float radix2 (5910521026878414) (-56);
          Float radix2 (8292893990428252) (-56); Float radix2 (5004201026610204) (-56); Float radix2 (4959071779322868) (-55); Float radix2 (8706942139305310) (-57); Float radix2 (6365330299893606) (-57);
          Float radix2 (8348050633893708) (-56); Float radix2 (7699942999984098) (-55); Float radix2 (7820405378497060) (-56); Float radix2 (5776864848772244) (-55); Float radix2 (5737014148144790) (-55);
          Float radix2 (-7504924686065434) (-55); Float radix2 (5235518204119618) (-55); Float radix2 (8022526045111370) (-56); Float radix2 (5811064249017172) (-55); Float radix2 (8652012760595706) (-59);
          Float radix2 (4947016939814436) (-55); Float radix2 (5222506801138606) (-55); Float radix2 (5151532197835158) (-54); Float radix2 (7400737766417018) (-55); Float radix2 (4861057341471284) (-56);
          Float radix2 (5793337377927518) (-55); Float radix2 (6087921752663004) (-56); Float radix2 (5251605121861420) (-54); Float radix2 (7517649830094456) (-55); Float radix2 (6866660949825620) (-51)]].

Time Eval vm_compute in map (map B2F) (cholesky m8).

(* size 55, positive definite *)
Definition m9 := map (map b64_normalize)
  [:: [:: Float radix2 (4948616174949527) (-53); Float radix2 (4613439333249439) (-55); Float radix2 (-7642976984091443) (-54); Float radix2 (-5817121129155008) (-57); Float radix2 (-5830210004078894) (-54);
          Float radix2 (-8289140700220633) (-56); Float radix2 (-7007841016430853) (-56); Float radix2 (5052887833147554) (-57); Float radix2 (5294152888315646) (-55); Float radix2 (6072881432532926) (-55);
          Float radix2 (6441256027802954) (-55); Float radix2 (-4767187777618678) (-57); Float radix2 (-8907440377085863) (-59); Float radix2 (-8566417470575370) (-56); Float radix2 (-6374909364587220) (-57);
          Float radix2 (-6091906501203892) (-57); Float radix2 (-6958397194975532) (-58); Float radix2 (5441919537240624) (-56); Float radix2 (8426289887506719) (-56); Float radix2 (-4563693698751689) (-53);
          Float radix2 (-6277080544373593) (-56); Float radix2 (-8362654729315226) (-56); Float radix2 (-5394296604895518) (-55); Float radix2 (5300996249835889) (-56); Float radix2 (5892198286404979) (-58);
          Float radix2 (8118745610733304) (-55); Float radix2 (6890352826721833) (-55); Float radix2 (-6119686682860162) (-56); Float radix2 (-5272801495329036) (-56); Float radix2 (-5802496571819831) (-55);
          Float radix2 (-7283672568615945) (-56); Float radix2 (-5641380652212573) (-57); Float radix2 (7428034608274604) (-57); Float radix2 (4771030569741338) (-55); Float radix2 (-8706082582581517) (-55);
          Float radix2 (-6324643346817721) (-59); Float radix2 (5162666563645130) (-56); Float radix2 (6955982078216938) (-61); Float radix2 (6066990124460158) (-55); Float radix2 (7250815373058611) (-56);
          Float radix2 (-4819126808945325) (-55); Float radix2 (-6513979511013357) (-57); Float radix2 (-5045305332122827) (-57); Float radix2 (7346501773903744) (-57); Float radix2 (6363825724650215) (-55);
          Float radix2 (6670302940630024) (-58); Float radix2 (-7545426726297108) (-57); Float radix2 (8824271581252179) (-56); Float radix2 (7524178601613986) (-57); Float radix2 (-8683113771026343) (-58);
          Float radix2 (6650609107206260) (-57); Float radix2 (5979965524073339) (-55); Float radix2 (6042954174369836) (-55); Float radix2 (8392874863369318) (-57); Float radix2 (7655224865430619) (-56)];
      [:: Float radix2 (4613439333249439) (-55); Float radix2 (5579670056501009) (-52); Float radix2 (8645097421683892) (-57); Float radix2 (-7214398706330009) (-52); Float radix2 (-6128637792364661) (-54);
          Float radix2 (-5323754936796308) (-53); Float radix2 (7644924734589648) (-56); Float radix2 (7594513188880758) (-57); Float radix2 (8448017757615004) (-54); Float radix2 (8382906941481637) (-54);
          Float radix2 (4587354057628521) (-54); Float radix2 (7627902415034837) (-58); Float radix2 (-5193758669552699) (-55); Float radix2 (5991566659430803) (-56); Float radix2 (-5422633208049825) (-55);
          Float radix2 (7277030661496701) (-56); Float radix2 (-5507597179457772) (-55); Float radix2 (7364466887134357) (-55); Float radix2 (6600915920928178) (-55); Float radix2 (-8984686261424692) (-55);
          Float radix2 (-7758709652592201) (-53); Float radix2 (-5274516708760473) (-53); Float radix2 (-5452373814254882) (-55); Float radix2 (-7634595133991116) (-57); Float radix2 (4865978629507765) (-54);
          Float radix2 (5199788622272154) (-54); Float radix2 (7030716718733755) (-54); Float radix2 (-6759500807336781) (-63); Float radix2 (-7922157603356308) (-54); Float radix2 (-5901808904115106) (-54);
          Float radix2 (-7887982237236882) (-56); Float radix2 (-6430639134717669) (-55); Float radix2 (5979557339574092) (-55); Float radix2 (5420994808298673) (-54); Float radix2 (-4637027261748401) (-55);
          Float radix2 (-6622642171178803) (-55); Float radix2 (5735820517222672) (-56); Float radix2 (8625988706136560) (-56); Float radix2 (4800944203936869) (-55); Float radix2 (7709301135965633) (-55);
          Float radix2 (-5332948127864159) (-55); Float radix2 (-5695994977829855) (-55); Float radix2 (-7661605223029987) (-56); Float radix2 (5356584713883744) (-54); Float radix2 (6684022803050698) (-54);
          Float radix2 (-5646068652244605) (-66); Float radix2 (-6090197138528062) (-55); Float radix2 (6353354617928129) (-57); Float radix2 (6884829887381514) (-55); Float radix2 (-4783512488360534) (-57);
          Float radix2 (5236767724416579) (-55); Float radix2 (7807322357494331) (-55); Float radix2 (6854142789807986) (-56); Float radix2 (4717651962967857) (-54); Float radix2 (5753232666759987) (-56)];
      [:: Float radix2 (-7642976984091443) (-54); Float radix2 (8645097421683892) (-57); Float radix2 (5369597253423073) (-51); Float radix2 (-5805856431242288) (-54); Float radix2 (-8685538504917502) (-52);
          Float radix2 (8294503132436182) (-60); Float radix2 (-5781029491534111) (-53); Float radix2 (6179241819266479) (-54); Float radix2 (8761115550383951) (-55); Float radix2 (7210845987800472) (-55);
          Float radix2 (-4915792945801850) (-55); Float radix2 (4550289378388025) (-54); Float radix2 (-8815470236802569) (-55); Float radix2 (6392086101546970) (-54); Float radix2 (-5251017745099231) (-57);
          Float radix2 (8558876414731043) (-57); Float radix2 (-6175834336481601) (-56); Float radix2 (-6866755243143901) (-56); Float radix2 (8451541868098729) (-57); Float radix2 (5591629168183517) (-56);
          Float radix2 (-4914873963453508) (-53); Float radix2 (-4689305470393815) (-53); Float radix2 (-7002357864777241) (-57); Float radix2 (8064874315380520) (-57); Float radix2 (7402805415883056) (-55);
          Float radix2 (8111669368051231) (-59); Float radix2 (-5605619728302842) (-55); Float radix2 (5965170185439928) (-58); Float radix2 (-5161993835016395) (-58); Float radix2 (-6536018746381718) (-56);
          Float radix2 (-5518852661081221) (-56); Float radix2 (-5269911690106588) (-55); Float radix2 (8936046337086542) (-58); Float radix2 (4616753314048758) (-54); Float radix2 (6595290261736937) (-54);
          Float radix2 (7145260716856725) (-55); Float radix2 (7815961740068248) (-56); Float radix2 (6159889323030219) (-60); Float radix2 (-5904611720519977) (-55); Float radix2 (-6676024026659671) (-55);
          Float radix2 (5866916783145904) (-56); Float radix2 (-5345684139364454) (-58); Float radix2 (8465238974960245) (-56); Float radix2 (8044141471529490) (-55); Float radix2 (5315978898643783) (-56);
          Float radix2 (5573874216202666) (-56); Float radix2 (-5350229315865976) (-56); Float radix2 (-6694939527005720) (-55); Float radix2 (4640642452632431) (-57); Float radix2 (7610627282428631) (-55);
          Float radix2 (6152285561116884) (-57); Float radix2 (-8381803768116405) (-56); Float radix2 (-8429387108203587) (-58); Float radix2 (7662609878872630) (-55); Float radix2 (-6653528197072366) (-55)];
      [:: Float radix2 (-5817121129155008) (-57); Float radix2 (-7214398706330009) (-52); Float radix2 (-5805856431242288) (-54); Float radix2 (4664026768411127) (-50); Float radix2 (6105130710402065) (-55);
          Float radix2 (-5805599037055250) (-52); Float radix2 (-6161820321940441) (-58); Float radix2 (-4865111722477679) (-53); Float radix2 (-5527134128287933) (-55);
          Float radix2 (-7731711911305720) (-54); Float radix2 (-5820592730826204) (-55); Float radix2 (-8780876792203782) (-55); Float radix2 (4679290462929572) (-53); Float radix2 (-6681960659358356) (-54);
          Float radix2 (5557053525584568) (-54); Float radix2 (-4688850150903665) (-54); Float radix2 (7356287265284808) (-56); Float radix2 (-4993343388399281) (-54); Float radix2 (-4949671880420534) (-55);
          Float radix2 (-4922408692547791) (-57); Float radix2 (5327476976230184) (-53); Float radix2 (7667466884572059) (-54); Float radix2 (-7150889755905046) (-58); Float radix2 (6667529078518237) (-55);
          Float radix2 (-6367814842276355) (-54); Float radix2 (-6280418193855328) (-54); Float radix2 (-6183916068702789) (-54); Float radix2 (-5002491731308870) (-56); Float radix2 (5694263688189769) (-53);
          Float radix2 (5787922553414117) (-54); Float radix2 (-8248020857137575) (-56); Float radix2 (8787570695727477) (-56); Float radix2 (4845709863688774) (-58); Float radix2 (-7360632737413102) (-55);
          Float radix2 (4826487610966924) (-54); Float radix2 (7647855533316577) (-54); Float radix2 (6252680741894910) (-60); Float radix2 (-4721075587784649) (-54); Float radix2 (-4914796598282004) (-54);
          Float radix2 (-8533437791992679) (-55); Float radix2 (6543787565296866) (-57); Float radix2 (5553076570543601) (-54); Float radix2 (5366036549621618) (-54); Float radix2 (-7744727700257538) (-55);
          Float radix2 (-6320624197431359) (-54); Float radix2 (5634495180962716) (-58); Float radix2 (7326003914558141) (-59); Float radix2 (-6437363799793258) (-57); Float radix2 (7562043465751746) (-60);
          Float radix2 (8835214031002688) (-57); Float radix2 (-5380935978922171) (-57); Float radix2 (-5089738297970715) (-54); Float radix2 (5342128813366289) (-58); Float radix2 (-6678266687070615) (-57);
          Float radix2 (-5467652718319269) (-56)];
      [:: Float radix2 (-5830210004078894) (-54); Float radix2 (-6128637792364661) (-54); Float radix2 (-8685538504917502) (-52); Float radix2 (6105130710402065) (-55); Float radix2 (5767901768585052) (-50);
          Float radix2 (8800282369680949) (-56); Float radix2 (-7577091892725227) (-53); Float radix2 (-7383293040373679) (-54); Float radix2 (-5359221389603693) (-52); Float radix2 (-7342695004494139) (-54);
          Float radix2 (-4912132493372667) (-54); Float radix2 (4818603650014834) (-55); Float radix2 (-8893620392904899) (-55); Float radix2 (8401001038873485) (-56); Float radix2 (-8436956236742066) (-55);
          Float radix2 (6245885256142952) (-55); Float radix2 (4861564792309642) (-59); Float radix2 (4859270702683439) (-56); Float radix2 (-5767495461490995) (-54); Float radix2 (5157871455512579) (-53);
          Float radix2 (8905317035482784) (-54); Float radix2 (5341673038141136) (-53); Float radix2 (7370381466527835) (-54); Float radix2 (-6500632697006342) (-54); Float radix2 (-5417484228173940) (-54);
          Float radix2 (-5979727132086719) (-54); Float radix2 (-5919944912490577) (-55); Float radix2 (5685760691532363) (-54); Float radix2 (6625661161879531) (-56); Float radix2 (7149232942432849) (-54);
          Float radix2 (6751477725668520) (-54); Float radix2 (8075307453113248) (-54); Float radix2 (-5993673329444874) (-57); Float radix2 (-4543181096493995) (-53); Float radix2 (4803338536628193) (-54);
          Float radix2 (-8447768306128145) (-55); Float radix2 (-4594349922243351) (-54); Float radix2 (-5871718789934429) (-57); Float radix2 (7117090854867370) (-59); Float radix2 (-5039690797954162) (-58);
          Float radix2 (4820819377326802) (-54); Float radix2 (8221219958289595) (-55); Float radix2 (5045612577587891) (-57); Float radix2 (-5767514890799193) (-54); Float radix2 (-7561794937645611) (-54);
          Float radix2 (-7343073615346359) (-55); Float radix2 (8279736695291953) (-55); Float radix2 (5003882147504528) (-54); Float radix2 (-7427046211067375) (-56); Float radix2 (-4752572757507188) (-54);
          Float radix2 (-4536317326745498) (-54); Float radix2 (-6082190705540838) (-56); Float radix2 (-5660897563443618) (-54); Float radix2 (-7407677228519179) (-54); Float radix2 (-5099681884854006) (-56)];
      [:: Float radix2 (-8289140700220633) (-56); Float radix2 (-5323754936796308) (-53); Float radix2 (8294503132436182) (-60); Float radix2 (-5805599037055250) (-52); Float radix2 (8800282369680949) (-56);
          Float radix2 (5985087354539460) (-50); Float radix2 (-6869953375124714) (-54); Float radix2 (-7555397496138383) (-52); Float radix2 (-7385733980178402) (-53); Float radix2 (-4799853355311676) (-53);
          Float radix2 (-6494901190994575) (-56); Float radix2 (-4560822757713931) (-55); Float radix2 (7512812825381219) (-55); Float radix2 (-6651185121929524) (-54); Float radix2 (6671020614753330) (-56);
          Float radix2 (-8821691381869663) (-55); Float radix2 (6353573567309921) (-54); Float radix2 (-7949837881595862) (-55); Float radix2 (-7209862337054098) (-56); Float radix2 (7629133987934577) (-55);
          Float radix2 (7266505870089473) (-53); Float radix2 (6256469510937649) (-53); Float radix2 (-4859503111489701) (-57); Float radix2 (-8180123543883266) (-55); Float radix2 (-8180022810242208) (-54);
          Float radix2 (-7797763569223832) (-56); Float radix2 (-4749901839952367) (-56); Float radix2 (-6163213864658785) (-55); Float radix2 (4504307619892181) (-54); Float radix2 (5419363941533587) (-54);
          Float radix2 (5693940853325277) (-53); Float radix2 (5803564624233669) (-54); Float radix2 (-5916675650151916) (-54); Float radix2 (-8139986044261322) (-54); Float radix2 (-8814208541396210) (-57);
          Float radix2 (-5007688442147531) (-55); Float radix2 (-5494440984196218) (-54); Float radix2 (5910546216668233) (-60); Float radix2 (7307879818275467) (-56); Float radix2 (8339336876472298) (-57);
          Float radix2 (7758197552913119) (-54); Float radix2 (7468761388709681) (-55); Float radix2 (-5999491020580191) (-55); Float radix2 (-7598867204468332) (-54); Float radix2 (-5432612612923251) (-54);
          Float radix2 (8151792431320711) (-56); Float radix2 (5253197279268330) (-53); Float radix2 (7438185454395963) (-56); Float radix2 (-6426950580795255) (-54); Float radix2 (-7035940454879486) (-55);
          Float radix2 (-7726749128859824) (-56); Float radix2 (-8800133769805754) (-57); Float radix2 (-6605500573784286) (-55); Float radix2 (-7973913564190957) (-54); Float radix2 (6893029468799670) (-57)];
      [:: Float radix2 (-7007841016430853) (-56); Float radix2 (7644924734589648) (-56); Float radix2 (-5781029491534111) (-53); Float radix2 (-6161820321940441) (-58); Float radix2 (-7577091892725227) (-53);
          Float radix2 (-6869953375124714) (-54); Float radix2 (5105916167239448) (-50); Float radix2 (-8081947239053653) (-53); Float radix2 (-5681970463660177) (-52); Float radix2 (-6531950135814411) (-54);
          Float radix2 (-6845699652447132) (-57); Float radix2 (7856759653610091) (-57); Float radix2 (-4925852117845312) (-55); Float radix2 (5700300601233524) (-56); Float radix2 (-4711123680503672) (-54);
          Float radix2 (6655153326904175) (-55); Float radix2 (-6310006267040361) (-55); Float radix2 (5559198406132922) (-55); Float radix2 (-6450090375965515) (-55); Float radix2 (6231164327198985) (-54);
          Float radix2 (4923411798215532) (-54); Float radix2 (5014017220399677) (-55); Float radix2 (8971086880402592) (-58); Float radix2 (-8802692600895413) (-55); Float radix2 (6760502817079518) (-60);
          Float radix2 (-7918516976406020) (-57); Float radix2 (5495363401408080) (-55); Float radix2 (6358250999434496) (-56); Float radix2 (-8352269962896813) (-56); Float radix2 (7626199583812246) (-54);
          Float radix2 (7977905181652332) (-55); Float radix2 (5758906511251029) (-62); Float radix2 (-5815734265902751) (-56); Float radix2 (-7086499510950033) (-55); Float radix2 (-5899665755714806) (-55);
          Float radix2 (-5098966034308809) (-54); Float radix2 (-6977281627790649) (-57); Float radix2 (7397031070241821) (-57); Float radix2 (7820452534617537) (-56); Float radix2 (5924869113914737) (-55);
          Float radix2 (8762557436017480) (-57); Float radix2 (-8263629424464349) (-56); Float radix2 (-8129988699559275) (-56); Float radix2 (-6035483223291273) (-56); Float radix2 (-7204031589988434) (-57);
          Float radix2 (4666357760021424) (-55); Float radix2 (5667710499608331) (-56); Float radix2 (-6180782714506925) (-57); Float radix2 (-6111961179226044) (-56); Float radix2 (-8761584460918620) (-56);
          Float radix2 (-7397851676412588) (-57); Float radix2 (5232285029560115) (-56); Float radix2 (-6203056586474023) (-55); Float radix2 (-5695047772743175) (-55); Float radix2 (-4994343353321530) (-56)];
      [:: Float radix2 (5052887833147554) (-57); Float radix2 (7594513188880758) (-57); Float radix2 (6179241819266479) (-54); Float radix2 (-4865111722477679) (-53); Float radix2 (-7383293040373679) (-54);
          Float radix2 (-7555397496138383) (-52); Float radix2 (-8081947239053653) (-53); Float radix2 (6154030497906818) (-50); Float radix2 (-5198126708072517) (-53); Float radix2 (-6899218350439455) (-52);
          Float radix2 (-4870635175158290) (-58); Float radix2 (-5299630490402259) (-55); Float radix2 (4526066920280776) (-55); Float radix2 (6210130438711963) (-58); Float radix2 (5463117648153720) (-54);
          Float radix2 (-8397121726740020) (-55); Float radix2 (7427411323441012) (-55); Float radix2 (-5029206802077767) (-54); Float radix2 (-5978169403518903) (-54); Float radix2 (7068137819166173) (-57);
          Float radix2 (6449669235935607) (-68); Float radix2 (-5127199165574315) (-55); Float radix2 (-5527266298951049) (-58); Float radix2 (8582063354903080) (-55); Float radix2 (7975620209474399) (-54);
          Float radix2 (5844431933618193) (-55); Float radix2 (-6664830356364242) (-53); Float radix2 (-4748859234690121) (-57); Float radix2 (8004711241450818) (-54); Float radix2 (-8364566157595407) (-60);
          Float radix2 (-6667574382500631) (-55); Float radix2 (-8677640393264431) (-57); Float radix2 (-8606229974245686) (-56); Float radix2 (7504645653372605) (-58); Float radix2 (-6400701184042145) (-55);
          Float radix2 (7008046927381004) (-55); Float radix2 (5856087007397243) (-55); Float radix2 (5509661634689016) (-54); Float radix2 (7474294761902398) (-58); Float radix2 (-7458249466377257) (-55);
          Float radix2 (-6310793050624578) (-55); Float radix2 (-5594628442258019) (-55); Float radix2 (8524142233502607) (-56); Float radix2 (8059233057937532) (-57); Float radix2 (-6007648936483716) (-58);
          Float radix2 (8671257216139418) (-57); Float radix2 (-6731009104020048) (-56); Float radix2 (-6161111314556445) (-55); Float radix2 (-8214519681724268) (-57); Float radix2 (4767771239009284) (-54);
          Float radix2 (-6373784468807228) (-57); Float radix2 (-8188887712106757) (-56); Float radix2 (4917862773035000) (-56); Float radix2 (-7851156784105515) (-59); Float radix2 (-5585101848694409) (-56)];
      [:: Float radix2 (5294152888315646) (-55); Float radix2 (8448017757615004) (-54); Float radix2 (8761115550383951) (-55); Float radix2 (-5527134128287933) (-55); Float radix2 (-5359221389603693) (-52);
          Float radix2 (-7385733980178402) (-53); Float radix2 (-5681970463660177) (-52); Float radix2 (-5198126708072517) (-53); Float radix2 (8651373438966529) (-51); Float radix2 (-7759565370109270) (-54);
          Float radix2 (6152099666049898) (-56); Float radix2 (5959065816364789) (-57); Float radix2 (-6440534499836454) (-57); Float radix2 (5624560742278398) (-55); Float radix2 (-6409223469179303) (-56);
          Float radix2 (6341822484321677) (-56); Float radix2 (-8088421480069069) (-55); Float radix2 (8067682752936822) (-57); Float radix2 (4961687161556069) (-59); Float radix2 (-4869153363230965) (-55);
          Float radix2 (-7809213875318986) (-54); Float radix2 (-4625989858072827) (-54); Float radix2 (-5339822826960398) (-56); Float radix2 (8479355475573358) (-56); Float radix2 (5772788168088315) (-54);
          Float radix2 (-4517829328905850) (-53); Float radix2 (7901990313377945) (-54); Float radix2 (6177076631264223) (-55); Float radix2 (-8856577086441446) (-55); Float radix2 (-4923251751843711) (-54);
          Float radix2 (-6881082803358541) (-54); Float radix2 (-6892880403445247) (-55); Float radix2 (5520191769928556) (-55); Float radix2 (8138955929921216) (-54); Float radix2 (-6107140742768413) (-56);
          Float radix2 (4808895660438629) (-58); Float radix2 (8708200987985776) (-55); Float radix2 (6241866120605628) (-57); Float radix2 (-8513670156245324) (-55); Float radix2 (7756335039134226) (-55);
          Float radix2 (-6371387164005130) (-54); Float radix2 (-7182181689447252) (-55); Float radix2 (7930301242614811) (-57); Float radix2 (8046694542531842) (-55); Float radix2 (6151515555697786) (-54);
          Float radix2 (-6538359914843652) (-55); Float radix2 (-6348560251109615) (-54); Float radix2 (-6190097439194719) (-55); Float radix2 (4782477502932450) (-54); Float radix2 (6407863065772252) (-56);
          Float radix2 (8679017270896484) (-56); Float radix2 (5744038318506246) (-55); Float radix2 (5914745610607293) (-55); Float radix2 (4981957251820431) (-54); Float radix2 (5760723128902287) (-56)];
      [:: Float radix2 (6072881432532926) (-55); Float radix2 (8382906941481637) (-54); Float radix2 (7210845987800472) (-55); Float radix2 (-7731711911305720) (-54); Float radix2 (-7342695004494139) (-54);
          Float radix2 (-4799853355311676) (-53); Float radix2 (-6531950135814411) (-54); Float radix2 (-6899218350439455) (-52); Float radix2 (-7759565370109270) (-54); Float radix2 (6956548291457189) (-51);
          Float radix2 (7193726094153658) (-55); Float radix2 (8620170671773438) (-58); Float radix2 (-4752282654704517) (-56); Float radix2 (-7067356108083823) (-56); Float radix2 (-5262926598012377) (-56);
          Float radix2 (-5646499426765647) (-57); Float radix2 (-8018438726354646) (-55); Float radix2 (8179935788684770) (-56); Float radix2 (4704336609715644) (-53); Float radix2 (-4689923464742397) (-54);
          Float radix2 (-7736029358333132) (-55); Float radix2 (-4639043327396165) (-54); Float radix2 (-5418743475345968) (-58); Float radix2 (5076071883086167) (-56); Float radix2 (-5570404793308960) (-54);
          Float radix2 (7748080523719431) (-54); Float radix2 (8894349070511192) (-56); Float radix2 (-4735610988028777) (-55); Float radix2 (-6089012197396358) (-54); Float radix2 (-6896814809778807) (-54);
          Float radix2 (-7911771834927019) (-56); Float radix2 (-5865242566454450) (-55); Float radix2 (4854295628476038) (-54); Float radix2 (5190850504904299) (-54); Float radix2 (-4795952395506245) (-56);
          Float radix2 (6062073394858258) (-57); Float radix2 (4992351429367133) (-58); Float radix2 (-4842005402052777) (-55); Float radix2 (6891076013089666) (-55); Float radix2 (-5077663091337098) (-60);
          Float radix2 (-4722391218520754) (-55); Float radix2 (-4632237045749212) (-56); Float radix2 (-5598066146146421) (-55); Float radix2 (8866682104487429) (-55); Float radix2 (8785611688157459) (-55);
          Float radix2 (-8818910373658562) (-57); Float radix2 (-6417740301503238) (-55); Float radix2 (7299096651795105) (-56); Float radix2 (8138267847088906) (-56); Float radix2 (-8500876931073627) (-58);
          Float radix2 (4820955497456607) (-55); Float radix2 (4798061669642579) (-55); Float radix2 (6366256098495933) (-55); Float radix2 (4507821930961363) (-54); Float radix2 (5249182826103844) (-55)];
      [:: Float radix2 (6441256027802954) (-55); Float radix2 (4587354057628521) (-54); Float radix2 (-4915792945801850) (-55); Float radix2 (-5820592730826204) (-55); Float radix2 (-4912132493372667) (-54);
          Float radix2 (-6494901190994575) (-56); Float radix2 (-6845699652447132) (-57); Float radix2 (-4870635175158290) (-58); Float radix2 (6152099666049898) (-56); Float radix2 (7193726094153658) (-55);
          Float radix2 (6000682706847567) (-52); Float radix2 (-7829265951648157) (-55); Float radix2 (-7864042857666547) (-53); Float radix2 (-4649022294424624) (-53); Float radix2 (-5255270265599901) (-54);
          Float radix2 (-6746966053453156) (-57); Float radix2 (7091745344826196) (-56); Float radix2 (5899402728259788) (-54); Float radix2 (5666004510753933) (-54); Float radix2 (-7576431621461329) (-56);
          Float radix2 (8494695174346541) (-56); Float radix2 (-6809060161636851) (-54); Float radix2 (-8049851082758201) (-55); Float radix2 (-7564966969333283) (-57); Float radix2 (-8838649276730727) (-56);
          Float radix2 (7179101918659840) (-55); Float radix2 (5252924498231099) (-54); Float radix2 (-7373179853332707) (-52); Float radix2 (-8064992550397477) (-56); Float radix2 (-7364954936933970) (-55);
          Float radix2 (7132929087320197) (-57); Float radix2 (8143797759448387) (-56); Float radix2 (5965605132045218) (-55); Float radix2 (6677407221141618) (-55); Float radix2 (-5319467383454613) (-54);
          Float radix2 (-6881318345731391) (-57); Float radix2 (-4961358364387062) (-56); Float radix2 (-7970709136758395) (-57); Float radix2 (4648661457521504) (-54); Float radix2 (6216081568137374) (-54);
          Float radix2 (-5495570831503920) (-54); Float radix2 (-5358940174641313) (-59); Float radix2 (-6055428993329514) (-57); Float radix2 (8498325334980772) (-61); Float radix2 (4918398388272684) (-54);
          Float radix2 (8136146339642218) (-55); Float radix2 (-6352832386539949) (-56); Float radix2 (4970796117237271) (-54); Float radix2 (4523191879325806) (-55); Float radix2 (-6025252263549510) (-56);
          Float radix2 (6221402616084023) (-56); Float radix2 (6551476719684503) (-54); Float radix2 (5959062830221290) (-54); Float radix2 (8812690476034848) (-57); Float radix2 (6862746455978877) (-54)];
      [:: Float radix2 (-4767187777618678) (-57); Float radix2 (7627902415034837) (-58); Float radix2 (4550289378388025) (-54); Float radix2 (-8780876792203782) (-55); Float radix2 (4818603650014834) (-55);
          Float radix2 (-4560822757713931) (-55); Float radix2 (7856759653610091) (-57); Float radix2 (-5299630490402259) (-55); Float radix2 (5959065816364789) (-57); Float radix2 (8620170671773438) (-58);
          Float radix2 (-7829265951648157) (-55); Float radix2 (5768114854426498) (-51); Float radix2 (-8105965579208688) (-53); Float radix2 (-6099573681694768) (-52); Float radix2 (-5600570506047699) (-54);
          Float radix2 (-4997862723138160) (-54); Float radix2 (5369045285422030) (-55); Float radix2 (8442150640161233) (-57); Float radix2 (5011619408588334) (-55); Float radix2 (8555261247300533) (-54);
          Float radix2 (-5597218832657034) (-52); Float radix2 (7005459731288196) (-55); Float radix2 (-5616768159169402) (-55); Float radix2 (4883801599353563) (-55); Float radix2 (-4628824861531252) (-57);
          Float radix2 (4575399160363337) (-54); Float radix2 (7452774932464072) (-54); Float radix2 (-6343553093424534) (-56); Float radix2 (-5561077072115378) (-52); Float radix2 (6434693723140966) (-57);
          Float radix2 (-4538259342211998) (-56); Float radix2 (4959003974451007) (-56); Float radix2 (6882206787366952) (-56); Float radix2 (6027036416436242) (-55); Float radix2 (5349681391132715) (-55);
          Float radix2 (-7956677217473080) (-54); Float radix2 (7794864081441006) (-59); Float radix2 (5722589892516249) (-56); Float radix2 (6311377389650347) (-54); Float radix2 (4551668560517226) (-54);
          Float radix2 (7622123218018064) (-60); Float radix2 (-8627762384552681) (-55); Float radix2 (-5068350625704246) (-55); Float radix2 (4646887450493358) (-55); Float radix2 (8079165341578318) (-55);
          Float radix2 (-5313281562690545) (-56); Float radix2 (6780320954022419) (-56); Float radix2 (-7305294435044764) (-61); Float radix2 (5077172797123189) (-54); Float radix2 (-8461408789217643) (-55);
          Float radix2 (7280445105036037) (-55); Float radix2 (8748637061695611) (-55); Float radix2 (-8482796558098848) (-57); Float radix2 (8974263018041365) (-56); Float radix2 (8895719441833967) (-58)];
      [:: Float radix2 (-8907440377085863) (-59); Float radix2 (-5193758669552699) (-55); Float radix2 (-8815470236802569) (-55); Float radix2 (4679290462929572) (-53); Float radix2 (-8893620392904899) (-55);
          Float radix2 (7512812825381219) (-55); Float radix2 (-4925852117845312) (-55); Float radix2 (4526066920280776) (-55); Float radix2 (-6440534499836454) (-57); Float radix2 (-4752282654704517) (-56);
          Float radix2 (-7864042857666547) (-53); Float radix2 (-8105965579208688) (-53); Float radix2 (4897420642957166) (-50); Float radix2 (-6223978813822463) (-58); Float radix2 (-8374466918464595) (-53);
          Float radix2 (-4531994496706137) (-56); Float radix2 (-6620133875499592) (-53); Float radix2 (-7795631264697985) (-54); Float radix2 (-6991944021385273) (-54);
          Float radix2 (-5230349334612810) (-53); Float radix2 (4749634102010163) (-53); Float radix2 (-8536671139050627) (-54); Float radix2 (4835295800485129) (-53); Float radix2 (-5236107512877099) (-54);
          Float radix2 (5673701548505309) (-54); Float radix2 (7030062769796418) (-59); Float radix2 (-4532554400317830) (-55); Float radix2 (8572227707744849) (-54); Float radix2 (5805653109074715) (-54);
          Float radix2 (-5502952626647179) (-53); Float radix2 (-7747705006245161) (-58); Float radix2 (-4986228562311796) (-53); Float radix2 (-6255992861456613) (-55);
          Float radix2 (-6599391538752137) (-55); Float radix2 (7366941320903911) (-54); Float radix2 (6766056245315798) (-54); Float radix2 (-5809373060800200) (-55); Float radix2 (6557889884896051) (-54);
          Float radix2 (-5314810217653029) (-54); Float radix2 (-4756933956447855) (-54); Float radix2 (5909163594033986) (-54); Float radix2 (4780933652661440) (-56); Float radix2 (-8660515300292178) (-55);
          Float radix2 (6203741548992366) (-57); Float radix2 (6421172541857588) (-56); Float radix2 (6166051457768323) (-54); Float radix2 (4506206531872447) (-58); Float radix2 (-7448774565106818) (-55);
          Float radix2 (-4580264239892101) (-54); Float radix2 (8887412161570024) (-55); Float radix2 (7594473040396330) (-56); Float radix2 (-8856185441962742) (-56); Float radix2 (-7987505715018793) (-56);
          Float radix2 (-5925217804820315) (-57); Float radix2 (-5459038112797243) (-55)];
      [:: Float radix2 (-8566417470575370) (-56); Float radix2 (5991566659430803) (-56); Float radix2 (6392086101546970) (-54); Float radix2 (-6681960659358356) (-54); Float radix2 (8401001038873485) (-56);
          Float radix2 (-6651185121929524) (-54); Float radix2 (5700300601233524) (-56); Float radix2 (6210130438711963) (-58); Float radix2 (5624560742278398) (-55); Float radix2 (-7067356108083823) (-56);
          Float radix2 (-4649022294424624) (-53); Float radix2 (-6099573681694768) (-52); Float radix2 (-6223978813822463) (-58); Float radix2 (6055647650348640) (-50); Float radix2 (4739185317335543) (-56);
          Float radix2 (-4829449689255441) (-52); Float radix2 (-5482951793501150) (-53); Float radix2 (-8049274339569744) (-53); Float radix2 (-7392867055180816) (-54); Float radix2 (4714329835675945) (-59);
          Float radix2 (-6862174375032580) (-55); Float radix2 (6875270084076913) (-54); Float radix2 (-6608532893699492) (-54); Float radix2 (7360465132186484) (-54); Float radix2 (8662772452152584) (-55);
          Float radix2 (-8641177350178852) (-60); Float radix2 (-5314639650132905) (-53); Float radix2 (6538878978677921) (-53); Float radix2 (8358201338290403) (-57); Float radix2 (8296544431225698) (-57);
          Float radix2 (-7248048767031949) (-53); Float radix2 (-6216761191784658) (-55); Float radix2 (-6603232677580848) (-54); Float radix2 (5047107711437665) (-60); Float radix2 (8121707918211479) (-55);
          Float radix2 (7820029123916027) (-54); Float radix2 (5460738504970938) (-53); Float radix2 (-7272102803356020) (-55); Float radix2 (-6051835626539165) (-54); Float radix2 (-5588801825603152) (-53);
          Float radix2 (-7269429670455572) (-56); Float radix2 (4868892030011041) (-60); Float radix2 (5903569771580543) (-54); Float radix2 (8273042036478900) (-55); Float radix2 (-4761334285009622) (-56);
          Float radix2 (-8079477301321826) (-55); Float radix2 (4543743493146986) (-56); Float radix2 (-4872357587981668) (-54); Float radix2 (-4628354001721704) (-54); Float radix2 (7962845008446901) (-54);
          Float radix2 (7537888159974305) (-56); Float radix2 (-6927621884237680) (-54); Float radix2 (-8082922787602256) (-56); Float radix2 (6995992693127176) (-54); Float radix2 (-5338939834530455) (-54)];
      [:: Float radix2 (-6374909364587220) (-57); Float radix2 (-5422633208049825) (-55); Float radix2 (-5251017745099231) (-57); Float radix2 (5557053525584568) (-54); Float radix2 (-8436956236742066) (-55);
          Float radix2 (6671020614753330) (-56); Float radix2 (-4711123680503672) (-54); Float radix2 (5463117648153720) (-54); Float radix2 (-6409223469179303) (-56); Float radix2 (-5262926598012377) (-56);
          Float radix2 (-5255270265599901) (-54); Float radix2 (-5600570506047699) (-54); Float radix2 (-8374466918464595) (-53); Float radix2 (4739185317335543) (-56); Float radix2 (5826968465708168) (-50);
          Float radix2 (-4816878062743684) (-53); Float radix2 (-8711747457881294) (-53); Float radix2 (-4780542613939407) (-53); Float radix2 (-5387925887998310) (-53);
          Float radix2 (-4655148858487884) (-57); Float radix2 (6223444413490347) (-54); Float radix2 (-5001472705236812) (-54); Float radix2 (6143100947294213) (-54); Float radix2 (4833281271864895) (-55);
          Float radix2 (6268566509137818) (-54); Float radix2 (-7545332805375236) (-54); Float radix2 (-6557234986822473) (-54); Float radix2 (7592819790376053) (-54); Float radix2 (6925449043986450) (-55);
          Float radix2 (-7858538087651574) (-54); Float radix2 (-5576841226475155) (-55); Float radix2 (-5922973052486544) (-54); Float radix2 (5024469245838847) (-60); Float radix2 (-8135991825481322) (-56);
          Float radix2 (5038615524005191) (-55); Float radix2 (8085690551291497) (-54); Float radix2 (4526643871914046) (-55); Float radix2 (8768136841470974) (-57); Float radix2 (-8530446813906646) (-54);
          Float radix2 (-8421643176513708) (-55); Float radix2 (-5238774538735307) (-55); Float radix2 (7777785383701632) (-58); Float radix2 (7750768770282385) (-54); Float radix2 (4921334767993304) (-55);
          Float radix2 (-5110648099525066) (-54); Float radix2 (-7527220209070552) (-56); Float radix2 (-7259927682892498) (-55); Float radix2 (-5171170531937855) (-55);
          Float radix2 (-4988390367050940) (-56); Float radix2 (8806891565934662) (-55); Float radix2 (-6620433855429781) (-55); Float radix2 (-5418155057702660) (-54); Float radix2 (8760514843956796) (-57);
          Float radix2 (-8455874148917756) (-57); Float radix2 (-7121569919072259) (-55)];
      [:: Float radix2 (-6091906501203892) (-57); Float radix2 (7277030661496701) (-56); Float radix2 (8558876414731043) (-57); Float radix2 (-4688850150903665) (-54); Float radix2 (6245885256142952) (-55);
          Float radix2 (-8821691381869663) (-55); Float radix2 (6655153326904175) (-55); Float radix2 (-8397121726740020) (-55); Float radix2 (6341822484321677) (-56); Float radix2 (-5646499426765647) (-57);
          Float radix2 (-6746966053453156) (-57); Float radix2 (-4997862723138160) (-54); Float radix2 (-4531994496706137) (-56); Float radix2 (-4829449689255441) (-52);
          Float radix2 (-4816878062743684) (-53); Float radix2 (5804648685539040) (-50); Float radix2 (-6623506481516906) (-54); Float radix2 (-6944213750464188) (-53); Float radix2 (-7692538392554253) (-54);
          Float radix2 (5520096510916269) (-56); Float radix2 (5302866817616493) (-58); Float radix2 (5246781962667290) (-54); Float radix2 (7124839308313047) (-57); Float radix2 (4995242118057669) (-55);
          Float radix2 (-6784825672391251) (-54); Float radix2 (-6073957403038634) (-55); Float radix2 (-4651670451009381) (-54); Float radix2 (8603101273596800) (-57); Float radix2 (-6559195992485039) (-55);
          Float radix2 (8838826429669734) (-58); Float radix2 (-4748786381361347) (-54); Float radix2 (7407800532459704) (-56); Float radix2 (-4865566392550426) (-54); Float radix2 (4843717926069445) (-57);
          Float radix2 (7398703821201195) (-55); Float radix2 (8935041614344417) (-57); Float radix2 (-6034980522915703) (-59); Float radix2 (-6988231972299100) (-55); Float radix2 (7096000202106179) (-61);
          Float radix2 (-4706965490228480) (-55); Float radix2 (8104577091061533) (-57); Float radix2 (6415724111885987) (-54); Float radix2 (7443750215336753) (-57); Float radix2 (-5985628113586331) (-54);
          Float radix2 (-5288600799147952) (-55); Float radix2 (-5932318834517782) (-55); Float radix2 (6868852852491361) (-55); Float radix2 (-5858329155468250) (-59); Float radix2 (-7851350272128353) (-57);
          Float radix2 (-5035991936801809) (-56); Float radix2 (-4610721202477963) (-56); Float radix2 (-8112489390960090) (-57); Float radix2 (-8414548812291411) (-57);
          Float radix2 (-7417673070043496) (-55); Float radix2 (-4559205790183406) (-57)];
      [:: Float radix2 (-6958397194975532) (-58); Float radix2 (-5507597179457772) (-55); Float radix2 (-6175834336481601) (-56); Float radix2 (7356287265284808) (-56); Float radix2 (4861564792309642) (-59);
          Float radix2 (6353573567309921) (-54); Float radix2 (-6310006267040361) (-55); Float radix2 (7427411323441012) (-55); Float radix2 (-8088421480069069) (-55); Float radix2 (-8018438726354646) (-55);
          Float radix2 (7091745344826196) (-56); Float radix2 (5369045285422030) (-55); Float radix2 (-6620133875499592) (-53); Float radix2 (-5482951793501150) (-53); Float radix2 (-8711747457881294) (-53);
          Float radix2 (-6623506481516906) (-54); Float radix2 (6658287266586576) (-50); Float radix2 (-5877554044529405) (-54); Float radix2 (-6906019163145878) (-52); Float radix2 (7301436942854792) (-57);
          Float radix2 (6261713331409190) (-54); Float radix2 (7685218099344899) (-54); Float radix2 (8785268589311079) (-55); Float radix2 (-7133126393186340) (-54); Float radix2 (-6608185697015371) (-55);
          Float radix2 (-6914256973775833) (-54); Float radix2 (-7124393374967764) (-56); Float radix2 (-5089089894136071) (-54); Float radix2 (-7591853599639743) (-57); Float radix2 (5975605875170251) (-59);
          Float radix2 (5587089893515728) (-54); Float radix2 (6220200934124852) (-55); Float radix2 (5536770186123511) (-58); Float radix2 (-5052924163095546) (-53); Float radix2 (-6558163657199423) (-62);
          Float radix2 (-6056989878757665) (-55); Float radix2 (-5484100315874898) (-54); Float radix2 (8897017677501596) (-56); Float radix2 (6003396262064762) (-57); Float radix2 (4855331281540218) (-56);
          Float radix2 (8516007762695565) (-54); Float radix2 (7449571016201350) (-56); Float radix2 (-7586865972843311) (-56); Float radix2 (-5189108585023176) (-54); Float radix2 (-7029428657980263) (-54);
          Float radix2 (5040717285112418) (-56); Float radix2 (8326848351319555) (-55); Float radix2 (4948384570675721) (-55); Float radix2 (-8271301296474809) (-58); Float radix2 (-7320806692428273) (-56);
          Float radix2 (-6960874276313799) (-56); Float radix2 (-6129676959329247) (-58); Float radix2 (-5377485702029190) (-54); Float radix2 (-7088008661742846) (-54); Float radix2 (5406566760518556) (-60)];
      [:: Float radix2 (5441919537240624) (-56); Float radix2 (7364466887134357) (-55); Float radix2 (-6866755243143901) (-56); Float radix2 (-4993343388399281) (-54); Float radix2 (4859270702683439) (-56);
          Float radix2 (-7949837881595862) (-55); Float radix2 (5559198406132922) (-55); Float radix2 (-5029206802077767) (-54); Float radix2 (8067682752936822) (-57); Float radix2 (8179935788684770) (-56);
          Float radix2 (5899402728259788) (-54); Float radix2 (8442150640161233) (-57); Float radix2 (-7795631264697985) (-54); Float radix2 (-8049274339569744) (-53); Float radix2 (-4780542613939407) (-53);
          Float radix2 (-6944213750464188) (-53); Float radix2 (-5877554044529405) (-54); Float radix2 (5317830822121405) (-50); Float radix2 (-5077106434841400) (-55); Float radix2 (6700824179924228) (-56);
          Float radix2 (4934022811692181) (-54); Float radix2 (6637952290898130) (-62); Float radix2 (-6913174071008211) (-54); Float radix2 (-7902688129540230) (-55); Float radix2 (-6919357750777766) (-54);
          Float radix2 (7791669210469994) (-56); Float radix2 (5584778050752983) (-54); Float radix2 (-8874579375119505) (-55); Float radix2 (-6009912417809189) (-56); Float radix2 (7336030715688561) (-63);
          Float radix2 (-8174153026900056) (-57); Float radix2 (8362664681740370) (-56); Float radix2 (-4648601332897237) (-53); Float radix2 (6779637080496909) (-55); Float radix2 (-8811390287534042) (-55);
          Float radix2 (-5486857582961681) (-54); Float radix2 (-7360516484228017) (-55); Float radix2 (-5266787223922539) (-55); Float radix2 (7863317213366629) (-55); Float radix2 (5204365052781957) (-54);
          Float radix2 (6406201044110646) (-58); Float radix2 (-6455766922306999) (-55); Float radix2 (-5901545202878682) (-54); Float radix2 (-7719691329370380) (-54); Float radix2 (6426134776048516) (-55);
          Float radix2 (7183823485069957) (-59); Float radix2 (8257038570999202) (-57); Float radix2 (7054702093097073) (-55); Float radix2 (6866632345751461) (-55); Float radix2 (-4547947482555100) (-54);
          Float radix2 (-4987526877867563) (-55); Float radix2 (8710664284495506) (-55); Float radix2 (-8222277459055189) (-60); Float radix2 (7085753007466213) (-56); Float radix2 (6865807149184637) (-55)];
      [:: Float radix2 (8426289887506719) (-56); Float radix2 (6600915920928178) (-55); Float radix2 (8451541868098729) (-57); Float radix2 (-4949671880420534) (-55); Float radix2 (-5767495461490995) (-54);
          Float radix2 (-7209862337054098) (-56); Float radix2 (-6450090375965515) (-55); Float radix2 (-5978169403518903) (-54); Float radix2 (4961687161556069) (-59); Float radix2 (4704336609715644) (-53);
          Float radix2 (5666004510753933) (-54); Float radix2 (5011619408588334) (-55); Float radix2 (-6991944021385273) (-54); Float radix2 (-7392867055180816) (-54); Float radix2 (-5387925887998310) (-53);
          Float radix2 (-7692538392554253) (-54); Float radix2 (-6906019163145878) (-52); Float radix2 (-5077106434841400) (-55); Float radix2 (5761421437536595) (-50); Float radix2 (7840555236333991) (-56);
          Float radix2 (-5397383892276821) (-57); Float radix2 (-6519701119504454) (-54); Float radix2 (-6083575104473411) (-54); Float radix2 (-5203268813609060) (-55);
          Float radix2 (-4921499287859547) (-55); Float radix2 (6367504133681376) (-54); Float radix2 (7791055654005100) (-54); Float radix2 (-4521958904877944) (-55); Float radix2 (6529451939129358) (-62);
          Float radix2 (-6557857258346599) (-57); Float radix2 (-5689441126207206) (-58); Float radix2 (-8577347229402079) (-54); Float radix2 (4523017981375490) (-54); Float radix2 (-8752574305855272) (-54);
          Float radix2 (-8010128930959770) (-54); Float radix2 (-6886991955703208) (-55); Float radix2 (5374891147961958) (-58); Float radix2 (-6324406501217753) (-55); Float radix2 (4719353600641113) (-54);
          Float radix2 (5615706601388962) (-54); Float radix2 (-4957707260182234) (-54); Float radix2 (-4921151729743908) (-54); Float radix2 (-5224714496860084) (-54); Float radix2 (5130725109302183) (-55);
          Float radix2 (-7656963901930662) (-55); Float radix2 (4725719655712599) (-58); Float radix2 (-6278575889633133) (-55); Float radix2 (5286576783167076) (-54); Float radix2 (8694244727523221) (-55);
          Float radix2 (-6145251864811965) (-55); Float radix2 (7188767581333868) (-57); Float radix2 (-7737286660673174) (-60); Float radix2 (7205525292391603) (-55); Float radix2 (6177203408175063) (-55);
          Float radix2 (4970987127483366) (-54)];
      [:: Float radix2 (-4563693698751689) (-53); Float radix2 (-8984686261424692) (-55); Float radix2 (5591629168183517) (-56); Float radix2 (-4922408692547791) (-57); Float radix2 (5157871455512579) (-53);
          Float radix2 (7629133987934577) (-55); Float radix2 (6231164327198985) (-54); Float radix2 (7068137819166173) (-57); Float radix2 (-4869153363230965) (-55); Float radix2 (-4689923464742397) (-54);
          Float radix2 (-7576431621461329) (-56); Float radix2 (8555261247300533) (-54); Float radix2 (-5230349334612810) (-53); Float radix2 (4714329835675945) (-59); Float radix2 (-4655148858487884) (-57);
          Float radix2 (5520096510916269) (-56); Float radix2 (7301436942854792) (-57); Float radix2 (6700824179924228) (-56); Float radix2 (7840555236333991) (-56); Float radix2 (6313497819880468) (-51);
          Float radix2 (-8540514190930090) (-55); Float radix2 (-8477894605246354) (-54); Float radix2 (8686621599459209) (-57); Float radix2 (-5652546901972453) (-55); Float radix2 (-8601842048645073) (-56);
          Float radix2 (-4960433225688918) (-54); Float radix2 (-8541816504874636) (-57); Float radix2 (-6380659065591480) (-53); Float radix2 (5141035309176337) (-54); Float radix2 (5196660321446458) (-55);
          Float radix2 (7880992202744007) (-55); Float radix2 (5738699511785147) (-55); Float radix2 (7362659814928620) (-55); Float radix2 (-4519933250623132) (-57); Float radix2 (-5947620866668377) (-52);
          Float radix2 (-8541948155250125) (-55); Float radix2 (-7575591355471485) (-55); Float radix2 (-8793586914414337) (-56); Float radix2 (-5479289104406593) (-58); Float radix2 (5249054672944322) (-55);
          Float radix2 (-7041176881612952) (-56); Float radix2 (-5199541108356014) (-59); Float radix2 (4769298054293080) (-55); Float radix2 (-7388174182915079) (-56); Float radix2 (-4699740372020040) (-56);
          Float radix2 (-7078342089210327) (-54); Float radix2 (-5471470532045824) (-56); Float radix2 (6302608933185698) (-57); Float radix2 (6800532456306585) (-55); Float radix2 (-4546942064771409) (-56);
          Float radix2 (-7317901995889466) (-56); Float radix2 (-4578457968495159) (-58); Float radix2 (6903406945715847) (-55); Float radix2 (-7713904529400321) (-56); Float radix2 (5729712469016106) (-55)];
      [:: Float radix2 (-6277080544373593) (-56); Float radix2 (-7758709652592201) (-53); Float radix2 (-4914873963453508) (-53); Float radix2 (5327476976230184) (-53); Float radix2 (8905317035482784) (-54);
          Float radix2 (7266505870089473) (-53); Float radix2 (4923411798215532) (-54); Float radix2 (6449669235935607) (-68); Float radix2 (-7809213875318986) (-54); Float radix2 (-7736029358333132) (-55);
          Float radix2 (8494695174346541) (-56); Float radix2 (-5597218832657034) (-52); Float radix2 (4749634102010163) (-53); Float radix2 (-6862174375032580) (-55); Float radix2 (6223444413490347) (-54);
          Float radix2 (5302866817616493) (-58); Float radix2 (6261713331409190) (-54); Float radix2 (4934022811692181) (-54); Float radix2 (-5397383892276821) (-57); Float radix2 (-8540514190930090) (-55);
          Float radix2 (5280412020839570) (-50); Float radix2 (7073694809427435) (-55); Float radix2 (-5122188961032714) (-53); Float radix2 (-5534951503989271) (-54); Float radix2 (-6414215448980156) (-53);
          Float radix2 (-6434634444067955) (-54); Float radix2 (-5529897696087181) (-54); Float radix2 (4558156370316424) (-54); Float radix2 (-4579320654809775) (-53); Float radix2 (7553512660649984) (-54);
          Float radix2 (6402964616090721) (-55); Float radix2 (8617155873552920) (-54); Float radix2 (-4638835968339500) (-56); Float radix2 (-4667399863213790) (-54); Float radix2 (-7466516363258110) (-55);
          Float radix2 (-8993693358967030) (-53); Float radix2 (-6696156545387531) (-54); Float radix2 (-6428778460250521) (-54); Float radix2 (5672238370150924) (-59); Float radix2 (4792132121988935) (-54);
          Float radix2 (4888824374113869) (-54); Float radix2 (-6156761261911262) (-55); Float radix2 (-8171455143335232) (-56); Float radix2 (-7413197655300612) (-55); Float radix2 (-6360538453221157) (-54);
          Float radix2 (-4854202227480589) (-61); Float radix2 (-4638286324185228) (-54); Float radix2 (5676776983816389) (-55); Float radix2 (-8378234736107626) (-58); Float radix2 (7530096141968434) (-59);
          Float radix2 (-4692483116152332) (-54); Float radix2 (-7431419197440816) (-56); Float radix2 (-5589989016432706) (-55); Float radix2 (-8062272365038589) (-55); Float radix2 (6064866832114880) (-59)];
      [:: Float radix2 (-8362654729315226) (-56); Float radix2 (-5274516708760473) (-53); Float radix2 (-4689305470393815) (-53); Float radix2 (7667466884572059) (-54); Float radix2 (5341673038141136) (-53);
          Float radix2 (6256469510937649) (-53); Float radix2 (5014017220399677) (-55); Float radix2 (-5127199165574315) (-55); Float radix2 (-4625989858072827) (-54); Float radix2 (-4639043327396165) (-54);
          Float radix2 (-6809060161636851) (-54); Float radix2 (7005459731288196) (-55); Float radix2 (-8536671139050627) (-54); Float radix2 (6875270084076913) (-54); Float radix2 (-5001472705236812) (-54);
          Float radix2 (5246781962667290) (-54); Float radix2 (7685218099344899) (-54); Float radix2 (6637952290898130) (-62); Float radix2 (-6519701119504454) (-54); Float radix2 (-8477894605246354) (-54);
          Float radix2 (7073694809427435) (-55); Float radix2 (6202191275757833) (-50); Float radix2 (-5738832280645723) (-57); Float radix2 (-4538313590275405) (-52); Float radix2 (-8493621129493540) (-54);
          Float radix2 (-6353307703970195) (-53); Float radix2 (-6393064867754198) (-54); Float radix2 (4783056156142327) (-54); Float radix2 (5432350163744163) (-54); Float radix2 (-7648944782351390) (-55);
          Float radix2 (5732381226150876) (-53); Float radix2 (-6495856497187444) (-56); Float radix2 (-4976033446697506) (-54); Float radix2 (-5966629907538739) (-53); Float radix2 (4569773064269212) (-56);
          Float radix2 (-7675539045322107) (-55); Float radix2 (-8143501241631853) (-53); Float radix2 (5413162174505341) (-58); Float radix2 (-6622237873804310) (-56); Float radix2 (-5698985221288385) (-55);
          Float radix2 (6074063803211905) (-53); Float radix2 (5024071542219672) (-55); Float radix2 (-7693752968849916) (-54); Float radix2 (-7441366799380233) (-54); Float radix2 (-4899169083848189) (-53);
          Float radix2 (7216071328788571) (-56); Float radix2 (5041470671834106) (-53); Float radix2 (-6309851602058645) (-54); Float radix2 (-5763321243557773) (-54); Float radix2 (4736563374770758) (-56);
          Float radix2 (-5646058586169452) (-58); Float radix2 (-5944920436590666) (-55); Float radix2 (-6404058428579973) (-55); Float radix2 (-5805343155184713) (-54); Float radix2 (-5866089663279103) (-58)];
      [:: Float radix2 (-5394296604895518) (-55); Float radix2 (-5452373814254882) (-55); Float radix2 (-7002357864777241) (-57); Float radix2 (-7150889755905046) (-58); Float radix2 (7370381466527835) (-54);
          Float radix2 (-4859503111489701) (-57); Float radix2 (8971086880402592) (-58); Float radix2 (-5527266298951049) (-58); Float radix2 (-5339822826960398) (-56); Float radix2 (-5418743475345968) (-58);
          Float radix2 (-8049851082758201) (-55); Float radix2 (-5616768159169402) (-55); Float radix2 (4835295800485129) (-53); Float radix2 (-6608532893699492) (-54); Float radix2 (6143100947294213) (-54);
          Float radix2 (7124839308313047) (-57); Float radix2 (8785268589311079) (-55); Float radix2 (-6913174071008211) (-54); Float radix2 (-6083575104473411) (-54); Float radix2 (8686621599459209) (-57);
          Float radix2 (-5122188961032714) (-53); Float radix2 (-5738832280645723) (-57); Float radix2 (5955098000152128) (-50); Float radix2 (-5040659456342570) (-54); Float radix2 (-5605174630809688) (-53);
          Float radix2 (-6201268178652700) (-54); Float radix2 (-8583889381707884) (-54); Float radix2 (4813219630933171) (-54); Float radix2 (7965304169394907) (-57); Float radix2 (8662732788336563) (-54);
          Float radix2 (-5380770657922017) (-54); Float radix2 (7071383779662709) (-57); Float radix2 (-5075309924248858) (-53); Float radix2 (-5447805331523760) (-54); Float radix2 (8952749369924117) (-57);
          Float radix2 (-4708006094359024) (-54); Float radix2 (-4762696141403261) (-57); Float radix2 (-6693922468817519) (-56); Float radix2 (-7037164014521526) (-55);
          Float radix2 (-5337785454581192) (-53); Float radix2 (5076718933151069) (-56); Float radix2 (5131063886261644) (-55); Float radix2 (8988418146145149) (-60); Float radix2 (-7562148556143452) (-54);
          Float radix2 (-4634669511340131) (-54); Float radix2 (6773933484273141) (-55); Float radix2 (6815383886543898) (-55); Float radix2 (-6026153386050579) (-55); Float radix2 (-4958763759815333) (-53);
          Float radix2 (8944953821603050) (-56); Float radix2 (7678218983548177) (-55); Float radix2 (-5805071965914666) (-55); Float radix2 (-6713153247514244) (-55); Float radix2 (-8685327736416784) (-56);
          Float radix2 (-6719816941254387) (-55)];
      [:: Float radix2 (5300996249835889) (-56); Float radix2 (-7634595133991116) (-57); Float radix2 (8064874315380520) (-57); Float radix2 (6667529078518237) (-55); Float radix2 (-6500632697006342) (-54);
          Float radix2 (-8180123543883266) (-55); Float radix2 (-8802692600895413) (-55); Float radix2 (8582063354903080) (-55); Float radix2 (8479355475573358) (-56); Float radix2 (5076071883086167) (-56);
          Float radix2 (-7564966969333283) (-57); Float radix2 (4883801599353563) (-55); Float radix2 (-5236107512877099) (-54); Float radix2 (7360465132186484) (-54); Float radix2 (4833281271864895) (-55);
          Float radix2 (4995242118057669) (-55); Float radix2 (-7133126393186340) (-54); Float radix2 (-7902688129540230) (-55); Float radix2 (-5203268813609060) (-55); Float radix2 (-5652546901972453) (-55);
          Float radix2 (-5534951503989271) (-54); Float radix2 (-4538313590275405) (-52); Float radix2 (-5040659456342570) (-54); Float radix2 (6452853681789591) (-50); Float radix2 (4584780223944058) (-56);
          Float radix2 (-7640598904913347) (-54); Float radix2 (-7358371992607282) (-55); Float radix2 (8734053365247062) (-55); Float radix2 (6864098428280843) (-54); Float radix2 (-6252110262511918) (-54);
          Float radix2 (-7743458894736798) (-55); Float radix2 (-8589985587414518) (-54); Float radix2 (-6353658379774022) (-57); Float radix2 (-7753323764327223) (-56);
          Float radix2 (-8339782674051398) (-56); Float radix2 (5693865479128820) (-55); Float radix2 (4879117755351107) (-55); Float radix2 (-6786632573470730) (-58); Float radix2 (-5860587249588993) (-53);
          Float radix2 (-7293029778609484) (-54); Float radix2 (-5114666559060399) (-55); Float radix2 (-5582360516382794) (-55); Float radix2 (8537827754257229) (-56); Float radix2 (8882874784031699) (-56);
          Float radix2 (-7968799586137265) (-56); Float radix2 (-7616400178939159) (-56); Float radix2 (-6461015736178834) (-55); Float radix2 (-8177172269011756) (-54);
          Float radix2 (-8863715951752937) (-56); Float radix2 (4691437946391105) (-53); Float radix2 (-4590525107052628) (-56); Float radix2 (-4624564093714899) (-53); Float radix2 (4606162152538399) (-58);
          Float radix2 (6451828435131747) (-57); Float radix2 (-8078175165855076) (-55)];
      [:: Float radix2 (5892198286404979) (-58); Float radix2 (4865978629507765) (-54); Float radix2 (7402805415883056) (-55); Float radix2 (-6367814842276355) (-54); Float radix2 (-5417484228173940) (-54);
          Float radix2 (-8180022810242208) (-54); Float radix2 (6760502817079518) (-60); Float radix2 (7975620209474399) (-54); Float radix2 (5772788168088315) (-54); Float radix2 (-5570404793308960) (-54);
          Float radix2 (-8838649276730727) (-56); Float radix2 (-4628824861531252) (-57); Float radix2 (5673701548505309) (-54); Float radix2 (8662772452152584) (-55); Float radix2 (6268566509137818) (-54);
          Float radix2 (-6784825672391251) (-54); Float radix2 (-6608185697015371) (-55); Float radix2 (-6919357750777766) (-54); Float radix2 (-4921499287859547) (-55);
          Float radix2 (-8601842048645073) (-56); Float radix2 (-6414215448980156) (-53); Float radix2 (-8493621129493540) (-54); Float radix2 (-5605174630809688) (-53); Float radix2 (4584780223944058) (-56);
          Float radix2 (6970943466889528) (-50); Float radix2 (-8147102063518485) (-57); Float radix2 (-6322805112238479) (-53); Float radix2 (8039819147335330) (-54); Float radix2 (4975238550042417) (-56);
          Float radix2 (-8479237351057233) (-56); Float radix2 (-5813058295053824) (-53); Float radix2 (-4808100279757970) (-55); Float radix2 (-5036020856697205) (-54); Float radix2 (4614597112193952) (-58);
          Float radix2 (6347360056797590) (-56); Float radix2 (7251018391508156) (-54); Float radix2 (6944369754906080) (-55); Float radix2 (-5406823018106925) (-54); Float radix2 (-7772023807427877) (-54);
          Float radix2 (-6352607256950141) (-53); Float radix2 (-5439295896490682) (-54); Float radix2 (6834002861111827) (-58); Float radix2 (4632371644067968) (-54); Float radix2 (5570852650518752) (-56);
          Float radix2 (5983300480142571) (-56); Float radix2 (-5187739475181108) (-55); Float radix2 (-4882572774122241) (-55); Float radix2 (-4891505109007775) (-54); Float radix2 (-7583310211635524) (-54);
          Float radix2 (5869015427240339) (-54); Float radix2 (-7216844393565166) (-55); Float radix2 (-6889441789217876) (-54); Float radix2 (5830355227208188) (-57); Float radix2 (4696272509858762) (-58);
          Float radix2 (-7837378462820918) (-55)];
      [:: Float radix2 (8118745610733304) (-55); Float radix2 (5199788622272154) (-54); Float radix2 (8111669368051231) (-59); Float radix2 (-6280418193855328) (-54); Float radix2 (-5979727132086719) (-54);
          Float radix2 (-7797763569223832) (-56); Float radix2 (-7918516976406020) (-57); Float radix2 (5844431933618193) (-55); Float radix2 (-4517829328905850) (-53); Float radix2 (7748080523719431) (-54);
          Float radix2 (7179101918659840) (-55); Float radix2 (4575399160363337) (-54); Float radix2 (7030062769796418) (-59); Float radix2 (-8641177350178852) (-60); Float radix2 (-7545332805375236) (-54);
          Float radix2 (-6073957403038634) (-55); Float radix2 (-6914256973775833) (-54); Float radix2 (7791669210469994) (-56); Float radix2 (6367504133681376) (-54); Float radix2 (-4960433225688918) (-54);
          Float radix2 (-6434634444067955) (-54); Float radix2 (-6353307703970195) (-53); Float radix2 (-6201268178652700) (-54); Float radix2 (-7640598904913347) (-54);
          Float radix2 (-8147102063518485) (-57); Float radix2 (6398373583034553) (-50); Float radix2 (4829089091414309) (-55); Float radix2 (-7412683493961738) (-57); Float radix2 (-5022773336465903) (-55);
          Float radix2 (-4936406837873759) (-53); Float radix2 (-8196529374094224) (-55); Float radix2 (-6850645130839566) (-54); Float radix2 (6471001278526889) (-57); Float radix2 (4821871365518161) (-55);
          Float radix2 (6827693841646916) (-55); Float radix2 (-5738328715350957) (-57); Float radix2 (-7315332976494990) (-54); Float radix2 (-5833631698434845) (-54); Float radix2 (-4725422701228910) (-53);
          Float radix2 (-7290416395763104) (-62); Float radix2 (-5708333211299045) (-56); Float radix2 (-6071255556701280) (-56); Float radix2 (-5212974479909039) (-55); Float radix2 (8029939453637258) (-55);
          Float radix2 (5454115027245411) (-54); Float radix2 (-6122611662508809) (-55); Float radix2 (-4835202644270380) (-54); Float radix2 (-6244192942421071) (-54); Float radix2 (6185732267859446) (-57);
          Float radix2 (-5377084013019316) (-54); Float radix2 (-7035686757727082) (-56); Float radix2 (5538266989228744) (-55); Float radix2 (6910583772276227) (-57); Float radix2 (7301094697793035) (-55);
          Float radix2 (8336561859730708) (-55)];
      [:: Float radix2 (6890352826721833) (-55); Float radix2 (7030716718733755) (-54); Float radix2 (-5605619728302842) (-55); Float radix2 (-6183916068702789) (-54); Float radix2 (-5919944912490577) (-55);
          Float radix2 (-4749901839952367) (-56); Float radix2 (5495363401408080) (-55); Float radix2 (-6664830356364242) (-53); Float radix2 (7901990313377945) (-54); Float radix2 (8894349070511192) (-56);
          Float radix2 (5252924498231099) (-54); Float radix2 (7452774932464072) (-54); Float radix2 (-4532554400317830) (-55); Float radix2 (-5314639650132905) (-53); Float radix2 (-6557234986822473) (-54);
          Float radix2 (-4651670451009381) (-54); Float radix2 (-7124393374967764) (-56); Float radix2 (5584778050752983) (-54); Float radix2 (7791055654005100) (-54); Float radix2 (-8541816504874636) (-57);
          Float radix2 (-5529897696087181) (-54); Float radix2 (-6393064867754198) (-54); Float radix2 (-8583889381707884) (-54); Float radix2 (-7358371992607282) (-55);
          Float radix2 (-6322805112238479) (-53); Float radix2 (4829089091414309) (-55); Float radix2 (6442749771727676) (-50); Float radix2 (-7342773821071265) (-55); Float radix2 (-7481673150199171) (-54);
          Float radix2 (-5265932672472546) (-54); Float radix2 (-8372564988273380) (-55); Float radix2 (-5806855492868126) (-55); Float radix2 (8770143925528791) (-57); Float radix2 (5154228343674004) (-54);
          Float radix2 (-5107427641363658) (-56); Float radix2 (-5915275847243018) (-54); Float radix2 (-7325747367068423) (-54); Float radix2 (-5015725526855964) (-53); Float radix2 (5737703616379934) (-56);
          Float radix2 (-7336851108143249) (-54); Float radix2 (-4729651806363610) (-56); Float radix2 (4815172548307385) (-56); Float radix2 (-7415968008288282) (-55); Float radix2 (8580056770520650) (-56);
          Float radix2 (6697747251198917) (-54); Float radix2 (-5164168675209999) (-56); Float radix2 (-7503844096402429) (-55); Float radix2 (6326995082042784) (-58); Float radix2 (-6164355841571045) (-54);
          Float radix2 (-7281836929602451) (-54); Float radix2 (6613244678348575) (-55); Float radix2 (4978282039688573) (-54); Float radix2 (5808962608570998) (-55); Float radix2 (8840850197194436) (-60);
          Float radix2 (8044710116465339) (-55)];
      [:: Float radix2 (-6119686682860162) (-56); Float radix2 (-6759500807336781) (-63); Float radix2 (5965170185439928) (-58); Float radix2 (-5002491731308870) (-56); Float radix2 (5685760691532363) (-54);
          Float radix2 (-6163213864658785) (-55); Float radix2 (6358250999434496) (-56); Float radix2 (-4748859234690121) (-57); Float radix2 (6177076631264223) (-55); Float radix2 (-4735610988028777) (-55);
          Float radix2 (-7373179853332707) (-52); Float radix2 (-6343553093424534) (-56); Float radix2 (8572227707744849) (-54); Float radix2 (6538878978677921) (-53); Float radix2 (7592819790376053) (-54);
          Float radix2 (8603101273596800) (-57); Float radix2 (-5089089894136071) (-54); Float radix2 (-8874579375119505) (-55); Float radix2 (-4521958904877944) (-55); Float radix2 (-6380659065591480) (-53);
          Float radix2 (4558156370316424) (-54); Float radix2 (4783056156142327) (-54); Float radix2 (4813219630933171) (-54); Float radix2 (8734053365247062) (-55); Float radix2 (8039819147335330) (-54);
          Float radix2 (-7412683493961738) (-57); Float radix2 (-7342773821071265) (-55); Float radix2 (5749885234524370) (-50); Float radix2 (-8942795976378782) (-55); Float radix2 (-7660393987235680) (-55);
          Float radix2 (-6370963381450714) (-54); Float radix2 (-5560867448268466) (-54); Float radix2 (-7032346411240275) (-56); Float radix2 (7441798243951325) (-55); Float radix2 (-7800796174267356) (-54);
          Float radix2 (5234613832726643) (-55); Float radix2 (5285412787487036) (-54); Float radix2 (-4845934032900018) (-58); Float radix2 (-7899695538411412) (-55); Float radix2 (-6248512150904816) (-54);
          Float radix2 (-4901911009714853) (-52); Float radix2 (-6656811190785666) (-55); Float radix2 (-6883008965428444) (-56); Float radix2 (8710819429947203) (-55); Float radix2 (-5882134110361339) (-56);
          Float radix2 (-6308993177544768) (-53); Float radix2 (-6344088870341996) (-57); Float radix2 (-5478387003814944) (-54); Float radix2 (-7439964921021122) (-59);
          Float radix2 (-4862196626604816) (-55); Float radix2 (-7998020817024411) (-55); Float radix2 (-5363126853794590) (-54); Float radix2 (-6903395386978513) (-56); Float radix2 (6197472481829149) (-59);
          Float radix2 (-5185367842581305) (-54)];
      [:: Float radix2 (-5272801495329036) (-56); Float radix2 (-7922157603356308) (-54); Float radix2 (-5161993835016395) (-58); Float radix2 (5694263688189769) (-53); Float radix2 (6625661161879531) (-56);
          Float radix2 (4504307619892181) (-54); Float radix2 (-8352269962896813) (-56); Float radix2 (8004711241450818) (-54); Float radix2 (-8856577086441446) (-55); Float radix2 (-6089012197396358) (-54);
          Float radix2 (-8064992550397477) (-56); Float radix2 (-5561077072115378) (-52); Float radix2 (5805653109074715) (-54); Float radix2 (8358201338290403) (-57); Float radix2 (6925449043986450) (-55);
          Float radix2 (-6559195992485039) (-55); Float radix2 (-7591853599639743) (-57); Float radix2 (-6009912417809189) (-56); Float radix2 (6529451939129358) (-62); Float radix2 (5141035309176337) (-54);
          Float radix2 (-4579320654809775) (-53); Float radix2 (5432350163744163) (-54); Float radix2 (7965304169394907) (-57); Float radix2 (6864098428280843) (-54); Float radix2 (4975238550042417) (-56);
          Float radix2 (-5022773336465903) (-55); Float radix2 (-7481673150199171) (-54); Float radix2 (-8942795976378782) (-55); Float radix2 (5966130774061382) (-50); Float radix2 (-5494317701096446) (-55);
          Float radix2 (-7891613298703567) (-54); Float radix2 (-8005548156199645) (-58); Float radix2 (5140103614565072) (-55); Float radix2 (-4726337488442791) (-55); Float radix2 (5243502999444651) (-56);
          Float radix2 (-7492516928920292) (-54); Float radix2 (-7556308381464117) (-63); Float radix2 (-6547738857485792) (-56); Float radix2 (-4982200213248972) (-54);
          Float radix2 (-5462241106891430) (-55); Float radix2 (-7519751752038377) (-56); Float radix2 (-7707838589041903) (-53); Float radix2 (4777302667545336) (-54); Float radix2 (-6645585582304228) (-55);
          Float radix2 (-8549762097835068) (-55); Float radix2 (4525514053132591) (-55); Float radix2 (-6078782980577977) (-53); Float radix2 (-8709140421679390) (-57); Float radix2 (8648826430471924) (-56);
          Float radix2 (8882387437626122) (-57); Float radix2 (-5458620741578639) (-53); Float radix2 (-5965059373944727) (-54); Float radix2 (5165010139613630) (-56); Float radix2 (-7015629353983453) (-55);
          Float radix2 (-6423028929716109) (-56)];
      [:: Float radix2 (-5802496571819831) (-55); Float radix2 (-5901808904115106) (-54); Float radix2 (-6536018746381718) (-56); Float radix2 (5787922553414117) (-54); Float radix2 (7149232942432849) (-54);
          Float radix2 (5419363941533587) (-54); Float radix2 (7626199583812246) (-54); Float radix2 (-8364566157595407) (-60); Float radix2 (-4923251751843711) (-54); Float radix2 (-6896814809778807) (-54);
          Float radix2 (-7364954936933970) (-55); Float radix2 (6434693723140966) (-57); Float radix2 (-5502952626647179) (-53); Float radix2 (8296544431225698) (-57); Float radix2 (-7858538087651574) (-54);
          Float radix2 (8838826429669734) (-58); Float radix2 (5975605875170251) (-59); Float radix2 (7336030715688561) (-63); Float radix2 (-6557857258346599) (-57); Float radix2 (5196660321446458) (-55);
          Float radix2 (7553512660649984) (-54); Float radix2 (-7648944782351390) (-55); Float radix2 (8662732788336563) (-54); Float radix2 (-6252110262511918) (-54); Float radix2 (-8479237351057233) (-56);
          Float radix2 (-4936406837873759) (-53); Float radix2 (-5265932672472546) (-54); Float radix2 (-7660393987235680) (-55); Float radix2 (-5494317701096446) (-55); Float radix2 (6250630621199700) (-50);
          Float radix2 (4749510883575597) (-55); Float radix2 (7912895539668171) (-58); Float radix2 (-8672916723473154) (-55); Float radix2 (-5417058791342734) (-53); Float radix2 (4762532881601535) (-54);
          Float radix2 (-5619435997857445) (-56); Float radix2 (-5101591130675109) (-53); Float radix2 (-4765799416564239) (-57); Float radix2 (-6363065557855677) (-54);
          Float radix2 (-4736999617613221) (-55); Float radix2 (-6032316688819256) (-60); Float radix2 (4572907447441810) (-54); Float radix2 (-4623079968628676) (-53); Float radix2 (-5758560275068313) (-54);
          Float radix2 (-6498619614985592) (-53); Float radix2 (5765913292773441) (-57); Float radix2 (6136666807901098) (-54); Float radix2 (-5710661566710022) (-54); Float radix2 (-5190379038555520) (-55);
          Float radix2 (5473586895639266) (-57); Float radix2 (-7619038997115152) (-56); Float radix2 (-5154391979138131) (-53); Float radix2 (6004052473506829) (-57); Float radix2 (-7828912086368754) (-55);
          Float radix2 (8175848529378487) (-58)];
      [:: Float radix2 (-7283672568615945) (-56); Float radix2 (-7887982237236882) (-56); Float radix2 (-5518852661081221) (-56); Float radix2 (-8248020857137575) (-56); Float radix2 (6751477725668520) (-54);
          Float radix2 (5693940853325277) (-53); Float radix2 (7977905181652332) (-55); Float radix2 (-6667574382500631) (-55); Float radix2 (-6881082803358541) (-54); Float radix2 (-7911771834927019) (-56);
          Float radix2 (7132929087320197) (-57); Float radix2 (-4538259342211998) (-56); Float radix2 (-7747705006245161) (-58); Float radix2 (-7248048767031949) (-53); Float radix2 (-5576841226475155) (-55);
          Float radix2 (-4748786381361347) (-54); Float radix2 (5587089893515728) (-54); Float radix2 (-8174153026900056) (-57); Float radix2 (-5689441126207206) (-58); Float radix2 (7880992202744007) (-55);
          Float radix2 (6402964616090721) (-55); Float radix2 (5732381226150876) (-53); Float radix2 (-5380770657922017) (-54); Float radix2 (-7743458894736798) (-55); Float radix2 (-5813058295053824) (-53);
          Float radix2 (-8196529374094224) (-55); Float radix2 (-8372564988273380) (-55); Float radix2 (-6370963381450714) (-54); Float radix2 (-7891613298703567) (-54); Float radix2 (4749510883575597) (-55);
          Float radix2 (7067274234315879) (-50); Float radix2 (5066421971565575) (-55); Float radix2 (-6246356666780197) (-53); Float radix2 (-5317305228503769) (-53); Float radix2 (-6208686748652991) (-59);
          Float radix2 (-8978708155610327) (-55); Float radix2 (-5324285016591903) (-54); Float radix2 (-7615072756915861) (-55); Float radix2 (6896219878155089) (-56); Float radix2 (-5770048840899454) (-56);
          Float radix2 (7619122967598844) (-54); Float radix2 (-7361409541658729) (-56); Float radix2 (-7835102331942119) (-55); Float radix2 (-7996952342545666) (-53); Float radix2 (-7033305809166929) (-54);
          Float radix2 (6558358586528913) (-55); Float radix2 (5199290058933577) (-53); Float radix2 (4540607757084788) (-55); Float radix2 (-6286570033265060) (-53); Float radix2 (-6552897642468496) (-55);
          Float radix2 (-7135885138083506) (-55); Float radix2 (-6618153776453140) (-57); Float radix2 (-8138337290169925) (-55); Float radix2 (-8187638125670298) (-54); Float radix2 (-4707932831726560) (-60)];
      [:: Float radix2 (-5641380652212573) (-57); Float radix2 (-6430639134717669) (-55); Float radix2 (-5269911690106588) (-55); Float radix2 (8787570695727477) (-56); Float radix2 (8075307453113248) (-54);
          Float radix2 (5803564624233669) (-54); Float radix2 (5758906511251029) (-62); Float radix2 (-8677640393264431) (-57); Float radix2 (-6892880403445247) (-55); Float radix2 (-5865242566454450) (-55);
          Float radix2 (8143797759448387) (-56); Float radix2 (4959003974451007) (-56); Float radix2 (-4986228562311796) (-53); Float radix2 (-6216761191784658) (-55); Float radix2 (-5922973052486544) (-54);
          Float radix2 (7407800532459704) (-56); Float radix2 (6220200934124852) (-55); Float radix2 (8362664681740370) (-56); Float radix2 (-8577347229402079) (-54); Float radix2 (5738699511785147) (-55);
          Float radix2 (8617155873552920) (-54); Float radix2 (-6495856497187444) (-56); Float radix2 (7071383779662709) (-57); Float radix2 (-8589985587414518) (-54); Float radix2 (-4808100279757970) (-55);
          Float radix2 (-6850645130839566) (-54); Float radix2 (-5806855492868126) (-55); Float radix2 (-5560867448268466) (-54); Float radix2 (-8005548156199645) (-58); Float radix2 (7912895539668171) (-58);
          Float radix2 (5066421971565575) (-55); Float radix2 (6742678537054210) (-50); Float radix2 (-5901034999245003) (-54); Float radix2 (-6573759927382696) (-53); Float radix2 (6498667702913833) (-58);
          Float radix2 (-7392399597832702) (-55); Float radix2 (-5508499013934734) (-54); Float radix2 (7418630297671726) (-56); Float radix2 (-8858172931909964) (-56); Float radix2 (6023495848773139) (-57);
          Float radix2 (7524172701100872) (-57); Float radix2 (-6141412268077609) (-57); Float radix2 (-5510285094925368) (-54); Float radix2 (-5947724719921536) (-54); Float radix2 (-6219995681603845) (-53);
          Float radix2 (5083569779501646) (-54); Float radix2 (5434653830008702) (-54); Float radix2 (-6953057667899059) (-54); Float radix2 (-5169765002969438) (-54); Float radix2 (7245810011680242) (-55);
          Float radix2 (-7892394542857181) (-56); Float radix2 (-7804669927737505) (-54); Float radix2 (-6809079157576537) (-55); Float radix2 (-7033538797858872) (-54); Float radix2 (-5077718521119199) (-54)];
      [:: Float radix2 (7428034608274604) (-57); Float radix2 (5979557339574092) (-55); Float radix2 (8936046337086542) (-58); Float radix2 (4845709863688774) (-58); Float radix2 (-5993673329444874) (-57);
          Float radix2 (-5916675650151916) (-54); Float radix2 (-5815734265902751) (-56); Float radix2 (-8606229974245686) (-56); Float radix2 (5520191769928556) (-55); Float radix2 (4854295628476038) (-54);
          Float radix2 (5965605132045218) (-55); Float radix2 (6882206787366952) (-56); Float radix2 (-6255992861456613) (-55); Float radix2 (-6603232677580848) (-54); Float radix2 (5024469245838847) (-60);
          Float radix2 (-4865566392550426) (-54); Float radix2 (5536770186123511) (-58); Float radix2 (-4648601332897237) (-53); Float radix2 (4523017981375490) (-54); Float radix2 (7362659814928620) (-55);
          Float radix2 (-4638835968339500) (-56); Float radix2 (-4976033446697506) (-54); Float radix2 (-5075309924248858) (-53); Float radix2 (-6353658379774022) (-57);
          Float radix2 (-5036020856697205) (-54); Float radix2 (6471001278526889) (-57); Float radix2 (8770143925528791) (-57); Float radix2 (-7032346411240275) (-56); Float radix2 (5140103614565072) (-55);
          Float radix2 (-8672916723473154) (-55); Float radix2 (-6246356666780197) (-53); Float radix2 (-5901034999245003) (-54); Float radix2 (6226147139260684) (-50); Float radix2 (7200869948385063) (-58);
          Float radix2 (-6579194996049290) (-55); Float radix2 (-7557319226165977) (-58); Float radix2 (-8413461381931314) (-58); Float radix2 (-4735985108184771) (-54); Float radix2 (6152909825801596) (-56);
          Float radix2 (5317736235239514) (-56); Float radix2 (-7001215911594057) (-55); Float radix2 (-7201328750918166) (-54); Float radix2 (-6733862672984877) (-55); Float radix2 (-5168100308430130) (-53);
          Float radix2 (8727506880996000) (-58); Float radix2 (6001632665635013) (-58); Float radix2 (-8125592105291894) (-54); Float radix2 (-8041421049713815) (-56); Float radix2 (-5869434392311099) (-59);
          Float radix2 (-5985094207638139) (-58); Float radix2 (-5578236499259004) (-54); Float radix2 (4574565568134626) (-56); Float radix2 (6599858574315492) (-57); Float radix2 (5901471970318252) (-54);
          Float radix2 (-5030796957665915) (-61)];
      [:: Float radix2 (4771030569741338) (-55); Float radix2 (5420994808298673) (-54); Float radix2 (4616753314048758) (-54); Float radix2 (-7360632737413102) (-55); Float radix2 (-4543181096493995) (-53);
          Float radix2 (-8139986044261322) (-54); Float radix2 (-7086499510950033) (-55); Float radix2 (7504645653372605) (-58); Float radix2 (8138955929921216) (-54); Float radix2 (5190850504904299) (-54);
          Float radix2 (6677407221141618) (-55); Float radix2 (6027036416436242) (-55); Float radix2 (-6599391538752137) (-55); Float radix2 (5047107711437665) (-60); Float radix2 (-8135991825481322) (-56);
          Float radix2 (4843717926069445) (-57); Float radix2 (-5052924163095546) (-53); Float radix2 (6779637080496909) (-55); Float radix2 (-8752574305855272) (-54); Float radix2 (-4519933250623132) (-57);
          Float radix2 (-4667399863213790) (-54); Float radix2 (-5966629907538739) (-53); Float radix2 (-5447805331523760) (-54); Float radix2 (-7753323764327223) (-56); Float radix2 (4614597112193952) (-58);
          Float radix2 (4821871365518161) (-55); Float radix2 (5154228343674004) (-54); Float radix2 (7441798243951325) (-55); Float radix2 (-4726337488442791) (-55); Float radix2 (-5417058791342734) (-53);
          Float radix2 (-5317305228503769) (-53); Float radix2 (-6573759927382696) (-53); Float radix2 (7200869948385063) (-58); Float radix2 (6469879959902518) (-50); Float radix2 (-7647035721582866) (-56);
          Float radix2 (7520205624381651) (-59); Float radix2 (8639333405045400) (-57); Float radix2 (-7367502653825369) (-56); Float radix2 (5633743984174669) (-57); Float radix2 (6651948890938001) (-55);
          Float radix2 (-8125227171967787) (-54); Float radix2 (-4788025963658407) (-54); Float radix2 (-7066612185973300) (-54); Float radix2 (6787038514765004) (-56); Float radix2 (-6810067258273858) (-54);
          Float radix2 (-5696669674296782) (-54); Float radix2 (-8528195061763721) (-54); Float radix2 (-5357583559214763) (-56); Float radix2 (7079826249747749) (-55); Float radix2 (-4577989715675299) (-56);
          Float radix2 (5926600013075883) (-57); Float radix2 (-4778446446328715) (-54); Float radix2 (6461414943261933) (-54); Float radix2 (5401008163287159) (-54); Float radix2 (8951435229526690) (-56)];
      [:: Float radix2 (-8706082582581517) (-55); Float radix2 (-4637027261748401) (-55); Float radix2 (6595290261736937) (-54); Float radix2 (4826487610966924) (-54); Float radix2 (4803338536628193) (-54);
          Float radix2 (-8814208541396210) (-57); Float radix2 (-5899665755714806) (-55); Float radix2 (-6400701184042145) (-55); Float radix2 (-6107140742768413) (-56);
          Float radix2 (-4795952395506245) (-56); Float radix2 (-5319467383454613) (-54); Float radix2 (5349681391132715) (-55); Float radix2 (7366941320903911) (-54); Float radix2 (8121707918211479) (-55);
          Float radix2 (5038615524005191) (-55); Float radix2 (7398703821201195) (-55); Float radix2 (-6558163657199423) (-62); Float radix2 (-8811390287534042) (-55); Float radix2 (-8010128930959770) (-54);
          Float radix2 (-5947620866668377) (-52); Float radix2 (-7466516363258110) (-55); Float radix2 (4569773064269212) (-56); Float radix2 (8952749369924117) (-57); Float radix2 (-8339782674051398) (-56);
          Float radix2 (6347360056797590) (-56); Float radix2 (6827693841646916) (-55); Float radix2 (-5107427641363658) (-56); Float radix2 (-7800796174267356) (-54); Float radix2 (5243502999444651) (-56);
          Float radix2 (4762532881601535) (-54); Float radix2 (-6208686748652991) (-59); Float radix2 (6498667702913833) (-58); Float radix2 (-6579194996049290) (-55); Float radix2 (-7647035721582866) (-56);
          Float radix2 (5879458854507090) (-50); Float radix2 (-4600155073997117) (-57); Float radix2 (-6992134077543682) (-55); Float radix2 (8204480679979285) (-55); Float radix2 (-7142086480784709) (-56);
          Float radix2 (-7685404459632821) (-55); Float radix2 (-6999464170966130) (-53); Float radix2 (5325196031265643) (-55); Float radix2 (-8239470711525065) (-56); Float radix2 (5892184307371683) (-56);
          Float radix2 (5210913240857685) (-56); Float radix2 (-6454042596371834) (-53); Float radix2 (-7536012199574977) (-57); Float radix2 (-6699152585381899) (-55); Float radix2 (-5927570813316940) (-55);
          Float radix2 (-7023297834978301) (-54); Float radix2 (-8036950184346286) (-59); Float radix2 (-6006203250843466) (-58); Float radix2 (-6805097109591160) (-53);
          Float radix2 (-6443187881952780) (-55); Float radix2 (-6563347031510396) (-54)];
      [:: Float radix2 (-6324643346817721) (-59); Float radix2 (-6622642171178803) (-55); Float radix2 (7145260716856725) (-55); Float radix2 (7647855533316577) (-54); Float radix2 (-8447768306128145) (-55);
          Float radix2 (-5007688442147531) (-55); Float radix2 (-5098966034308809) (-54); Float radix2 (7008046927381004) (-55); Float radix2 (4808895660438629) (-58); Float radix2 (6062073394858258) (-57);
          Float radix2 (-6881318345731391) (-57); Float radix2 (-7956677217473080) (-54); Float radix2 (6766056245315798) (-54); Float radix2 (7820029123916027) (-54); Float radix2 (8085690551291497) (-54);
          Float radix2 (8935041614344417) (-57); Float radix2 (-6056989878757665) (-55); Float radix2 (-5486857582961681) (-54); Float radix2 (-6886991955703208) (-55); Float radix2 (-8541948155250125) (-55);
          Float radix2 (-8993693358967030) (-53); Float radix2 (-7675539045322107) (-55); Float radix2 (-4708006094359024) (-54); Float radix2 (5693865479128820) (-55); Float radix2 (7251018391508156) (-54);
          Float radix2 (-5738328715350957) (-57); Float radix2 (-5915275847243018) (-54); Float radix2 (5234613832726643) (-55); Float radix2 (-7492516928920292) (-54); Float radix2 (-5619435997857445) (-56);
          Float radix2 (-8978708155610327) (-55); Float radix2 (-7392399597832702) (-55); Float radix2 (-7557319226165977) (-58); Float radix2 (7520205624381651) (-59); Float radix2 (-4600155073997117) (-57);
          Float radix2 (6092171695946263) (-50); Float radix2 (5825754741964555) (-54); Float radix2 (-5810758630327624) (-55); Float radix2 (-5452707040515746) (-54); Float radix2 (-8230876008025410) (-54);
          Float radix2 (4790776829952172) (-58); Float radix2 (-7662372334747873) (-53); Float radix2 (5248010829263431) (-54); Float radix2 (6741420691206725) (-55); Float radix2 (-8675682819507471) (-58);
          Float radix2 (-7842149895235290) (-56); Float radix2 (-8085844905525276) (-53); Float radix2 (-7259360964317384) (-55); Float radix2 (-7661239581044138) (-55); Float radix2 (5899148303350000) (-54);
          Float radix2 (-4765764730081597) (-53); Float radix2 (-5504895466743707) (-54); Float radix2 (5755336579398938) (-58); Float radix2 (-5714683684561130) (-54); Float radix2 (-7975401309909628) (-57)];
      [:: Float radix2 (5162666563645130) (-56); Float radix2 (5735820517222672) (-56); Float radix2 (7815961740068248) (-56); Float radix2 (6252680741894910) (-60); Float radix2 (-4594349922243351) (-54);
          Float radix2 (-5494440984196218) (-54); Float radix2 (-6977281627790649) (-57); Float radix2 (5856087007397243) (-55); Float radix2 (8708200987985776) (-55); Float radix2 (4992351429367133) (-58);
          Float radix2 (-4961358364387062) (-56); Float radix2 (7794864081441006) (-59); Float radix2 (-5809373060800200) (-55); Float radix2 (5460738504970938) (-53); Float radix2 (4526643871914046) (-55);
          Float radix2 (-6034980522915703) (-59); Float radix2 (-5484100315874898) (-54); Float radix2 (-7360516484228017) (-55); Float radix2 (5374891147961958) (-58); Float radix2 (-7575591355471485) (-55);
          Float radix2 (-6696156545387531) (-54); Float radix2 (-8143501241631853) (-53); Float radix2 (-4762696141403261) (-57); Float radix2 (4879117755351107) (-55); Float radix2 (6944369754906080) (-55);
          Float radix2 (-7315332976494990) (-54); Float radix2 (-7325747367068423) (-54); Float radix2 (5285412787487036) (-54); Float radix2 (-7556308381464117) (-63); Float radix2 (-5101591130675109) (-53);
          Float radix2 (-5324285016591903) (-54); Float radix2 (-5508499013934734) (-54); Float radix2 (-8413461381931314) (-58); Float radix2 (8639333405045400) (-57); Float radix2 (-6992134077543682) (-55);
          Float radix2 (5825754741964555) (-54); Float radix2 (6522833840985755) (-50); Float radix2 (-6157820468009355) (-56); Float radix2 (-6916198780251799) (-53); Float radix2 (-6884788623428157) (-54);
          Float radix2 (-5542661624004601) (-54); Float radix2 (4926505867275526) (-56); Float radix2 (-5101948919669021) (-58); Float radix2 (7200024898073402) (-55); Float radix2 (-4942195207140671) (-53);
          Float radix2 (-4727508346211701) (-54); Float radix2 (-7323033230783698) (-56); Float radix2 (-7050226825676363) (-53); Float radix2 (-5093621884638682) (-56); Float radix2 (5332596865091293) (-53);
          Float radix2 (-5770087448367768) (-59); Float radix2 (-7836742407860442) (-53); Float radix2 (5157764175347719) (-55); Float radix2 (6416895360662226) (-55); Float radix2 (-6942227894443037) (-56)];
      [:: Float radix2 (6955982078216938) (-61); Float radix2 (8625988706136560) (-56); Float radix2 (6159889323030219) (-60); Float radix2 (-4721075587784649) (-54); Float radix2 (-5871718789934429) (-57);
          Float radix2 (5910546216668233) (-60); Float radix2 (7397031070241821) (-57); Float radix2 (5509661634689016) (-54); Float radix2 (6241866120605628) (-57); Float radix2 (-4842005402052777) (-55);
          Float radix2 (-7970709136758395) (-57); Float radix2 (5722589892516249) (-56); Float radix2 (6557889884896051) (-54); Float radix2 (-7272102803356020) (-55); Float radix2 (8768136841470974) (-57);
          Float radix2 (-6988231972299100) (-55); Float radix2 (8897017677501596) (-56); Float radix2 (-5266787223922539) (-55); Float radix2 (-6324406501217753) (-55); Float radix2 (-8793586914414337) (-56);
          Float radix2 (-6428778460250521) (-54); Float radix2 (5413162174505341) (-58); Float radix2 (-6693922468817519) (-56); Float radix2 (-6786632573470730) (-58); Float radix2 (-5406823018106925) (-54);
          Float radix2 (-5833631698434845) (-54); Float radix2 (-5015725526855964) (-53); Float radix2 (-4845934032900018) (-58); Float radix2 (-6547738857485792) (-56);
          Float radix2 (-4765799416564239) (-57); Float radix2 (-7615072756915861) (-55); Float radix2 (7418630297671726) (-56); Float radix2 (-4735985108184771) (-54); Float radix2 (-7367502653825369) (-56);
          Float radix2 (8204480679979285) (-55); Float radix2 (-5810758630327624) (-55); Float radix2 (-6157820468009355) (-56); Float radix2 (6641463641020929) (-50); Float radix2 (-6029093158513743) (-55);
          Float radix2 (-5280224166193120) (-53); Float radix2 (8393281591399962) (-56); Float radix2 (7172823798487432) (-55); Float radix2 (6041021878570607) (-55); Float radix2 (-6017503540550277) (-53);
          Float radix2 (-5878685157975411) (-54); Float radix2 (-6178203817592553) (-58); Float radix2 (7720434547695770) (-55); Float radix2 (-7574992688119906) (-56); Float radix2 (-5750829921314522) (-53);
          Float radix2 (5339329193880594) (-55); Float radix2 (-7235461706779554) (-55); Float radix2 (-8521102306141600) (-55); Float radix2 (-7557862297635576) (-56); Float radix2 (-8203883809171240) (-53);
          Float radix2 (-6321446672853552) (-55)];
      [:: Float radix2 (6066990124460158) (-55); Float radix2 (4800944203936869) (-55); Float radix2 (-5904611720519977) (-55); Float radix2 (-4914796598282004) (-54); Float radix2 (7117090854867370) (-59);
          Float radix2 (7307879818275467) (-56); Float radix2 (7820452534617537) (-56); Float radix2 (7474294761902398) (-58); Float radix2 (-8513670156245324) (-55); Float radix2 (6891076013089666) (-55);
          Float radix2 (4648661457521504) (-54); Float radix2 (6311377389650347) (-54); Float radix2 (-5314810217653029) (-54); Float radix2 (-6051835626539165) (-54); Float radix2 (-8530446813906646) (-54);
          Float radix2 (7096000202106179) (-61); Float radix2 (6003396262064762) (-57); Float radix2 (7863317213366629) (-55); Float radix2 (4719353600641113) (-54); Float radix2 (-5479289104406593) (-58);
          Float radix2 (5672238370150924) (-59); Float radix2 (-6622237873804310) (-56); Float radix2 (-7037164014521526) (-55); Float radix2 (-5860587249588993) (-53); Float radix2 (-7772023807427877) (-54);
          Float radix2 (-4725422701228910) (-53); Float radix2 (5737703616379934) (-56); Float radix2 (-7899695538411412) (-55); Float radix2 (-4982200213248972) (-54); Float radix2 (-6363065557855677) (-54);
          Float radix2 (6896219878155089) (-56); Float radix2 (-8858172931909964) (-56); Float radix2 (6152909825801596) (-56); Float radix2 (5633743984174669) (-57); Float radix2 (-7142086480784709) (-56);
          Float radix2 (-5452707040515746) (-54); Float radix2 (-6916198780251799) (-53); Float radix2 (-6029093158513743) (-55); Float radix2 (6541947142443276) (-50); Float radix2 (5270482467706506) (-55);
          Float radix2 (5591100680120976) (-54); Float radix2 (-8603457554477776) (-61); Float radix2 (-7261348605408974) (-53); Float radix2 (-8451985855018208) (-55); Float radix2 (-7882525811189559) (-56);
          Float radix2 (7422522328611785) (-61); Float radix2 (5044544645833426) (-56); Float radix2 (-7367619655844771) (-54); Float radix2 (4599040093018117) (-56); Float radix2 (-5830971204205932) (-54);
          Float radix2 (-7795550124997709) (-58); Float radix2 (7675087722524981) (-55); Float radix2 (-8729177895391396) (-54); Float radix2 (-7053651573400874) (-55); Float radix2 (6838497276757265) (-54)];
      [:: Float radix2 (7250815373058611) (-56); Float radix2 (7709301135965633) (-55); Float radix2 (-6676024026659671) (-55); Float radix2 (-8533437791992679) (-55); Float radix2 (-5039690797954162) (-58);
          Float radix2 (8339336876472298) (-57); Float radix2 (5924869113914737) (-55); Float radix2 (-7458249466377257) (-55); Float radix2 (7756335039134226) (-55); Float radix2 (-5077663091337098) (-60);
          Float radix2 (6216081568137374) (-54); Float radix2 (4551668560517226) (-54); Float radix2 (-4756933956447855) (-54); Float radix2 (-5588801825603152) (-53); Float radix2 (-8421643176513708) (-55);
          Float radix2 (-4706965490228480) (-55); Float radix2 (4855331281540218) (-56); Float radix2 (5204365052781957) (-54); Float radix2 (5615706601388962) (-54); Float radix2 (5249054672944322) (-55);
          Float radix2 (4792132121988935) (-54); Float radix2 (-5698985221288385) (-55); Float radix2 (-5337785454581192) (-53); Float radix2 (-7293029778609484) (-54); Float radix2 (-6352607256950141) (-53);
          Float radix2 (-7290416395763104) (-62); Float radix2 (-7336851108143249) (-54); Float radix2 (-6248512150904816) (-54); Float radix2 (-5462241106891430) (-55);
          Float radix2 (-4736999617613221) (-55); Float radix2 (-5770048840899454) (-56); Float radix2 (6023495848773139) (-57); Float radix2 (5317736235239514) (-56); Float radix2 (6651948890938001) (-55);
          Float radix2 (-7685404459632821) (-55); Float radix2 (-8230876008025410) (-54); Float radix2 (-6884788623428157) (-54); Float radix2 (-5280224166193120) (-53); Float radix2 (5270482467706506) (-55);
          Float radix2 (6481383067152126) (-50); Float radix2 (6889529944013945) (-57); Float radix2 (-6231817939896598) (-54); Float radix2 (-8441244125569659) (-54); Float radix2 (-8540151477533237) (-55);
          Float radix2 (8707793662860750) (-56); Float radix2 (4657229248901262) (-56); Float radix2 (-8591296316216849) (-55); Float radix2 (4667793219138693) (-55); Float radix2 (-8360569836416205) (-54);
          Float radix2 (-6800622625358499) (-54); Float radix2 (8565621845832844) (-55); Float radix2 (5643321098944686) (-54); Float radix2 (-4789954584087290) (-56); Float radix2 (-5805032552468901) (-54);
          Float radix2 (4872522097735580) (-54)];
      [:: Float radix2 (-4819126808945325) (-55); Float radix2 (-5332948127864159) (-55); Float radix2 (5866916783145904) (-56); Float radix2 (6543787565296866) (-57); Float radix2 (4820819377326802) (-54);
          Float radix2 (7758197552913119) (-54); Float radix2 (8762557436017480) (-57); Float radix2 (-6310793050624578) (-55); Float radix2 (-6371387164005130) (-54); Float radix2 (-4722391218520754) (-55);
          Float radix2 (-5495570831503920) (-54); Float radix2 (7622123218018064) (-60); Float radix2 (5909163594033986) (-54); Float radix2 (-7269429670455572) (-56); Float radix2 (-5238774538735307) (-55);
          Float radix2 (8104577091061533) (-57); Float radix2 (8516007762695565) (-54); Float radix2 (6406201044110646) (-58); Float radix2 (-4957707260182234) (-54); Float radix2 (-7041176881612952) (-56);
          Float radix2 (4888824374113869) (-54); Float radix2 (6074063803211905) (-53); Float radix2 (5076718933151069) (-56); Float radix2 (-5114666559060399) (-55); Float radix2 (-5439295896490682) (-54);
          Float radix2 (-5708333211299045) (-56); Float radix2 (-4729651806363610) (-56); Float radix2 (-4901911009714853) (-52); Float radix2 (-7519751752038377) (-56);
          Float radix2 (-6032316688819256) (-60); Float radix2 (7619122967598844) (-54); Float radix2 (7524172701100872) (-57); Float radix2 (-7001215911594057) (-55); Float radix2 (-8125227171967787) (-54);
          Float radix2 (-6999464170966130) (-53); Float radix2 (4790776829952172) (-58); Float radix2 (-5542661624004601) (-54); Float radix2 (8393281591399962) (-56); Float radix2 (5591100680120976) (-54);
          Float radix2 (6889529944013945) (-57); Float radix2 (6265601703769100) (-50); Float radix2 (-5012156028056416) (-56); Float radix2 (-6488561382346584) (-54); Float radix2 (-4980831676062484) (-54);
          Float radix2 (-7014537296994973) (-55); Float radix2 (-5833183496156006) (-53); Float radix2 (4594607769764388) (-54); Float radix2 (7691277587092199) (-55); Float radix2 (-7917516063294512) (-55);
          Float radix2 (-6288891193000692) (-52); Float radix2 (-4803921931071615) (-55); Float radix2 (5971308369890176) (-55); Float radix2 (-8322654519205700) (-53); Float radix2 (-8737522749934441) (-56);
          Float radix2 (-8181932947329981) (-55)];
      [:: Float radix2 (-6513979511013357) (-57); Float radix2 (-5695994977829855) (-55); Float radix2 (-5345684139364454) (-58); Float radix2 (5553076570543601) (-54); Float radix2 (8221219958289595) (-55);
          Float radix2 (7468761388709681) (-55); Float radix2 (-8263629424464349) (-56); Float radix2 (-5594628442258019) (-55); Float radix2 (-7182181689447252) (-55); Float radix2 (-4632237045749212) (-56);
          Float radix2 (-5358940174641313) (-59); Float radix2 (-8627762384552681) (-55); Float radix2 (4780933652661440) (-56); Float radix2 (4868892030011041) (-60); Float radix2 (7777785383701632) (-58);
          Float radix2 (6415724111885987) (-54); Float radix2 (7449571016201350) (-56); Float radix2 (-6455766922306999) (-55); Float radix2 (-4921151729743908) (-54); Float radix2 (-5199541108356014) (-59);
          Float radix2 (-6156761261911262) (-55); Float radix2 (5024071542219672) (-55); Float radix2 (5131063886261644) (-55); Float radix2 (-5582360516382794) (-55); Float radix2 (6834002861111827) (-58);
          Float radix2 (-6071255556701280) (-56); Float radix2 (4815172548307385) (-56); Float radix2 (-6656811190785666) (-55); Float radix2 (-7707838589041903) (-53); Float radix2 (4572907447441810) (-54);
          Float radix2 (-7361409541658729) (-56); Float radix2 (-6141412268077609) (-57); Float radix2 (-7201328750918166) (-54); Float radix2 (-4788025963658407) (-54); Float radix2 (5325196031265643) (-55);
          Float radix2 (-7662372334747873) (-53); Float radix2 (4926505867275526) (-56); Float radix2 (7172823798487432) (-55); Float radix2 (-8603457554477776) (-61); Float radix2 (-6231817939896598) (-54);
          Float radix2 (-5012156028056416) (-56); Float radix2 (5896629097292741) (-50); Float radix2 (-6898530690690053) (-58); Float radix2 (-7583633130403397) (-54); Float radix2 (-4668716387762874) (-55);
          Float radix2 (8785272093415061) (-56); Float radix2 (-6961633792943250) (-54); Float radix2 (-7256580678394122) (-57); Float radix2 (-6610660706792464) (-54); Float radix2 (-7430502420284153) (-57);
          Float radix2 (-6789951096739948) (-53); Float radix2 (-5544498822451651) (-59); Float radix2 (7972207090845700) (-56); Float radix2 (-6520614564595836) (-53); Float radix2 (5850951591353814) (-60)];
      [:: Float radix2 (-5045305332122827) (-57); Float radix2 (-7661605223029987) (-56); Float radix2 (8465238974960245) (-56); Float radix2 (5366036549621618) (-54); Float radix2 (5045612577587891) (-57);
          Float radix2 (-5999491020580191) (-55); Float radix2 (-8129988699559275) (-56); Float radix2 (8524142233502607) (-56); Float radix2 (7930301242614811) (-57); Float radix2 (-5598066146146421) (-55);
          Float radix2 (-6055428993329514) (-57); Float radix2 (-5068350625704246) (-55); Float radix2 (-8660515300292178) (-55); Float radix2 (5903569771580543) (-54); Float radix2 (7750768770282385) (-54);
          Float radix2 (7443750215336753) (-57); Float radix2 (-7586865972843311) (-56); Float radix2 (-5901545202878682) (-54); Float radix2 (-5224714496860084) (-54); Float radix2 (4769298054293080) (-55);
          Float radix2 (-8171455143335232) (-56); Float radix2 (-7693752968849916) (-54); Float radix2 (8988418146145149) (-60); Float radix2 (8537827754257229) (-56); Float radix2 (4632371644067968) (-54);
          Float radix2 (-5212974479909039) (-55); Float radix2 (-7415968008288282) (-55); Float radix2 (-6883008965428444) (-56); Float radix2 (4777302667545336) (-54); Float radix2 (-4623079968628676) (-53);
          Float radix2 (-7835102331942119) (-55); Float radix2 (-5510285094925368) (-54); Float radix2 (-6733862672984877) (-55); Float radix2 (-7066612185973300) (-54);
          Float radix2 (-8239470711525065) (-56); Float radix2 (5248010829263431) (-54); Float radix2 (-5101948919669021) (-58); Float radix2 (6041021878570607) (-55); Float radix2 (-7261348605408974) (-53);
          Float radix2 (-8441244125569659) (-54); Float radix2 (-6488561382346584) (-54); Float radix2 (-6898530690690053) (-58); Float radix2 (6916098696662228) (-50); Float radix2 (8879349139595320) (-58);
          Float radix2 (-5580513917414688) (-53); Float radix2 (6819744921289600) (-56); Float radix2 (6692639417930178) (-56); Float radix2 (-7423298118556271) (-53); Float radix2 (-8396447048912311) (-55);
          Float radix2 (7339827692265614) (-53); Float radix2 (-4885445356107915) (-57); Float radix2 (-6880910428647834) (-52); Float radix2 (5664454916684537) (-56); Float radix2 (-5949716454204897) (-57);
          Float radix2 (-4702574720962094) (-53)];
      [:: Float radix2 (7346501773903744) (-57); Float radix2 (5356584713883744) (-54); Float radix2 (8044141471529490) (-55); Float radix2 (-7744727700257538) (-55); Float radix2 (-5767514890799193) (-54);
          Float radix2 (-7598867204468332) (-54); Float radix2 (-6035483223291273) (-56); Float radix2 (8059233057937532) (-57); Float radix2 (8046694542531842) (-55); Float radix2 (8866682104487429) (-55);
          Float radix2 (8498325334980772) (-61); Float radix2 (4646887450493358) (-55); Float radix2 (6203741548992366) (-57); Float radix2 (8273042036478900) (-55); Float radix2 (4921334767993304) (-55);
          Float radix2 (-5985628113586331) (-54); Float radix2 (-5189108585023176) (-54); Float radix2 (-7719691329370380) (-54); Float radix2 (5130725109302183) (-55); Float radix2 (-7388174182915079) (-56);
          Float radix2 (-7413197655300612) (-55); Float radix2 (-7441366799380233) (-54); Float radix2 (-7562148556143452) (-54); Float radix2 (8882874784031699) (-56); Float radix2 (5570852650518752) (-56);
          Float radix2 (8029939453637258) (-55); Float radix2 (8580056770520650) (-56); Float radix2 (8710819429947203) (-55); Float radix2 (-6645585582304228) (-55); Float radix2 (-5758560275068313) (-54);
          Float radix2 (-7996952342545666) (-53); Float radix2 (-5947724719921536) (-54); Float radix2 (-5168100308430130) (-53); Float radix2 (6787038514765004) (-56); Float radix2 (5892184307371683) (-56);
          Float radix2 (6741420691206725) (-55); Float radix2 (7200024898073402) (-55); Float radix2 (-6017503540550277) (-53); Float radix2 (-8451985855018208) (-55); Float radix2 (-8540151477533237) (-55);
          Float radix2 (-4980831676062484) (-54); Float radix2 (-7583633130403397) (-54); Float radix2 (8879349139595320) (-58); Float radix2 (6455541880625701) (-50); Float radix2 (6989931259553877) (-55);
          Float radix2 (-5033561785514468) (-55); Float radix2 (-5097825276825503) (-53); Float radix2 (-8612423579628739) (-56); Float radix2 (-5682657681750664) (-57); Float radix2 (4759634002392516) (-56);
          Float radix2 (-8791785962233459) (-53); Float radix2 (-8351054721707953) (-55); Float radix2 (8014902479407207) (-57); Float radix2 (8873792195460910) (-54); Float radix2 (5709374353302033) (-57)];
      [:: Float radix2 (6363825724650215) (-55); Float radix2 (6684022803050698) (-54); Float radix2 (5315978898643783) (-56); Float radix2 (-6320624197431359) (-54); Float radix2 (-7561794937645611) (-54);
          Float radix2 (-5432612612923251) (-54); Float radix2 (-7204031589988434) (-57); Float radix2 (-6007648936483716) (-58); Float radix2 (6151515555697786) (-54); Float radix2 (8785611688157459) (-55);
          Float radix2 (4918398388272684) (-54); Float radix2 (8079165341578318) (-55); Float radix2 (6421172541857588) (-56); Float radix2 (-4761334285009622) (-56); Float radix2 (-5110648099525066) (-54);
          Float radix2 (-5288600799147952) (-55); Float radix2 (-7029428657980263) (-54); Float radix2 (6426134776048516) (-55); Float radix2 (-7656963901930662) (-55); Float radix2 (-4699740372020040) (-56);
          Float radix2 (-6360538453221157) (-54); Float radix2 (-4899169083848189) (-53); Float radix2 (-4634669511340131) (-54); Float radix2 (-7968799586137265) (-56); Float radix2 (5983300480142571) (-56);
          Float radix2 (5454115027245411) (-54); Float radix2 (6697747251198917) (-54); Float radix2 (-5882134110361339) (-56); Float radix2 (-8549762097835068) (-55); Float radix2 (-6498619614985592) (-53);
          Float radix2 (-7033305809166929) (-54); Float radix2 (-6219995681603845) (-53); Float radix2 (8727506880996000) (-58); Float radix2 (-6810067258273858) (-54); Float radix2 (5210913240857685) (-56);
          Float radix2 (-8675682819507471) (-58); Float radix2 (-4942195207140671) (-53); Float radix2 (-5878685157975411) (-54); Float radix2 (-7882525811189559) (-56); Float radix2 (8707793662860750) (-56);
          Float radix2 (-7014537296994973) (-55); Float radix2 (-4668716387762874) (-55); Float radix2 (-5580513917414688) (-53); Float radix2 (6989931259553877) (-55); Float radix2 (6692762919481448) (-50);
          Float radix2 (-5398844585407018) (-55); Float radix2 (-7766421515970138) (-54); Float radix2 (-4703638329799831) (-56); Float radix2 (7827277816327970) (-55); Float radix2 (-6714867454417053) (-53);
          Float radix2 (-7220614153003366) (-56); Float radix2 (-5731949580834533) (-54); Float radix2 (4769325297922225) (-53); Float radix2 (8207297276689221) (-54); Float radix2 (7385697722947025) (-55)];
      [:: Float radix2 (6670302940630024) (-58); Float radix2 (-5646068652244605) (-66); Float radix2 (5573874216202666) (-56); Float radix2 (5634495180962716) (-58); Float radix2 (-7343073615346359) (-55);
          Float radix2 (8151792431320711) (-56); Float radix2 (4666357760021424) (-55); Float radix2 (8671257216139418) (-57); Float radix2 (-6538359914843652) (-55); Float radix2 (-8818910373658562) (-57);
          Float radix2 (8136146339642218) (-55); Float radix2 (-5313281562690545) (-56); Float radix2 (6166051457768323) (-54); Float radix2 (-8079477301321826) (-55); Float radix2 (-7527220209070552) (-56);
          Float radix2 (-5932318834517782) (-55); Float radix2 (5040717285112418) (-56); Float radix2 (7183823485069957) (-59); Float radix2 (4725719655712599) (-58); Float radix2 (-7078342089210327) (-54);
          Float radix2 (-4854202227480589) (-61); Float radix2 (7216071328788571) (-56); Float radix2 (6773933484273141) (-55); Float radix2 (-7616400178939159) (-56); Float radix2 (-5187739475181108) (-55);
          Float radix2 (-6122611662508809) (-55); Float radix2 (-5164168675209999) (-56); Float radix2 (-6308993177544768) (-53); Float radix2 (4525514053132591) (-55); Float radix2 (5765913292773441) (-57);
          Float radix2 (6558358586528913) (-55); Float radix2 (5083569779501646) (-54); Float radix2 (6001632665635013) (-58); Float radix2 (-5696669674296782) (-54); Float radix2 (-6454042596371834) (-53);
          Float radix2 (-7842149895235290) (-56); Float radix2 (-4727508346211701) (-54); Float radix2 (-6178203817592553) (-58); Float radix2 (7422522328611785) (-61); Float radix2 (4657229248901262) (-56);
          Float radix2 (-5833183496156006) (-53); Float radix2 (8785272093415061) (-56); Float radix2 (6819744921289600) (-56); Float radix2 (-5033561785514468) (-55); Float radix2 (-5398844585407018) (-55);
          Float radix2 (5432976699608491) (-50); Float radix2 (-7963481081248002) (-59); Float radix2 (7830966737867528) (-56); Float radix2 (-6081349798489677) (-57); Float radix2 (-5353794733386285) (-52);
          Float radix2 (6233920835040364) (-55); Float radix2 (5103879373748010) (-55); Float radix2 (-4749474046627015) (-52); Float radix2 (-7460127697624605) (-56); Float radix2 (-6223989294669107) (-54)];
      [:: Float radix2 (-7545426726297108) (-57); Float radix2 (-6090197138528062) (-55); Float radix2 (-5350229315865976) (-56); Float radix2 (7326003914558141) (-59); Float radix2 (8279736695291953) (-55);
          Float radix2 (5253197279268330) (-53); Float radix2 (5667710499608331) (-56); Float radix2 (-6731009104020048) (-56); Float radix2 (-6348560251109615) (-54); Float radix2 (-6417740301503238) (-55);
          Float radix2 (-6352832386539949) (-56); Float radix2 (6780320954022419) (-56); Float radix2 (4506206531872447) (-58); Float radix2 (4543743493146986) (-56); Float radix2 (-7259927682892498) (-55);
          Float radix2 (6868852852491361) (-55); Float radix2 (8326848351319555) (-55); Float radix2 (8257038570999202) (-57); Float radix2 (-6278575889633133) (-55); Float radix2 (-5471470532045824) (-56);
          Float radix2 (-4638286324185228) (-54); Float radix2 (5041470671834106) (-53); Float radix2 (6815383886543898) (-55); Float radix2 (-6461015736178834) (-55); Float radix2 (-4882572774122241) (-55);
          Float radix2 (-4835202644270380) (-54); Float radix2 (-7503844096402429) (-55); Float radix2 (-6344088870341996) (-57); Float radix2 (-6078782980577977) (-53); Float radix2 (6136666807901098) (-54);
          Float radix2 (5199290058933577) (-53); Float radix2 (5434653830008702) (-54); Float radix2 (-8125592105291894) (-54); Float radix2 (-8528195061763721) (-54); Float radix2 (-7536012199574977) (-57);
          Float radix2 (-8085844905525276) (-53); Float radix2 (-7323033230783698) (-56); Float radix2 (7720434547695770) (-55); Float radix2 (5044544645833426) (-56); Float radix2 (-8591296316216849) (-55);
          Float radix2 (4594607769764388) (-54); Float radix2 (-6961633792943250) (-54); Float radix2 (6692639417930178) (-56); Float radix2 (-5097825276825503) (-53); Float radix2 (-7766421515970138) (-54);
          Float radix2 (-7963481081248002) (-59); Float radix2 (7107481104183171) (-50); Float radix2 (8706816532467105) (-57); Float radix2 (-4883871909969112) (-52); Float radix2 (6323518364905937) (-54);
          Float radix2 (-6611474328103675) (-53); Float radix2 (-5767958804807127) (-55); Float radix2 (-6637986439670831) (-55); Float radix2 (-4532936505577194) (-51); Float radix2 (-6164358141799911) (-56)];
      [:: Float radix2 (8824271581252179) (-56); Float radix2 (6353354617928129) (-57); Float radix2 (-6694939527005720) (-55); Float radix2 (-6437363799793258) (-57); Float radix2 (5003882147504528) (-54);
          Float radix2 (7438185454395963) (-56); Float radix2 (-6180782714506925) (-57); Float radix2 (-6161111314556445) (-55); Float radix2 (-6190097439194719) (-55); Float radix2 (7299096651795105) (-56);
          Float radix2 (4970796117237271) (-54); Float radix2 (-7305294435044764) (-61); Float radix2 (-7448774565106818) (-55); Float radix2 (-4872357587981668) (-54); Float radix2 (-5171170531937855) (-55);
          Float radix2 (-5858329155468250) (-59); Float radix2 (4948384570675721) (-55); Float radix2 (7054702093097073) (-55); Float radix2 (5286576783167076) (-54); Float radix2 (6302608933185698) (-57);
          Float radix2 (5676776983816389) (-55); Float radix2 (-6309851602058645) (-54); Float radix2 (-6026153386050579) (-55); Float radix2 (-8177172269011756) (-54); Float radix2 (-4891505109007775) (-54);
          Float radix2 (-6244192942421071) (-54); Float radix2 (6326995082042784) (-58); Float radix2 (-5478387003814944) (-54); Float radix2 (-8709140421679390) (-57); Float radix2 (-5710661566710022) (-54);
          Float radix2 (4540607757084788) (-55); Float radix2 (-6953057667899059) (-54); Float radix2 (-8041421049713815) (-56); Float radix2 (-5357583559214763) (-56); Float radix2 (-6699152585381899) (-55);
          Float radix2 (-7259360964317384) (-55); Float radix2 (-7050226825676363) (-53); Float radix2 (-7574992688119906) (-56); Float radix2 (-7367619655844771) (-54); Float radix2 (4667793219138693) (-55);
          Float radix2 (7691277587092199) (-55); Float radix2 (-7256580678394122) (-57); Float radix2 (-7423298118556271) (-53); Float radix2 (-8612423579628739) (-56); Float radix2 (-4703638329799831) (-56);
          Float radix2 (7830966737867528) (-56); Float radix2 (8706816532467105) (-57); Float radix2 (5637827859529400) (-50); Float radix2 (-6446567981589745) (-55); Float radix2 (6781454270326869) (-59);
          Float radix2 (6210764069401734) (-57); Float radix2 (-7922530818994195) (-57); Float radix2 (-6213127539437073) (-53); Float radix2 (8301178619466286) (-55); Float radix2 (4974214342345697) (-54)];
      [:: Float radix2 (7524178601613986) (-57); Float radix2 (6884829887381514) (-55); Float radix2 (4640642452632431) (-57); Float radix2 (7562043465751746) (-60); Float radix2 (-7427046211067375) (-56);
          Float radix2 (-6426950580795255) (-54); Float radix2 (-6111961179226044) (-56); Float radix2 (-8214519681724268) (-57); Float radix2 (4782477502932450) (-54); Float radix2 (8138267847088906) (-56);
          Float radix2 (4523191879325806) (-55); Float radix2 (5077172797123189) (-54); Float radix2 (-4580264239892101) (-54); Float radix2 (-4628354001721704) (-54); Float radix2 (-4988390367050940) (-56);
          Float radix2 (-7851350272128353) (-57); Float radix2 (-8271301296474809) (-58); Float radix2 (6866632345751461) (-55); Float radix2 (8694244727523221) (-55); Float radix2 (6800532456306585) (-55);
          Float radix2 (-8378234736107626) (-58); Float radix2 (-5763321243557773) (-54); Float radix2 (-4958763759815333) (-53); Float radix2 (-8863715951752937) (-56);
          Float radix2 (-7583310211635524) (-54); Float radix2 (6185732267859446) (-57); Float radix2 (-6164355841571045) (-54); Float radix2 (-7439964921021122) (-59); Float radix2 (8648826430471924) (-56);
          Float radix2 (-5190379038555520) (-55); Float radix2 (-6286570033265060) (-53); Float radix2 (-5169765002969438) (-54); Float radix2 (-5869434392311099) (-59); Float radix2 (7079826249747749) (-55);
          Float radix2 (-5927570813316940) (-55); Float radix2 (-7661239581044138) (-55); Float radix2 (-5093621884638682) (-56); Float radix2 (-5750829921314522) (-53); Float radix2 (4599040093018117) (-56);
          Float radix2 (-8360569836416205) (-54); Float radix2 (-7917516063294512) (-55); Float radix2 (-6610660706792464) (-54); Float radix2 (-8396447048912311) (-55);
          Float radix2 (-5682657681750664) (-57); Float radix2 (7827277816327970) (-55); Float radix2 (-6081349798489677) (-57); Float radix2 (-4883871909969112) (-52); Float radix2 (-6446567981589745) (-55);
          Float radix2 (6413823964237254) (-50); Float radix2 (-4742544836878654) (-54); Float radix2 (4960959592916389) (-54); Float radix2 (7446990615055679) (-54); Float radix2 (4670226064105849) (-54);
          Float radix2 (-8409456219792443) (-54); Float radix2 (5229053703069833) (-56)];
      [:: Float radix2 (-8683113771026343) (-58); Float radix2 (-4783512488360534) (-57); Float radix2 (7610627282428631) (-55); Float radix2 (8835214031002688) (-57); Float radix2 (-4752572757507188) (-54);
          Float radix2 (-7035940454879486) (-55); Float radix2 (-8761584460918620) (-56); Float radix2 (4767771239009284) (-54); Float radix2 (6407863065772252) (-56); Float radix2 (-8500876931073627) (-58);
          Float radix2 (-6025252263549510) (-56); Float radix2 (-8461408789217643) (-55); Float radix2 (8887412161570024) (-55); Float radix2 (7962845008446901) (-54); Float radix2 (8806891565934662) (-55);
          Float radix2 (-5035991936801809) (-56); Float radix2 (-7320806692428273) (-56); Float radix2 (-4547947482555100) (-54); Float radix2 (-6145251864811965) (-55);
          Float radix2 (-4546942064771409) (-56); Float radix2 (7530096141968434) (-59); Float radix2 (4736563374770758) (-56); Float radix2 (8944953821603050) (-56); Float radix2 (4691437946391105) (-53);
          Float radix2 (5869015427240339) (-54); Float radix2 (-5377084013019316) (-54); Float radix2 (-7281836929602451) (-54); Float radix2 (-4862196626604816) (-55); Float radix2 (8882387437626122) (-57);
          Float radix2 (5473586895639266) (-57); Float radix2 (-6552897642468496) (-55); Float radix2 (7245810011680242) (-55); Float radix2 (-5985094207638139) (-58); Float radix2 (-4577989715675299) (-56);
          Float radix2 (-7023297834978301) (-54); Float radix2 (5899148303350000) (-54); Float radix2 (5332596865091293) (-53); Float radix2 (5339329193880594) (-55); Float radix2 (-5830971204205932) (-54);
          Float radix2 (-6800622625358499) (-54); Float radix2 (-6288891193000692) (-52); Float radix2 (-7430502420284153) (-57); Float radix2 (7339827692265614) (-53); Float radix2 (4759634002392516) (-56);
          Float radix2 (-6714867454417053) (-53); Float radix2 (-5353794733386285) (-52); Float radix2 (6323518364905937) (-54); Float radix2 (6781454270326869) (-59); Float radix2 (-4742544836878654) (-54);
          Float radix2 (6852744035192556) (-50); Float radix2 (-8239526984205288) (-56); Float radix2 (-5417432953156985) (-52); Float radix2 (-4782819809733703) (-52); Float radix2 (-5332647124028085) (-56);
          Float radix2 (-7225220437279982) (-52)];
      [:: Float radix2 (6650609107206260) (-57); Float radix2 (5236767724416579) (-55); Float radix2 (6152285561116884) (-57); Float radix2 (-5380935978922171) (-57); Float radix2 (-4536317326745498) (-54);
          Float radix2 (-7726749128859824) (-56); Float radix2 (-7397851676412588) (-57); Float radix2 (-6373784468807228) (-57); Float radix2 (8679017270896484) (-56); Float radix2 (4820955497456607) (-55);
          Float radix2 (6221402616084023) (-56); Float radix2 (7280445105036037) (-55); Float radix2 (7594473040396330) (-56); Float radix2 (7537888159974305) (-56); Float radix2 (-6620433855429781) (-55);
          Float radix2 (-4610721202477963) (-56); Float radix2 (-6960874276313799) (-56); Float radix2 (-4987526877867563) (-55); Float radix2 (7188767581333868) (-57); Float radix2 (-7317901995889466) (-56);
          Float radix2 (-4692483116152332) (-54); Float radix2 (-5646058586169452) (-58); Float radix2 (7678218983548177) (-55); Float radix2 (-4590525107052628) (-56); Float radix2 (-7216844393565166) (-55);
          Float radix2 (-7035686757727082) (-56); Float radix2 (6613244678348575) (-55); Float radix2 (-7998020817024411) (-55); Float radix2 (-5458620741578639) (-53); Float radix2 (-7619038997115152) (-56);
          Float radix2 (-7135885138083506) (-55); Float radix2 (-7892394542857181) (-56); Float radix2 (-5578236499259004) (-54); Float radix2 (5926600013075883) (-57); Float radix2 (-8036950184346286) (-59);
          Float radix2 (-4765764730081597) (-53); Float radix2 (-5770087448367768) (-59); Float radix2 (-7235461706779554) (-55); Float radix2 (-7795550124997709) (-58); Float radix2 (8565621845832844) (-55);
          Float radix2 (-4803921931071615) (-55); Float radix2 (-6789951096739948) (-53); Float radix2 (-4885445356107915) (-57); Float radix2 (-8791785962233459) (-53);
          Float radix2 (-7220614153003366) (-56); Float radix2 (6233920835040364) (-55); Float radix2 (-6611474328103675) (-53); Float radix2 (6210764069401734) (-57); Float radix2 (4960959592916389) (-54);
          Float radix2 (-8239526984205288) (-56); Float radix2 (4894666927072916) (-50); Float radix2 (7131609175531569) (-54); Float radix2 (5139412364165751) (-55); Float radix2 (-4589577025612800) (-53);
          Float radix2 (6370453663198863) (-55)];
      [:: Float radix2 (5979965524073339) (-55); Float radix2 (7807322357494331) (-55); Float radix2 (-8381803768116405) (-56); Float radix2 (-5089738297970715) (-54); Float radix2 (-6082190705540838) (-56);
          Float radix2 (-8800133769805754) (-57); Float radix2 (5232285029560115) (-56); Float radix2 (-8188887712106757) (-56); Float radix2 (5744038318506246) (-55); Float radix2 (4798061669642579) (-55);
          Float radix2 (6551476719684503) (-54); Float radix2 (8748637061695611) (-55); Float radix2 (-8856185441962742) (-56); Float radix2 (-6927621884237680) (-54); Float radix2 (-5418155057702660) (-54);
          Float radix2 (-8112489390960090) (-57); Float radix2 (-6129676959329247) (-58); Float radix2 (8710664284495506) (-55); Float radix2 (-7737286660673174) (-60); Float radix2 (-4578457968495159) (-58);
          Float radix2 (-7431419197440816) (-56); Float radix2 (-5944920436590666) (-55); Float radix2 (-5805071965914666) (-55); Float radix2 (-4624564093714899) (-53);
          Float radix2 (-6889441789217876) (-54); Float radix2 (5538266989228744) (-55); Float radix2 (4978282039688573) (-54); Float radix2 (-5363126853794590) (-54); Float radix2 (-5965059373944727) (-54);
          Float radix2 (-5154391979138131) (-53); Float radix2 (-6618153776453140) (-57); Float radix2 (-7804669927737505) (-54); Float radix2 (4574565568134626) (-56); Float radix2 (-4778446446328715) (-54);
          Float radix2 (-6006203250843466) (-58); Float radix2 (-5504895466743707) (-54); Float radix2 (-7836742407860442) (-53); Float radix2 (-8521102306141600) (-55); Float radix2 (7675087722524981) (-55);
          Float radix2 (5643321098944686) (-54); Float radix2 (5971308369890176) (-55); Float radix2 (-5544498822451651) (-59); Float radix2 (-6880910428647834) (-52); Float radix2 (-8351054721707953) (-55);
          Float radix2 (-5731949580834533) (-54); Float radix2 (5103879373748010) (-55); Float radix2 (-5767958804807127) (-55); Float radix2 (-7922530818994195) (-57); Float radix2 (7446990615055679) (-54);
          Float radix2 (-5417432953156985) (-52); Float radix2 (7131609175531569) (-54); Float radix2 (6373614836855980) (-50); Float radix2 (5889817236508872) (-54); Float radix2 (6294822700877229) (-55);
          Float radix2 (4792587429662568) (-54)];
      [:: Float radix2 (6042954174369836) (-55); Float radix2 (6854142789807986) (-56); Float radix2 (-8429387108203587) (-58); Float radix2 (5342128813366289) (-58); Float radix2 (-5660897563443618) (-54);
          Float radix2 (-6605500573784286) (-55); Float radix2 (-6203056586474023) (-55); Float radix2 (4917862773035000) (-56); Float radix2 (5914745610607293) (-55); Float radix2 (6366256098495933) (-55);
          Float radix2 (5959062830221290) (-54); Float radix2 (-8482796558098848) (-57); Float radix2 (-7987505715018793) (-56); Float radix2 (-8082922787602256) (-56); Float radix2 (8760514843956796) (-57);
          Float radix2 (-8414548812291411) (-57); Float radix2 (-5377485702029190) (-54); Float radix2 (-8222277459055189) (-60); Float radix2 (7205525292391603) (-55); Float radix2 (6903406945715847) (-55);
          Float radix2 (-5589989016432706) (-55); Float radix2 (-6404058428579973) (-55); Float radix2 (-6713153247514244) (-55); Float radix2 (4606162152538399) (-58); Float radix2 (5830355227208188) (-57);
          Float radix2 (6910583772276227) (-57); Float radix2 (5808962608570998) (-55); Float radix2 (-6903395386978513) (-56); Float radix2 (5165010139613630) (-56); Float radix2 (6004052473506829) (-57);
          Float radix2 (-8138337290169925) (-55); Float radix2 (-6809079157576537) (-55); Float radix2 (6599858574315492) (-57); Float radix2 (6461414943261933) (-54); Float radix2 (-6805097109591160) (-53);
          Float radix2 (5755336579398938) (-58); Float radix2 (5157764175347719) (-55); Float radix2 (-7557862297635576) (-56); Float radix2 (-8729177895391396) (-54); Float radix2 (-4789954584087290) (-56);
          Float radix2 (-8322654519205700) (-53); Float radix2 (7972207090845700) (-56); Float radix2 (5664454916684537) (-56); Float radix2 (8014902479407207) (-57); Float radix2 (4769325297922225) (-53);
          Float radix2 (-4749474046627015) (-52); Float radix2 (-6637986439670831) (-55); Float radix2 (-6213127539437073) (-53); Float radix2 (4670226064105849) (-54); Float radix2 (-4782819809733703) (-52);
          Float radix2 (5139412364165751) (-55); Float radix2 (5889817236508872) (-54); Float radix2 (7978367399018330) (-51); Float radix2 (5803845904068088) (-54); Float radix2 (-6594798858988486) (-55)];
      [:: Float radix2 (8392874863369318) (-57); Float radix2 (4717651962967857) (-54); Float radix2 (7662609878872630) (-55); Float radix2 (-6678266687070615) (-57); Float radix2 (-7407677228519179) (-54);
          Float radix2 (-7973913564190957) (-54); Float radix2 (-5695047772743175) (-55); Float radix2 (-7851156784105515) (-59); Float radix2 (4981957251820431) (-54); Float radix2 (4507821930961363) (-54);
          Float radix2 (8812690476034848) (-57); Float radix2 (8974263018041365) (-56); Float radix2 (-5925217804820315) (-57); Float radix2 (6995992693127176) (-54); Float radix2 (-8455874148917756) (-57);
          Float radix2 (-7417673070043496) (-55); Float radix2 (-7088008661742846) (-54); Float radix2 (7085753007466213) (-56); Float radix2 (6177203408175063) (-55); Float radix2 (-7713904529400321) (-56);
          Float radix2 (-8062272365038589) (-55); Float radix2 (-5805343155184713) (-54); Float radix2 (-8685327736416784) (-56); Float radix2 (6451828435131747) (-57); Float radix2 (4696272509858762) (-58);
          Float radix2 (7301094697793035) (-55); Float radix2 (8840850197194436) (-60); Float radix2 (6197472481829149) (-59); Float radix2 (-7015629353983453) (-55); Float radix2 (-7828912086368754) (-55);
          Float radix2 (-8187638125670298) (-54); Float radix2 (-7033538797858872) (-54); Float radix2 (5901471970318252) (-54); Float radix2 (5401008163287159) (-54); Float radix2 (-6443187881952780) (-55);
          Float radix2 (-5714683684561130) (-54); Float radix2 (6416895360662226) (-55); Float radix2 (-8203883809171240) (-53); Float radix2 (-7053651573400874) (-55); Float radix2 (-5805032552468901) (-54);
          Float radix2 (-8737522749934441) (-56); Float radix2 (-6520614564595836) (-53); Float radix2 (-5949716454204897) (-57); Float radix2 (8873792195460910) (-54); Float radix2 (8207297276689221) (-54);
          Float radix2 (-7460127697624605) (-56); Float radix2 (-4532936505577194) (-51); Float radix2 (8301178619466286) (-55); Float radix2 (-8409456219792443) (-54); Float radix2 (-5332647124028085) (-56);
          Float radix2 (-4589577025612800) (-53); Float radix2 (6294822700877229) (-55); Float radix2 (5803845904068088) (-54); Float radix2 (5548372316077799) (-50); Float radix2 (7003594646820384) (-55)];
      [:: Float radix2 (7655224865430619) (-56); Float radix2 (5753232666759987) (-56); Float radix2 (-6653528197072366) (-55); Float radix2 (-5467652718319269) (-56); Float radix2 (-5099681884854006) (-56);
          Float radix2 (6893029468799670) (-57); Float radix2 (-4994343353321530) (-56); Float radix2 (-5585101848694409) (-56); Float radix2 (5760723128902287) (-56); Float radix2 (5249182826103844) (-55);
          Float radix2 (6862746455978877) (-54); Float radix2 (8895719441833967) (-58); Float radix2 (-5459038112797243) (-55); Float radix2 (-5338939834530455) (-54); Float radix2 (-7121569919072259) (-55);
          Float radix2 (-4559205790183406) (-57); Float radix2 (5406566760518556) (-60); Float radix2 (6865807149184637) (-55); Float radix2 (4970987127483366) (-54); Float radix2 (5729712469016106) (-55);
          Float radix2 (6064866832114880) (-59); Float radix2 (-5866089663279103) (-58); Float radix2 (-6719816941254387) (-55); Float radix2 (-8078175165855076) (-55); Float radix2 (-7837378462820918) (-55);
          Float radix2 (8336561859730708) (-55); Float radix2 (8044710116465339) (-55); Float radix2 (-5185367842581305) (-54); Float radix2 (-6423028929716109) (-56); Float radix2 (8175848529378487) (-58);
          Float radix2 (-4707932831726560) (-60); Float radix2 (-5077718521119199) (-54); Float radix2 (-5030796957665915) (-61); Float radix2 (8951435229526690) (-56); Float radix2 (-6563347031510396) (-54);
          Float radix2 (-7975401309909628) (-57); Float radix2 (-6942227894443037) (-56); Float radix2 (-6321446672853552) (-55); Float radix2 (6838497276757265) (-54); Float radix2 (4872522097735580) (-54);
          Float radix2 (-8181932947329981) (-55); Float radix2 (5850951591353814) (-60); Float radix2 (-4702574720962094) (-53); Float radix2 (5709374353302033) (-57); Float radix2 (7385697722947025) (-55);
          Float radix2 (-6223989294669107) (-54); Float radix2 (-6164358141799911) (-56); Float radix2 (4974214342345697) (-54); Float radix2 (5229053703069833) (-56); Float radix2 (-7225220437279982) (-52);
          Float radix2 (6370453663198863) (-55); Float radix2 (4792587429662568) (-54); Float radix2 (-6594798858988486) (-55); Float radix2 (7003594646820384) (-55); Float radix2 (5649048701653322) (-51)]].

Time Eval vm_compute in map (map B2F) (cholesky m9).

End seq_cholesky.

Section GenericFcmdotprod.

Local Open Scope ring_scope.

Import Refinements.Op.

Class hmulvB {I} B T := hmulvB_op : forall n : I, T -> B n -> B n -> T.
(* Local Notation "*v%HC" := hmulv_op.
Reserved Notation "A *v B" (at level 40, left associativity, format "A  *v  B").
Local Notation "x *v y" := (hmulv_op x y) : hetero_computable_scope. *)

Open Scope computable_scope.
Open Scope hetero_computable_scope.

Variable T : Type.
Variable mxA : nat -> nat -> Type.

Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hcast mxA}.
(* Context `{!ulsub mxA, !ursub mxA, !dlsub mxA, !drsub mxA, !block mxA}. *)
Context `{!hmulvB (mxA 1) T, !scalar_mx_class T mxA}.

(* Check forall n c (a b : mxA n 1), hmulvB_op c a b = c - \sum_i (a i * b i). *)

(*
(** Sum [c + \sum a_i] computed in float from left to right. *)
Fixpoint fsum_l2r_rec n (c : F fs) : F fs ^ n -> F fs :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (fplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum a_i] computed in float from left to right. *)
Definition fsum_l2r n : F fs ^ n -> F fs :=
  match n with
    | 0%N => fun _ => F0 fs
    | n'.+1 =>
      fun a => fsum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.
*)

Definition gfcmdotprod_l2r n (c : T) (a b : mxA 1 n) : T :=
  hmulvB_op c a b.


End GenericFcmdotprod.

Section GenericHmulvb.

Import Refinements.Op.
Open Scope computable_scope.
Open Scope hetero_computable_scope.

Variable T : Type.
Variable mxA : nat -> nat -> Type.

Context `{!add T, !opp T, !mul T}.
(* Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hopp mxA}. *)

Compute hmulvB (mxA 1) T.
(*
Fixpoint hmulvB n c {struct n} :=
  match n return (mxA 1 n) -> (mxA 1 n) -> T with
    | 0%N => fun _ _ => c
    | n'.+1 => fun a b => hmulvB n' (c - (a ord0 * b ord0))%C (fun i => a (lift ord0 i)) (fun i => b (lift ord0 i))
  end.
*)

End GenericHmulvb.
