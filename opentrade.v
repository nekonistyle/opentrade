From mathcomp
     Require Import all_ssreflect.
(*
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
Import Order.TTheory.
*)
(* ***************************** *)
Section Seq.    
  Variable (T:Type).
  Variable (R:rel T).

  Fixpoint insert (t:T) (s:seq T) :=
    if s is x :: s'
    then if R t x then t :: s else x :: insert t s'
    else [:: t].

  Lemma all_insert (P:pred T) (t:T) (s:seq T) :
    all P (insert t s) = P t && all P s.
  Proof.
    elim : s =>[|x s IHs]//=.
    case : ifP =>/=; first by rewrite andbC. by rewrite IHs andbCA.
  Qed.

  Lemma insert_sorted (t:T) (s:seq T) :
    transitive R -> total R -> sorted R s -> sorted R (insert t s).
  Proof.
    move => Htrans Htotal.
    elim : s =>[|x s IHs]//=. case : ifP =>/=[->|H Hpath]//.
    rewrite path_min_sorted; [exact : IHs (path_sorted Hpath)|].
    move : (Htotal t x). by rewrite H all_insert order_path_min //= =>->.
  Qed.
End Seq.

Lemma mem_insert (T:eqType) R t (s:seq T) x:
  x \in (insert R t s) = (x == t) || (x \in s).
Proof.
  elim : s =>[|h s IH]//=. by case : ifP =>_; rewrite !in_cons // IH orbCA.
Qed.

Section Rel.

  Definition oop (T:Type) (op:T -> T -> T) (x y:option T) : option T :=
    match x,y with
    | None, _ => y
    | _, None => x
    | Some x', Some y' => Some (op x' y')
    end.

  Lemma isSome_oop (T:Type) op (x y:option T) :
    isSome (oop op x y) = isSome x || isSome y.
  Proof. case : x y =>[x|][y|]//=. Qed.

  Definition orel T (R:rel T) : rel (option T) :=
    fun x y => match x, y with
               | None, _ => true
               | Some _, None => false
               | Some a, Some b => R a b
               end.

  Lemma orel_refl T (R:rel T) : reflexive R -> reflexive (orel R).
  Proof. by move => Hrefl [x|]//=. Qed.

  Lemma orel_trans T (R:rel T) : transitive R -> transitive (orel R).
  Proof. move => Htrans [y|] [x|] [z|]//=. exact : Htrans. Qed.

  Lemma orel_total T (R:rel T) : total R -> total (orel R).
  Proof. by move => Htotal [x|] [y|]/=. Qed.

  Lemma orel_oopl T (R:rel T) op:
    reflexive R -> (forall x y, R x (op x y)) ->
    forall x y, orel R x (oop op x y).
  Proof. by move => Hrefl H [x|][y|]/=. Qed.

  Lemma orel_oopr T (R:rel T) op:
    reflexive R -> (forall x y, R x (op y x)) ->
    forall x y, orel R y (oop op x y).
  Proof. by move => Hrefl H [x|][y|]/=. Qed.

  Definition strict T (R:rel T) : rel T := fun x y => R x y && ~~ R y x.

  Lemma strict_trans T (R:rel T) : transitive R -> transitive (strict R).
  Proof.
    move => Htrans y x z /andP[xy nyx]/andP[yz nzy].
    rewrite /strict (Htrans _ _ _ xy yz). case zx : (R z x)=>//.
      by move : (Htrans _ _ _ zx xy) nzy =>->.
  Qed.

  Lemma strictN T (R:rel T) x y : total R -> strict R x y = false -> R y x.
  Proof.
    rewrite /strict =>/(_ x y). case : (R y x)=>//. by rewrite orbF =>->.
  Qed.

  Lemma antisymP T (R:rel T):
    reflexive R -> antisymmetric R ->
    forall x y, reflect (x = y) (R x y && R y x).
  Proof.
    move => refl anti x y.
      by apply /(iffP idP) =>[|->]; [exact : anti|rewrite refl].
  Qed.

  Lemma antisym_eq (T:eqType) (R:rel T):
    reflexive R -> antisymmetric R -> forall x y, x == y = R x y && R y x.
  Proof.
    move => refl anti x y. by case : (antisymP refl anti) =>/eqP// /negbTE.
  Qed.

  Variant rel_spec T (R:rel T) x y :
    bool -> bool -> bool -> bool -> bool -> bool -> Prop :=
  | RelLtSpec of R x y & ~~ R y x :
      rel_spec R x y false false true false true false
  | RelEqSpec of R x y & R y x :
      rel_spec R x y true true false false true true
  | RelGtSpec of ~~ R x y & R y x :
      rel_spec R x y false false false true false true
  | RelIncompSpec of ~~ R x y & ~~ R y x :
      rel_spec R x y false false false false false false.

  Lemma relP (T:eqType) (R:rel T):
    reflexive R ->
    antisymmetric R ->
    forall x y,rel_spec R x y (x == y) (y == x)
                        (strict R x y) (strict R y x) (R x y) (R y x).
  Proof.
    rewrite /strict => refl anti x y. rewrite !(antisym_eq refl anti).
      by case xy : (R x y); case yx : (R y x);
        constructor =>//; rewrite ?xy ?yx.
  Qed.

  Variant total_spec T (R:rel T) x y :
    bool -> bool -> bool -> bool -> bool -> bool -> Prop :=
  | TotalLtSpec of R x y & ~~ R y x :
      total_spec R x y false false true false true false
  | TotalEqSpec of R x y & R y x :
      total_spec R x y true true false false true true
  | TotallGtSpec of ~~ R x y & R y x :
      total_spec R x y false false false true false true.

  Lemma totalP (T:eqType) (R:rel T):
    reflexive R ->
    antisymmetric R ->
    total R ->
    forall x y, total_spec R x y (x == y) (y == x)
                           (strict R x y) (strict R y x) (R x y) (R y x).
  Proof.
    rewrite /strict => refl anti total x y. move : (total x y).
      by case : (relP refl anti)=>//; constructor.
  Qed.
  
  Definition argrel (S T:Type) (f:S -> T) (R:rel T) : rel S :=
    fun x y => R (f x) (f y).

  Definition argrel_trans S T (f:S -> T) R :
    transitive R -> transitive (argrel f R)
    := fun Htrans _ _ _ => Htrans _ _ _.
End Rel.

Section Lexi.
  Variable (T:eqType).
  Variable (S:Type).
  Variable (R:rel T) (Q:rel S).

  Definition lexi : rel (T * S) :=
    fun x y => (x.1 == y.1) && Q x.2 y.2 || strict R x.1 y.1.

  Hypothesis (Hrefl : reflexive R).

  Lemma lexiW x y : lexi x y -> R x.1 y.1.
  Proof. by rewrite /lexi /strict =>/orP[/andP[/eqP->]|/andP[]]//. Qed.

  Hypothesis (Hanti : antisymmetric R).

  Lemma lexi_eql x y : Q x.2 y.2 -> lexi x y = R x.1 y.1.
  Proof.
    rewrite /lexi /strict =>->. rewrite andbT. case HR : (R x.1 y.1) =>/=.
    - case HR' : (R y.1 x.1); rewrite ?orbT // orbF. apply /eqP /Hanti.
        by rewrite HR.
    - rewrite orbF. apply /eqP => Heq. by move : Heq (Hrefl x.1) HR =>->->.
  Qed.

  Hypothesis (HtransR : transitive R).
  Hypothesis (HtransQ : transitive Q).

  Lemma lexi_trans : transitive lexi.
  Proof.
    rewrite /lexi => y x z /orP [/andP [/eqP -> HQxy]|Hxy]
                           /orP [/andP [/eqP <- HQyz]|Hyz].
    - by rewrite eq_refl (HtransQ HQxy HQyz).
    - by rewrite Hyz orbT.
    - by rewrite Hxy orbT.
    - by rewrite (strict_trans HtransR Hxy Hyz) orbT.
  Qed.
End Lexi.


Section market.
  Variable priceType : eqType.
  Variable pricerel : rel priceType.
  Variable otherdataType : eqType.
  Variable timerel : rel otherdataType.
  Hypothesis (pricerel_refl : reflexive pricerel).
  Hypothesis (pricerel_anti : antisymmetric pricerel).
  Hypothesis (pricerel_trans : transitive pricerel).
  Hypothesis (pricerel_total : total pricerel).
  Hypothesis (timerel_refl : reflexive timerel).
  Hypothesis (timerel_trans : transitive timerel).

  Variable (priceop:priceType -> priceType -> priceType).

  Hypothesis (pricerel_opl :
                forall x y, pricerel x y -> pricerel x (priceop x y)).
  Hypothesis (pricerel_opr :
                forall x y, pricerel x y -> pricerel (priceop y x) y).

  Variable (ple : rel priceType).
  Hypothesis (ple_refl : reflexive ple).
  Hypothesis (priceop_ple:
                forall x y, pricerel x y -> ple (priceop x y) (priceop y x)).

  Definition orderType : Type
    := nat * option priceType * otherdataType.
  Variable tobool : pred otherdataType.
  Notation is_bid := (fun x : orderType => tobool x.2).
  Notation share_of := (fun x : orderType => x.1.1).
  Notation price_of := (fun x : orderType => x.1.2).
  Notation otherdata_of := (fun x : orderType => x.2).

  Notation orderbookType := (seq orderType * seq orderType:Type).

  Definition opricerel (mode:bool) : rel (option priceType) :=
    (orel (fun x y => if mode then pricerel x y else pricerel y x)).

  Definition orderpricerel (mode:bool) : rel orderType :=
    argrel price_of (strict (opricerel mode)).

  Definition orderrel (mode:bool) : rel orderType :=
    argrel (fun x => (price_of x, otherdata_of x))
           (lexi (opricerel mode) timerel).

  Definition addorder (order : orderType) (b:orderbookType) :=
    if is_bid order
    then (insert (orderpricerel true) order b.1, b.2)
    else (b.1, insert (orderpricerel false) order b.2).

  Lemma opricerel_refl b : reflexive (opricerel b).
  Proof.
    rewrite /opricerel /orel =>[][x|]//.
    case : ifP =>_; exact : pricerel_refl.
  Qed.

  Lemma opricerel_anti b : antisymmetric (opricerel b).
  Proof.
    rewrite /opricerel /orel =>[][x|][y|]//.
      by case : ifP =>_/pricerel_anti ->.
  Qed.

  Lemma opricerel_trans b : transitive (opricerel b).
  Proof.
    apply : orel_trans. case : b => y x z; first exact : pricerel_trans.
    move => Hyx Hzy. exact : pricerel_trans Hzy Hyx.
  Qed.

  Lemma opricerel_total b : total (opricerel b).
  Proof. apply : orel_total. by case : b => x y. Qed.

  Definition orderrel_trans b : transitive (orderrel b) :=
    argrel_trans (lexi_trans (@opricerel_trans _) timerel_trans).

  Definition seq_order_valid (mode:bool) : pred (seq orderType) :=
    fun book => [&& sorted (orderrel mode) book,
                 uniq [seq otherdata_of order | order <- book] &
                 all (fun k => is_bid k == mode) book].

  Lemma seq_order_valid_cons (mode:bool) x s:
    seq_order_valid mode (x :: s) =
    [&& all (orderrel mode x) s,
     otherdata_of x \notin [seq otherdata_of x | x <- s],
     is_bid x == mode & seq_order_valid mode s].
  Proof.
    rewrite /seq_order_valid /= (path_sortedE (@orderrel_trans _)) -!andbA.
    congr (_ && _). rewrite andbCA. congr(_ && _). rewrite !andbA.
    congr(_ && _). by rewrite andbC andbA.
  Qed.

  Definition orderbook_valid : pred orderbookType :=
    fun book => seq_order_valid true book.1 && seq_order_valid false book.2.

  Definition neworder_valid (order:orderType) (book:seq orderType) :=
    all (argrel otherdata_of timerel^~ order) book &&
    (otherdata_of order \notin [seq otherdata_of x | x <- book]).

  Lemma neworder_valid_cons order x book:
    neworder_valid order (x :: book) =
    [&& argrel otherdata_of timerel x order,
     order.2 != x.2 & neworder_valid order book].
  Proof.
    rewrite /neworder_valid /= in_cons negb_or -!andbA. congr(_ && _).
      by rewrite andbCA.
  Qed.

  Lemma seq_order_orderrel_insert b order book :
    is_bid order = b ->
    seq_order_valid b book -> neworder_valid order book ->
    seq_order_valid b (insert (orderpricerel b) order book).
  Proof.
    move =><-.
    elim : book =>[|x s IHs]/=; [by rewrite /seq_order_valid /= eq_refl|].
    case : ifP.
    - rewrite /seq_order_valid /= /orderpricerel eq_refl /orderrel.
      rewrite /lexi /argrel /neworder_valid
      =>->/and4P[->->->->]/=/andP[/andP[_ _ ->]]. by rewrite orbT.
    - rewrite /orderpricerel !seq_order_valid_cons neworder_valid_cons.
      rewrite all_insert /orderrel /argrel
      => Hprice /and4P[-> Hx -> /IHs IH]/and3P[Htime Hneq /IH ->].
      rewrite !andbT (lexi_eql (opricerel_refl _) (@opricerel_anti _)) //=.
      rewrite (strictN (opricerel_total _) Hprice) /=. apply /mapP =>[[h]].
      rewrite mem_insert =>/orP[/eqP->Heq|hs xh];
        [by move : Heq Hneq =>->/eqP|].
      move /mapP : Hx. apply. by exists h.
  Qed.

  Theorem addOrder_valid order book :
    orderbook_valid book ->
    (if is_bid order then neworder_valid order book.1
     else neworder_valid order book.2) ->
    orderbook_valid (addorder order book).
  Proof.
    rewrite /addorder /orderbook_valid.
    case : ifP => Hmode /=/andP[sov1 sov2];
                    [by move /(seq_order_orderrel_insert Hmode sov1)->|
                             move /(seq_order_orderrel_insert Hmode sov2)->].
      by rewrite sov1.
  Qed.

  (**)

  Definition head_price (default:option priceType)
             (s:seq orderType) : option priceType :=
    head default (filter isSome (map price_of s)).

  Definition check_price : rel orderType :=
    fun x y =>
      match price_of x, price_of y with
      | Some x', Some y' => pricerel x' y'
      | _, _ => true
      end.

  Definition deal_price
             (default:option priceType) (x y:orderType) : option priceType :=
    let xy := oop priceop (price_of x) (price_of y) in
    if isSome xy then xy else default.

  Lemma isSome_deal_price default x y:
    isSome (deal_price default x y) =
    [|| isSome default, isSome x.1.2 | isSome y.1.2].
  Proof.
    rewrite /deal_price. by case : default x.1.2 y.1.2 =>[d|][a|][b|].
  Qed.

  Definition deal_order
             (default:option priceType) (x y:orderType) : orderType :=
    (minn (share_of x) (share_of y),
     let price := oop priceop (price_of x) (price_of y) in
     if price then price else default, otherdata_of x).
(*     if isSome (price_of x) then (price_of x) else default, otherdata_of x).*)

  Definition deals (default:option priceType) (x y:orderType) :
    orderType * orderType :=
    (deal_order default x y, deal_order default y x).

  Fixpoint opentrade_rec
           (price:option priceType) (a:seq orderType) (b:seq orderType) :
    option priceType * seq (orderType * orderType) * orderbookType :=
    if a is xa :: sa
    then
      let fix recf (price:option priceType) (xa:orderType) (b:seq orderType) :
            option priceType * seq (orderType * orderType) * orderbookType :=
          if b is xb :: sb
          then
            if check_price xa xb
            then
              if share_of xa == share_of xb
              then
                let result :=
                    opentrade_rec (deal_price price xa xb) sa sb in
                (result.1.1, deals result.1.1 xa xb :: result.1.2, result.2)
              else
                if share_of xa > share_of xb
                then
                  let result :=
                      recf
                        (deal_price price xa xb)
                        (share_of xa - share_of xb,
                         price_of xa, otherdata_of xa) sb in
                  (result.1.1, deals result.1.1 xa xb :: result.1.2, result.2)
                else
                  let result :=
                      opentrade_rec
                        (deal_price price xb xa) sa
                        ((share_of xb - share_of xa,
                          price_of xb, otherdata_of xb) :: sb) in
                  (result.1.1, deals result.1.1 xa xb :: result.1.2, result.2)
            else
              (price_of xa, [::], (xa :: sa, b))
          else
            (head_price price (xa :: sa), [::], (xa :: sa, b))
      in recf price xa b
    else
      (head_price price b, [::], (a, b)).

  Definition opentrade (price:option priceType) (book:orderbookType)
    := opentrade_rec price book.1 book.2.

  Lemma opentrade_equation
        (price:option priceType) (book:orderbookType) : 
        opentrade price book =
  if book.1 is xa :: sa
  then
    if book.2 is xb :: sb
    then
      if check_price xa xb
      then
        if share_of xa == share_of xb
        then
          let result :=
              opentrade (deal_price price xa xb) (sa, sb) in
                (result.1.1, deals result.1.1 xa xb :: result.1.2, result.2)
        else
          if share_of xa > share_of xb
          then
            let result :=
                opentrade
                  (deal_price price xa xb)
                  ((share_of xa - share_of xb,
                    price_of xa, otherdata_of xa) :: sa, sb) in
            (result.1.1, deals result.1.1 xa xb :: result.1.2, result.2)
          else
            let result :=
                opentrade
                  (deal_price price xb xa)
                  (sa,
                   (share_of xb - share_of xa,
                    price_of xb, otherdata_of xb) :: sb) in
            (result.1.1, deals result.1.1 xa xb :: result.1.2, result.2)
      else
        (price_of xa, [::], book)
    else
      (head_price price book.1, [::], book)
  else
    (head_price price book.2, [::], book).
  Proof.
      by case : book =>[[|xa sa][|xb sb]].
  Qed.

  Lemma opentrade_ind
        (P:option priceType -> seq orderType -> seq orderType -> Prop) :
    (forall price b, P price [::] b) ->
    (forall price xa sa, P price (xa :: sa) [::]) ->
    (forall price xa sa xb sb,
        check_price xa xb -> share_of xa == share_of xb ->
        P (deal_price price xa xb) sa sb -> P price (xa :: sa) (xb :: sb)) ->
    (forall price xa sa xb sb,
        check_price xa xb -> share_of xa == share_of xb = false ->
        share_of xa > share_of xb ->
        P (deal_price price xa xb)
          ((share_of xa - share_of xb, price_of xa, otherdata_of xa) :: sa)
          sb -> P price (xa :: sa) (xb :: sb)) ->
    (forall price xa sa xb sb,
        check_price xa xb -> share_of xa == share_of xb = false ->
        share_of xa > share_of xb = false ->
        share_of xa < share_of xb ->
        P (deal_price price xb xa) sa
          ((share_of xb - share_of xa, price_of xb, otherdata_of xb) :: sb) ->
        P price (xa :: sa) (xb :: sb)) ->
    (forall price xa sa xb sb,
        check_price xa xb = false ->
        P price (xa :: sa) (xb :: sb)) ->
    forall price a b, P price a b.
  Proof.
    move => Hns Hsn Heq Hlt Hgt Hfalse price a b.
    elim : a =>[|xa sa IHa] in price b *=>//.
    elim : b =>[|xb sb IHb] in price xa *=>//.
    case Hcheck : (check_price xa xb); last exact : Hfalse.
    case : (ltngtP (share_of xa) (share_of xb)) => H.
    - apply : Hgt =>//; by case : ltngtP H.
    - apply : Hlt =>//. by case : ltngtP H.
    - apply : Heq =>//. exact /eqP.
  Qed.

  Lemma orderbook_valid_eq xa sa xb sb :
    orderbook_valid (xa :: sa, xb :: sb) -> orderbook_valid (sa, sb).
  Proof.
      by rewrite /orderbook_valid !seq_order_valid_cons /=
                 =>/andP[/and4P[_ _ _->]/and4P[_ _ _->]].
  Qed.

  Lemma orderbook_valid_lt xa sa xb sb :
    orderbook_valid (xa :: sa, xb :: sb) ->
    orderbook_valid
      (sa, (share_of xb - share_of xa, price_of xb, otherdata_of xb) :: sb).
  Proof.
    rewrite /orderbook_valid !seq_order_valid_cons /=
            =>/andP[/and4P[_ _ _->]/and4P[Hxb ->->->]]/=. by rewrite andbT.
  Qed.

  Lemma orderbook_valid_gt xa sa xb sb :
    orderbook_valid (xa :: sa, xb :: sb) ->
    orderbook_valid
      ((share_of xa - share_of xb, price_of xa, otherdata_of xa) :: sa, sb).
  Proof.
    rewrite /orderbook_valid !seq_order_valid_cons /=
            =>/andP[/and4P[Hxa ->->->]/and4P[_ _ _->]]/=. by rewrite !andbT.
  Qed.

  (**)

  Definition traderesult_valid1
             (result:
                option priceType * seq (orderType * orderType) * orderbookType)
    :=
    let book := result.2 in
    (book.2 <> [::] -> all (isSome \o price_of) book.1) /\
    (book.1 <> [::] -> all (isSome \o price_of) book.2).

  Definition traderesult_valid2'
             (result:
                option priceType * seq (orderType * orderType) * orderbookType)
    :=
    let price := result.1.1 in
    let book  := result.2 in
    orel pricerel price (head_price price book.1) /\
    orel (fun x y => pricerel y x) price (head_price price book.2).

  Definition traderesult_valid2
             (result:
                option priceType * seq (orderType * orderType) * orderbookType)
    :=
    let price := result.1.1 in
    let book  := result.2 in
    all (fun x => price_of x ==> opricerel true price (price_of x)) book.1 &&
    all (fun x => price_of x ==> opricerel false price (price_of x)) book.2.

  Definition traderesult_valid3
             (result:
                option priceType * seq (orderType * orderType) * orderbookType)
    :=
    let price := result.1.1 in
    let book  := result.2 in
    price ->
    all (fun x => price_of x != price) book.2 \/
    all (fun x => price_of x != price) book.1.

  Definition traderesult_valid
             (result:
                option priceType * seq (orderType * orderType) * orderbookType)
    :=
    [/\ traderesult_valid1 result, traderesult_valid2 result &
                                   traderesult_valid3 result].

  Lemma all_isSome_price_of b x s :
    price_of x -> path (orderrel b) x s -> all (isSome \o price_of) s.
  Proof.
    elim : s =>[|y s IHs] in x *=>//= Hx /andP[Hxy Hpath].
    have Hy : y.1.2. move : Hxy Hx.
    - rewrite /orderrel /argrel =>/(lexiW (@opricerel_refl _)) /=.
      case : x.1.2=>// a. by case : y.1.2.
    -  by rewrite (IHs _ Hy Hpath) Hy.
  Qed.

  (**)

  Lemma head_price_head price book :
    all (isSome \o price_of) book ->
    head_price price book = head price (map price_of book).
  Proof.
    rewrite /head_price =>/all_filterP {2}<-. by rewrite filter_map.
  Qed.

  Lemma eq_head_price default' default s:
    head_price default s =
    if has (isSome \o price_of) s
    then head_price default' s
    else default.
  Proof.
    elim : s =>[|[[shape p] other] s IHs]//=. by case : p.
  Qed.

  Lemma head_price_id price s:
    head_price (head_price price s) s = head_price price s.
  Proof.
    elim : s =>[|[[share p] other] s IHs]//=. by case : p.
  Qed.

  (**)

  Theorem opentrade_valid1 (price:option priceType) (book:orderbookType) :
    orderbook_valid book -> traderesult_valid1 (opentrade price book).
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s|
       |price xa sa xb sb Hcheck Heq IH /orderbook_valid_eq /IH H
       |price xa sa xb sb Hcheck Heq Hgt IH /orderbook_valid_gt /IH H
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH /orderbook_valid_lt /IH H
       |price xa sa xb sb Hcheck]//;
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //.
    rewrite /traderesult_valid1
            =>/andP/=[/and3P[Hpatha _ _]/and3P[Hpathb _ _]].
      have [Ha Hb]: xa.1.2 /\ xb.1.2.
      + move : Hcheck. rewrite /check_price. by case : xa.1.2 xb.1.2 =>[a|][b|].
      + rewrite Ha (all_isSome_price_of Ha Hpatha).
          by rewrite Hb (all_isSome_price_of Hb Hpathb).
  Qed.

  Theorem opentrade_valid2' (price:option priceType) (book:orderbookType) :
    traderesult_valid2' (opentrade price book).
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH
       |price xa sa xb sb Hcheck Heq Hgt IH
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //.
    - rewrite /traderesult_valid2' /= head_price_id.
        by split; apply : orel_refl; apply : pricerel_refl.
    - rewrite /traderesult_valid2' /= head_price_id.
        by split; apply : orel_refl; apply : pricerel_refl.
    - move : Hcheck. rewrite /traderesult_valid2' /head_price /check_price /=.
      move : xa.1.2 xb.1.2 =>[a|][b|]//=.
        by case : (totalP pricerel_refl pricerel_anti pricerel_total).
  Qed.

  Theorem opentrade_valid2 (price:option priceType) (book:orderbookType) :
    orderbook_valid book -> traderesult_valid2 (opentrade price book).
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s 
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH /orderbook_valid_eq /IH H
       |price xa sa xb sb Hcheck Heq Hgt IH /orderbook_valid_gt /IH H
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH /orderbook_valid_lt /IH H
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //.
    - rewrite /traderesult_valid2 /head_price =>/and3P/=[_ H _].
      elim : s H =>[|h s IH]//=. case : ifP =>_/=.
      + rewrite opricerel_refl =>/(order_path_min (@orderrel_trans _)) /=.
        apply : sub_all => z /(lexiW (opricerel_refl _)) /=->. exact /implyP.
      + by rewrite (path_sortedE (@orderrel_trans _)) =>/andP[_/IH].
    - rewrite /traderesult_valid2 /head_price =>/andP[/and3P[H _ _] _].
      rewrite andbT. move : (xa :: sa) H =>/=. elim =>[|h s IH]//=.
      case : ifP =>_/=.
      + rewrite opricerel_refl =>/(order_path_min (@orderrel_trans _)) /=.
        apply : sub_all => z /(lexiW (opricerel_refl _)) /=->. exact /implyP.
      + by rewrite (path_sortedE (@orderrel_trans _)) =>/andP[_/IH].
    - rewrite /traderesult_valid2 =>/andP[/and3P/=[Ha _ _]/and3P/=[Hb _ _]].
      apply /and3P. split.
      + rewrite opricerel_refl implybT /=.
        apply : sub_all (order_path_min (@orderrel_trans _) Ha) => z.
        move /(lexiW (opricerel_refl _)) =>/=->. exact /implyP.
      + move : Hcheck. rewrite /check_price. case : xa.1.2 xb.1.2 =>[a|][b|]//=.
          by case /orP : (pricerel_total a b) =>->.
      + move : Hb. rewrite (path_sortedE (@orderrel_trans _)) =>/andP[H _].
        apply : sub_all H => z /(lexiW (opricerel_refl _)) /= H.
        apply /implyP =>_. apply : opricerel_trans H. move : Hcheck.
        rewrite /check_price. case : xa.1.2 xb.1.2 =>[a|][b|]//=.
          by case /orP : (pricerel_total a b) =>->.
  Qed.

  Theorem opentrade_valid3 (price:option priceType) (book:orderbookType) :
    orderbook_valid book -> traderesult_valid3 (opentrade price book).
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s _
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH /orderbook_valid_eq /IH H
       |price xa sa xb sb Hcheck Heq Hgt IH /orderbook_valid_gt /IH H
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH /orderbook_valid_lt /IH H
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //.
    - by right.
    - by left.
    - rewrite /traderesult_valid3 =>/andP/=[_/and3P[Hb _ _]] Hxa. left.
      move : Hxa Hcheck (order_path_min (@orderrel_trans _) Hb).
      rewrite /check_price /orderrel /argrel. case : xa.1.2 =>[a|]//_.
      case : xb.1.2 =>[b|]//.
      case : (totalP pricerel_refl pricerel_anti pricerel_total b a)
               =>//= Hba Hab _.
      have -> : (Some b != Some a);
        [by apply /eqP=>[[/(antisymP pricerel_refl pricerel_anti)/andP[]]];
                        move : Hab =>/negbTE->|].
      apply : sub_all => y /(lexiW (@opricerel_refl _)) /=.
      case : y.1.2 =>[c|]// Hcb.
      apply /eqP=>[[/(antisymP pricerel_refl pricerel_anti)/andP[_ Hac]]].
        by move : (pricerel_trans Hac Hcb) Hab =>->.
  Qed.

  (**)

  Lemma isSome_head_price default s :
    isSome (head_price default s) = default || has (isSome \o price_of) s.
  Proof.
    rewrite /head_price. elim : s =>[|a s IHs]/=; first by rewrite orbF.
      by case : a.1.2 =>[x|]//; rewrite orbT.
  Qed.

  Lemma deals_price_isSome_default
        (price:option priceType) (book:orderbookType) :
    isSome price -> isSome (opentrade price book).1.1.
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s 
      |price xa sa
      |price xa sa xb sb Hcheck Heq IH Hprice
      |price xa sa xb sb Hcheck Heq Hgt IH Hprice
      |price xa sa xb sb Hcheck Heq Hgt Hlt IH Hprice
      |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //.
    - by rewrite isSome_head_price =>->.
    - by rewrite isSome_head_price =>->.
    - apply : IH. by rewrite isSome_deal_price Hprice.
    - apply : IH. by rewrite isSome_deal_price Hprice.
    - apply : IH. by rewrite isSome_deal_price Hprice.
    - move : Hcheck. rewrite /check_price. by case : xa.1.2.
  Qed.

  Lemma deals_price_isSomeP
        (price:option priceType) (book:orderbookType) :
    reflect
      [\/ isSome price,
       has (isSome \o price_of) book.1 |
       has (isSome \o price_of) book.2]
      (isSome (opentrade price book).1.1).
  Proof.
    apply /(iffP idP).
    - case : book. move : price.
      apply : opentrade_ind
      =>[price s 
        |price xa sa
        |price xa sa xb sb Hcheck Heq IH
        |price xa sa xb sb Hcheck Heq Hgt IH
        |price xa sa xb sb Hcheck Heq Hgt Hlt IH
        |price xa sa xb sb Hcheck];
          rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
      + rewrite isSome_head_price => H. by apply /or3P.
      + rewrite isSome_head_price =>/= H. apply /or3P. by rewrite orbF.
      + move /IH. by rewrite isSome_deal_price /=
                  =>[][/or3P[]||]->; apply /or3P; rewrite ?orbT.
      + move /IH. by rewrite isSome_deal_price /=
                  =>[][/or3P[]||]->; apply /or3P; rewrite ?orbT.
      + move /IH. by rewrite isSome_deal_price /=
                  =>[][/or3P[]||]->; apply /or3P; rewrite ?orbT.
      + move=>->. by apply /or3P; rewrite ?orbT.
    - case; first exact : deals_price_isSome_default;
      case : book; move : price;
      apply : opentrade_ind
      =>[price s 
        |price xa sa
        |price xa sa xb sb Hcheck Heq IH
        |price xa sa xb sb Hcheck Heq Hgt IH
        |price xa sa xb sb Hcheck Heq Hgt Hlt IH
        |price xa sa xb sb Hcheck];
          rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
      + rewrite isSome_head_price /==>->. by rewrite orbT.
      + case /orP =>// Ha. apply : deals_price_isSome_default.
          by rewrite isSome_deal_price Ha orbT.
      + case /orP =>// Ha. apply : deals_price_isSome_default.
          by rewrite isSome_deal_price Ha !orbT.
      + move : Hcheck. rewrite /check_price. by case : xa.1.2.
      + rewrite isSome_head_price =>->. exact : orbT.
      + case /orP =>// Hb. apply : deals_price_isSome_default.
          by rewrite isSome_deal_price Hb !orbT.
      + case /orP =>// Hb. apply : deals_price_isSome_default.
          by rewrite isSome_deal_price Hb !orbT.
      + move : Hcheck.
        rewrite /check_price. by case : xa.1.2 xb.1.2 =>[a|][b|].
  Qed.

  Definition deals_share_valid (deals:seq (orderType * orderType)) :=
    \sum_(x <- deals) share_of x.1 = \sum_(x <- deals) share_of x.2.

  Theorem opentrade_deals_share_valid
          (price:option priceType) (book:orderbookType) :
    deals_share_valid (opentrade price book).1.2.
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH
       |price xa sa xb sb Hcheck Heq Hgt IH
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
    - by rewrite /deals_share_valid !big_nil.
    - by rewrite /deals_share_valid !big_nil.
    - rewrite /deals_share_valid !big_cons /= minnC. congr(_ + _).
      exact : IH.
    - rewrite /deals_share_valid !big_cons /= minnC. congr(_ + _).
      exact : IH.
    - rewrite /deals_share_valid !big_cons /= minnC. congr(_ + _).
      exact : IH.
    - by rewrite /deals_share_valid !big_nil.
  Qed.

  Definition ople : rel (option priceType) :=
    fun x y => match x, y with
               | None, None => true
               | Some a, Some b => ple a b
               | _, _ => false
               end.

  Lemma ople_refl : reflexive ople.
  Proof. by case =>[a|]/=. Qed.

  Definition contract_valid (contracts:seq (orderType * orderType)) :=
    all (fun contract =>
           [&& is_bid contract.1, ~~ is_bid contract.2,
           share_of contract.1 == share_of contract.2 &
           ople (price_of contract.1) (price_of contract.2)]) contracts.

  Lemma opentrade_contract_valid (price:option priceType) (book:orderbookType):
    orderbook_valid book -> contract_valid (opentrade price book).1.2.
  Proof.
    case : book. move : price.
    apply : opentrade_ind
    =>[price s
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH Hbook
       |price xa sa xb sb Hcheck Heq Hgt IH Hbook
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH Hbook
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
    - move /andP : (Hbook)
      =>[/and3P/=[_ _/andP[/eqP->_]/and3P/=[_ _/andP[/eqP->_]]]].
      rewrite minnC !eq_refl (IH (orderbook_valid_eq Hbook)).
      move : Hcheck. rewrite /check_price.
      case : xa.1.2 xb.1.2 =>[a|][b|]/=; rewrite ?ple_refl ?ople_refl // andbT.
      exact : priceop_ple.
    - move /andP : (Hbook)
      =>[/and3P/=[_ _/andP[/eqP->_]/and3P/=[_ _/andP[/eqP->_]]]].
      rewrite minnC !eq_refl (IH (orderbook_valid_gt Hbook)) //.
      move : Hcheck. rewrite /check_price.
      case : xa.1.2 xb.1.2 =>[a|][b|]/=; rewrite ?ple_refl ?ople_refl // andbT.
      exact : priceop_ple.
    - move /andP : (Hbook)
      =>[/and3P/=[_ _/andP[/eqP->_]/and3P/=[_ _/andP[/eqP->_]]]].
      rewrite minnC !eq_refl (IH (orderbook_valid_lt Hbook)) //.
      move : Hcheck. rewrite /check_price.
      case : xa.1.2 xb.1.2 =>[a|][b|]/=; rewrite ?ple_refl ?ople_refl // andbT.
      exact : priceop_ple.
  Qed.

  Definition contract_valid1_def (usr:otherdataType) (mode:bool)
             (book contracts rbook:seq orderType) :=
      let order := head (0,None,usr) [seq x <- book | otherdata_of x == usr] in
      let rorder :=
          head (0,None,usr) [seq x <- rbook | otherdata_of x == usr] in
      share_of order =
      share_of rorder +
      \sum_(x <- contracts | otherdata_of x == usr) share_of x.

  Definition contract_valid1 (book:orderbookType)
             (result:option priceType * seq (orderType * orderType)
                     * orderbookType) :=
    forall usr : otherdataType,
      let mode := tobool usr in
      if mode
      then contract_valid1_def
             usr mode book.1 [seq x.1 | x <- result.1.2] result.2.1
      else contract_valid1_def
             usr mode book.2 [seq x.2 | x <- result.1.2] result.2.2.

  Lemma opentrade_contract_valid1
        (price:option priceType) (book:orderbookType) :
    orderbook_valid book -> contract_valid1 book (opentrade price book).
  Proof.
    move => Hbook usr /=. rewrite /contract_valid1_def.
    case : ifP =>_; case : book Hbook; move : price =>/=;
    apply : opentrade_ind
    =>[price s
      |price xa sa
      |price xa sa xb sb Hcheck Heq IH Hbook
      |price xa sa xb sb Hcheck Heq Hgt IH Hbook
      |price xa sa xb sb Hcheck Heq Hgt Hlt IH Hbook
      |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
    - by rewrite big_nil.
    - by rewrite big_nil /= addn0.
    - move /andP : (Hbook) =>/=[/and3P/=[_/andP[/mapP notin _] _] _].
      rewrite /deal_order. move /eqP : Heq =><-. rewrite minnn big_cons.
      case : ifP =>[/eqP xausr|_]/=; [|exact : IH (orderbook_valid_eq Hbook)].
      rewrite addnCA -(IH (orderbook_valid_eq Hbook)) /=.
      rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 /= ?addn0 =>// z Hz.
      apply /eqP => zusr. apply : notin. exists z =>//. by rewrite zusr.
    - rewrite /deal_order /minn (leq_gtF (ltnW Hgt)) big_cons.
      case : ifP =>[xausr|neq]/=.
      + rewrite addnCA -(IH (orderbook_valid_gt Hbook)) /= xausr.
          by rewrite subnKC // ltnW.
      + by rewrite -(IH (orderbook_valid_gt Hbook)) /= neq.
    - move /andP : (Hbook) =>/=[/and3P/=[_/andP[/mapP notin _] _] _].
      rewrite /deal_order /minn Hlt big_cons.
      case : ifP =>[/eqP xausr|neq];
                     [|exact : (IH (orderbook_valid_lt Hbook))].
      rewrite addnCA -(IH (orderbook_valid_lt Hbook)) /=.
      rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 /= ?addn0 =>// z Hz.
      apply /eqP => zusr. apply : notin. exists z =>//. by rewrite zusr.
    - by rewrite big_nil addn0.
    - by rewrite big_nil addn0.
    - by rewrite big_nil.
    - move /andP : (Hbook) =>/=[_/and3P/=[_/andP[/mapP notin _] _]].
      rewrite /deal_order. move /eqP : Heq =>->. rewrite minnn big_cons.
      case : ifP =>[/eqP xausr|_]/=; [|exact : IH (orderbook_valid_eq Hbook)].
      rewrite addnCA -(IH (orderbook_valid_eq Hbook)) /=.
      rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 /= ?addn0 =>// z Hz.
      apply /eqP => zusr. apply : notin. exists z =>//. by rewrite zusr.
    - move /andP : (Hbook) =>/=[_/and3P/=[_/andP[/mapP notin _] _]].
      rewrite /deal_order /minn Hgt big_cons.
      case : ifP =>[/eqP xausr|neq];
                     [|exact : (IH (orderbook_valid_gt Hbook))].
      rewrite addnCA -(IH (orderbook_valid_gt Hbook)) /=.
      rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 /= ?addn0 =>// z Hz.
      apply /eqP => zusr. apply : notin. exists z =>//. by rewrite zusr.
    - rewrite /deal_order /minn (leq_gtF (ltnW Hlt)) big_cons.
      case : ifP =>[xausr|neq]/=.
      + rewrite addnCA -(IH (orderbook_valid_lt Hbook)) /= xausr.
          by rewrite subnKC // ltnW.
      + by rewrite -(IH (orderbook_valid_lt Hbook)) /= neq.
    - by rewrite big_nil addn0.
  Qed.

  Lemma mem_contractl price book x:
    x \in [seq x.1 | x <- (opentrade price book).1.2] ->
          has (fun order => order.2 == x.2) book.1.
  Proof.
    case : book =>/=. move : price.
    apply : opentrade_ind
    =>[price s
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH
       |price xa sa xb sb Hcheck Heq Hgt IH
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
    - by rewrite in_cons =>/orP[/eqP->|/IH->]; rewrite ?eq_refl ?orbT.
    - rewrite in_cons =>/orP[/eqP->|/IH]//.
        by rewrite /deal_order /= eq_refl.
    - rewrite in_cons =>/orP[/eqP->|/IH]//.
        by rewrite /deal_order /= eq_refl.
    - move =>->. exact : orbT.
  Qed.

  Lemma mem_contractr price book x:
    x \in [seq x.2 | x <- (opentrade price book).1.2] ->
          has (fun order => order.2 == x.2) book.2.
  Proof.
    case : book =>/=. move : price.
    apply : opentrade_ind
    =>[price s
       |price xa sa
       |price xa sa xb sb Hcheck Heq IH
       |price xa sa xb sb Hcheck Heq Hgt IH
       |price xa sa xb sb Hcheck Heq Hgt Hlt IH
       |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
    - by rewrite in_cons =>/orP[/eqP->|/IH->]; rewrite ?eq_refl ?orbT.
    - rewrite in_cons =>/orP[/eqP->|/IH]//.
        by rewrite /deal_order /= eq_refl.
    - move =>->. exact : orbT.
    - rewrite in_cons =>/orP[/eqP->|/IH]//.
        by rewrite /deal_order /= eq_refl.
  Qed.

  Definition contract_valid2_def (usr:otherdataType) (mode:bool)
             (book contracts rbook:seq orderType) :=
      let order := head (0,None,usr) [seq x <- book | otherdata_of x == usr] in
      all (opricerel mode (price_of order) \o price_of)
          [seq x <- contracts | otherdata_of x == usr].

  Definition contract_valid2 (book:orderbookType)
             (result:option priceType * seq (orderType * orderType)
                     * orderbookType) :=
    forall usr : otherdataType,
      let mode := tobool usr in
      if mode
      then contract_valid2_def
             usr mode book.1 [seq x.1 | x <- result.1.2] result.2.1
      else contract_valid2_def
             usr mode book.2 [seq x.2 | x <- result.1.2] result.2.2.

  Lemma openorder_contract_valid2
        (price:option priceType) (book:orderbookType) :
    orderbook_valid book -> contract_valid2 book (opentrade price book).
  Proof.
    move => Hbook usr /=. rewrite /contract_valid2_def.
    case : ifP => Hmode; case : book Hbook; move : price =>/=;
    apply : opentrade_ind
    =>[price s
      |price xa sa
      |price xa sa xb sb Hcheck Heq IH Hbook
      |price xa sa xb sb Hcheck Heq Hgt IH Hbook
      |price xa sa xb sb Hcheck Heq Hgt Hlt IH Hbook
      |price xa sa xb sb Hcheck];
        rewrite opentrade_equation /= ?Hcheck ?Heq ?Hgt //=.
    - move /andP : (Hbook) =>/=[/and3P/=[_/andP[notin _] _] _].
      case : ifP =>[xausr|_]/=; [|exact : (IH (orderbook_valid_eq Hbook))].
      apply /andP. split.
      + move : Hcheck. rewrite /check_price.
        case : xa.1.2 xb.1.2 =>[a|][b|]//=; rewrite Hmode ?pricerel_refl //.
        exact : pricerel_opl.
      + rewrite (@eq_in_filter _ _ pred0)
        =>[|z /mem_contractl/hasP[x/(map_f snd)/= Hin xz]];
            [by rewrite filter_pred0|].
        apply /eqP => zusr.
          by move /eqP : xausr xz zusr Hin notin =><-/eqP->->->.
    - move : (IH (orderbook_valid_gt Hbook)) =>/=.
      case : ifP =>[xausr|_]//=.
      move : Hcheck. rewrite /check_price.
      case : xa.1.2 xb.1.2 =>[a|][b|]//=; rewrite Hmode ?pricerel_refl //.
        by move /pricerel_opl ->.
    - move /andP : (Hbook) =>/=[/and3P/=[_/andP[notin _] _] _].
      case : ifP =>[xausr|_]/=; [|exact : (IH (orderbook_valid_lt Hbook))].
      apply /andP. split.
      + move : Hcheck. rewrite /check_price.
        case : xa.1.2 xb.1.2 =>[a|][b|]//=; rewrite Hmode ?pricerel_refl //.
        exact : pricerel_opl.
      + rewrite (@eq_in_filter _ _ pred0)
        =>[|z /mem_contractl/hasP[x/(map_f snd)/= Hin xz]];
            [by rewrite filter_pred0|].
        apply /eqP => zusr.
          by move /eqP : xausr xz zusr Hin notin =><-/eqP->->->.
    - move /andP : (Hbook) =>/=[_/and3P/=[_/andP[notin _] _]].
      case : ifP =>[xbusr|_]/=; [|exact : (IH (orderbook_valid_eq Hbook))].
      apply /andP. split.
      + move : Hcheck. rewrite /check_price.
        case : xa.1.2 xb.1.2 =>[a|][b|]//=; rewrite Hmode ?pricerel_refl //.
        exact : pricerel_opr.
      + rewrite (@eq_in_filter _ _ pred0)
        =>[|z /mem_contractr/hasP[x/(map_f snd)/= Hin xz]];
            [by rewrite filter_pred0|].
        apply /eqP => zusr.
          by move /eqP : xbusr xz zusr Hin notin =><-/eqP->->->.
    - move /andP : (Hbook) =>/=[_/and3P/=[_/andP[notin _] _]].
      case : ifP =>[xbusr|_]/=; [|exact : (IH (orderbook_valid_gt Hbook))].
      apply /andP. split.
      + move : Hcheck. rewrite /check_price.
        case : xa.1.2 xb.1.2 =>[a|][b|]//=; rewrite Hmode ?pricerel_refl //.
        exact : pricerel_opr.
      + rewrite (@eq_in_filter _ _ pred0)
        =>[|z /mem_contractr/hasP[x/(map_f snd)/= Hin xz]];
            [by rewrite filter_pred0|].
        apply /eqP => zusr.
          by move /eqP : xbusr xz zusr Hin notin =><-/eqP->->->.
    - move : (IH (orderbook_valid_lt Hbook)) =>/=.
      case : ifP =>[xbusr|_]//=.
      move : Hcheck. rewrite /check_price.
      case : xa.1.2 xb.1.2 =>[a|][b|]//=; rewrite Hmode ?pricerel_refl //.
        by move /pricerel_opr ->.
  Qed.

End market.
