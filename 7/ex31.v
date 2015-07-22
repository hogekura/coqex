(* Section の練習 *)

Section Poslist.
  (* このセクションの中では、Aが共通の変数として使える。 *)
  Variable A : Type.
  (* 非空なリスト *)
  Inductive poslist : Type := 
    | psingle : A -> poslist
    | pcons : A -> poslist -> poslist.

  Section Fold.
    (* 二項演算 *)
    Variable g : A -> A -> A.

   (* gによって畳み込む。
    * 次のどちらかを定義すること。どちらでもよい。
    * 左畳み込み : リスト [a; b; c] に対して (a * b) * c を計算する。
    * 右畳み込み : リスト [a; b; c] に対して a * (b * c) を計算する。
    *)
    Definition fold : poslist -> A :=
      fix f (xs : poslist) :=
      match xs with
        | psingle x => x
        | pcons x xs => g x (f xs)
      end.
    (* DefinitionをFixpointなどに置き換えてもよい。 *)
  End Fold.
End Poslist.
(* Poslistから抜けたことにより、poslistは変数Aについて量化された形になる。 *)

(* このリストに関するmap関数 *)
Section PoslistMap.
  Variable A B : Type.
  Variable f : A -> B.

  Definition map : poslist A -> poslist B :=
    fix map (xs : poslist A) :=
    match xs with
      | psingle x => psingle _ (f x)
      | pcons x xs => pcons _ (f x) (map xs)
    end.
End PoslistMap.
