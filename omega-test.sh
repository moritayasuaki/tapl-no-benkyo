#!/bin/sh -e
res=$(mktemp)

./omega > $res << EOS
selfApp = fun x: forall X.X->X. x (forall X.X->X) x;
EOS
diff $res - << EOS
selfApp:(forall X.X->X)->forall X.X->X
EOS

./omega > $res << EOS
Nat:*;
zero:Nat;
succ:Nat->Nat;
id = fun X. fun x:X. x;
id Nat zero;
double = fun X. fun f:X->X. fun a:X. f (f a);
doubleNat = double Nat;
double Nat (fun x:Nat. succ(succ(x))) (succ(succ(succ(zero))));
doubleNatArrowNat = double (Nat->Nat);
EOS
diff $res - << EOS
Nat:*
zero:Nat
succ:Nat->Nat
id:forall X.X->X
zero
double:forall X.(X->X)->X->X
doubleNat:(Nat->Nat)->Nat->Nat
succ(succ(succ(succ(succ(succ(succ zero))))))
doubleNatArrowNat:((Nat->Nat)->Nat->Nat)->(Nat->Nat)->Nat->Nat
EOS

