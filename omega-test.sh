#!/bin/sh -e
res=$(mktemp)

./omega > $res << EOS
selfApp = fun x: forall X.X->X. x (forall X.X->X) x;
EOS
diff $res - << EOS
selfApp:(forall X.X->X)->forall X.X->X
EOS
