#!/bin/sh
res=`mktemp`

./lam > $res << in
(lambda x . lambda y . x y) lambda z . z
in
diff $res - << out
lambda y.(lambda z.z)y
out

./lam > $res << in
lambda x.lambda y.lambda z.x y z
in
diff $res - << out
lambda x.lambda y.lambda z.x y z
out

./lam > $res << in
lambda x.lambda y.lambda z.x(y z)
in
diff $res - << out
lambda x.lambda y.lambda z.x(y z)
out

./lam > $res << in
lambda x.lambda y.lambda z.lambda w.x(y(z w))
in
diff $res - << out
lambda x.lambda y.lambda z.lambda w.x(y(z w))
out

./lam > $res << in
lambda x.lambda y.lambda z.lambda w.x y z w
in
diff $res - << out
lambda x.lambda y.lambda z.lambda w.x y z w
out
