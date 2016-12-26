#!/bin/sh -e
res=`mktemp`

echo "test case 1"
./lam > $res << in
(lambda x . lambda y . x y) lambda z . z
in
diff $res - << out
lambda y.(lambda z.z) y
out

echo "test case 2"
./lam > $res << in
lambda x.lambda y.lambda z.x y z
in
diff $res - << out
lambda x.lambda y.lambda z.x y z
out

echo "test case 3"
./lam > $res << in
lambda x.lambda y.lambda z.x (y z)
in
diff $res - << out
lambda x.lambda y.lambda z.x (y z)
out

echo "test case 4"
./lam > $res << in
lambda x.lambda y.lambda z.lambda w.x (y (z w))
in
diff $res - << out
lambda x.lambda y.lambda z.lambda w.x (y (z w))
out

echo "test case 5"
./lam > $res << in
lambda x.lambda y.lambda z.lambda w.x y z w
in
diff $res - << out
lambda x.lambda y.lambda z.lambda w.x y z w
out
