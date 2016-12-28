#!/bin/sh -e
res=`mktemp`


echo "test case 1"
./lambda > $res << in
(lambda x . lambda y . x y) lambda z . z
in
diff $res - << out
lambda y.(lambda z.z) y
out

echo "test case 2"
./lambda > $res << in
lambda x.lambda y.lambda z.x y z
in
diff $res - << out
lambda x.lambda y.lambda z.x y z
out

echo "test case 3"
./lambda > $res << in
lambda x.lambda y.lambda z.x (y z)
in
diff $res - << out
lambda x.lambda y.lambda z.x (y z)
out

echo "test case 4"
./lambda > $res << in
lambda x.lambda y.lambda z.lambda w.x (y (z w))
in
diff $res - << out
lambda x.lambda y.lambda z.lambda w.x (y (z w))
out

echo "test case 5"
./lambda > $res << in
lambda x.lambda y.lambda z.lambda w.x y z w
in
diff $res - << out
lambda x.lambda y.lambda z.lambda w.x y z w
out

echo "test case 6"
./lambda > $res << in
(lambda x.x) (lambda x.x) (lambda x.x) (lambda x.x)
in
diff $res - << out
lambda x.x
out

echo "test case 7"
./lambda > $res << in
(lambda x.x) ((lambda x.x) (lambda x.x)) (lambda x.x)
in
diff $res - << out
lambda x.x
out

echo "test case 8"
./lambda > $res << in
(lambda x.lambda y.lambda z.lambda w.x y z w) (lambda a.a) (lambda b.b)
in
diff $res - << out
lambda z.lambda w.(lambda a.a) (lambda b.b) z w
out

