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

id="(lambda x.x)"
tru="(lambda t.lambda f. t)"
fls="(lambda t.lambda f. f)"
tst="(lambda l.lambda m.lambda n. l m n)"
and="(lambda b. lambda c. b c $fls)"
pair="(lambda f. lambda s. lambda b. b f s)"
fst="(lambda p. p $tru)"
snd="(lambda p. p $fls)"
c0="(lambda s.lambda z. z)"
c1="(lambda s.lambda z. s z)"
c2="(lambda s.lambda z. s (s z))"
scc="(lambda n. lambda s. lambda z. s (n s z))"
omega="((lambda x. x x) (lambda x. x x))"
fix="(lambda f. (lambda x f (lambda y. x x y)) (lambda x. f (lambda x x y)))"

echo "test case 9"
./lambda > $res << in
($tst) ($tru) (lambda then.then) (lambda else.else)
in
diff $res - << out
lambda then.then
out

echo "test case 10"
./lambda > $res << in
$tst $fls (lambda then.then) (lambda else.else)
in
diff $res - << out
lambda else.else
out

echo "test case 11"
./lambda > $res - << in
$and  $tru $tru
in
diff $res - << out
lambda t.lambda f.t
out

echo "test case 12"
./lambda > $res - << in
$and $tru $fls
in
diff $res - << out
lambda t.lambda f.f
out

echo "test case 13"
./lambda > $res - << in
$scc $c1
in
diff $res - << out
lambda s.lambda z.s ((lambda s.lambda z.s z) s z)
out
