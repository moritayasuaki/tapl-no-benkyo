#!/bin/sh -e
res=$(mktemp)

./letint > $res << EOS
(lambda x . lambda y . x y) lambda z . z
EOS
diff $res - << EOS
lambda y.(lambda z.z) y
EOS

./letint > $res << EOS
lambda x.lambda y.lambda z.x y z
EOS
diff $res - << EOS
lambda x.lambda y.lambda z.x y z
EOS

./letint > $res << EOS
lambda x.lambda y.lambda z.x (y z)
EOS
diff $res - << EOS
lambda x.lambda y.lambda z.x (y z)
EOS

./letint > $res << EOS
lambda x.lambda y.lambda z.lambda w.x (y (z w))
EOS
diff $res - << EOS
lambda x.lambda y.lambda z.lambda w.x (y (z w))
EOS

./letint > $res << EOS
lambda x.lambda y.lambda z.lambda w.x y z w
EOS
diff $res - << EOS
lambda x.lambda y.lambda z.lambda w.x y z w
EOS

./letint > $res << EOS
(lambda x.x) (lambda x.x) (lambda x.x) (lambda x.x)
EOS
diff $res - << EOS
lambda x.x
EOS

./letint > $res << EOS
(lambda x.x) ((lambda x.x) (lambda x.x)) (lambda x.x)
EOS
diff $res - << EOS
lambda x.x
EOS

./letint > $res << EOS
(lambda x.lambda y.lambda z.lambda w.x y z w) (lambda a.a) (lambda b.b)
EOS
diff $res - << EOS
lambda z.lambda w.(lambda a.a) (lambda b.b) z w
EOS

id="lambda x.x"
tru="lambda t.lambda f.t"
fls="lambda t.lambda f.f"
tst="lambda l.lambda m.lambda n.l m n"
and="lambda b.lambda c.b c $fls"
pair="lambda f.lambda s.lambda b.b f s"
fst="lambda p.p $tru"
snd="lambda p.p $fls"
c0="lambda s.lambda z.z"
c1="lambda s.lambda z.s z"
c2="lambda s.lambda z.s s z"
scc="lambda n.lambda s.lambda z.s (n s z)"
omega="(lambda x.x x) lambda x.x x"
fix="lambda f.(lambda x.f (lambda y.x x y)) lambda x.f (lambda x x y)"

./letint > $res << EOS
let tst = lambda l.lambda m.lambda n.l m n in
let tru = lambda t.lambda f.t in
tst tru (lambda then.then) lambda else.else
EOS
diff $res - << EOS
lambda then.then
EOS

./letint > $res << EOS
let tst = lambda l.lambda m.lambda n.l m n in
let fls = lambda t.lambda f.f in
tst fls (lambda then.then) lambda else.else
EOS
diff $res - << EOS
lambda else.else
EOS

./letint > $res - << EOS
let fls = lambda t.lambda f.f in
let tru = lambda t.lambda f.t in
let and = lambda b.lambda c.b c fls in
and tru tru
EOS
diff $res - << EOS
$tru
EOS

./letint > $res - << EOS
let fls = lambda t.lambda f.f in
let tru = lambda t.lambda f.t in
let and = lambda b.lambda c.b c fls in
and tru fls
EOS
diff $res - << EOS
$fls
EOS


./letint > $res - << EOS
let scc = lambda n.lambda s.lambda z.s (n s z) in
let c1 = lambda s.lambda z.s z in
scc c1
EOS
diff $res - << EOS
lambda s.lambda z.s ((lambda s.lambda z.s z) s z)
EOS

./letint > $res - << EOS
let id = lambda x.x in
id id
EOS
diff $res - << EOS
$id
EOS

