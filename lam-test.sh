#!/bin/sh
res=`mktemp`

./lam << in > $res
(lambda x . lambda y . x y) lambda z . z
in

diff $res - << out
lambda y.(lambda z.z) y
out
