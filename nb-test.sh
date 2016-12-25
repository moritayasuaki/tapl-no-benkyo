#!/bin/sh
res=`mktemp`

./nb << in > $res
(iszero 0)
in

diff $res - << out
true
out

./nb << in > $res
iszero(succ(0))
in

diff $res - << out
false
out

