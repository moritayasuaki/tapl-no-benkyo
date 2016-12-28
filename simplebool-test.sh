#!/bin/sh -e
res=`mktemp`

./simplebool > $res << in
lambda x:Bool->Bool.lambda y:Bool.if x y then true else false
in

./simplebool > $res << in
if true then false else false
in
diff $res - << out
false
out

./simplebool > $res << in
lambda x:Bool->Bool.x
in
diff $res - << out
lambda x:Bool->Bool.x
out


set -ne
./simplebool << in
if lambda x:Bool.x then true else false
in
