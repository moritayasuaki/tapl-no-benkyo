#!/bin/sh -e
res=$(mktemp)

./natbool > $res << in
iszero(0)
in
diff $res - << out
true
out

./natbool > $res << in
iszero(succ(0))
in
diff $res - << out
false
out

./natbool > $res << in 
pred(succ(0))
in
diff $res - << out
0
out

./natbool > $res << in
if true then false else true
in
diff $res - << out
false
out

./natbool > $res << in
if false then false else true
in
diff $res - << out
true
out

./natbool > $res << in
if succ(iszero(pred(succ(0)))) then succ(true) else succ(false)
in
diff $res - << out
if succ(true) then succ(true) else succ(false)
out

./natbool > $res << in
if true then true else (if false then false else false)
in
diff $res - << out
true
out
