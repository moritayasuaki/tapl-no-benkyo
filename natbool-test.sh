#!/bin/sh -e
res=$(mktemp)

echo "test case 1"
./natbool > $res << in
iszero(0)
in
diff $res - << out
true
out

echo "test case 2"
./natbool > $res << in
iszero(succ(0))
in
diff $res - << out
false
out

echo "test case 3"
./natbool > $res << in 
pred(succ(0))
in
diff $res - << out
0
out

echo "test case 4"
./natbool > $res << in
if true then false else true
in
diff $res - << out
false
out

echo "test case 5"
./natbool > $res << in
if false then false else true
in
diff $res - << out
true
out

echo "test case 6"
./natbool > $res << in
if succ(iszero(pred(succ(0)))) then succ(true) else succ(false)
in
diff $res - << out
if succ(true) then succ(true) else succ(false)
out

echo "test case tapl-p26-1"
./natbool > $res << in
if true then true else (if false then false else false)
in
diff $res - << out
true
out
