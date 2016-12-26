#!/bin/sh -e
res=`mktemp`

echo "test case 1"
./nb > $res << in
iszero(0)
in
diff $res - << out
true
out

echo "test case 2"
./nb > $res << in
iszero(succ(0))
in
diff $res - << out
false
out

echo "test case 3"
./nb > $res << in 
pred(succ(0))
in
diff $res - << out
0
out

echo "test case 4"
./nb > $res << in
if true then false else true
in
diff $res - << out
false
out

echo "test case 5"
./nb > $res << in
if false then false else true
in
diff $res - << out
true
out

echo "test case 6"
./nb > $res << in
if succ(iszero(pred(succ(0)))) then succ(true) else succ(false)
in
diff $res - << out
if succ(true) then succ(true) else succ(false)
out

