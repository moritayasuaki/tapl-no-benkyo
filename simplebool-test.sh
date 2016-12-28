#!/bin/sh -e
res=`mktemp`
err=`mktemp`

./simplebool > $res << in
lambda x:Bool->Bool.lambda y:Bool.if x y then true else false
in
diff $res - << out
lambda x:Bool->Bool.lambda y:Bool.if x y then true else false
out

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

set +e
./simplebool 2> $err << in
if lambda x:Bool.x then true else false
in
diff $err - << err
guard of conditional not a boolean types
err

./simplebool 2> $err << in
lambda x:Bool->Bool. x x
in
diff $err - << err
parameter type mismatch
err

./simplebool 2> $err << in
lambda x:Bool.lambda y:Bool->Bool.x y
in
diff $err - << err
arrow type expected
err

./simplebool 2> $err << in
lambda x:Bool.lambda y:Bool->Bool.x y
in
diff $err - << err
arrow type expected
err

./simplebool 2> $err << in
if true then lambda x:Bool->Bool.x else true
in
diff $err - << err
arms of conditional have different types
err

