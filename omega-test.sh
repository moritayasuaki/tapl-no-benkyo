#!/bin/sh -e
res=$(mktemp)

./omega > $res << EOS
lambda X. lambda x:X.x
EOS
diff $res - << EOS
lambda X. lambda x:X.x
EOS
